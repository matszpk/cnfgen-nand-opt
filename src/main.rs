// main.rs - cnfgen-nand-opt
//
// cnfgen-nand-opt - Check possibility to build NAND circuit that returns given values.
// Copyright (C) 2022  Mateusz Szpakowski
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License along with this library; if not, write to the Free Software
// Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

use cnfgen::boolexpr::*;
use cnfgen::dynintexpr::*;
use cnfgen::writer::*;
use exec_sat::*;
use serde::Deserializer;
use serde_derive::Deserialize;
use std::env;
use std::fs::File;
use std::io::{self, Read};

#[derive(thiserror::Error, Debug)]
enum Error {
    #[error("Empty table")]
    EmptyTable,
    #[error("No layers")]
    NoLayers,
    #[error("IO error: {0}")]
    IOError(#[from] io::Error),
    #[error("Problem parse error: {0}")]
    ParseError(#[from] toml::de::Error),
}

#[derive(Deserialize, Debug)]
enum GateType {
    Nand,
    Nor,
}

#[derive(Deserialize, Debug)]
struct Problem {
    pub gate: GateType,
    pub layers: usize,
    pub max_gates: usize,
    pub table: Vec<u64>,
}

fn read_problem(mut reader: impl Read) -> Result<Problem, Error> {
    let mut content = String::new();
    reader.read_to_string(&mut content)?;
    Ok(toml::from_str(&content)?)
}

const fn calc_log_2(n: usize) -> usize {
    let nbits = usize::BITS - n.leading_zeros();
    if (1 << (nbits - 1)) == n {
        (nbits - 1) as usize
    } else {
        nbits as usize
    }
}

struct GenSolution {
    expr: BoolExprNode<isize>,
    gates_input: Vec<UDynExprNode<isize>>,
    output: Vec<UDynExprNode<isize>>,
}

fn generate_cnf(problem: Problem) -> Result<GenSolution, Error> {
    let creator = ExprCreator::<isize>::new();

    if problem.table.is_empty() {
        return Err(Error::EmptyTable);
    }

    if problem.layers == 0 {
        return Err(Error::NoLayers);
    }

    let value_bits = u64::BITS - problem.table.iter().max().unwrap().leading_zeros();
    let index_bits = calc_log_2(problem.table.len());
    let index_bits_bits = calc_log_2(index_bits);
    let gate_num_bits = calc_log_2(problem.max_gates);
    let input_num_bits = calc_log_2(problem.max_gates + index_bits);

    let gate_num_for_layers = (0..problem.layers)
        .into_iter()
        .map(|i| UDynExprNode::variable(creator.clone(), gate_num_bits))
        .collect::<Vec<_>>();

    // generate sum of number gates for layers
    let first_gate_num_for_layers = gate_num_for_layers.first().unwrap().clone();
    let mut gnl_subsums = vec![first_gate_num_for_layers.clone()];
    let (num, conds) = gate_num_for_layers.into_iter().skip(1).fold(
        (
            first_gate_num_for_layers,
            BoolExprNode::single_value(creator.clone(), true),
        ),
        |(last_num, last_cond), num| {
            let (new_num, new_cond) = last_num.cond_add(num);
            gnl_subsums.push(UDynExprNode::try_from_n(new_num.clone(), input_num_bits).unwrap());
            (new_num, last_cond & new_cond)
        },
    );
    let conds = conds
        & num.less_equal(
            UDynExprNode::try_constant_n(creator.clone(), gate_num_bits, problem.max_gates)
                .unwrap(),
        );
    let gnl_total = gnl_subsums.pop().unwrap();

    let first_layer_inputs = (0..problem.max_gates)
        .into_iter()
        .map(|i| UDynExprNode::variable(creator.clone(), index_bits_bits))
        .collect::<Vec<_>>();

    // force index bit number for first input in range
    let max_index_bit =
        UDynExprNode::try_constant_n(creator.clone(), index_bits_bits, index_bits - 1).unwrap();
    let conds = first_layer_inputs.iter().fold(conds, |conds, input| {
        conds & input.clone().less_equal(max_index_bit.clone())
    });

    let next_layer_inputs = (0..(problem.max_gates * (problem.layers - 1)))
        .into_iter()
        .map(|i| UDynExprNode::variable(creator.clone(), input_num_bits))
        .collect::<Vec<_>>();

    let index_bits_val_m1 =
        UDynExprNode::try_constant_n(creator.clone(), input_num_bits, index_bits - 1).unwrap();
    let mut conds = conds.clone();
    let max_layer_inputs = gnl_subsums
        .into_iter()
        .map(|num| {
            let (out, new_cond) = num.cond_add(index_bits_val_m1.clone());
            conds &= new_cond;
            out
        })
        .collect::<Vec<_>>();

    // force next_layer_inputs in range 0..(index_bits+prev_layers_inputs)
    for i in 0..(problem.layers - 1) {
        conds = next_layer_inputs
            .iter()
            .skip(problem.max_gates * i)
            .take(problem.max_gates)
            .fold(conds, |conds, input| {
                conds & input.clone().less_equal(max_layer_inputs[i].clone())
            });
    }

    let outputs = (0..value_bits)
        .into_iter()
        .map(|i| UDynExprNode::variable(creator.clone(), input_num_bits))
        .collect::<Vec<_>>();

    let gnl_max_output = {
        let (out, new_cond) = gnl_total.cond_add(index_bits_val_m1.clone());
        conds &= new_cond;
        out
    };

    let conds = outputs.iter().fold(conds, |conds, input| {
        conds & input.clone().less_equal(gnl_max_output.clone())
    });

    println!("Debug problem: {:?}", problem);
    println!("Value bits: {}, Index bits: {}", value_bits, index_bits);

    for (idx, value) in problem.table.into_iter().enumerate() {}

    Err(io::Error::new(io::ErrorKind::Other, "oh no!").into())
}

fn main() -> Result<(), Error> {
    let mut args = env::args();
    args.next().unwrap();
    let command = args.next();
    let problem_path = args.next();

    if let Some(command) = command {
        match command.as_str() {
            "generate" => {
                let problem = if let Some(problem_path) = problem_path {
                    read_problem(File::open(problem_path)?)?
                } else {
                    read_problem(io::stdin())?
                };
                generate_cnf(problem)?;
            }
            "execute" => {
                let problem = if let Some(problem_path) = problem_path {
                    read_problem(File::open(problem_path)?)?
                } else {
                    read_problem(io::stdin())?
                };
            }
            "check" => {
                let sat_output = args.next();
                let (problem, sat_output) = if let Some(sat_output) = sat_output {
                    (
                        read_problem(File::open(problem_path.unwrap())?)?,
                        sat_output,
                    )
                } else {
                    (read_problem(io::stdin())?, problem_path.unwrap())
                };
            }
            "help" | "-h" | "--help" => {
                println!(
                    r##"cnfgen-nand-opt generate|execute|check [FILE] SAT-OUTPUT

This program can generate CNF (Conjunctive Normal Form) to check possibility to build
circuit built on NAND or NOR gates that returns given values from table.

This program can read problem from file. If no given file then program read problem
from standard input.

List of commands:
generate    - Generate CNF file and print it to standard output.
execute     - Generate CNF file and pass it to SAT solver, check and print results.
check       - Check and print results from SAT output. The SAT output file given as
              the second argument after command or the first FILE is not given.
help        - Print help.
"##
                );
            }
            _ => {
                println!(
                    "Unsupported command {} - please run with 'help' command.",
                    command
                );
            }
        }
    }
    Ok(())
}
