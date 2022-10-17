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

    let value_bits = (u64::BITS - problem.table.iter().max().unwrap().leading_zeros()) as usize;
    let index_bits = calc_log_2(problem.table.len());
    let index_bits_bits = calc_log_2(index_bits);
    let gate_num_bits = (usize::BITS - problem.max_gates.leading_zeros()) as usize;
    let input_num_bits = calc_log_2(problem.max_gates + index_bits);

    let mut max_gates_per_layer = vec![std::cmp::min(problem.max_gates, value_bits)];
    for i in 0..(problem.layers - 1) {
        max_gates_per_layer.push(std::cmp::min(
            problem.max_gates,
            max_gates_per_layer[i] << 1,
        ));
    }
    max_gates_per_layer.reverse();
    let mgpl_bits = max_gates_per_layer
        .iter()
        .map(|x| calc_log_2(*x))
        .collect::<Vec<_>>();

    let mut max_input_indexes = vec![index_bits];
    for i in &max_gates_per_layer {
        max_input_indexes.push(max_input_indexes.last().unwrap() + i);
    }
    let mii_bits = max_input_indexes
        .iter()
        .map(|x| calc_log_2(*x))
        .collect::<Vec<_>>();

    println!(
        "{:?} {:?} {:?}",
        max_gates_per_layer, max_input_indexes, mii_bits
    );

    let gate_num_for_layers = (0..problem.layers)
        .into_iter()
        .map(|i| UDynExprNode::variable(creator.clone(), mgpl_bits[i]))
        .collect::<Vec<_>>();

    let mut conds = BoolExprNode::single_value(creator.clone(), true);
    for (i, val) in gate_num_for_layers.iter().enumerate() {
        conds &= val.clone().less_equal(
            UDynExprNode::try_constant_n(creator.clone(), mgpl_bits[i], max_gates_per_layer[i] - 1)
                .unwrap(),
        );
    }

    // generate sum of number gates for layers
    let first_gate_num_for_layers =
        UDynExprNode::try_from_n(gate_num_for_layers.first().unwrap().clone(), gate_num_bits)
            .unwrap();
    let (num, conds) = gate_num_for_layers.iter().skip(1).fold(
        (first_gate_num_for_layers, conds),
        |(last_num, last_cond), num| {
            let num = UDynExprNode::try_from_n(num.clone(), gate_num_bits).unwrap();
            let (new_num, new_cond) = last_num.cond_add(num);
            (new_num, last_cond & new_cond)
        },
    );
    let conds = conds
        & num.less_equal(
            UDynExprNode::try_constant_n(creator.clone(), gate_num_bits, problem.max_gates)
                .unwrap(),
        );

    let mut index_input_starts = vec![0];
    index_input_starts.extend(max_input_indexes);

    // bits of index_input_ranges values: mii_bits[i]
    let mut index_input_ends =
        vec![UDynExprNode::try_constant_n(creator.clone(), mii_bits[0], index_bits - 1).unwrap()];

    for i in 0..problem.layers {
        let start_range = UDynExprNode::try_constant_n(
            creator.clone(),
            mii_bits[i + 1],
            // for start...=max - we must subtract 1
            index_input_starts[i + 1] - 1,
        )
        .unwrap();
        let gate_num_val =
            UDynExprNode::try_from_n(gate_num_for_layers[i].clone(), mii_bits[i + 1]).unwrap();
        // NG(N) + I0+GMAx0+GMax1 ... GMax(N-1)-1
        index_input_ends.push(start_range.mod_add(gate_num_val));
    }

    // create indexes of input layers
    let mut all_layer_inputs = vec![];
    let mut conds = conds;

    // helper to generate conditions for indexes of input or outputs
    let mut gen_conditions = |inputs: &[UDynExprNode<isize>], l: usize| {
        for li in inputs {
            // set up conditions for indexes of input from previous layers
            let lrange_end =
                UDynExprNode::try_from_n(index_input_ends[0].clone(), mii_bits[l]).unwrap();
            let mut li_range_cond = li.clone().less_equal(lrange_end);
            for ll in 1..l {
                let lrange_start = UDynExprNode::try_constant_n(
                    creator.clone(),
                    mii_bits[l],
                    index_input_starts[ll].clone(),
                )
                .unwrap();
                let lrange_end =
                    UDynExprNode::try_from_n(index_input_ends[l].clone(), mii_bits[l]).unwrap();
                li_range_cond |=
                    (li.clone().greater_equal(lrange_start) & li.clone().less_equal(lrange_end));
            }
            conds &= li_range_cond;
        }
    };

    for l in 0..problem.layers {
        let layer_inputs = (0..(max_gates_per_layer[l] << 1))
            .into_iter()
            .map(|_| UDynExprNode::variable(creator.clone(), mii_bits[l]))
            .collect::<Vec<_>>();
        // start from input of layer 0 - indexes
        gen_conditions(&layer_inputs, l);
        all_layer_inputs.push(layer_inputs);
    }

    // indexes of output layer
    let outputs = (0..*max_gates_per_layer.last().unwrap())
        .into_iter()
        .map(|i| UDynExprNode::variable(creator.clone(), *mii_bits.last().unwrap()))
        .collect::<Vec<_>>();
    gen_conditions(&outputs, problem.layers);

    //
    // println!("Debug problem: {:?}", problem);
    // println!("Value bits: {}, Index bits: {}", value_bits, index_bits);

    for (idx, value) in problem.table.into_iter().enumerate() {
        let mut all_inputs = (0..index_bits)
            .into_iter()
            .map(|i| {
                UDynExprNode::try_constant_n(creator.clone(), 1, u8::from(idx & (1 << i) != 0))
                    .unwrap()
            })
            .collect::<Vec<_>>();

        let mut gen_gates = |layer_inputs: &[UDynExprNode<isize>], l: usize| {
            let mut input_table = all_inputs.clone();
            // extend for dynint_table - rest is false
            input_table.extend(
                (0..((1 << mii_bits[l]) - all_inputs.len()))
                    .into_iter()
                    .map(|_| UDynExprNode::try_constant_n(creator.clone(), 1, 0u8).unwrap())
                    .collect::<Vec<_>>(),
            );

            for i in 0..max_gates_per_layer[l] {
                let aval = dynint_table(layer_inputs[(i << 1)].clone(), input_table.clone()).bit(0);
                let bval =
                    dynint_table(layer_inputs[(i << 1) + 1].clone(), input_table.clone()).bit(0);
                all_inputs.push(UDynExprNode::from_boolexprs([match problem.gate {
                    GateType::Nand => !(aval & bval),
                    GateType::Nor => !(aval | bval),
                }]));
            }
        };

        for l in 0..problem.layers {
            gen_gates(&all_layer_inputs[l], l);
        }
        // output
        let mut input_table = all_inputs.clone();
        // extend for dynint_table - rest is false
        input_table.extend(
            (0..((1 << *mii_bits.last().unwrap()) - all_inputs.len()))
                .into_iter()
                .map(|_| UDynExprNode::try_constant_n(creator.clone(), 1, 0u8).unwrap())
                .collect::<Vec<_>>(),
        );
        let output = UDynExprNode::from_boolexprs(
            (0..value_bits)
                .into_iter()
                .map(|i| dynint_table(outputs[i].clone(), input_table.clone()).bit(0)),
        );

        conds &=
            output.equal(UDynExprNode::try_constant_n(creator.clone(), value_bits, value).unwrap());
    }

    Ok(GenSolution {
        expr: conds,
        gates_input: all_layer_inputs
            .iter()
            .flatten()
            .cloned()
            .collect::<Vec<_>>(),
        output: outputs,
    })
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
