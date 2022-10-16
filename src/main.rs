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

use std::env;
use std::io::{self, Read};
use std::fs::File;
use serde::Deserializer;
use serde_derive::Deserialize;
use cnfgen::boolexpr::*;
use cnfgen::dynintexpr::*;
use cnfgen::writer::*;
use exec_sat::*;

#[derive(thiserror::Error, Debug)]
enum Error {
    #[error("Empty table")]
    EmptyTable,
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
    
    let value_bits = u64::BITS - problem.table.iter().max()
            .unwrap().leading_zeros();
    let index_bits = calc_log_2(problem.table.len());
    let gate_num_bits = calc_log_2(problem.max_gates);
    
    let gate_num_for_layers = (0..(problem.layers * gate_num_bits)).into_iter().map(|i|
            UDynExprNode::variable(creator.clone(), gate_num_bits));
    
    //(0..(index_bits * problem.gates)).into_iter()
      //      .map(|i| UDynExprNode::variable(creator.clone(), index_bits);
    
    println!("Debug problem: {:?}", problem);
    println!("Value bits: {}, Index bits: {}", value_bits, index_bits);
    
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
                    (read_problem(File::open(problem_path.unwrap())?)?, sat_output)
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
