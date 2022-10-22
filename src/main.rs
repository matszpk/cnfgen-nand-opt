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
use exec_sat::{exec_sat_simple, parse_sat_output, SatOutput};
use serde_derive::Deserialize;
use std::env;
use std::fs::File;
use std::io::{self, BufReader, Read};

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
    #[error("CNF error: {0}")]
    CNFError(#[from] CNFError),
    #[error("ExecSAT error: {0}")]
    ExecSATError(#[from] exec_sat::Error),
    #[error("Solution is not correct")]
    SolNotCorrect,
    #[error("Solution data is not correct")]
    SolDataNotCorrect,
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
    gate_num_for_layers: Vec<UDynExprNode<isize>>,
    gates_input: Vec<Vec<UDynExprNode<isize>>>,
    output: Vec<UDynExprNode<isize>>,
}

fn generate_formulae(problem: &Problem) -> Result<GenSolution, Error> {
    let creator = ExprCreator::<isize>::new();

    if problem.table.is_empty() {
        return Err(Error::EmptyTable);
    }

    if problem.layers == 0 {
        return Err(Error::NoLayers);
    }

    let value_bits = (u64::BITS - problem.table.iter().max().unwrap().leading_zeros()) as usize;
    let index_bits = calc_log_2(problem.table.len());
    let gate_num_bits = (usize::BITS - problem.max_gates.leading_zeros()) as usize;

    let mut max_gates_per_layer = vec![std::cmp::min(problem.max_gates, value_bits)];
    for i in 0..(problem.layers - 1) {
        max_gates_per_layer.push(std::cmp::min(
            problem.max_gates,
            max_gates_per_layer[i] << 1,
        ));
    }
    max_gates_per_layer.reverse();
    // reduce from from inputs
    {
        let mut max_inputs = index_bits;
        for mgpl in max_gates_per_layer.iter_mut() {
            // includes: all pairs of inputs and same gates with this same inputs
            // n*(n-1)/2 + n, where n is max_inputs.
            let max_gates = ((max_inputs * (max_inputs - 1)) >> 1) + max_inputs;
            if max_gates < *mgpl {
                *mgpl = max_gates;
                max_inputs += max_gates;
            } else {
                break;
            }
        }
    }

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

    // eprintln!(
    //     "{:?} {:?} {:?}",
    //     max_gates_per_layer, max_input_indexes, mii_bits
    // );

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

    let mut conds = conds;
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

    // helper to generate conditions for indexes of input or outputs
    let mut gen_conditions = |inputs: &[UDynExprNode<isize>], l: usize| {
        for li in inputs {
            // set up conditions for indexes of input from previous layers
            let lrange_end =
                UDynExprNode::try_from_n(index_input_ends[0].clone(), mii_bits[l]).unwrap();
            let mut li_range_cond = li.clone().less_equal(lrange_end);
            for ll in 1..=l {
                let lrange_start = UDynExprNode::try_constant_n(
                    creator.clone(),
                    mii_bits[l],
                    index_input_starts[ll],
                )
                .unwrap();
                let lrange_end =
                    UDynExprNode::try_from_n(index_input_ends[ll].clone(), mii_bits[l]).unwrap();
                li_range_cond |=
                    li.clone().greater_equal(lrange_start) & li.clone().less_equal(lrange_end);
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
        .map(|_| UDynExprNode::variable(creator.clone(), *mii_bits.last().unwrap()))
        .collect::<Vec<_>>();
    gen_conditions(&outputs, problem.layers);

    for (idx, value) in problem.table.iter().enumerate() {
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

            // generate outputs and put to all_inputs
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

        conds &= output
            .equal(UDynExprNode::try_constant_n(creator.clone(), value_bits, *value).unwrap());
    }

    Ok(GenSolution {
        expr: conds,
        gate_num_for_layers,
        gates_input: all_layer_inputs,
        output: outputs,
    })
}

struct Solution {
    gate_num_for_layers: Vec<usize>,
    gates_input: Vec<Vec<usize>>,
    output: Vec<usize>,
}

fn get_value_from_dynintexpr_node(intnode: &UDynExprNode<isize>, assignment: &[bool]) -> usize {
    (0..intnode.len())
        .into_iter()
        .map(|i| {
            let varlit = intnode.bit(i).varlit().unwrap();
            usize::from(assignment[varlit.checked_abs().unwrap() as usize] ^ (varlit < 0)) << i
        })
        .sum()
}

fn get_solution(gen: &GenSolution, assignment: &[bool]) -> Solution {
    Solution {
        gate_num_for_layers: gen
            .gate_num_for_layers
            .iter()
            .map(|x| get_value_from_dynintexpr_node(x, assignment))
            .collect::<Vec<_>>(),
        gates_input: gen
            .gates_input
            .iter()
            .map(|v| {
                v.iter()
                    .map(|x| get_value_from_dynintexpr_node(x, assignment))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>(),
        output: gen
            .output
            .iter()
            .map(|x| get_value_from_dynintexpr_node(x, assignment))
            .collect::<Vec<_>>(),
    }
}

fn check_layer_and_input_id(sol: &Solution, index_bits: usize, input: usize) -> bool {
    if input < index_bits {
        true
    } else {
        let mut input = input - index_bits;
        for gi in &sol.gates_input {
            if input < (gi.len() >> 1) {
                return true;
            } else if input >= (gi.len() >> 1) {
                input -= gi.len() >> 1;
            } else {
                return false;
            }
        }
        false
    }
}

// check data of solution - inputs and outputs
fn check_data_of_solution(sol: &Solution, index_bits: usize) -> bool {
    for (i, l) in sol.gates_input.iter().enumerate() {
        for ii in l.iter().take(sol.gate_num_for_layers[i] << 1) {
            if !check_layer_and_input_id(sol, index_bits, *ii) {
                return false;
            }
        }
    }
    for ii in &sol.output {
        if !check_layer_and_input_id(sol, index_bits, *ii) {
            return false;
        }
    }
    true
}

fn get_layer_and_input_id(sol: &Solution, index_bits: usize, input: usize) -> (usize, usize) {
    if input < index_bits {
        return (0, input);
    }
    let mut input = input - index_bits;
    for (l, gi) in sol.gates_input.iter().enumerate() {
        if input < (gi.len() >> 1) {
            return (l + 1, input);
        } else {
            input -= gi.len() >> 1;
        }
    }
    (sol.gates_input.len(), input)
}

fn print_solution(sol: &Solution, index_bits: usize) {
    println!("Gate number for layers: {:?}", sol.gate_num_for_layers);
    for (i, l) in sol.gates_input.iter().enumerate() {
        println!("Layer {}:", i + 1);
        for ii in l.iter().take(sol.gate_num_for_layers[i] << 1) {
            println!(
                "  {:?} {}",
                get_layer_and_input_id(sol, index_bits, *ii),
                *ii
            );
        }
    }
    println!("Output:");
    for ii in &sol.output {
        println!(
            "  {:?} {}",
            get_layer_and_input_id(sol, index_bits, *ii),
            *ii
        );
    }
}

fn check_solution(sol: &Solution, problem: &Problem) -> bool {
    let index_bits = calc_log_2(problem.table.len());
    let mut max_input_indexes = vec![index_bits];
    for i in 0..problem.layers {
        max_input_indexes.push(max_input_indexes[i] + (sol.gates_input[i].len() >> 1));
    }

    let mut gates_output = vec![false; *max_input_indexes.last().unwrap()];
    for (index, value) in problem.table.iter().enumerate() {
        gates_output.fill(false);
        // first input is index
        for i in 0..index_bits {
            gates_output[i] = (index & (1 << i)) != 0;
        }

        // evaluate all outputs
        for (l, layer_inputs) in sol.gates_input.iter().enumerate() {
            let start_index = max_input_indexes[l];
            for i in 0..(sol.gates_input[l].len() >> 1) {
                let a = gates_output[layer_inputs[i << 1]];
                let b = gates_output[layer_inputs[(i << 1) + 1]];
                gates_output[start_index + i] = match problem.gate {
                    GateType::Nand => !(a & b),
                    GateType::Nor => !(a | b),
                };
            }
        }

        // convert to number
        let exp_value: u64 = sol
            .output
            .iter()
            .enumerate()
            .map(|(i, x)| u64::from(gates_output[*x]) << i)
            .sum();
        if exp_value != *value {
            return false;
        }
    }
    true
}

fn check_from_sat_output(
    sat_output: SatOutput,
    gen: &GenSolution,
    problem: &Problem,
) -> Result<(), Error> {
    match sat_output {
        SatOutput::Satisfiable(Some(assignment)) => {
            let sol = get_solution(gen, &assignment);
            let index_bits = calc_log_2(problem.table.len());
            if !check_data_of_solution(&sol, index_bits) {
                println!("Data verification: Input indexes are incorrect.");
                return Err(Error::SolDataNotCorrect);
            }
            print_solution(&sol, index_bits);
            if check_solution(&sol, problem) {
                println!("Verification: Solution is correct.");
            } else {
                println!("Verification: Solution is incorrect!");
                return Err(Error::SolNotCorrect);
            }
        }
        SatOutput::Satisfiable(None) => {
            println!("Satisfiable but assignment is unknown");
        }
        SatOutput::Unsatisfiable => {
            println!("Unsatisfiable");
        }
        SatOutput::Unknown => {
            println!("Unknown state");
        }
    }
    Ok(())
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
                let gen_sol = generate_formulae(&problem)?;
                gen_sol.expr.write(&mut CNFWriter::new(io::stdout()))?;
            }
            "execute" => {
                let problem = if let Some(problem_path) = problem_path {
                    read_problem(File::open(problem_path)?)?
                } else {
                    read_problem(io::stdin())?
                };
                let gen_sol = generate_formulae(&problem)?;
                let output = vec![];
                let mut writer = CNFWriter::new(output);
                gen_sol.expr.write(&mut writer)?;
                let sat_output = exec_sat_simple(
                    env::var("SAT_SOLVER").expect("SAT_SOLVER not set"),
                    writer.inner().as_slice(),
                )?;
                return check_from_sat_output(sat_output, &gen_sol, &problem);
            }
            "check" => {
                let sat_output = args.next();
                let (problem, sat_output) = if let Some(sat_output) = sat_output {
                    (
                        read_problem(File::open(problem_path.unwrap())?)?,
                        sat_output,
                    )
                } else {
                    // treat first argument as sat output
                    (read_problem(io::stdin())?, problem_path.unwrap())
                };
                let gen_sol = generate_formulae(&problem)?;
                let sat_output = File::open(sat_output)?;
                let sat_output = parse_sat_output(BufReader::new(sat_output))?;
                return check_from_sat_output(sat_output, &gen_sol, &problem);
            }
            "help" | "-h" | "--help" => {
                println!(
                    r##"Usage: cnfgen-nand-opt generate|execute|check [FILE] [SAT-OUTPUT]

This program can generate CNF (Conjunctive Normal Form) to check possibility to build
circuit built on NAND or NOR gates that returns given values from table.

This program can read problem from file. If no given file then program read problem
from standard input.

List of commands:
generate    - Generate CNF file and print it to standard output.
execute     - Generate CNF file and pass it to SAT solver, check and print results.
              SAT_SOLVER environment variable must be set to path to SAT solver executable.
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
