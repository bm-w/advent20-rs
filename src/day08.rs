// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy)]
enum Op { Acc, Jmp, Nop }

#[cfg_attr(test, derive(Debug))]
struct Instr(Op, i32);

trait Program: AsRef<[Instr]> {
	/// Returns `Ok(acc)` if executed successfully, or
	/// `Err(instrs_executed, acc)` if an infinite loop is detected.
	fn execute(&self) -> Result<i32, (Vec<usize>, i32)> {
		let mut acc = 0;
		let mut i = 0;
		let mut prev_i = Vec::new();
		loop {
			let jmp = match &self.as_ref()[i] {
				Instr(Op::Acc, arg) => { acc += *arg; 1 }
				Instr(Op::Jmp, arg) => *arg,
				Instr(Op::Nop, _) => 1
			};
			i = (i as i32 + jmp) as usize;
			if i >= self.as_ref().len() { return Ok(acc) }
			else if prev_i.contains(&i) { return Err((prev_i, acc)) }
			prev_i.push(i);
		}
	}
}

impl Program for &[Instr] {}



fn input_instrs_from_str(s: &str) -> Vec<Instr> {
	parsing::try_instrs_from_str(s).unwrap()
}

fn input_instrs() -> Vec<Instr> {
	input_instrs_from_str(include_str!("day08.txt"))
}


fn part1_impl(input_instrs: &[Instr]) -> i32 {
	input_instrs.execute().unwrap_err().1
}

pub(crate) fn part1() -> i32 {
	part1_impl(&input_instrs())
}


fn part2_impl(input_instrs: &mut [Instr]) -> i32 {
	for i in (&*input_instrs).execute().unwrap_err().0 {
		let orig_op = input_instrs[i].0;
		match orig_op {
			Op::Acc => continue,
			Op::Jmp => input_instrs[i].0 = Op::Nop,
			Op::Nop => input_instrs[i].0 = Op::Jmp,
		}
		if let Ok(acc) = (&*input_instrs).execute() {
			return acc
		} else {
			input_instrs[i].0 = orig_op;
		}
	}
	unreachable!()
}

pub(crate) fn part2() -> i32 {
	part2_impl(&mut input_instrs())
}


mod parsing {
	use std::{num::ParseIntError, str::FromStr};
	use super::{Op, Instr};

	#[derive(Debug)]
	pub(super) struct InvalidOpError(String);

	impl FromStr for Op {
		type Err = InvalidOpError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			match s {
				"acc" => Ok(Op::Acc),
				"jmp" => Ok(Op::Jmp),
				"nop" => Ok(Op::Nop),
				found => Err(InvalidOpError(found.to_owned()))
			}
		}
	}

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum InstrError {
		InvalidFormat,
		InvalidOp(InvalidOpError),
		InvalidArg(ParseIntError),
	}

	impl FromStr for Instr {
		type Err = InstrError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use InstrError::*;
			let (op, arg) = s.split_once(' ')
				.ok_or(InvalidFormat)?;
			let op = op.parse().map_err(InvalidOp)?;
			let arg = arg.parse().map_err(InvalidArg)?;
			Ok(Instr(op, arg))
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct InstrsError { line: usize, source: InstrError }

	pub(super) fn try_instrs_from_str(s: &str) -> Result<Vec<Instr>, InstrsError> {
		s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| InstrsError { line: l + 1, source: e }))
			.collect()
	}


	#[test]
	fn op() {
		assert!(matches!("".parse::<Op>(), Err(InvalidOpError(found)) if found.is_empty()));
		assert!(matches!("x".parse::<Op>(), Err(InvalidOpError(found)) if found == "x"));
		assert!(matches!("acc".parse::<Op>(), Ok(_)));
	}

	#[test]
	fn instr() {
		use InstrError::*;
		assert!(matches!("".parse::<Instr>(), Err(InvalidFormat)));
		assert!(matches!("x y".parse::<Instr>(), Err(InvalidOp(_))));
		assert!(matches!("acc y".parse::<Instr>(), Err(InvalidArg(_))));
		assert!(matches!("jmp -1337".parse::<Instr>(), Ok(Instr(Op::Jmp, -1337))));
	}

	#[test]
	fn instrs() -> Result<(), InstrsError> {
		try_instrs_from_str(super::TEST_INPUT).map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUT: &str = indoc::indoc! { "
	nop +0
	acc +1
	jmp +4
	acc +3
	jmp -3
	acc -99
	acc +1
	jmp -4
	acc +6
" };

#[test]
fn tests() {
	assert_eq!(part1_impl(&input_instrs_from_str(TEST_INPUT)), 5);
	assert_eq!(part1(), 1394);
	assert_eq!(part2_impl(&mut input_instrs_from_str(TEST_INPUT)), 8);
	assert_eq!(part2(), 1626);
}
