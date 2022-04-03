// Copyright (c) 2022 Bastiaan Marinus van de Weerd



const MASK_LEN: usize = 36;


/// Mask of length {MASK_LEN} and format `XX1XX0XX1XX…X1X0` where `ones`
/// specifies the positions of the ones (and zeros; i.e. the 1s in the binary
/// representation of `ones` correspond to 1s in the mask) and `x_es` the
/// positions of the X-es (i.e. 1s correspond to X-es). I.e. (pseudo-code):
/// ```
/// match (bits!(ones)[i], bits!(x_es)[i]) {
///     (1, 0) => '1',
///     (0, 0) => '0',
///     (_, 1) => 'X',
/// }
/// ```
#[cfg_attr(test, derive(Debug))]
#[derive(Default, PartialEq, Eq, Clone, Copy)]
struct Mask {
	ones: u64,
	x_es: u64,
}

enum Instr {
	SetMask(Mask),
	WriteVal { addr: usize, val: u64 },
}

impl Mask {
	fn value_v1(&self, val: u64) -> u64 {
		val & self.x_es | self.ones
	}

	fn addr_mask_v2(&self, addr: usize) -> Mask {
		Mask { ones: self.ones | (addr as u64 & !self.x_es), ..*self }
	}

	fn addresses_v2(&self) -> impl Iterator<Item = usize> + '_ {
		let tos = (0..MASK_LEN as u8)
			.map(|i| MASK_LEN as u8 - 1 - i)
			.filter(|shift| self.x_es & 1 << shift != 0)
			.collect::<Vec<_>>();
		let len = tos.len();
		(0..2usize.pow(len as u32))
			.map(move |i| tos.iter()
				.enumerate()
				.fold(self.ones as usize, |acc, (from_inv, &to)|
					acc + ((i & (1 << (len - from_inv - 1))) << (to as usize + 1 + from_inv - len))))
	}
}

use std::collections::HashMap;

trait Program: IntoIterator<Item = Instr> {
	fn execute_common<Item, Map, Extend>(self, map: Map, extend: Extend) -> u64
	where
		Self: Sized,
		Map: Fn(Mask, usize, u64) -> Item,
		Extend: Fn(&mut HashMap<usize, u64>, Item)
	{
		self.into_iter()
			.scan(Mask::default(), |accum_mask, instr| match instr {
				Instr::SetMask(mask) => { *accum_mask = mask; Some(None) }
				Instr::WriteVal { addr, val } => Some(Some(map(*accum_mask, addr, val)))
			})
			.flatten()
			.fold(HashMap::new(), |mut mem, item| {
				extend(&mut mem, item);
				mem
			})
			.values()
			.sum()
	}

	fn execute_v1(self) -> u64 where Self: Sized {
		self.execute_common(
			|mask, addr, val| (addr, mask.value_v1(val)),
			|mem, (addr, val)| { mem.insert(addr, val); })
	}

	/// Essentially brute-force, but it’s fast enough with the given input.
	fn execute_v2(self) -> u64 where Self: Sized {
		self.execute_common(
			|mask, addr, val| (mask.addr_mask_v2(addr), val),
			|mem, (addr_mask, val)| {
				mem.extend(addr_mask.addresses_v2().map(|addr| (addr, val))); })
	}
}

impl<I> Program for I where I: IntoIterator<Item = Instr> {}


fn input_instrs_from_str(s: &str) -> impl Iterator<Item = Instr> + '_ {
	parsing::instrs_from_str(s).map(|r| r.unwrap())
}

fn input_instrs() -> impl Iterator<Item = Instr> {
	input_instrs_from_str(include_str!("day14.txt"))
}


fn part1_impl(input_instrs: impl Iterator<Item = Instr>) -> u64 {
	input_instrs.execute_v1()
}

pub(crate) fn part1() -> u64 {
	part1_impl(input_instrs())
}


fn part2_impl(input_instrs: impl Iterator<Item = Instr>) -> u64 {
	input_instrs.execute_v2()
}

pub(crate) fn part2() -> u64 {
	part2_impl(input_instrs())
}


mod parsing {
	use std::{num::ParseIntError, str::FromStr};
	use itertools::Itertools;
	use super::{MASK_LEN, Mask, Instr};

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum MaskError {
		InvalidLen(usize),
		InvalidChar { column: usize, found: char }
	}

	impl FromStr for Mask {
		type Err = MaskError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use MaskError::*;
			if s.len() != MASK_LEN { return Err(InvalidLen(s.len())) }
			let (ones, x_es) = s.chars()
				.enumerate()
				.map(|(c, chr)| match chr {
					'1' | '0' | 'X' => Ok((c, chr)),
					found => Err(InvalidChar { column: c + 1, found }),
				})
				.fold_ok((0, 0), |(ones, x_es), (c, chr)| match chr {
					'1' => (ones + (0b1 << (MASK_LEN - 1 - c)), x_es),
					'X' => (ones, x_es + (0b1 << (MASK_LEN - 1 - c))),
					_ => (ones, x_es)
				})?;
			Ok(Mask { ones, x_es })
		}
	}

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum InstrError {
		InvalidFormat,
		InvalidOp(String),
		InvalidMask(MaskError),
		InvalidAddr(Option<ParseIntError>),
		InvalidVal(ParseIntError)	
	}

	impl FromStr for Instr {
		type Err = InstrError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use InstrError::*;
			let (op, arg) = s.split_once(" = ").ok_or(InvalidFormat)?;
			if op == "mask" {
				Ok(Instr::SetMask(arg.parse().map_err(InvalidMask)?))
			} else if let Some(addr) = op.strip_prefix("mem[") {
				let addr = addr.strip_suffix(']').ok_or(InvalidAddr(None))?
					.parse().map_err(|e| InvalidAddr(Some(e)))?;
				let val = arg.parse().map_err(InvalidVal)?;
				Ok(Instr::WriteVal { addr, val })
			} else {
				Err(InvalidOp(op.to_owned()))
			}
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct InstrsError { line: usize, source: InstrError }

	pub(super) fn instrs_from_str(s: &str) -> impl Iterator<Item = Result<Instr, InstrsError>> + '_ {
		s.lines().enumerate().map(|(l, line)| line.parse()
			.map_err(|e| InstrsError { line: l + 1, source: e }))
	}


	#[cfg(test)]
	const TEST_MASK: &str = "10X10X10X10X10X10X10X10X10X10X10X10X";

	#[test]
	fn mask() {
		use MaskError::*;
		assert!(matches!("10X".parse::<Mask>(), Err(InvalidLen(3))));
		assert!(matches!(TEST_MASK.replace('X', "x").parse::<Mask>(), Err(InvalidChar { column: 3, found: 'x' })));
		assert!(matches!(TEST_MASK.parse::<Mask>(),
			Ok(Mask { ones, x_es })
			if ones == 0b100100100100100100100100100100100100
			&& x_es == 0b001001001001001001001001001001001001));
	}

	#[test]
	fn instr() {
		use InstrError::*;
		assert!(matches!("".parse::<Instr>(), Err(InvalidFormat)));
		assert!(matches!("x".parse::<Instr>(), Err(InvalidFormat)));
		assert!(matches!("x = y".parse::<Instr>(), Err(InvalidOp(found)) if found == "x"));
		assert!(matches!("mask = x".parse::<Instr>(), Err(InvalidMask(_))));
		assert!(matches!("mask = 10X".parse::<Instr>(), Err(InvalidMask(_))));
		assert!(matches!(format!("mask = {TEST_MASK}").parse::<Instr>(), Ok(Instr::SetMask(_))));
		assert!(matches!("mem[x = y".parse::<Instr>(), Err(InvalidAddr(None))));
		assert!(matches!("mem[x] = y".parse::<Instr>(), Err(InvalidAddr(Some(_)))));
		assert!(matches!("mem[1337] = x".parse::<Instr>(), Err(InvalidVal(_))));
		assert!(matches!("mem[13] = 37".parse::<Instr>(), Ok(Instr::WriteVal { addr, val })
			if addr == 13 && val == 37));
	}

	#[test]
	fn instrs() -> Result<(), InstrsError> {
		instrs_from_str(super::TEST_INPUT_PART1).collect::<Result<Vec<_>, _>>().map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUT_PART1: &str = indoc::indoc! { "
	mask = XXXXXXXXXXXXXXXXXXXXXXXXXXXXX1XXXX0X
	mem[8] = 11
	mem[7] = 101
	mem[8] = 0
" };

#[cfg(test)]
const TEST_INPUT_PART2: &str = indoc::indoc! { "
	mask = 000000000000000000000000000000X1001X
	mem[42] = 100
	mask = 00000000000000000000000000000000X0XX
	mem[26] = 1
" };

#[test]
fn tests() {
	assert_eq!(part1_impl(input_instrs_from_str(TEST_INPUT_PART1)), 165);
	assert_eq!(part1(), 13105044880745);
	assert_eq!(part2_impl(input_instrs_from_str(TEST_INPUT_PART2)), 208);
	assert_eq!(part2(), 3505392154485);
}
