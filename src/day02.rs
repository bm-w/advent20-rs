// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::ops::RangeInclusive;


struct Policy {
	char: char,
	freq_range: RangeInclusive<u8>,
}

impl Policy {
	fn is_valid_password_part1(&self, password: &str) -> bool {
		let count = password.chars().filter(|c| *c == self.char).count();
		count <= u8::MAX as usize && self.freq_range.contains(&(count as u8))
	}

	fn is_valid_password_part2(&self, password: &str) -> bool {
		let n0 = *self.freq_range.start() as usize - 1;
		let n1 = *self.freq_range.end() as usize - n0 - 2;
		let mut chars = password.chars();
		match (chars.nth(n0), chars.nth(n1)) {
			(Some(c0), Some(c1)) => if c0 == self.char { c0 != c1 } else { c1 == self.char },
			_ => false,
		}
	}
}


fn input_entries_from_str(s: &str) -> Vec<(Policy, &str)> {
	parsing::try_entries_from_str(s).unwrap()
}

fn input_entries<'a>() -> Vec<(Policy, &'a str)> {
	input_entries_from_str(include_str!("day02.txt"))
}



fn part1_impl(input_entries: &[(Policy, &str)]) -> usize {
	input_entries.iter().filter(|(pol, pw)| pol.is_valid_password_part1(pw)).count()
}

pub(crate) fn part1() -> usize {
	part1_impl(&input_entries())
}



fn part2_impl(input_entries: &[(Policy, &str)]) -> usize {
	input_entries.iter().filter(|(pol, pw)| pol.is_valid_password_part2(pw)).count()
}

pub(crate) fn part2() -> usize {
	part2_impl(&input_entries())
}


mod parsing {
	use std::{num::ParseIntError, ops::RangeInclusive, str::FromStr};
	use super::Policy;

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum RangeError {
		InvalidFormat,
		InvalidFrom(ParseIntError),
		InvalidThrough(ParseIntError),
	}

	fn try_range_from_str(s: &str) -> Result<RangeInclusive<u8>, RangeError> {
		use RangeError::*;
		let (from, through) = s.split_once('-').ok_or(InvalidFormat)?;
		let from = from.parse().map_err(InvalidFrom)?;
		let through = through.parse().map_err(InvalidFrom)?;
		Ok(from..=through)
	}

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum PolicyError {
		InvalidFormat,
		InvalidRange(RangeError),
	}

	impl FromStr for Policy {
		type Err = PolicyError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use PolicyError::*;
			let (range, chr) = s.split_once(' ').ok_or(InvalidFormat)?;
			let chr = {
				let mut chars = chr.chars();
				match (chars.next(), chars.next()) {
					(Some(chr), None) => chr,
					_ => return Err(InvalidFormat)
				}
			};
			let freq_range = try_range_from_str(range).map_err(InvalidRange)?;
			Ok(Policy { char: chr, freq_range })
		}
	}

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum EntriesError {
		InvalidFormat { line: usize },
		InvalidPolicy { line: usize, source: PolicyError },
	}

	pub(super) fn try_entries_from_str(s: &str) -> Result<Vec<(Policy, &str)>, EntriesError> {
		use EntriesError::*;
		s.lines()
			.enumerate()
			.map(|(l, line)| {
				let (policy, password) = line.split_once(": ")
					.ok_or(InvalidFormat { line: l + 1 })?;
				let policy = policy.parse()
					.map_err(|e| InvalidPolicy { line: l + 1, source: e})?;
				Ok((policy, password))
			})
			.collect()
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		1-3 a: abcde
		1-3 b: cdefg
		2-9 c: ccccccccc
	" };
	assert_eq!(part1_impl(&input_entries_from_str(INPUT)), 2);
	assert_eq!(part1(), 519);
	assert_eq!(part2_impl(&input_entries_from_str(INPUT)), 1);
	assert_eq!(part2(), 708);
}
