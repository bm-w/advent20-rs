// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use itertools::Itertools as _;


fn input_entries_from_str(s: &str) -> Vec<u32> {
	parsing::entries_from_str(s).unwrap()
}

fn input_entries() -> Vec<u32> {
	input_entries_from_str(include_str!("day01.txt"))
}


fn part1_impl(input_entries: &[u32]) -> u64 {
	input_entries.iter()
		.tuple_combinations()
		.find(|(l, r)| *l + *r == 2020)
		.map(|(l, r)| *l as u64 * *r as u64)
		.unwrap()
}

pub(crate) fn part1() -> u64 {
	part1_impl(&input_entries())
}


fn part2_impl(input_entries: &[u32]) -> u64 {
	input_entries.iter()
		.tuple_combinations()
		.find(|(l, m, r)| *l + *m + *r == 2020)
		.map(|(l, m, r)| *l as u64 * *m as u64 * *r as u64)
		.unwrap()
}

pub(crate) fn part2() -> u64 {
	part2_impl(&input_entries())
}


mod parsing {
	use std::num::ParseIntError;

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct EntriesError {
		line: usize,
		source: ParseIntError
	}

	pub(super) fn entries_from_str(s: &str) -> Result<Vec<u32>, EntriesError> {
		s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| EntriesError { line: l + 1, source: e }))
			.collect()
	}
}


#[test]
fn tests() {
	const INPUT: &str = indoc::indoc! { "
		1721
		979
		366
		299
		675
		1456
	" };
	assert_eq!(part1_impl(&input_entries_from_str(INPUT)), 514579);
	assert_eq!(part1(), 997899);
	assert_eq!(part2_impl(&input_entries_from_str(INPUT)), 241861950);
	assert_eq!(part2(), 131248694);
}
