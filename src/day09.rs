// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::collections::VecDeque;
use itertools::Itertools as _;


trait FindWithoutSumPair: Iterator<Item = u64> {
	fn find_without_sum_pair<const N: usize>(&mut self) -> Option<(usize, u64)> {
		let mut ring = [0u64; N];
		for (i, num) in self.enumerate() {
			if i < N || (i - N..i).tuple_combinations()
				.any(|(j, k)| ring[j % ring.len()] + ring[k % ring.len()] == num)
			{
				ring[i % ring.len()] = num;
			} else {
				return Some((i, num))
			}
		}
		None
	}
}

impl<T> FindWithoutSumPair for T where T: Iterator<Item = u64> {}


fn input_numbers_from_str(s: &str) -> impl Iterator<Item = u64> + Clone + '_ {
	parsing::numbers_from_str(s).map(|r| r.unwrap())
}

fn input_numbers() -> impl Iterator<Item = u64> + Clone {
	input_numbers_from_str(include_str!("day09.txt"))
}


fn part1_impl<const N: usize, I>(mut input_numbers: I) -> u64
where I: Iterator<Item = u64> {
	input_numbers.find_without_sum_pair::<N>().unwrap().1
}

pub(crate) fn part1() -> u64 {
	part1_impl::<25, _>(input_numbers())
}


fn part2_impl<const N: usize, I>(input_numbers: I) -> u64
where I: Iterator<Item = u64> + Clone {
	let (len, sum) = input_numbers.clone().find_without_sum_pair::<N>().unwrap();

	// TODO(bm-w): Somehow skip early stretch of of innput numbers?
	let mut buffer = VecDeque::new();
	'outer: for num in input_numbers.take(len) {
		buffer.push_back(num);
		loop {
			match if buffer.len() > 1 { buffer.iter().sum::<u64>() } else { 0 } {
				low if low < sum => {
					continue 'outer
				}
				exact if exact == sum => {
					return buffer.iter()
						.minmax()
						.into_option()
						.map(|(min, max)| *min + *max)
						.unwrap()
				}
				_ => {
					buffer.pop_front();
				}
			}
		}
	}
	unreachable!()
}

pub(crate) fn part2() -> u64 {
	part2_impl::<25, _>(input_numbers())
}


mod parsing {
	use std::num::ParseIntError;

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct NumbersError { line: usize, source: ParseIntError }

	pub(super) fn numbers_from_str(s: &str) -> impl Iterator<Item = Result<u64, NumbersError>> + Clone + '_ {
		s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| NumbersError { line: l + 1, source: e }))
	}


	#[test]
	fn tests() -> Result<(), NumbersError> {
		numbers_from_str(super::TEST_INPUT).collect::<Result<Vec<_>, _>>().map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUT: &str = indoc::indoc! { "
	35
	20
	15
	25
	47
	40
	62
	55
	65
	95
	102
	117
	150
	182
	127
	219
	299
	277
	309
	576
" };

#[test]
fn tests() {
	assert_eq!(part1_impl::<5, _>(input_numbers_from_str(TEST_INPUT)), 127);
	assert_eq!(part1(), 21806024);
	assert_eq!(part2_impl::<5, _>(input_numbers_from_str(TEST_INPUT)), 62);
	assert_eq!(part2(), 2986195);
}
