// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::iter;
use itertools::Itertools as _;


type AdapterRating = u8;

trait AdapterChain: Iterator<Item = AdapterRating> {
	fn joltage_differences_distribution(self) -> [usize; 3] where Self: Sized {
		iter::once(0)
			.chain(self.sorted())
			.tuple_windows()
			.map(|(l, r)| r - l)
			.fold([0, 0, 1], |mut accum_diffs, diff| {
				assert!((1..=3).contains(&diff));
				accum_diffs[diff as usize - 1] += 1;
				accum_diffs
			})
	}

	fn adapter_combinations_count(self) -> usize where Self: Sized {
		iter::once(0)
			.chain(self.sorted())
			.tuple_windows()
			.map(|(l, r)| r - l)
			.chain(iter::once(3))
			.fold((1, 1), |(combinations, ones_run_len), diff| {
				// TODO(bm-w): Handle differences of 2 (even though the input ratings don’t contain any)?
				assert_ne!(diff, 2);
				if diff == 1 {
					(combinations, ones_run_len + 1)
				} else {
					/// Tribonacci numbers (https://oeis.org/A000073)
					/// > Number of binary sequences of length n-3 that have no three consecutive 0's.
					/// — Emeric Deutsch, Apr 27 2006
					const ONES_RUN_COMBINATIONS: [usize; 7] = [0, 0, 1, 1, 2, 4, 7]; // …, 13, 24, etc.
					(combinations * ONES_RUN_COMBINATIONS[ones_run_len + 1], 1)
				}
			}).0
	}
}

impl<I> AdapterChain for I where I: Iterator<Item = AdapterRating> {}


fn input_adapter_ratings_from_str(s: &str) -> impl Iterator<Item = AdapterRating> + '_ {
	parsing::adapter_ratings_from_str(s).map(|ar| ar.unwrap())
}

fn input_adapter_ratings() -> impl Iterator<Item = AdapterRating> {
	input_adapter_ratings_from_str(include_str!("day10.txt"))
}


fn part1_impl(input_adapter_ratings: impl Iterator<Item = AdapterRating>) -> usize {
	let [ones, _, threes] = input_adapter_ratings.joltage_differences_distribution();
	ones * threes
}

pub(crate) fn part1() -> usize {
	part1_impl(input_adapter_ratings())
}


fn part2_impl(input_adapter_ratings: impl Iterator<Item = AdapterRating>) -> usize {
	input_adapter_ratings.adapter_combinations_count()
}

pub(crate) fn part2() -> usize {
	part2_impl(input_adapter_ratings())
}


mod parsing {
	use std::num::ParseIntError;
	use super::AdapterRating;

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct RatingsError { line: usize, source: ParseIntError }

	pub(super) fn adapter_ratings_from_str(s: &str) -> impl Iterator<Item = Result<AdapterRating, RatingsError>> + Clone + '_ {
		s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| RatingsError { line: l + 1, source: e }))
	}


	#[test]
	fn tests() -> Result<(), RatingsError> {
		adapter_ratings_from_str(super::SMALL_TEST_INPUT).collect::<Result<Vec<_>, _>>().map(|_| ())?;
		adapter_ratings_from_str(super::LARGER_TEST_INPUT).collect::<Result<Vec<_>, _>>().map(|_| ())
	}
}


#[cfg(test)]
const SMALL_TEST_INPUT: &str = indoc::indoc! { "
	16
	10
	15
	5
	1
	11
	7
	19
	6
	12
	4
" };

#[cfg(test)]
const LARGER_TEST_INPUT: &str = indoc::indoc! { "
	28
	33
	18
	42
	31
	14
	46
	20
	48
	47
	24
	23
	49
	45
	19
	38
	39
	11
	1
	32
	25
	35
	8
	17
	7
	9
	4
	2
	34
	10
	3
" };

#[test]
fn tests() {
	assert_eq!(part1_impl(input_adapter_ratings_from_str(SMALL_TEST_INPUT)), 35);
	assert_eq!(part1_impl(input_adapter_ratings_from_str(LARGER_TEST_INPUT)), 220);
	assert_eq!(part1(), 2201);
	assert_eq!(part2_impl(input_adapter_ratings_from_str(SMALL_TEST_INPUT)), 8);
	assert_eq!(part2_impl(input_adapter_ratings_from_str(LARGER_TEST_INPUT)), 19208);
	assert_eq!(part2(), 169255295254528);
}
