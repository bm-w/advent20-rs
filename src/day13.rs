// Copyright (c) 2022 Bastiaan Marinus van de Weerd


enum Bus {
	OutOfService,
	InService { freq: usize },
}

struct Input {
	time: usize,
	schedule: Vec<Bus>,
}


fn input_from_str(s: &str) -> Input {
	s.parse().unwrap()
}

fn input() -> Input {
	input_from_str(include_str!("day13.txt"))
}


fn part1_impl(input: Input) -> usize {
	input.schedule.iter()
		.filter_map(|bus| if let Bus::InService { freq } = bus { Some(*freq) } else { None })
		.map(|freq| (freq, freq - input.time % freq))
		.min_by_key(|&(_, ttw)| ttw)
		.map(|(freq, ttw)| freq * ttw).unwrap()
}

pub(crate) fn part1() -> usize {
	part1_impl(input())
}


#[allow(dead_code)]
fn part2_brute(input: Input) -> usize {
	use itertools::Itertools as _;	

	let mut ii_freqs = input.schedule.iter()
		.enumerate()
		.filter_map(|(i, bus)| if let Bus::InService { freq } = bus { Some((i, *freq)) } else { None })
		.collect::<Vec<_>>();
	let (i_max, freq_max) = ii_freqs.remove(ii_freqs.iter()
		.position_max_by_key(|&(_, freq)| freq)
		.unwrap());

	assert!(freq_max >= input.schedule.len());

	let mut time = freq_max - i_max;
	loop {
		time += freq_max;
		if ii_freqs.iter().all(|&(i, freq)| {
			(time + i) % freq == 0
		}) {
			return time
		}
	}
}

/// Chinese remainder theorem (sieve implementation)
///
/// (Found by Googling “least common multiple with remainders”)
/// 
/// See: https://en.wikipedia.org/wiki/Chinese_remainder_theorem#Search_by_sieving
fn part2_impl(input: Input) -> usize {
	use std::cmp::Reverse;
	use itertools::Itertools as _;

	// Normalize (such that always `rem` < `div`) and sort by ascending `div`.
	let divs_rems = input.schedule.iter()
		.enumerate()
		.filter_map(|(i, bus)| if let Bus::InService { freq } = bus { Some((*freq, i)) } else { None })
		.map(|(div, offset)| (div, if offset == 0 { 0 } else { div - offset % div }))
		.sorted_by_key(|&(div, _)| Reverse(div))
		.collect::<Vec<_>>();

	// Frequencies (divisors) must be coprime
	#[cfg(test)]
	debug_assert!(divs_rems.iter().tuple_combinations()
		.all(|(&(l, _), &(r, _))| num::integer::gcd(l, r) == 1));

	let big_n = divs_rems.iter().map(|&(div, _)| div).product::<usize>();

	divs_rems.iter()
		.fold(None, |start_incr, &(div, rem)|
			if let Some((start, incr)) = start_incr {
				let num = (0..).map(|i| start + i * incr).find(|num| num % div == rem).unwrap();
				Some((num, incr * div))
			} else {
				Some((rem, div))
			})
		.unwrap().0 % big_n
}

pub(crate) fn part2() -> usize {
	part2_impl(input())
}


mod parsing {
	use std::{num::ParseIntError, str::FromStr};
	use super::{Bus, Input};

	#[derive(Debug)]
	pub(super) struct InvalidBusError(ParseIntError);

	impl FromStr for Bus {
		type Err = InvalidBusError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			if s.starts_with('x') {
				Ok(Bus::OutOfService)
			} else {
				s.parse()
					.map(|freq| Bus::InService { freq })
					.map_err(InvalidBusError)
			}
		}
	}

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum InputError {
		InvalidFormat { line: usize },
		InvalidTime(ParseIntError),
		InvalidBus { column: usize, source: InvalidBusError },
	}

	impl FromStr for Input {
		type Err = InputError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use InputError::*;
			let mut lines = s.lines();
			let time = lines.next().ok_or(InvalidFormat { line: 1 })?
				.parse().map_err(InvalidTime)?;
			let schedule: Vec<_> = lines.next().ok_or(InvalidFormat { line: 2 })?
				.split(',')
				.scan(0, |schedule_c, bus| {
					let c = *schedule_c;
					*schedule_c += bus.len() + 1;
					Some(bus.parse()
						.map_err(|e| InvalidBus { column: c + 1, source: e }))
				})
				.collect::<Result<_, _>>()?;
			if lines.next().is_some() { return Err(InvalidFormat { line: 3 }) }
			Ok(Input { time, schedule })
		}
	}


	#[test]
	fn bus() {
		assert!(matches!("".parse::<Bus>(), Err(InvalidBusError(_))));
		assert!(matches!("X".parse::<Bus>(), Err(InvalidBusError(_))));
		assert!(matches!("x".parse::<Bus>(), Ok(Bus::OutOfService)));
		assert!(matches!("1337".parse::<Bus>(), Ok(Bus::InService { freq: 1337 })));
	}

	#[test]
	fn context() -> Result<(), InputError> {
		use InputError::*;
		assert!(matches!("".parse::<Input>(), Err(InvalidFormat { line: 1 })));
		assert!(matches!("x".parse::<Input>(), Err(InvalidTime(_))));
		assert!(matches!("1337".parse::<Input>(), Err(InvalidFormat { line: 2 })));
		assert!(matches!("1337\n13,37,X".parse::<Input>(), Err(InvalidBus { column: 7, .. })));
		super::TEST_INPUT.parse::<Input>().map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUT: &str = indoc::indoc! { "
	939
	7,13,x,x,59,x,31,19
" };

#[test]
fn tests() {
	assert_eq!(part1_impl(input_from_str(TEST_INPUT)), 295);
	assert_eq!(part1(), 4782);
	assert_eq!(part2_brute(input_from_str(TEST_INPUT)), 1068781);
	assert_eq!(part2_impl(input_from_str(TEST_INPUT)), 1068781);
	assert_eq!(part2(), 1118684865113056);
}
