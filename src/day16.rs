// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::ops::RangeInclusive;


#[derive(PartialEq, Eq, Hash, Clone)]
struct Rule {
	name: String,
	or_ranges: [RangeInclusive<u32>; 2],
}

struct Ticket(Vec<u32>);

struct Input {
	rules: Vec<Rule>,
	own_ticket: Ticket,
	nearby_tickets: Vec<Ticket>,
}

impl Input {
	fn invalid_ticket_numbers<'a>(&'a self, ticket: &'a Ticket) -> impl Iterator<Item = &u32> + 'a {
		ticket.0.iter()
			.filter(|num| !self.rules.iter()
				.any(|rule| rule.or_ranges[0].contains(num)
					|| rule.or_ranges[1].contains(num)))
	}

	fn is_valid_ticket(&self, ticket: &Ticket) -> bool {
		self.invalid_ticket_numbers(ticket).next().is_none()
	}

	fn nearby_tickets_scanning_error_rate(&self) -> u32 {
		self.nearby_tickets.iter()
			.flat_map(|ticket| self.invalid_ticket_numbers(ticket))
			.sum()
	}

	fn discard_invalid_tickets(&mut self) {
		// TODO(bm-w): Use `drain_filter` in-place once it’s stabilized?
		let nearby_tickets = std::mem::take(&mut self.nearby_tickets);
		self.nearby_tickets = nearby_tickets.into_iter().filter(|t| self.is_valid_ticket(t)).collect();
	}

	/// May panic if `nearby_tickets` are not all valid.
	fn sort_matched_rules(&mut self) {
		use std::collections::HashSet;

		let mut applying_rules = vec![HashSet::<&Rule>::default(); self.rules.len()];

		for rule in self.rules.iter() {
			for i in 0..self.rules.len() {
				let applies = self.nearby_tickets.iter()
					.all(|Ticket(nums)| rule.or_ranges[0].contains(&nums[i])
						|| rule.or_ranges[1].contains(&nums[i]));
				if applies { applying_rules[i].insert(rule); }
			}
		}

		let mut sorted_rules = vec![None; applying_rules.len()];
		while let Some(i) = applying_rules.iter().position(|rr| rr.len() == 1) {
			let rule = std::mem::take(&mut applying_rules[i]).into_iter().next().unwrap();
			for rules in applying_rules.iter_mut() {
				rules.remove(rule);
			}
			sorted_rules[i] = Some(rule);
		}

		// TODO(bm-w): Permutate in-place instead of cloning?
		self.rules = sorted_rules.into_iter().flatten().cloned().collect();
	}
}


fn input_from_str(s: &str) -> Input {
	s.parse().unwrap()
}

fn input() -> Input {
	input_from_str(include_str!("day16.txt"))
}


fn part1_impl(input: Input) -> u32 {
	input.nearby_tickets_scanning_error_rate()
}

pub(crate) fn part1() -> u32 {
	part1_impl(input())
}


fn part2_impl(mut input: Input, filter_rule: impl Fn(&Rule) -> bool) -> u64 {
	input.discard_invalid_tickets();
	input.sort_matched_rules();
	input.rules.iter().zip(input.own_ticket.0.iter())
		.filter(|&(rule, _)| filter_rule(rule))
		.map(|(_, num)| *num as u64)
		.product()
}

pub(crate) fn part2() -> u64 {
	part2_impl(input(), |r| r.name.starts_with("departure "))
}


mod parsing {
	use std::{num::ParseIntError, ops::RangeInclusive, str::FromStr};
	use super::{Rule, Ticket, Input};

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum RangeError {
		InvalidFormat,
		InvalidFrom(ParseIntError),
		InvalidThrough(ParseIntError),
	}

	fn try_range_from_str(s: &str) -> Result<RangeInclusive<u32>, RangeError> {
		use RangeError::*;
		let (from, through) = s.split_once('-').ok_or(InvalidFormat)?;
		let from = from.parse().map_err(InvalidFrom)?;
		let through = through.parse().map_err(InvalidThrough)?;
		Ok(from..=through)
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum RuleError {
		InvalidFormat,
		EmptyName,
		InvalidOrRangesFormat,
		InvalidRange { left: bool, source: RangeError },
		OverlappingRanges,
	}

	impl FromStr for Rule {
		type Err = RuleError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use RuleError::*;
			let (name, ranges) = s.split_once(": ")
				.ok_or(InvalidFormat)?;
			if name.is_empty() { return Err(EmptyName) }
			let (left_range, right_range) = ranges.split_once(" or ")
				.ok_or(InvalidOrRangesFormat)?;
			let left_range = try_range_from_str(left_range)
				.map_err(|e| InvalidRange { left: true, source: e })?;
			let right_range = try_range_from_str(right_range)
				.map_err(|e| InvalidRange { left: false, source: e })?;
			if *left_range.end() >= *right_range.start() { return Err(OverlappingRanges) }
			Ok(Rule{ name: name.to_owned(), or_ranges: [left_range, right_range] })
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct TicketError { column: usize, source: ParseIntError }

	impl FromStr for Ticket {
		type Err = TicketError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			Ok(Ticket(s.split(',')
				.take_while(|num| !num.is_empty())
				.scan(0, |c, num| {
					let num_c = *c;
					*c += 1 + num.len();
					Some(num.parse()
						.map_err(|e| TicketError { column: num_c + 1, source: e }))
				})
				.collect::<Result<_, _>>()?))
		}
	}


	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum InputError {
		InvalidFormat { line: usize },
		InvalidRule { line: usize, source: RuleError },
		InvalidTicket { line: usize, source: TicketError },
	}

	impl FromStr for Input {
		type Err = InputError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use InputError::*;
			let mut lines = s.lines().enumerate();
			let rules = lines.by_ref()
				.take_while(|(_, line)| !line.is_empty())
				.map(|(l, line)| line.parse()
					.map_err(|e| InvalidRule { line: l + 1, source: e }))
				.collect::<Result<Vec<_>, _>>()?;
			if lines.next().map_or(true, |(_, line)| line != "your ticket:") {
				return Err(InvalidFormat { line: rules.len() + 2 })
			}
			let own_ticket = lines.next()
				.ok_or(InvalidFormat { line: rules.len() + 3 })
				.and_then(|(l, line)| line.parse()
					.map_err(|e| InvalidTicket { line: l + 1, source: e }))?;
			if lines.next().map_or(true, |(_, line)| !line.is_empty()) {
				return Err(InvalidFormat { line: rules.len() + 4 })
			}
			if lines.next().map_or(true, |(_, line)| line != "nearby tickets:") {
				return Err(InvalidFormat { line: rules.len() + 5 })
			}
			let nearby_tickets = lines
				.map(|(l, line)| line.parse()
					.map_err(|e| InvalidTicket { line: l + 1, source: e }))
				.collect::<Result<_, _>>()?;
			Ok(Input { rules, own_ticket, nearby_tickets })
		}
	}


	#[test]
	fn range() {
		use RangeError::*;
		assert!(matches!(try_range_from_str(""), Err(InvalidFormat)));
		assert!(matches!(try_range_from_str("x-"), Err(InvalidFrom(_))));
		assert!(matches!(try_range_from_str("1337-"), Err(InvalidThrough(_))));
		assert!(matches!(try_range_from_str("13-37"), Ok(range) if *range.start() == 13 && *range.end() == 37));
	}

	#[test]
	fn rule() {
		use RuleError::*;
		assert!(matches!("".parse::<Rule>(), Err(InvalidFormat)));
		assert!(matches!(": ".parse::<Rule>(), Err(EmptyName)));
		assert!(matches!("foo: ".parse::<Rule>(), Err(InvalidOrRangesFormat)));
		assert!(matches!("foo: x or ".parse::<Rule>(), Err(InvalidRange { left: true, .. })));
		assert!(matches!("foo: 13-37 or ".parse::<Rule>(), Err(InvalidRange { left: false, .. })));
		assert!(matches!("foo: 1-3 or 3-7".parse::<Rule>(), Err(OverlappingRanges)));
		assert!(matches!("foo: 13-37 or 54-321".parse::<Rule>(), Ok(Rule { name, .. }) if name == "foo"));
	}

	#[test]
	fn ticket() {
		assert!(matches!("".parse::<Ticket>(), Ok(ticket) if ticket.0.is_empty()));
		assert!(matches!("13,x".parse::<Ticket>(), Err(TicketError { column: 4, .. })));
		assert!(matches!("13,37,54,321".parse::<Ticket>(), Ok(ticket) if ticket.0.len() == 4));
	}

	#[test]
	fn input() -> Result<(), InputError> {
		[super::TEST_INPUT_PART1, super::TEST_INPUT_PART2].into_iter()
			.map(|s| s.parse::<Input>())
			.collect::<Result<_, _>>()
			.map(|_: Vec<_>| ())
	}
}


#[cfg(test)]
const TEST_INPUT_PART1: &str = indoc::indoc! { "
	class: 1-3 or 5-7
	row: 6-11 or 33-44
	seat: 13-40 or 45-50

	your ticket:
	7,1,14

	nearby tickets:
	7,3,47
	40,4,50
	55,2,20
	38,6,12
" };

#[cfg(test)]
const TEST_INPUT_PART2: &str = indoc::indoc! { "
	class: 0-1 or 4-19
	row: 0-5 or 8-19
	seat: 0-13 or 16-19

	your ticket:
	11,12,13

	nearby tickets:
	3,9,18
	15,1,5
	5,14,9
" };

#[test]
fn tests() {
	assert_eq!(part1_impl(input_from_str(TEST_INPUT_PART1)), 71);
	assert_eq!(part1(), 27898);
	assert_eq!(part2_impl(input_from_str(TEST_INPUT_PART2), |r| r.name != "class"), 143);
	assert_eq!(part2(), 2766491048287);
}
