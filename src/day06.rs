// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::collections::HashSet;
use itertools::Itertools;


#[cfg_attr(test, derive(Debug))]
struct Person(Vec<char>);

#[cfg_attr(test, derive(Debug))]
struct Group(Vec<Person>);

impl Person {
	fn unique_answers(&self) -> HashSet<char> {
		self.0.iter().copied().sorted().dedup().collect()
	}
}

impl Group {
	fn unique_answers(&self) -> HashSet<char> {
		self.0.iter().fold(HashSet::new(), |mut unique_answers, person| {
			unique_answers.extend(person.unique_answers());
			unique_answers
		})
	}

	fn common_answers(&self) -> HashSet<char> {
		self.0.iter().map(|g| g.unique_answers()).reduce(|answers, group_answer| {
			answers.intersection(&group_answer).copied().collect()
		}).unwrap_or_default()
	}
}


fn input_groups_from_str(s: &str) -> Vec<Group> {
	parsing::try_groups_from_str(s).unwrap()
}

fn input_groups() -> Vec<Group> {
	input_groups_from_str(include_str!("day06.txt"))
}


fn part1_impl(input_groups: &[Group]) -> usize {
	input_groups.iter().map(|g| g.unique_answers().len()).sum()
}

pub(crate) fn part1() -> usize {
	part1_impl(&input_groups())
}


fn part2_impl(input_groups: &[Group]) -> usize {
	input_groups.iter().map(|g| g.common_answers().len()).sum()
}

pub(crate) fn part2() -> usize {
	part2_impl(&input_groups())
}


mod parsing {
	use std::str::FromStr;
	use itertools::Itertools;
	use super::{Person, Group};

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum PersonError {
		InvalidFormat,
		InvalidChar { column: usize, found: char },
	}

	impl FromStr for Person {
		type Err = PersonError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use PersonError::*;
			if s.is_empty() { return Err(InvalidFormat) }
			Ok(Person(s.chars()
				.enumerate()
				.map(|(c, chr)| if chr.is_ascii_alphabetic() { Ok(chr) }
					else { Err(InvalidChar { column: c + 1, found: chr }) })
				.collect::<Result<_, _>>()?))
		}
	}

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum GroupError {
		InvalidFormat { line: usize },
		InvalidPerson { line: usize, source: PersonError },
	}

	struct EnumeratedLines<'l, L>(L) where L: Iterator<Item = (usize, &'l str)>;

	impl<'l, L> TryFrom<EnumeratedLines<'l, L>> for Group
	where L: Iterator<Item = (usize, &'l str)> {
		type Error = GroupError;
		fn try_from(lines: EnumeratedLines<'l, L>) -> Result<Self, Self::Error> {
			use GroupError::*;
			let mut lines = lines.0.peekable();
			if lines.peek().is_none() { return Err(InvalidFormat { line: 1 }) }
			Ok(Group(lines
				.map(|(l, line)| line.parse()
					.map_err(|e| InvalidPerson { line: l + 1, source: e }))
				.collect::<Result<_, _>>()?))
		}
	}

	pub(super) fn try_groups_from_str(s: &str) -> Result<Vec<Group>, GroupError> {
		s.lines().enumerate()
			.group_by(|(_, line)| line.is_empty())
			.into_iter()
			.filter_map(|(discard, lines)| if discard { None }
				else { Some(EnumeratedLines(lines).try_into()) })
			.collect::<Result<_, _>>()
	}


	#[test]
	fn person() {
		use PersonError::*;
		assert!(matches!("".parse::<Person>(), Err(InvalidFormat)));
		assert!(matches!("a1".parse::<Person>(), Err(InvalidChar { column: 2, found: '1' })));
		assert!(matches!("abc".parse::<Person>(), Ok(Person(chars)) if chars[..] == ['a', 'b', 'c']));
	}

	#[test]
	fn group() {
		use GroupError::*;
		assert!(matches!(EnumeratedLines("".lines().enumerate()).try_into() as Result<Group, _>, Err(InvalidFormat { line: 1 })));
		assert!(matches!(EnumeratedLines("a\n\n".lines().enumerate()).try_into() as Result<Group, _>, Err(InvalidPerson { line: 2, source: PersonError::InvalidFormat })));
		assert!((EnumeratedLines("a\nb".lines().enumerate()).try_into() as Result<Group, _>).is_ok());
	}

	#[test]
	fn groups() {
		assert!(try_groups_from_str(super::TEST_INPUT).is_ok());
	}
}


#[cfg(test)]
const TEST_INPUT: &str = indoc::indoc! { "
	abc

	a
	b
	c

	ab
	ac

	a
	a
	a
	a

	b
" };

#[test]
fn tests() {
	assert_eq!(part1_impl(&input_groups_from_str(TEST_INPUT)), 11);
	assert_eq!(part1(), 6809);
	assert_eq!(part2_impl(&input_groups_from_str(TEST_INPUT)), 6);
	assert_eq!(part2(), 3394);
}
