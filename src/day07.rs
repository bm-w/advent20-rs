// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::collections::{HashSet, HashMap, VecDeque, hash_map::Entry};


#[cfg_attr(test, derive(Debug))]
#[derive(PartialEq, Eq, Hash)]
struct Bag(String);

struct Rule(Bag, Vec<(usize, Bag)>);


fn input_rules_from_str(s: &str) -> Vec<Rule> {
	parsing::try_rules_from_str(s).unwrap()
}

fn input_rules() -> Vec<Rule> {
	input_rules_from_str(include_str!("day07.txt"))
}


fn part1_impl(input_rules: &[Rule]) -> usize {
	let shiny_gold_bag = Bag("shiny gold".to_owned());
	let mut seen = HashSet::new();
	let mut queue = VecDeque::from([&shiny_gold_bag]);
	while let Some(bag) = queue.pop_front() {
		if !seen.insert(bag) { continue }
		for rule in input_rules.iter() {
			if rule.1.iter().any(|(_, b)| b == bag) {
				queue.push_back(&rule.0);
			}
		}
	}
	assert!(seen.remove(&shiny_gold_bag));
	seen.len()
}

pub(crate) fn part1() -> usize {
	part1_impl(&input_rules())
}


fn part2_impl(input_rules: &[Rule]) -> usize {
	let indexed_rules = input_rules.iter()
		.map(|r| (&r.0, &r.1))
		.collect::<HashMap<_, _>>();
	let shiny_gold_bag = Bag("shiny gold".to_owned());
	let mut seen = HashMap::new();
	let mut queue = VecDeque::from([(1, &shiny_gold_bag)]);
	while let Some((count, bag)) = queue.pop_front() {
		match seen.entry(bag) {
			Entry::Vacant(entry) => { entry.insert(count); }
			Entry::Occupied(mut entry) => { *entry.get_mut() += count; }
		}
		for &(contained_count, ref contained_bag) in indexed_rules[bag].iter() {
			queue.push_back((count * contained_count, contained_bag));
		}
	}
	seen.values().sum::<usize>() - 1
}

pub(crate) fn part2() -> usize {
	part2_impl(&input_rules())
}


mod parsing {
	use std::{num::ParseIntError, str::FromStr};
	use super::{Bag, Rule};


	#[derive(Debug)]
	pub(super) enum BagError {
		InvalidSuffix,
		InvalidColorWords(usize),
	}

	impl FromStr for Bag {
		type Err = BagError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use BagError::*;
			let s = s.strip_suffix('s').unwrap_or(s);
			let color = s.strip_suffix(" bag")
				.ok_or(InvalidSuffix)?;
			let color_words = color.split(' ').count();
			if color_words != 2 {
				return Err(InvalidColorWords(color_words))
			}
			Ok(Bag(color.to_owned()))
		}
	}

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum RuleError {
		InvalidFormat { column: usize },
		InvalidBag { column: usize, source: BagError },
		InvalidQuantity { column: usize, source: ParseIntError },
	}

	impl FromStr for Rule {
		type Err = RuleError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use RuleError::*;
			const CONTAIN_MIDFIX: &str = " contain ";
			let (container_bag, containees) = s.split_once(CONTAIN_MIDFIX)
				.ok_or(InvalidFormat { column: 1 })?;
			let containees_c = container_bag.len() + CONTAIN_MIDFIX.len();
			let container_bag = container_bag.parse()
				.map_err(|e| InvalidBag { column: 1, source: e })?;
			let containees = containees.strip_suffix('.')
				.ok_or(InvalidFormat { column: containees_c + containees.len().max(1) })?;
			let containees = if containees == "no other bags" {
				Vec::new()
			} else {
				const CONTAINEES_SPLIT: &str = ", ";
				containees
					.split(CONTAINEES_SPLIT)
					.scan(containees_c, |c, s| {
						let cs = *c;
						*c += s.len() + CONTAINEES_SPLIT.len();
						Some((cs, s))
					})
					.map(|(c, containee)| {
						let (quant, bag) = containee.split_once(' ')
							.ok_or(InvalidFormat { column: c + 1 })?;
						let bag_c = c + quant.len() + 1;
						let quant = quant.parse()
							.map_err(|e| InvalidQuantity { column: c + 1, source: e })?;
						if quant == 1 && bag.ends_with('s') {
							return Err(InvalidFormat { column: bag_c + bag.len() })
						}
						let bag = bag.parse()
							.map_err(|e| InvalidBag { column: bag_c + 1, source: e })?;
						Ok((quant, bag))
					})
					.collect::<Result<_, _>>()?
			};
			Ok(Rule(container_bag, containees))
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct RulesError { line: usize, source: RuleError }

	pub(super) fn try_rules_from_str(s: &str) -> Result<Vec<Rule>, RulesError> {
		s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| RulesError { line: l + 1, source: e }))
			.collect()
	}


	#[test]
	fn bag() {
		assert!(matches!("".parse::<Bag>(), Err(BagError::InvalidSuffix)));
		assert!(matches!("x bags".parse::<Bag>(), Err(BagError::InvalidColorWords(1))));
		assert!(matches!("a b bags".parse::<Bag>(), Ok(Bag(color)) if color == "a b"));
	}

	#[test]
	fn rule() {
		assert!(matches!("".parse::<Rule>(), Err(RuleError::InvalidFormat { column: 1 })));
		assert!(matches!("x contain y".parse::<Rule>(), Err(RuleError::InvalidBag { column: 1, .. })));
		assert!(matches!("a b bags contain xy".parse::<Rule>(), Err(RuleError::InvalidFormat { column: 19 })));
		assert!(matches!("a b bags contain no other bags.".parse::<Rule>(), Ok(rule) if rule.1.is_empty()));
		assert!(matches!("a b bags contain x.".parse::<Rule>(), Err(RuleError::InvalidFormat { column: 18 })));
		assert!(matches!("a b bags contain x y.".parse::<Rule>(), Err(RuleError::InvalidQuantity { column: 18, .. })));
		assert!(matches!("a b bags contain 1 x.".parse::<Rule>(), Err(RuleError::InvalidBag { column: 20, .. })));
		assert!(matches!("a b bags contain 1 c d bags.".parse::<Rule>(), Err(RuleError::InvalidFormat { column: 27, .. })));
		assert!(matches!("a b bags contain 1 c d bag, x.".parse::<Rule>(), Err(RuleError::InvalidFormat { column: 29, .. })));
		assert!(matches!("a b bags contain 1 c d bag, 2 e f bags.".parse::<Rule>(), Ok(rule) if rule.1.len() == 2));
	}

	#[test]
	fn rules() -> Result<(), RulesError> {
		let rules = try_rules_from_str(super::TEST_INPUT)?;
		assert_eq!(rules.len(), 9);
		assert_eq!(rules[0].0.0, "light red");
		assert_eq!(rules[4].1.len(), 2);
		assert_eq!(rules[4].1[1], (2, Bag("vibrant plum".to_owned())));
		assert!(rules[8].1.is_empty());
		Ok(())
	}
}


#[cfg(test)]
const TEST_INPUT: &str = indoc::indoc! { "
	light red bags contain 1 bright white bag, 2 muted yellow bags.
	dark orange bags contain 3 bright white bags, 4 muted yellow bags.
	bright white bags contain 1 shiny gold bag.
	muted yellow bags contain 2 shiny gold bags, 9 faded blue bags.
	shiny gold bags contain 1 dark olive bag, 2 vibrant plum bags.
	dark olive bags contain 3 faded blue bags, 4 dotted black bags.
	vibrant plum bags contain 5 faded blue bags, 6 dotted black bags.
	faded blue bags contain no other bags.
	dotted black bags contain no other bags.
" };

#[test]
fn tests() {
	assert_eq!(part1_impl(&input_rules_from_str(TEST_INPUT)), 4);
	assert_eq!(part1(), 316);
	assert_eq!(part2_impl(&input_rules_from_str(TEST_INPUT)), 32);
	assert_eq!(part2(), 11310);
}
