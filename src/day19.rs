// Copyright (c) 2022 Bastiaan Marinus van de Weerd


struct RuleRefs(Vec<usize>);

enum Rule {
	Char(char),
	Refs(RuleRefs, Option<RuleRefs>),
}

struct Input<'m> {
	rules: Vec<Rule>,
	messages: Box<dyn Iterator<Item = &'m str> + 'm>,
}


mod matching {
	use std::{str::Chars, convert::identity};
	use super::{Rule, Input};

	#[derive(Clone)]
	struct StateElt {
		rule_idx: usize,
		or_refs: bool,
		refs_idx: usize,
	}

	type State = Vec<StateElt>;

	struct Checkpoint<'m> {
		state: State,
		chars: Chars<'m>,
	}

	trait MatchingResult<'m> {
		fn checkpoints(&mut self) -> &mut Vec<Checkpoint<'m>>;
		fn merge(&mut self, other: Self);
	}

	type Result<'m> = std::result::Result<Vec<Checkpoint<'m>>, Vec<Checkpoint<'m>>>;

	impl<'m> MatchingResult<'m> for Result<'m> {
		fn checkpoints(&mut self) -> &mut Vec<Checkpoint<'m>> {
			self.as_mut().unwrap_or_else(identity)
		}

		fn merge(&mut self, other: Self) {
			let cp = std::mem::replace(self, other).unwrap_or_else(identity);
			let self_cp = self.checkpoints();
			let other_cp = std::mem::replace(self_cp, cp);
			self_cp.extend(other_cp);
		}
	}

	impl<'m> Input<'m> {
		fn _chars_match_rule(
			rules: &[Rule],
			rule_idx: usize,
			state: &mut State,
			alt: bool,
			chars: &mut Chars<'m>,
		) -> Result<'m> {
			macro_rules! match_rules { ($refs:expr, $state_or_refs:literal, $chars:expr) => {
				Self::_chars_match_rules(rules, &$refs.0, state, rule_idx, $state_or_refs, $chars)
			} }
			match &rules[rule_idx] {
				Rule::Char(chr) => {
					assert!(!alt);
					(if chars.next().map_or(false, |c| c == *chr) { Ok } else { Err })(vec![])
				}
				Rule::Refs(refs, None) => {
					assert!(!alt);
					match_rules!(refs, false, chars)
				}
				Rule::Refs(either_refs, Some(or_refs)) if !alt => {
					let mut either_chars = chars.clone();
					let mut res = match_rules!(either_refs, false, &mut either_chars);
					if res.is_ok() {
						let or_chars = std::mem::replace(chars, either_chars);
						res.checkpoints().push(Checkpoint { state: state.clone(), chars: or_chars });
						res
					} else {
						match_rules!(or_refs, true, chars)
					}
				}
				Rule::Refs(_, Some(refs)) => {
					match_rules!(refs, true, chars)
				}
			}
		}

		fn _chars_match_rules(
			rules: &[Rule],
			rule_idxs: &[usize],
			state: &mut State,
			state_rule_idx: usize,
			state_or_refs: bool,
			chars: &mut Chars<'m>,
		) -> Result<'m> {
			state.push(StateElt { rule_idx: state_rule_idx, refs_idx: 0, or_refs: state_or_refs });
			let mut res = Ok(vec![]);
			for &rule_idx in rule_idxs {
				res.merge(Self::_chars_match_rule(rules, rule_idx, state, false, chars));
				if res.is_err() { break }
				state.last_mut().unwrap().refs_idx += 1;
			}
			state.pop();
			res
		}

		fn _chars_match_rules_from_state(
			rules: &[Rule],
			state: &mut State,
			mut alt: bool,
			chars: &mut Chars<'m>,
		) -> Result<'m> {
			let mut rule_idx = state.last()
				.map(|state| match &rules[state.rule_idx] {
					Rule::Refs(refs, None) if !state.or_refs => refs.0[state.refs_idx],
					Rule::Refs(either_refs, Some(or_refs)) =>
						(if state.or_refs { or_refs } else { either_refs }).0[state.refs_idx],
					_ => unreachable!()
				})
				.unwrap();

			let mut res = Ok(vec![]);
			'matching: loop {
				res.merge(Self::_chars_match_rule(rules, rule_idx, state, alt, chars));
				alt = false;

				#[allow(clippy::question_mark)]
				if res.is_err() { return res }

				while let Some(state_elt) = state.last_mut() {
					state_elt.refs_idx += 1;
					let refs = match &rules[state_elt.rule_idx] {
						Rule::Refs(refs, None) if !state_elt.or_refs => refs,
						Rule::Refs(either_refs, Some(or_refs)) =>
							if state_elt.or_refs { or_refs } else { either_refs },
						_ => unreachable!()
					};
					if state_elt.refs_idx < refs.0.len() {
						rule_idx = refs.0[state_elt.refs_idx];
						continue 'matching
					}
					state.pop();
				}

				return res
			}
		}

		fn _backtrack(rules: &[Rule], mut res: Result<'m>, chars: &mut Chars<'m>) -> Result<'m> {
			while let Some(mut checkpoint) = res.checkpoints().pop() {
				res.merge(Self::_chars_match_rules_from_state(rules, &mut checkpoint.state, true, &mut checkpoint.chars));
				if res.is_ok() {
					*chars = checkpoint.chars;
					break
				}
			}
			res
		}

		pub(super) fn message_matches_rule0(rules: &[Rule], msg: &'m str) -> bool {
			let mut chars = msg.chars();
			let mut res = Self::_chars_match_rule(rules, 0, &mut vec![], false, &mut chars);
			while res.is_err() || !chars.as_str().is_empty() {
				if res.checkpoints().is_empty() { break }
				res = Self::_backtrack(rules, res, &mut chars);
			}
			res.is_ok()
		}
	}

	#[test]
	fn simplified() {
		use super::RuleRefs;

		let rules = vec![
			Rule::Refs(RuleRefs(vec![1, 3]), None),
			Rule::Refs(RuleRefs(vec![2]), Some(RuleRefs(vec![2, 1]))),
			Rule::Char('a'),
			Rule::Char('b'),
		];

		assert!(Input::message_matches_rule0(&rules, "ab"));
		assert!(Input::message_matches_rule0(&rules, "aab"));
		assert!(Input::message_matches_rule0(&rules, "aaab"));
		assert!(!Input::message_matches_rule0(&rules, "aaaa"));
		assert!(!Input::message_matches_rule0(&rules, "aaabb"));
	}
}


fn input_from_str(s: &str) -> Input {
	Input::try_from(s).unwrap()
}

fn input() -> Input<'static> {
	input_from_str(include_str!("day19.txt"))
}


fn part1_impl(input: Input) -> usize {
	let Input { rules, messages } = input;
	messages.filter(|m| Input::message_matches_rule0(&rules, m)).count()
}

pub(crate) fn part1() -> usize {
	part1_impl(input())
}


fn part2_impl(input: Input) -> usize {
	let Input { mut rules, messages } = input;
	rules[8] = Rule::Refs(RuleRefs(vec![42]), Some(RuleRefs(vec![42, 8])));
	rules[11] = Rule::Refs(RuleRefs(vec![42, 31]), Some(RuleRefs(vec![42, 11, 31])));
	messages.filter(|m| Input::message_matches_rule0(&rules, m)).count()
}

pub(crate) fn part2() -> usize {
	part2_impl(input())
}


mod parsing {
	use std::{num::ParseIntError, str::FromStr};
	use itertools::Itertools as _;
	use super::{RuleRefs, Rule, Input};

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum RuleRefsError {
		InvalidFormat,
		InvalidIndex { column: usize, source: ParseIntError },
	}

	impl FromStr for RuleRefs {
		type Err = RuleRefsError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use RuleRefsError::*;
			let refs = s.split(' ')
				.scan(0, |c, rf| {
					let column = *c + 1;
					*c += rf.len() + 1;
					Some(rf.parse().map_err(|e| InvalidIndex { column, source: e }))
				})
				.collect::<Result<Vec<_>, _>>()?;
			if refs.is_empty() { return Err(InvalidFormat) }
			Ok(RuleRefs(refs))
		}
	}

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum RuleError {
		InvalidFormat,
		InvalidChar,
		InvalidRuleRefs(RuleRefsError),
	}

	impl FromStr for Rule {
		type Err = RuleError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use RuleError::*;
			if let Some(chr) = s.strip_prefix('"') {
				let chr = chr.strip_suffix('"').ok_or(InvalidChar)?;
				Ok(Rule::Char(chr.chars().exactly_one().map_err(|_| InvalidChar)?))
			} else if let Some((left, right)) = {
				let mut split = s.splitn(2, " | ");
				split.next().map(|s| (s, split.next()))
			} {
				let left = left.parse().map_err(InvalidRuleRefs)?;
				let right = right.map(|r| r.parse().map_err(InvalidRuleRefs)).transpose()?;
				Ok(Rule::Refs(left, right))
			} else {
				Err(InvalidFormat)
			}
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum RulesLineErrorSource {
		InvalidFormat,
		Id(ParseIntError),
		Rule(RuleError),
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum RulesError {
		Line { line: usize, source: RulesLineErrorSource },
		MissingRef(usize),
		InvalidRef(usize),
	}

	fn try_rules_from_lines<'a>(lines: impl Iterator<Item = (usize, &'a str)>) -> Result<Vec<Rule>, RulesError> {
		let mut rules = lines
			.map(|(l, line)| {
				let err = move |source| RulesError::Line { line: l + 1, source };
				let (id, rule) = line.split_once(": ").ok_or_else(|| err(RulesLineErrorSource::InvalidFormat))?;
				let id = id.parse::<usize>().map_err(|e| err(RulesLineErrorSource::Id(e)))?;
				let rule = rule.parse().map_err(|e| err(RulesLineErrorSource::Rule(e)))?;
				Ok((id, rule))
			})
			.collect::<Result<Vec<_>, _>>()?;

		rules.sort_by_key(|(id, _)| *id);

		// TODO(bm-w): Check for circular rules?
		for (i, (id, rule)) in rules.iter().enumerate() {
			if i != *id {
				return Err(RulesError::MissingRef(i)) }
			if let Rule::Refs(left, right) = rule {
				for &rf in left.0.iter().chain(right.iter().flat_map(|r| r.0.iter())) {
					if rf >= rules.len() {
						return Err(RulesError::MissingRef(rf)) }
				}
			}
		}
		
		Ok(rules.into_iter().map(|(_, rule)| rule).collect())
	}

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum InputError {
		InvalidRule(RulesError),
		InvalidFormat { line: usize },
	}

	impl<'m> TryFrom<&'m str> for Input<'m> {
		type Error = InputError;
		fn try_from(value: &'m str) -> Result<Self, Self::Error> {
			use InputError::*;
			let mut lines = value.lines();
			let rules = try_rules_from_lines(lines.by_ref()
				.take_while_ref(|line| !line.is_empty())
				.enumerate())
				.map_err(InvalidRule)?;
			if !matches!(lines.next(), Some("")) {
				return Err(InvalidFormat { line: rules.len() + 1 })
			}
			Ok(Input { rules, messages: Box::new(lines) })
		}
	}


	#[test]
	fn input() -> Result<(), InputError> {
		Input::try_from(super::TEST_INPUT_PART1).map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUT_PART1: &str = indoc::indoc! { r#"
	0: 4 1 5
	1: 2 3 | 3 2
	2: 4 4 | 5 5
	3: 4 5 | 5 4
	4: "a"
	5: "b"

	ababbb
	bababa
	abbbab
	aaabbb
	aaaabbb
"# };

#[cfg(test)]
const TEST_INPUT_PART2: &str = indoc::indoc! { r#"
	42: 9 14 | 10 1
	9: 14 27 | 1 26
	10: 23 14 | 28 1
	1: "a"
	11: 42 31
	5: 1 14 | 15 1
	19: 14 1 | 14 14
	12: 24 14 | 19 1
	16: 15 1 | 14 14
	31: 14 17 | 1 13
	6: 14 14 | 1 14
	2: 1 24 | 14 4
	0: 8 11
	13: 14 3 | 1 12
	15: 1 | 14
	17: 14 2 | 1 7
	23: 25 1 | 22 14
	28: 16 1
	4: 1 1
	20: 14 14 | 1 15
	3: 5 14 | 16 1
	27: 1 6 | 14 18
	14: "b"
	21: 14 1 | 1 14
	25: 1 1 | 1 14
	22: 14 14
	8: 42
	26: 14 22 | 1 20
	18: 15 15
	7: 14 5 | 1 21
	24: 14 1
	29: "!"
	30: "!"
	32: "!"
	33: "!"
	34: "!"
	35: "!"
	36: "!"
	37: "!"
	38: "!"
	39: "!"
	40: "!"
	41: "!"

	abbbbbabbbaaaababbaabbbbabababbbabbbbbbabaaaa
	bbabbbbaabaabba
	babbbbaabbbbbabbbbbbaabaaabaaa
	aaabbbbbbaaaabaababaabababbabaaabbababababaaa
	bbbbbbbaaaabbbbaaabbabaaa
	bbbababbbbaaaaaaaabbababaaababaabab
	ababaaaaaabaaab
	ababaaaaabbbaba
	baabbaaaabbaaaababbaababb
	abbbbabbbbaaaababbbbbbaaaababb
	aaaaabbaabaaaaababaa
	aaaabbaaaabbaaa
	aaaabbaabbaaaaaaabbbabbbaaabbaabaaa
	babaaabbbaaabaababbaabababaaab
	aabbbbbaabbbaaaaaabbbbbababaaaaabbaaabba
"# };

#[test]
fn tests() {
	assert_eq!(part1_impl(input_from_str(TEST_INPUT_PART1)), 2);
	assert_eq!(part1(), 113);
	assert_eq!(part1_impl(input_from_str(TEST_INPUT_PART2)), 3);
	assert_eq!(part2_impl(input_from_str(TEST_INPUT_PART2)), 12);
	assert_eq!(part2(), 253);
}
