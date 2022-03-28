// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::collections::{HashMap, HashSet};


#[derive(PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
enum Field {
	BirthYear,
	IssueYear,
	ExpirationYear,
	Height,
	HairColor,
	EyeColor,
	PassportId,
	CountryId,
}

#[cfg_attr(test, derive(Debug))]
struct Passport<'v>(HashMap<Field, &'v str>);

impl Field {
	fn is_valid(&self, value: &str) -> bool {
		use Field::*;
		match self {
			BirthYear =>
				value.parse::<u16>().map(|y| (1920..=2002).contains(&y)),
			IssueYear =>
				value.parse::<u16>().map(|y| (2010..=2020).contains(&y)),
			ExpirationYear =>
				value.parse::<u16>().map(|y| (2020..=2030).contains(&y)),
			Height =>
				if let Some(height) = value.strip_suffix("cm") {
					height.parse::<u8>().map(|h| (150..=193).contains(&h))
				} else if let Some(height) = value.strip_suffix("in") {
					height.parse::<u8>().map(|h| (59..=76).contains(&h))
				} else {
					Ok(false)
				}
			HairColor =>
				Ok(if let Some(hair_color) = value.strip_prefix('#') {
					hair_color.len() == 6 && !hair_color.contains(|c: char| !c.is_ascii_hexdigit())
				} else {
					false
				}),
			EyeColor =>
				Ok(["amb", "blu", "brn", "gry", "grn", "hzl", "oth"].contains(&value)),
			PassportId =>
				Ok(value.len() == 9 && !value.contains(|c: char| !c.is_numeric())),
			CountryId =>
				Ok(true),
		}.unwrap_or(false)
	}
}

impl Passport<'_> {
	fn has_required_fields(&self) -> bool {
		lazy_static! {
			static ref REQ_FIELDS: HashSet<Field> = {
				use Field::*;
				HashSet::from([BirthYear, IssueYear, ExpirationYear, Height, HairColor, EyeColor, PassportId])
			};
		}
		REQ_FIELDS.iter().all(|f| self.0.contains_key(f))
	}

	fn is_valid(&self) -> bool {
		self.has_required_fields() && self.0.iter().all(|(f, v)| f.is_valid(v))
	}
}


fn input_passports_from_str(s: &str) -> Vec<Passport> {
	parsing::try_passports_from_string(s).unwrap()
}

fn input_passports<'a>() -> Vec<Passport<'a>> {
	input_passports_from_str(include_str!("day04.txt"))
}


fn part1_impl(input_passports: &[Passport]) -> usize {
	input_passports.iter().filter(|p| p.has_required_fields()).count()
}

pub(crate) fn part1() -> usize {
	part1_impl(&input_passports())
}


fn part2_impl(input_passports: &[Passport]) -> usize {
	input_passports.iter().filter(|p| p.is_valid()).count()
}

pub(crate) fn part2() -> usize {
	part2_impl(&input_passports())
}


mod parsing {
	use std::str::FromStr;
	use itertools::Itertools as _;
	use super::{Field, Passport};

	#[derive(Debug)]
	pub(super) struct InvalidFieldError(String);

	impl FromStr for Field {
		type Err = InvalidFieldError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use Field::*;
			match s {
				"byr" => Ok(BirthYear),
				"iyr" => Ok(IssueYear),
				"eyr" => Ok(ExpirationYear),
				"hgt" => Ok(Height),
				"hcl" => Ok(HairColor),
				"ecl" => Ok(EyeColor),
				"pid" => Ok(PassportId),
				"cid" => Ok(CountryId),
				found => Err(InvalidFieldError(found.to_owned())),
			}
		}
	}

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum PassportError {
		InvalidFormat { line: usize, column: usize },
		InvalidField { line: usize, column: usize, source: InvalidFieldError },
	}

	struct EnumeratedLines<'l, I>(I) where I: Iterator<Item = (usize, &'l str)>;

	impl<'l, I> TryFrom<EnumeratedLines<'l, I>> for Passport<'l>
	where I: Iterator<Item = (usize, &'l str)> {
		type Error = PassportError;
		fn try_from(lines: EnumeratedLines<'l, I>) -> Result<Self, Self::Error> {
			use PassportError::*;
			let fields = lines.0
				.flat_map(|(l, line)|
					line.split_ascii_whitespace()
						.scan(0, |c, s| {
							let cs = *c;
							*c += s.len() + 1;
							Some((cs, s))
						})
						.map(move |(c, s)| s.split_once(':')
							.ok_or(InvalidFormat { line: l + 1, column: c + 1 })
							.and_then(|(s, v)| s.parse()
								.map(|f| (f, v))
								.map_err(|e| InvalidField { line: l + 1, column: c + 1, source: e }))))
				.collect::<Result<_, _>>()?;
			Ok(Passport(fields))
		}
	}

	pub(super) fn try_passports_from_string(s: &str) -> Result<Vec<Passport>, PassportError> {
		s.lines()
			.enumerate()
			.group_by(|(_, line)| line.is_empty())
			.into_iter()
			.filter_map(|(discard, lines)| if discard { None }
				else { Some(Passport::try_from(EnumeratedLines(lines))) })
			.collect::<Result<_, _>>()
	}


	#[test]
	fn test() -> Result<(), PassportError> {
		try_passports_from_string(super::TEST_INPUT).map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUT: &str = indoc::indoc! { "
	ecl:gry pid:860033327 eyr:2020 hcl:#fffffd
	byr:1937 iyr:2017 cid:147 hgt:183cm

	iyr:2013 ecl:amb cid:350 eyr:2023 pid:028048884
	hcl:#cfa07d byr:1929

	hcl:#ae17e1 iyr:2013
	eyr:2024
	ecl:brn pid:760753108 byr:1931
	hgt:179cm

	hcl:#cfa07d eyr:2025 pid:166559648
	iyr:2011 ecl:brn hgt:59in
" };

#[test]
fn tests() {
	assert_eq!(part1_impl(&input_passports_from_str(TEST_INPUT)), 2);
	assert_eq!(part1(), 210);
	assert_eq!(part2_impl(&input_passports_from_str(TEST_INPUT)), 2);
	assert_eq!(part2(), 131);
}
