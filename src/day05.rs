// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::collections::HashSet;
use itertools::Itertools as _;


const ROWS: usize = 7;
const COLUMNS: usize = 3;


#[cfg_attr(test, derive(Debug))]
enum Row { Front, Back }

#[cfg_attr(test, derive(Debug))]
enum Column { Left, Right }

#[cfg_attr(test, derive(Debug))]
struct Seat([Row; ROWS], [Column; COLUMNS]);

impl Seat {
	/// Row & column numbers (e.g. `[44, 5]`).
	fn numeric(&self) -> [u8; 2] {
		macro_rules! num {
			( $idx:tt, $lim:literal, $low:path, $high:path ) => {
				self.$idx.iter().fold((0, $lim), |num, row| {
					let half = (num.0 + num.1) / 2;
					match row {
						$low => (num.0, half),
						$high => (half, num.1),
					}
				}).0
			}
		}
		[num!(0, 128, Row::Front, Row::Back), num!(1, 8, Column::Left, Column::Right)]
	}

	fn id(&self) -> u32 {
		let [row, column] = self.numeric();
		row as u32 * 8 + column as u32
	}

	fn with_highest_id(from: &[Seat]) -> Option<&Seat> {
		from.iter().max_by_key(|s| s.id())
	}
}


fn input_seats() -> Vec<Seat> {
	parsing::try_seats_from_str(include_str!("day05.txt")).unwrap()
}


fn part1_impl(input_seats: &[Seat]) -> u32 {
	Seat::with_highest_id(input_seats).unwrap().id()
}

pub(crate) fn part1() -> u32 {
	part1_impl(&input_seats())
}


pub(crate) fn part2() -> u32 {
	let input_seats = input_seats();
	let seat_with_highest_id = Seat::with_highest_id(&input_seats).unwrap();
	let [highest_row, _] = seat_with_highest_id.numeric();

	// Except very front and back
	let mut most_seats = (1..highest_row)
		.cartesian_product(0..=7)
		.map(|(r, c)| [r as u8, c as u8])
		.collect::<HashSet<_>>();

	for seat in input_seats {
		most_seats.remove(&seat.numeric());
	}

	assert!(most_seats.len() == 1);
	let [row, column] = most_seats.into_iter().next().unwrap();
	row as u32 * 8 + column	as u32
}


mod parsing {
	use std::str::FromStr;
	use super::{ROWS, COLUMNS, Row, Column, Seat};

	#[derive(Debug)]
	pub(super) struct InvalidRowError(char);

	impl TryFrom<char> for Row {
		type Error = InvalidRowError;
		fn try_from(value: char) -> Result<Self, Self::Error> {
			match value {
				'F' => Ok(Row::Front),
				'B' => Ok(Row::Back),
				found => Err(InvalidRowError(found)),
			}
		}
	}

	#[derive(Debug)]
	pub(super) struct InvalidColumnError(char);

	impl TryFrom<char> for Column {
		type Error = InvalidColumnError;
		fn try_from(value: char) -> Result<Self, Self::Error> {
			match value {
				'L' => Ok(Column::Left),
				'R' => Ok(Column::Right),
				found => Err(InvalidColumnError(found)),
			}
		}
	}


	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum SeatError {
		InvalidFormat { column: usize },
		InvalidRow { column: usize, source: InvalidRowError },
		InvalidColumn { column: usize, source: InvalidColumnError },
	}

	impl FromStr for Seat {
		type Err= SeatError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use SeatError::*;
			let mut chars = s.chars().enumerate();
			let rows = chars.by_ref().take(ROWS)
				.map(|(c, chr)| chr.try_into()
					.map_err(|e| InvalidRow { column: c + 1, source: e }))
				.collect::<Result<Vec<_>, _>>()?
				.try_into()
				.map_err(|e: Vec<_>| InvalidFormat { column: e.len() + 1 })?;
			let columns = chars.by_ref().take(COLUMNS)
				.map(|(c, chr)| chr.try_into()
					.map_err(|e| InvalidColumn { column: c + 1, source: e }))
				.collect::<Result<Vec<_>, _>>()?
				.try_into()
				.map_err(|e: Vec<_>| InvalidFormat { column: ROWS + e.len() + 1 })?;
			if chars.next().is_some() {
				return Err(InvalidFormat { column: ROWS + COLUMNS + 1 });
			}
			Ok(Seat(rows, columns))
		}
	}

	#[derive(Debug)]
	#[allow(dead_code)]
	pub(super) struct InvalidSeatsError { line: usize, source: SeatError }

	pub(super) fn try_seats_from_str(s: &str) -> Result<Vec<Seat>, InvalidSeatsError> {
		s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| InvalidSeatsError { line: l + 1, source: e }))
			.collect()
	}


	#[test]
	fn row() {
		('X'.try_into() as Result<Row, _>).unwrap_err();
		('F'.try_into() as Result<Row, _>).unwrap();
		('B'.try_into() as Result<Row, _>).unwrap();
	}

	#[test]
	fn column() {
		('X'.try_into() as Result<Column, _>).unwrap_err();
		('L'.try_into() as Result<Column, _>).unwrap();
		('R'.try_into() as Result<Column, _>).unwrap();
	}

	#[test]
	fn seat() {
		use SeatError::*;
		assert!(matches!("".parse::<Seat>(), Err(InvalidFormat { column: 1 })));
		assert!(matches!("FBX".parse::<Seat>(), Err(InvalidRow { column: 3, source: _ })));
		assert!(matches!("FBF".parse::<Seat>(), Err(InvalidFormat { column: 4 })));
		assert!(matches!("FBFBFBFX".parse::<Seat>(), Err(InvalidColumn { column: 8, source: _ })));
		assert!(matches!("FBFBFBFLR".parse::<Seat>(), Err(InvalidFormat { column: 10 })));
		assert!(matches!("FBFBFBFLRLX".parse::<Seat>(), Err(InvalidFormat { column: 11 })));
		assert!(matches!("FBFBFBFLRL".parse::<Seat>(), Ok(_)));
	}
}


#[test]
fn tests() -> Result<(), parsing::SeatError> {
	assert_eq!("FBFBBFFRLR".parse::<Seat>()?.numeric(), [44, 5]);
	assert_eq!("FBFBBFFRLR".parse::<Seat>()?.id(), 357);
	assert_eq!("BFFFBBFRRR".parse::<Seat>()?.numeric(), [70, 7]);
	assert_eq!("BFFFBBFRRR".parse::<Seat>()?.id(), 567);
	assert_eq!("FFFBBBFRRR".parse::<Seat>()?.numeric(), [14, 7]);
	assert_eq!("FFFBBBFRRR".parse::<Seat>()?.id(), 119);
	assert_eq!("BBFFBBFRLL".parse::<Seat>()?.numeric(), [102, 4]);
	assert_eq!("BBFFBBFRLL".parse::<Seat>()?.id(), 820);
	assert_eq!(part1(), 894);
	assert_eq!(part2(), 579);
	Ok(())
}
