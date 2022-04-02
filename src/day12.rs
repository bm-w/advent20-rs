// Copyright (c) 2022 Bastiaan Marinus van de Weerd


/// Cardinal direction / heading (AoC uses “direction”).
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy)]
enum CardDir {
	North,
	East,
	South,
	West,
}

#[cfg_attr(test, derive(Debug))]
enum TurnDir {
	Left,
	Right,
	/// 180°
	Around,
}

#[cfg_attr(test, derive(Debug))]
enum Instr {
	MoveDir(CardDir, u32),
	MoveForw(u32),
	Turn(TurnDir),
}


mod evasive_actions {
	use std::ops::AddAssign;
	use super::{CardDir, TurnDir, Instr};

	impl CardDir {
		fn vec(&self, dist: u32) -> [i32; 2] {
			use CardDir::*;
			match self {
				North => [0, -(dist as i32)],
				East => [dist as i32, 0],
				South => [0, dist as i32],
				West => [-(dist as i32), 0],
			}
		}
	}

	impl AddAssign<TurnDir> for CardDir {
		fn add_assign(&mut self, rhs: TurnDir) {
			use {CardDir::*, TurnDir::*};
			match (&self, rhs) {
				(North, Left) => *self = West,
				(North, Right) => *self = East,
				(North, Around) => *self = South,
				(East, Left) => *self = North,
				(East, Right) => *self = South,
				(East, Around) => *self = West,
				(South, Left) => *self = East,
				(South, Right) => *self = West,
				(South, Around) => *self = North,
				(West, Left) => *self = South,
				(West, Right) => *self = North,
				(West, Around) => *self = East,
			}
		}
	}

	// TODO(bm-w): Use opaque `impl` return types once they’re available in traits?
	pub(super) trait EvasiveActions: Iterator<Item = Instr> {
		/// Part 1.
		fn perform_wrong(self) -> Box<dyn Iterator<Item = [i32; 2]>>
		where Self: Sized + 'static {
			use Instr::*;
			let mut pos = ([0, 0], CardDir::East);
			Box::new(self.map(move |instr| {
				match instr {
					MoveDir(card_dir, dist) => {
						let vec = card_dir.vec(dist);
						pos.0[0] += vec[0];
						pos.0[1] += vec[1];
					}
					MoveForw(dist) => {
						let vec = pos.1.vec(dist);
						pos.0[0] += vec[0];
						pos.0[1] += vec[1];
					}
					Turn(turn_dir) => {
						pos.1 += turn_dir;
					}
				}
				pos.0
			}))
		}

		/// Part 1.
		fn perform_right(self) -> Box<dyn Iterator<Item = [i32; 2]>>
		where Self: Sized + 'static {
			use Instr::*;
			let mut pos = [0, 0];
			let mut waypoint = [10, -1];
			Box::new(self.map(move |instr| {
				match instr {
					MoveDir(card_dir, dist) => {
						let vec = card_dir.vec(dist);
						waypoint[0] += vec[0];
						waypoint[1] += vec[1];
					}
					MoveForw(dist) => {
						pos[0] += waypoint[0] * dist as i32;
						pos[1] += waypoint[1] * dist as i32;
					}
					Turn(turn_dir) => match turn_dir {
						TurnDir::Left => { waypoint.swap(0, 1); waypoint[1] *= -1; }
						TurnDir::Right => { waypoint.swap(0, 1); waypoint[0] *= -1; },
						TurnDir::Around => { waypoint[0] *= -1; waypoint[1] *= -1; }
					}
				}
				pos
			}))
		}
	}

	impl<I> EvasiveActions for I where I: Iterator<Item = Instr> {}
}

use evasive_actions::EvasiveActions as _;


fn input_instrs_from_str(s: &str) -> impl Iterator<Item = Instr> + '_ {
	parsing::instrs_from_str(s).map(|r| r.unwrap())
}

fn input_instrs() -> impl Iterator<Item = Instr> + 'static {
	input_instrs_from_str(include_str!("day12.txt"))
}


fn part1_impl(input_instrs: impl Iterator<Item = Instr> + 'static) -> u32 {
	input_instrs.perform_wrong().last().map(|pos| pos[0].abs() as u32 + pos[1].abs() as u32).unwrap()
}

pub(crate) fn part1() -> u32 {
	part1_impl(input_instrs())
}


fn part2_impl(input_instrs: impl Iterator<Item = Instr> + 'static) -> u32 {
	input_instrs.perform_right().last().map(|pos| pos[0].abs() as u32 + pos[1].abs() as u32).unwrap()
}

pub(crate) fn part2() -> u32 {
	part2_impl(input_instrs_from_str(include_str!("day12.txt")))
}


mod parsing {
	use std::{num::ParseIntError, str::FromStr};
	use super::{CardDir, TurnDir, Instr};

	fn card_dir_from_char(chr: char) -> Option<CardDir> {
		use CardDir::*;
		match chr {
			'N' => Some(North),
			'E' => Some(East),
			'S' => Some(South),
			'W' => Some(West),
			_ => None
		}
	}

	fn turn_dir_from_char(chr: char) -> Option<TurnDir> {
		use TurnDir::*;
		match chr {
			'L' => Some(Left),
			'R' => Some(Right),
			_ => None
		}
	}

	impl TurnDir {
		fn flip(&self) -> TurnDir {
			use TurnDir::*;
			match self {
				Left => Right,
				Right => Left,
				_ => panic!()
			}
		}
	}

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum InstrError {
		InvalidFormat,
		InvalidOp(char),
		InvalidArg(ParseIntError),
		InvalidTurn(u32),
	}

	impl FromStr for Instr {
		type Err = InstrError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use {Instr::*, InstrError::*};
			let parse_arg = || s[1..].parse::<u32>().map_err(InvalidArg);
			s.chars().next().map_or(Err(InvalidFormat), |chr|
				if let Some(card_dir) = card_dir_from_char(chr) {
					Ok(MoveDir(card_dir, parse_arg()?))
				} else if let Some(turn_dir) = turn_dir_from_char(chr) {
					match parse_arg()? {
						90 => Ok(Turn(turn_dir)),
						180 => Ok(Turn(TurnDir::Around)),
						270 => Ok(Turn(turn_dir.flip())),
						found => Err(InvalidTurn(found)),
					}
				} else if chr == 'F' {
					Ok(MoveForw(parse_arg()?))
				} else {
					Err(InvalidOp(chr))
				})
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct InstrsError { line: usize, source: InstrError }

	pub(super) fn instrs_from_str(s: &str) -> impl Iterator<Item = Result<Instr, InstrsError>> + '_ {
		s.lines()
			.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| InstrsError { line: l + 1, source: e }))
	}


	#[test]
	fn tests() -> Result<(), InstrsError> {
		use InstrError::*;
		assert!(matches!(card_dir_from_char('x'), None));
		assert!(matches!(card_dir_from_char('N'), Some(CardDir::North)));
		assert!(matches!(turn_dir_from_char('x'), None));
		assert!(matches!(turn_dir_from_char('L'), Some(TurnDir::Left)));
		assert!(matches!("".parse::<Instr>(), Err(InvalidFormat)));
		assert!(matches!("x".parse::<Instr>(), Err(InvalidOp('x'))));
		assert!(matches!("Fx".parse::<Instr>(), Err(InvalidArg(_))));
		assert!(matches!("L13".parse::<Instr>(), Err(InvalidTurn(13))));
		assert!(matches!("W1337".parse::<Instr>(), Ok(Instr::MoveDir(CardDir::West, 1337))));
		assert!(matches!("R180".parse::<Instr>(), Ok(Instr::Turn(TurnDir::Around))));
		assert!(matches!("L270".parse::<Instr>(), Ok(Instr::Turn(TurnDir::Right))));
		assert!(matches!("F54321".parse::<Instr>(), Ok(Instr::MoveForw(54321))));
		instrs_from_str(super::TEST_INPUT).collect::<Result<Vec<_>, _>>().map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUT: &str = indoc::indoc! { "
	F10
	N3
	F7
	R90
	F11
" };

#[test]
fn tests() {
	assert_eq!(part1_impl(input_instrs_from_str(TEST_INPUT)), 25);
	assert_eq!(part1(), 441);
	assert_eq!(part2_impl(input_instrs_from_str(TEST_INPUT)), 286);
	assert_eq!(part2(), 40014);
}
