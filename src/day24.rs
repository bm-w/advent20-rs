// Copyright (c) 2022 Bastiaan Marinus van de Weerd


enum Dir { East, SouthEast, SouthWest, West, NorthWest, NorthEast }

struct Instr(Vec<Dir>);

struct Floor(Vec<[i32; 2]>);

impl Floor {
	// TODO(bm-w): Return `impl IntoIterator<…, IntoIter: ExactSizeIterator>`?
	fn black_tiles_from_instrs<I>(instrs: I) -> impl ExactSizeIterator<Item = [i32; 2]>
	where I: AsRef<[Instr]> {
		use std::collections::HashSet;

		let mut black_tiles = HashSet::new();

		for instr in instrs.as_ref() {
			let mut pos = [0_i32; 2];
			let mut add_to_pos = |d0, d1| { pos[0] += d0; pos[1] += d1 };

			use Dir::*;
			for dir in &instr.0 { match dir {
				East => add_to_pos(1, 0),
				SouthEast => add_to_pos(1, 1),
				SouthWest => add_to_pos(0, 1),
				West => add_to_pos(-1, 0),
				NorthWest => add_to_pos(-1, -1),
				NorthEast => add_to_pos(0, -1),
			} }

			if !black_tiles.insert(pos) {
				black_tiles.remove(&pos);
			}
		}

		black_tiles.into_iter()
	}
}

impl<I> From<I> for Floor where I: AsRef<[Instr]> {
	fn from(instrs: I) -> Self {
		Floor(Floor::black_tiles_from_instrs(instrs).collect())
	}
}

impl Floor {
	fn tick(&mut self) {
		use std::{iter, mem};
		use itertools::Itertools;

		fn pos_adjacent(pos: &[i32; 2]) -> [[i32; 2]; 6] {
			[
				[pos[0] + 1, pos[1]    ],
				[pos[0] + 1, pos[1] + 1],
				[pos[0]    , pos[1] + 1],
				[pos[0] - 1, pos[1]    ],
				[pos[0] - 1, pos[1] - 1],
				[pos[0]    , pos[1] - 1],
			]
		}

		for (pos, (is_black, adjacent_count)) in mem::take(&mut self.0)
			.iter()
			.flat_map(|pos| iter::once((*pos, (true, 0_usize)))
				.chain(pos_adjacent(pos)
					.map(|adj_pos| (adj_pos, (false, 1_usize)))))
			.into_grouping_map()
			.fold_first(|(acc_ib, acc_ac), _, (is_black, adjacent_count)|
				(acc_ib || is_black, acc_ac + adjacent_count))
		{
			if if is_black { adjacent_count != 0 && adjacent_count <= 2 } else { adjacent_count == 2 } {
				self.0.push(pos)
			}
		}
	}
}


fn input_instrs_from_str(s: &str) -> Vec<Instr> {
	parsing::try_instrs_from_str(s).unwrap()
}

fn input_instrs() -> Vec<Instr> {
	input_instrs_from_str(include_str!("day24.txt"))
}


fn part1_impl(input_instrs: &[Instr]) -> usize {
	Floor::black_tiles_from_instrs(input_instrs).len()
}

pub(crate) fn part1() -> usize {
	part1_impl(&input_instrs())
}


fn part2_impl(input_instrs: &[Instr]) -> usize {
	let mut floor = Floor::from(input_instrs);
	for _ in 0..100 { floor.tick() }
	floor.0.len()
}

pub(crate) fn part2() -> usize {
	part2_impl(&input_instrs())
}


mod parsing {
	use std::str::FromStr;
	use super::{Dir, Instr};

	#[derive(Debug)]
	pub(super) enum DirError {
		Char(char),
		Next(Option<char>)
	}

	impl<F> TryFrom<(char, F)> for Dir
	where F: FnOnce() -> Option<char> {
		type Error = DirError;
		fn try_from((chr, next): (char, F)) -> Result<Self, Self::Error> {
			use {Dir::*, DirError::*};
			match chr {
				'e' => Ok(East),
				'w' => Ok(West),
				'n' => match next() {
					Some('e') => Ok(NorthEast),
					Some('w') => Ok(NorthWest),
					next => Err(Next(next)),
				}
				's' => match next() {
					Some('e') => Ok(SouthEast),
					Some('w') => Ok(SouthWest),
					next => Err(Next(next)),
				}
				chr => Err(Char(chr)),
			}
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum InstrError {
		Empty,
		Dir { column: usize, source: DirError },
	}

	impl FromStr for Instr {
		type Err = InstrError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use InstrError::{Empty, Dir as DirError};
			let mut chars = s.chars().enumerate();
			let mut dirs = Vec::new();
			while let Some((mut c, chr)) = chars.next() {
				let next = || match chars.next() {
					Some((next_c, next_char)) => { c = next_c; Some(next_char) }
					None => None
				};
				dirs.push(Dir::try_from((chr, next))
					.map_err(|e| DirError { column: c + 1, source: e })?);
			}
			if dirs.is_empty() { return Err(Empty) }
			Ok(Instr(dirs))
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum InstrsError {
		Empty,
		Instr { line: usize, source: InstrError }
	}

	pub(super) fn try_instrs_from_str(s: &str) -> Result<Vec<Instr>, InstrsError> {
		use InstrsError::{Empty, Instr as InstrError};
		let instrs = s.lines().enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| InstrError { line: l + 1, source: e }))
			.collect::<Result<Vec<_>, _>>()?;
		if instrs.is_empty() { return Err(Empty) }
		Ok(instrs)
	}


	#[test]
	fn input() -> Result<(), InstrsError> {
		try_instrs_from_str(super::TEST_INPUT).map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUT: &str = indoc::indoc! { "
	sesenwnenenewseeswwswswwnenewsewsw
	neeenesenwnwwswnenewnwwsewnenwseswesw
	seswneswswsenwwnwse
	nwnwneseeswswnenewneswwnewseswneseene
	swweswneswnenwsewnwneneseenw
	eesenwseswswnenwswnwnwsewwnwsene
	sewnenenenesenwsewnenwwwse
	wenwwweseeeweswwwnwwe
	wsweesenenewnwwnwsenewsenwwsesesenwne
	neeswseenwwswnwswswnw
	nenwswwsewswnenenewsenwsenwnesesenew
	enewnwewneswsewnwswenweswnenwsenwsw
	sweneswneswneneenwnewenewwneswswnese
	swwesenesewenwneswnwwneseswwne
	enesenwswwswneneswsenwnewswseenwsese
	wnwnesenesenenwwnenwsewesewsesesew
	nenewswnwewswnenesenwnesewesw
	eneswnwswnwsenenwnwnwwseeswneewsenese
	neswnwewnwnwseenwseesewsenwsweewe
	wseweeenwnesenwwwswnew
" };

#[test]
fn tests() {
	assert_eq!(part1_impl(&input_instrs_from_str(TEST_INPUT)), 10);
	assert_eq!(part1(), 436);
	assert_eq!(part2_impl(&input_instrs_from_str(TEST_INPUT)), 2208);
	assert_eq!(part2(), 4133);
}
