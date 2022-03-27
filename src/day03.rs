// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::iter;


#[cfg_attr(test, derive(Debug))]
struct Grid {
	/// Trees on the `true` spaces.
	spaces: Vec<bool>,
	width: usize,
}

impl Grid {
	fn spaces_along_slope(&self, slope: [u32; 2]) -> impl Iterator<Item = bool> + '_ {
		assert!(slope[1] > 0);
		let height = self.spaces.len() / self.width;
		let mut pos = [0, 0];
		iter::from_fn(move || {
			pos[0] += slope[0];
			pos[1] += slope[1];
			if pos[1] as usize >= height { return None }
			let wrapped_x = pos[0] as usize % self.width;
			let idx = pos[1] as usize * self.width + wrapped_x;
			Some(self.spaces[idx])
		})
	}
}


fn input_grid_from_str(s: &str) -> Grid {
	s.parse().unwrap()
}

fn input_grid() -> Grid {
	input_grid_from_str(include_str!("day03.txt"))
}


fn part1_impl(input_grid: Grid) -> usize {
	input_grid.spaces_along_slope([3, 1]).filter(|s| *s).count()
}

pub(crate) fn part1() -> usize {
	part1_impl(input_grid())
}


fn part2_impl(input_grid: Grid) -> usize {
	[[1, 1], [3, 1], [5, 1], [7, 1], [1, 2]]
		.into_iter()
		.map(|s| input_grid.spaces_along_slope(s).filter(|s| *s).count())
		.product()
}

pub(crate) fn part2() -> usize {
	part2_impl(input_grid())
}


mod parsing {
	use std::{str::FromStr, iter};
	use itertools::Either;
	use super::Grid;

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum GridError {
		InvalidFormat { line: usize, column: usize },
		InvalidSpace { line: usize, column: usize, found: char },
	}

	impl FromStr for Grid {
		type Err = GridError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use GridError::*;
			let (width, lines) = {
				let mut lines = s.lines();
				let first_line = lines.next()
					.and_then(|line| if line.is_empty() { None } else { Some(line) })
					.ok_or(InvalidFormat { line: 1, column: 1 })?;
				(first_line.len(), iter::once(first_line).chain(lines))
			};
			let spaces = lines
				.enumerate()
				.flat_map(|(l, line)| if line.len() != width {
					Either::Left(iter::once(Err(InvalidFormat { line: l + 1, column: line.len().min(width) + 1 })))
				} else {
					Either::Right(line.chars()
						.enumerate()
						.map(move |(c, chr)| match chr {
							'#' => Ok(true),
							'.' => Ok(false),
							found => Err(InvalidSpace { line: l + 1, column: c + 1, found })
						}))
				})
				.collect::<Result<_, _>>()?;
			Ok(Grid { spaces, width })
		}
	}


	#[test]
	fn test() -> Result<(), GridError> {
		use GridError::*;
		assert!(matches!("".parse::<Grid>(), Err(InvalidFormat { line: 1, column: 1 })));
		assert!(matches!("..\n.".parse::<Grid>(), Err(InvalidFormat { line: 2, column: 2 })));
		assert!(matches!("..\n...".parse::<Grid>(), Err(InvalidFormat { line: 2, column: 3 })));
		assert!(matches!("..\n.x".parse::<Grid>(), Err(InvalidSpace { line: 2, column: 2, found: 'x' })));
		super::TEST_INPUT.parse::<Grid>().map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUT: &str = indoc::indoc! { "
	..##.......
	#...#...#..
	.#....#..#.
	..#.#...#.#
	.#...##..#.
	..#.##.....
	.#.#.#....#
	.#........#
	#.##...#...
	#...##....#
	.#..#...#.#
" };

#[test]
fn tests() {
	assert_eq!(part1_impl(input_grid_from_str(TEST_INPUT)), 7);
	assert_eq!(part1(), 294);
	assert_eq!(part2_impl(input_grid_from_str(TEST_INPUT)), 336);
	assert_eq!(part2(), 5774564250);			
}
