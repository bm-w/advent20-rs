// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::collections::HashSet;


#[cfg_attr(test, derive(Debug))]
struct Grid<const N: usize> {
	active_spaces: HashSet<[isize; N]>,
}

impl<const N: usize> Grid<N> {
	fn adjacent_spaces(&self, from: [isize; N]) -> impl Iterator<Item = [isize; N]> + '_ {
		use {std::iter, itertools::Itertools as _};
		iter::repeat(-1..=1).take(N).multi_cartesian_product()
			.map(move |diffs| {
				let mut space = from;
				for (s, d) in space.iter_mut().zip(diffs.into_iter()) { *s += d }
				space
			})
			.filter(move |space| *space != from)
	}

	fn tick(&mut self) {
		use std::collections::HashMap;

		// All neighbors of an active space have at least one active neighbor
		let mut active_neighbor_counts = HashMap::<_, usize>::with_capacity(self.active_spaces.len() * N * 5);
		for neighbor_space in self.active_spaces.iter()
			.copied() // Copying so that we can modify in-place below
			.flat_map(|space| self.adjacent_spaces(space))
		{
			*active_neighbor_counts.entry(neighbor_space).or_default() += 1;
		}

		// TODO(bm-w): Rather use `drain_filter` once it becomes stable
		// Some active spaces may themselves not have any active neighbors so
		// wouldn’t have been found above, but we still want to include them below
		for space in self.active_spaces.iter() {
			active_neighbor_counts.entry(*space).or_default();
		}

		// Iterate and apply the (de)activation rules
		for (space, active_neighbors_count) in active_neighbor_counts {
			if self.active_spaces.contains(&space) {
				if active_neighbors_count != 2 && active_neighbors_count != 3 {
					self.active_spaces.remove(&space);
				}
			} else if active_neighbors_count == 3 {
				self.active_spaces.insert(space);
			}
		}
	}

	fn tickn(&mut self, times: usize) {
		for _ in 0..times { self.tick(); }
	}
}


fn input_grid_from_str<const N: usize>(s: &str) -> Grid<N> {
	s.parse().unwrap()
}

fn input_grid<const N: usize>() -> Grid<N> {
	input_grid_from_str(include_str!("day17.txt"))
}


fn part1_impl(mut input_grid: Grid<3>) -> usize {
	input_grid.tickn(6);
	input_grid.active_spaces.len()
}

pub(crate) fn part1() -> usize {
	part1_impl(input_grid())
}


fn part2_impl(mut input_grid: Grid<4>) -> usize {
	input_grid.tickn(6);
	input_grid.active_spaces.len()
}

pub(crate) fn part2() -> usize {
	part2_impl(input_grid())
}


#[cfg(test)]
use std::{fmt::Write, ops::RangeInclusive};

#[cfg(test)]
impl<const N: usize> Grid<N> {
	fn bounds(&self) -> Option<[RangeInclusive<isize>; N]> {
		if self.active_spaces.is_empty() { return None }
		let (min, max) = self.active_spaces.iter()
			.fold(([isize::MAX; N], [isize::MIN; N]), |(mut min, mut max), space| {
				for (min, max, s) in itertools::izip!(min.iter_mut(), max.iter_mut(), space) {
					*min  = *s.min(min);
					*max  = *s.min(max);
				}
				(min, max)
			});
		min.into_iter().zip(max.into_iter()).map(|(min, max)| min..=max).collect::<Vec<_>>().try_into().ok()
	}
}

// TODO(bm-w): Generalize to 3 or 4 dimensions
#[cfg(test)]
impl std::fmt::Display for Grid<3> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use itertools::iproduct;

		let [.., x_bounds, y_bounds, z_bounds ] = match self.bounds() {
			Some(bounds) => bounds,
			_ => return write!(f, "(Empty grid)")
		};

		for z in z_bounds {
			writeln!(f, "z={z}")?;
			for (y, x) in iproduct!(y_bounds.clone(), x_bounds.clone()) {
				f.write_char(if self.active_spaces.contains(&[x, y, z]) { '#' } else { '.' })?;
				if x == *x_bounds.end() { f.write_char('\n')? }
			}
			f.write_char('\n')?
		}
		Ok(())
	}
}


mod parsing {
	use std::str::FromStr;
	use super::Grid;

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum GridError {
		InvalidFormat { line: usize, column: usize },
		InvalidSpace { line: usize, column: usize, found: char },
	}

	impl<const N: usize> FromStr for Grid<N> {
		type Err = GridError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use {std::iter, itertools::Either, GridError::*};
			let space = [0isize; N];
			let mut lines = s.lines().peekable();
			let width = lines.peek().map(|line| line.len())
				.ok_or(InvalidFormat { line: 1, column: 1 })?;
			let active_spaces = lines.enumerate()
				.flat_map(|(l, line)|
					if line.len() != width {
						Either::Left(iter::once(Err(InvalidFormat { line: l + 1, column: line.len().min(width) + 1 })))
					} else {
						Either::Right(line.chars()
							.enumerate()
							.filter_map(move |(c, chr)| match chr {
								'#' => {
									let mut space = space;
									space[N - 3] = c as isize;
									space[N - 2] = l as isize;
									Some(Ok(space))
								}
								'.' => None,
								found => Some(Err(InvalidSpace { line: l + 1, column: c + 1, found }))
							}))
					})
				.collect::<Result<_, _>>()?;	
			Ok(Grid { active_spaces })
		}
	}


	#[test]
	fn grid() {
		use {std::collections::HashSet, GridError::*};
		assert!(matches!("".parse::<Grid<3>>(), Err(InvalidFormat { line: 1, column: 1 })));
		assert!(matches!(".\n\n".parse::<Grid<3>>(), Err(InvalidFormat { line: 2, column: 1 })));
		assert!(matches!(".#\n.#.\n".parse::<Grid<3>>(), Err(InvalidFormat { line: 2, column: 3 })));
		assert!(matches!(".#.\n#.#\n.#x\n".parse::<Grid<3>>(), Err(InvalidSpace { line: 3, column: 3, found: 'x'})));
		assert!(matches!(".#.\n#.#\n.#.\n".parse::<Grid<3>>(), Ok(Grid { active_spaces })
			if active_spaces == HashSet::from([[1, 0, 0], [0, 1, 0], [2, 1, 0], [1, 2, 0]])));
	}

	#[test]
	fn input() -> Result<(), GridError> {
		super::TEST_INPUT.parse::<Grid<3>>()
			.and(super::TEST_INPUT.parse::<Grid<4>>())
			.map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUT: &str = indoc::indoc! { "
	.#.
	..#
	###
" };

#[test]
fn tests() {
	assert_eq!(part1_impl(input_grid_from_str(TEST_INPUT)), 112);
	assert_eq!(part1(), 375);
	assert_eq!(part2_impl(input_grid_from_str(TEST_INPUT)), 848);
	assert_eq!(part2(), 2192);
}
