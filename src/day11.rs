// Copyright (c) 2022 Bastiaan Marinus van de Weerd


/// `true` for occupied, else `false`.
type Seat = bool;

#[cfg_attr(test, derive(Debug))]
#[derive(Clone)]
struct WaitingArea {
	/// `Some(…)` for seat, else `None` for open space.
	spaces: Vec<Option<Seat>>,
	width: usize,
}

impl WaitingArea {
	/// Returns clockwise from top-left.
	fn adjacent_spaces(&self, from: usize) -> [Option<Seat>; 8] {
		let top = from < self.width;
		let right = from % self.width == self.width - 1;
		let bottom = from >= self.spaces.len() - self.width;
		let left = from % self.width == 0;

		let mut adj_spaces = [None; 8];
		if !left && !top { adj_spaces[0] = self.spaces[from - self.width - 1]; }
		if !top { adj_spaces[1] = self.spaces[from - self.width]; }
		if !top && !right { adj_spaces[2] = self.spaces[from - self.width + 1]; }
		if !right { adj_spaces[3] = self.spaces[from + 1]; }
		if !right && !bottom { adj_spaces[4] = self.spaces[from + self.width + 1]; }
		if !bottom { adj_spaces[5] = self.spaces[from + self.width]; }
		if !bottom && !left { adj_spaces[6] = self.spaces[from + self.width - 1]; }
		if !left { adj_spaces[7] = self.spaces[from - 1]; }
		adj_spaces
	}

	/// Returns clockwise from top-left (not necessarily adjacent).
	fn visible_spaces(&self, from: usize) -> [Option<Seat>; 8] {
		/// Returns the visible space — `Some(occupied)` seat or `None` — `from`
		/// a seat in some `dir` (`[Some(false), Some(false)]` towards the top-left,
		/// `[S(t), None]` towards the right, etc.).
		fn visible_space(spaces: &[Option<Seat>], width: usize, from: usize, dir: [Option<bool>; 2]) -> Option<Seat> {
			if dir[0] == Some(false) && from % width == 0 { return None }
			if dir[0] == Some(true) && from % width == width - 1 { return None }
			if dir[1] == Some(false) && from < width { return None }
			if dir[1] == Some(true) && from >= spaces.len() - width { return None }
			let idx_dir = [
				dir[0].map_or(0, |p| if p { 1 } else { -1isize }),
				dir[1].map_or(0, |p| if p { width as isize } else { -(width as isize) }),
			];
			let to = (from as isize + idx_dir[0] + idx_dir[1]) as usize;
			spaces[to].or_else(|| visible_space(spaces, width, to, dir))
		}
		[
			visible_space(&self.spaces, self.width, from, [Some(false), Some(false)]),
			visible_space(&self.spaces, self.width, from, [None, Some(false)]),
			visible_space(&self.spaces, self.width, from, [Some(true), Some(false)]),
			visible_space(&self.spaces, self.width, from, [Some(true), None]),
			visible_space(&self.spaces, self.width, from, [Some(true), Some(true)]),
			visible_space(&self.spaces, self.width, from, [None, Some(true)]),
			visible_space(&self.spaces, self.width, from, [Some(false), Some(true)]),
			visible_space(&self.spaces, self.width, from, [Some(false), None]),
		]
	}

	fn tick<const N: usize, F>(&mut self, considering_spaces: F) -> bool
	where F: Fn(&Self, usize) -> [Option<Seat>; 8] {
		let mut any_change = false;
		let mut next_spaces = self.spaces.clone();
		for (idx, seat) in next_spaces.iter_mut().enumerate() {
			if let Some(occupied) = seat.as_mut() {
				let adj_spaces = considering_spaces(self, idx);
				if *occupied && adj_spaces.into_iter().filter(|s| *s == Some(true)).count() >= N {
					any_change = true;
					*occupied = false;
				} else if !*occupied && adj_spaces.into_iter().all(|s| s != Some(true)) {
					any_change = true;
					*occupied = true;
				}
			}
		}
		self.spaces = next_spaces;
		any_change
	}
}


fn input_waiting_area_from_str(s: &str) -> WaitingArea {
	s.parse().unwrap()
}

fn input_waiting_area() -> WaitingArea {
	input_waiting_area_from_str(include_str!("day11.txt"))
}


fn part1_impl(mut input_waiting_area: WaitingArea) -> usize {
	while input_waiting_area.tick::<4, _>(WaitingArea::adjacent_spaces) {}
	input_waiting_area.spaces.into_iter().filter(|s| *s == Some(true)).count()
}

pub(crate) fn part1() -> usize {
	part1_impl(input_waiting_area())
}


fn part2_impl(mut input_waiting_area: WaitingArea) -> usize {
	while input_waiting_area.tick::<5, _>(WaitingArea::visible_spaces) {}
	input_waiting_area.spaces.into_iter().filter(|s| *s == Some(true)).count()
}

pub(crate) fn part2() -> usize {
	part2_impl(input_waiting_area())
}


mod parsing {
	use std::str::FromStr;
	use super::WaitingArea;

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum WaitingAreaError {
		InvalidFormat { line: usize, column: usize },
		InvalidSpace { line: usize, column: usize, found: char },
	}

	impl FromStr for WaitingArea {
		type Err = WaitingAreaError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use {std::iter, itertools::Either, WaitingAreaError::*};
			let mut lines = s.lines()
				.enumerate()
				.peekable();
			let width = lines.peek()
				.map(|(_, line)| line.len())
				.ok_or(InvalidFormat { line: 1, column: 1 })?;
			let spaces = lines
				.flat_map(|(l, line)| if line.len() != width {
					Either::Left(iter::once(Err(InvalidFormat { line: l + 1, column: width.min(line.len()) + 1 })))
				} else {
					Either::Right(line.chars()
						.enumerate()
						.map(move |(c, chr)| match chr {
							'#' => Ok(Some(true)),
							'L' => Ok(Some(false)),
							'.' => Ok(None),
							found => Err(InvalidSpace { line: l + 1, column: c + 1, found })
						}))
				})
				.collect::<Result<_, _>>()?;
			Ok(WaitingArea { spaces, width })
		}
	}

	#[test]
	fn test() -> Result<(), WaitingAreaError> {
		use WaitingAreaError::*;
		assert!(matches!("".parse::<WaitingArea>(), Err(InvalidFormat { line: 1, column: 1 })));
		assert!(matches!("..\n.".parse::<WaitingArea>(), Err(InvalidFormat { line: 2, column: 2 })));
		assert!(matches!(super::TEST_INPUT.replacen('.', "x", 1).parse::<WaitingArea>(), Err(InvalidSpace { line: 1, column: 2, found: 'x' })));
		super::TEST_INPUT.parse::<WaitingArea>().map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUT: &str = indoc::indoc! { "
	L.LL.LL.LL
	LLLLLLL.LL
	L.L.L..L..
	LLLL.LL.LL
	L.LL.LL.LL
	L.LLLLL.LL
	..L.L.....
	LLLLLLLLLL
	L.LLLLLL.L
	L.LLLLL.LL
" };


#[test]
fn tests() {
	assert_eq!(part1_impl(input_waiting_area_from_str(TEST_INPUT)), 37);
	assert_eq!(part1(), 2441);
	assert_eq!(part2_impl(input_waiting_area_from_str(TEST_INPUT)), 26);
	assert_eq!(part2(), 2190);
}
