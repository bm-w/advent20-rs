// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::{collections::{VecDeque, HashSet}, ops::{Index, IndexMut}};


#[derive(Debug)]
struct Game {
	players: [VecDeque<u8>; 2],
}

#[derive(Debug)]
enum Player { One, Two }

/// `Ok((cards_played, round_winning_player))` if the game advanced,
/// or `Err(game_winning_player)` once either player has already won.
type GameTickResult = Result<([u8; 2], Player), Player>;


impl<T> Index<Player> for [T; 2] {
	type Output = T;
	fn index(&self, player: Player) -> &Self::Output {
		match player {
			Player::One => &self[0],
			Player::Two => &self[1],
		}
	}
}

impl<T> IndexMut<Player> for [T; 2] {
	fn index_mut(&mut self, player: Player) -> &mut Self::Output {
		match player {
			Player::One => &mut self[0],
			Player::Two => &mut self[1],
		} 
	}
}


impl Game {
	fn tick(&mut self) -> GameTickResult {
		use Player::*;
		if self.players[Two].is_empty() { return Err(One) }
		if self.players[One].is_empty() { return Err(Two) }
		let (c_one, c_two) = (
			self.players[One].pop_front().unwrap(),
			self.players[Two].pop_front().unwrap()
		);
		let winning_player = if c_one > c_two {
			self.players[One].push_back(c_one);
			self.players[One].push_back(c_two);
			One
		} else {
			self.players[Two].push_back(c_two);
			self.players[Two].push_back(c_one);
			Two
		};
		Ok(([c_one, c_two], winning_player))
	}

	fn score(self) -> u64 {
		self.players.into_iter()
			.find(|p| !p.is_empty())
			.map(|c| c.into_iter()
				.rev()
				.enumerate()
				.map(|(i, c)| (i as u64 + 1) * c as u64)
				.sum())
			.unwrap()
	}
}


struct RecursiveGame {
	players: [VecDeque<u8>; 2],
	prev_states: HashSet<[VecDeque<u8>; 2]>
}

impl From<Game> for RecursiveGame {
	fn from(game: Game) -> Self {
		RecursiveGame { players: game.players, prev_states: HashSet::new() }
	}
}

impl RecursiveGame {
	fn tick(&mut self) -> GameTickResult {
		use Player::*;
		if self.prev_states.contains(&self.players) || self.players[Two].is_empty() { return Err(One) }
		if self.players[One].is_empty() { return Err(Two) }
		self.prev_states.insert(self.players.clone());
		let (c_one, c_two) = (
			self.players[One].pop_front().unwrap(),
			self.players[Two].pop_front().unwrap()
		);
		let winning_player = if c_one as usize <= self.players[One].len() && c_two as usize <= self.players[Two].len() {
			let mut subgame = RecursiveGame::from(Game { players: [
				VecDeque::from_iter(self.players[One].iter().copied().take(c_one as usize)),
				VecDeque::from_iter(self.players[Two].iter().copied().take(c_two as usize)),
			] });
			let mut res;
			loop { res = subgame.tick(); if res.is_err() { break } }
			res.unwrap_err()
		} else if c_one > c_two {
			One
		} else {
			Two
		};
		if matches!(winning_player, One) {
			self.players[One].push_back(c_one);
			self.players[One].push_back(c_two);
		} else {
			self.players[Two].push_back(c_two);
			self.players[Two].push_back(c_one);
		}
		Ok(([c_one, c_two], winning_player))
	}

	fn score(self) -> u64 {
		Game { players: self.players }.score()
	}
}


fn input_game_from_str(s: &str) -> Game {
	s.parse().unwrap()
}

fn input_game() -> Game {
	input_game_from_str(include_str!("day22.txt"))
}


fn part1_impl(mut input_game: Game) -> u64 {
	while input_game.tick().is_ok() {}
	input_game.score()
}

pub(crate) fn part1() -> u64 {
	part1_impl(input_game())
}


fn part2_impl(input_game: Game) -> u64 {
	let mut input_game = RecursiveGame::from(input_game);
	while input_game.tick().is_ok() {}
	input_game.score()
}

pub(crate) fn part2() -> u64 {
	part2_impl(input_game())
}


mod parsing {
	use std::{num::ParseIntError, str::FromStr, collections::VecDeque};
	use super::{Player, Game};

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum GameError {
		MissingPlayer1Prefix,
		MissingBlankLineAndPlayer2Prefix,
		InvalidPlayer { player: Player, line: usize, source: ParseIntError },
	}

	impl FromStr for Game {
		type Err = GameError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use GameError::*;
			let s = s.strip_prefix("Player 1:\n").ok_or(MissingPlayer1Prefix)?;
			let (player1, player2) = s.split_once("\nPlayer 2:\n").ok_or(MissingBlankLineAndPlayer2Prefix)?;
			let player1 = player1.lines()
				.enumerate()
				.map(|(l, line)| line.parse()
					.map_err(|e| InvalidPlayer { player: Player::One, line: l + 2, source: e }))
				.collect::<Result<VecDeque<_>, _>>()?;
			let player2 = player2.lines()
				.enumerate()
				.map(|(l, line)| line.parse()
					.map_err(|e| InvalidPlayer { player: Player::Two, line: l + player1.len() + 4, source: e }))
				.collect::<Result<_, _>>()?;
			Ok(Game { players: [player1, player2] })
		}
	}


	#[test]
	fn input() -> Result<(), GameError> {
		super::TEST_INPUT.parse::<Game>().map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUT: &str = indoc::indoc! { "
	Player 1:
	9
	2
	6
	3
	1

	Player 2:
	5
	8
	4
	7
	10
" };

#[test]
fn tests() {
	assert_eq!(part1_impl(input_game_from_str(TEST_INPUT)), 306);
	assert_eq!(part1(), 32083);
	assert_eq!(part2_impl(input_game_from_str(TEST_INPUT)), 291);
	assert_eq!(part2(), 35495);
}
