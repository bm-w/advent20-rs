// Copyright (c) 2022 Bastiaan Marinus van de Weerd


const INPUT: &str = "158937462";

mod linked {
	use itertools::Itertools as _;

	struct Game {
		nexts: Vec<u32>,
		current: u32,	
	}

	impl<T> From<T> for Game where T: AsRef<[u32]> {
		fn from(cup_labels: T) -> Self {
			let cup_labels = cup_labels.as_ref();

			let mut cup_nexts = vec![0; cup_labels.len()];
			for (label, next) in cup_labels.iter()
				.chain(cup_labels.first())
				.copied()
				.tuple_windows()
			{
				cup_nexts[label as usize - 1] = next;
			}

			Game { nexts: cup_nexts, current: cup_labels[0] }
		}
	}

	impl Game {
		fn idx(cups_len: usize, label: u32) -> usize {
			(cups_len + label as usize - 1) % cups_len
		}

		fn tick(&mut self) {
			let cups_len = self.nexts.len();
			let idx = |label| Self::idx(cups_len, label);

			let picked_up_first = self.nexts[idx(self.current)];
			let mut picked_up_nexts = [picked_up_first; 3];
			picked_up_nexts[0] = self.nexts[idx(picked_up_first)];
			picked_up_nexts[1] = self.nexts[idx(picked_up_nexts[0])];
			picked_up_nexts[2] = self.nexts[idx(picked_up_nexts[1])];
			let dest = (1..)
				.map(|d| (cups_len as u32 + self.current - 1 - d) % cups_len as u32 + 1)
				.find(|&dest| dest != picked_up_first && dest != picked_up_nexts[0] && dest != picked_up_nexts[1])
				.unwrap();
			let dest_next = self.nexts[idx(dest)];

			self.nexts[idx(self.current)] = picked_up_nexts[2];
			self.nexts[idx(picked_up_nexts[1])] = dest_next;
			self.nexts[idx(dest)] = picked_up_first;

			self.current = picked_up_nexts[2]
		}

		fn cup_labels(&self) -> impl Iterator<Item = u32> + '_ {
			let cups_len = self.nexts.len();
			(1..=cups_len).scan(1, move |label, _| {
				Some(std::mem::replace(label, self.nexts[Self::idx(cups_len, *label)]))
			})
		}
	}

	pub(super) enum Output { All, FirstThree }

	pub(super) fn r#impl<const N: usize>(cups: &mut [u32], output: Output) {
		let mut game = Game::from(&cups);
		for _ in 0..N { game.tick() }
		let output_iter = cups.iter_mut().zip(game.cup_labels());
		macro_rules! assign_output { ($iter:expr) => { for (output, label) in $iter { *output = label } } }
		match output {
			Output::All => assign_output!(output_iter),
			Output::FirstThree => assign_output!(output_iter.take(3)),
		}
	}
}

#[allow(dead_code)]
fn brute<const N: usize>(cups: &mut [u32]) {
	use itertools::Itertools as _;

	let ordered_cups = cups.iter().copied().sorted().collect::<Vec<_>>();

	let mut current = 0;
	let mut picked_up = [u32::MAX; 3];
	for _ in 0..N {
		let current_cup = cups[current];

		let (next, next_offset) = if current + 4 > cups.len() {
			let tail = cups.len() - current - 1;
			picked_up[..tail].clone_from_slice(&cups[current + 1..]);
			picked_up[tail..].clone_from_slice(&cups[..3 - tail]);
			(itertools::Either::Left(cups[3 - tail..current].iter()), 3 - tail)
		} else {
			picked_up.clone_from_slice(&cups[current + 1..current + 4]);
			(itertools::Either::Right(cups[current + 4..].iter()
				.chain(cups[..current].iter())), current + 4)
		};
		let next = (next_offset + {
				let ordered_current = ordered_cups.iter()
					.position(|&c| c == current_cup)
					.unwrap();
				ordered_cups[..ordered_current].iter().rev()
					.chain(ordered_cups[ordered_current + 1..].iter().rev())
					.filter(|c| !picked_up.contains(c))
			}
			.flat_map(|&n| next.clone().position(|&c| c == n))
			.next()
			.unwrap()) % cups.len();

		if next > current {
			assert!(next >= current + 4);
			cups.copy_within(current + 4..=next, current + 1);
		} else if current + 4 <= cups.len() {
			cups.copy_within(current + 4.., current + 1);
			if next <= 2 {
				cups.copy_within(..=next, cups.len() - 3);
			} else {
				cups.copy_within(..3, cups.len() - 3);
				cups.copy_within(3..=next, 0);
			}
		} else {
			let tail = cups.len() - current - 1;
			if next < 3 {
				cups.copy_within(3 - tail..=next, current + 1);
			} else {
				cups.copy_within(3 - tail..3, current + 1);
				cups.copy_within(3..=next, 0);
			}
		}

		if next >= 2 {
			cups[next - 2..=next].copy_from_slice(&picked_up);
		} else {
			let start = cups.len() + next - 2;
			cups[start..].copy_from_slice(&picked_up[..2 - next]);
			cups[0..=next].copy_from_slice(&picked_up[2 - next..]);
		}

		current = (current + 1) % cups.len();
	}
}


fn input_cups_from_str(s: &str) -> Vec<u32> {
	s.chars().map(|c| c.to_digit(10).unwrap() as u32).collect()
}

fn input_cups() -> Vec<u32> {
	input_cups_from_str(INPUT)
}


fn part1_impl<const N: usize>(input_cups: &mut [u32]) -> String {
	use std::fmt::Write as _;

	if input_cups.is_empty() { return "".to_owned() }

	// brute::<N>(input_cups);
	// let one = input_cups.iter().position(|&c| c == 1).unwrap();
	// input_cups[one + 1..].iter()
	// 	.chain(input_cups[..one].iter())
	linked::r#impl::<N>(input_cups, linked::Output::All);
	input_cups[1..].iter()
		.fold(String::with_capacity(input_cups.len()), |mut s, c| {
			write!(s, "{c}").unwrap();
			s
		})
}

pub(crate) fn part1() -> String {
	part1_impl::<100>(&mut input_cups())
}


fn part2_impl(input_cups: &[u32]) -> u64 {
	assert!(!input_cups.is_empty());

	let mut million_and_one_cups = (0..=1_000_000).collect::<Vec<_>>();
	million_and_one_cups[1..=input_cups.len()].copy_from_slice(input_cups);

	// brute::<10_000_000>(&mut million_and_one_cups[1..]);
	// let one = million_and_one_cups.iter().position(|&c| c == 1).unwrap();
	// million_and_one_cups[(one + 1) % million_and_one_cups.len()] as u64
	// 	* million_and_one_cups[(one + 2) % million_and_one_cups.len()] as u64
	linked::r#impl::<10_000_000>(&mut million_and_one_cups[1..], linked::Output::FirstThree);
	million_and_one_cups[2] as u64 * million_and_one_cups[3] as u64
}

pub(crate) fn part2() -> u64 {
	part2_impl(&input_cups())
}


#[cfg(test)]
const TEST_INPUT: &str = "389125467";

#[test]
fn tests() {
	assert_eq!(part1_impl::<10>(&mut input_cups_from_str(TEST_INPUT)), "92658374");
	assert_eq!(part1(), "69473825");
	assert_eq!(part2_impl(&input_cups_from_str(TEST_INPUT)), 149245887792);
	assert_eq!(part2(), 96604396189);
}
