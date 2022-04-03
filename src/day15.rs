// Copyright (c) 2022 Bastiaan Marinus van de Weerd


const PART1_N: usize = 2020;
const PART2_N: usize = 30_000_000;


fn input_numbers_from_str(s: &str) -> impl Iterator<Item = u32> + '_ {
	s.split(',').map(|n| n.parse().unwrap())
}

fn input_numbers() -> impl Iterator<Item = u32> {
	input_numbers_from_str("0,13,1,16,6,17")
}


// NOTE(bm-w): Apparently there’s no trick to part 2 -- just brute-force it? ¯\_(ツ)_/¯
fn part1and2_brute<const N: usize, I>(input_numbers: I) -> u32
where I: Iterator<Item = u32> {
	// Using a pre-allocated `Vec` for performance
	let mut prevs = vec![N; N];
	let (input_len, last_number) = input_numbers
		.enumerate()
		.map(|(i, n)| (i + 1, n as usize))
		.inspect(|&(i, n)| prevs[n] = i)
		.last().unwrap();
	(input_len + 1..=N).fold(last_number, |last_number, i| {
		let prev = std::mem::replace(
			// SAFETY: Pre-allocated a sufficiently large `Vec`
			unsafe { prevs.get_unchecked_mut(last_number) },
			i - 1);
		(i - 1).saturating_sub(prev)
	}) as u32
}

pub(crate) fn part1() -> u32 {
	part1and2_brute::<PART1_N, _>(input_numbers())
}

pub(crate) fn part2() -> u32 {
	part1and2_brute::<PART2_N, _>(input_numbers())
}


#[test]
fn tests() {
	const TESTS: [(&str, u32, u32); 7] = [
		("0,3,6", 436, 175594),
		("1,3,2", 1, 2578),
		("2,1,3", 10, 3544142),
		("1,2,3", 27, 261214),
		("2,3,1", 78, 6895259),
		("3,2,1", 438, 18),
		("3,1,2", 1836, 362),
	];
	for (input, part1_answer, _) in TESTS {
		assert_eq!(part1and2_brute::<PART1_N, _>(input_numbers_from_str(input)), part1_answer);
	}
	assert_eq!(part1(), 234);
	for (input, _, part2_answer) in TESTS {
		assert_eq!(part1and2_brute::<PART2_N, _>(input_numbers_from_str(input)), part2_answer);
	}
	assert_eq!(part2(), 8984);
}
