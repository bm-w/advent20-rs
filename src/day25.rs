// Copyright (c) 2022 Bastiaan Marinus van de Weerd


const INPUT: [u64; 2] = [
	17607508,
	15065270,
];

const MAGIC_MOD: u64 = 20201227;


#[derive(Clone, Copy)]
enum Device { Card, Door }

impl<T> std::ops::Index<Device> for [T; 2] {
	type Output = T;
	fn index(&self, index: Device) -> &Self::Output {
		match index {
			Device::Card => &self[0],
			Device::Door => &self[1],
		}
	}
}


pub(crate) fn part1_impl(input_public_keys: &[u64; 2]) -> u64 {
	use Device::*;

	let compute_loop_size = |device|
		(1_usize..)
			.scan(1_u64, |val, loop_iters| {
				*val = (*val * 7) % MAGIC_MOD;
				Some((loop_iters, *val))
			})
			.find_map(|(loop_iters, key)|
				if key == input_public_keys[device] { Some(loop_iters) }
				else { None })
			.unwrap();

	let card_loop_size = compute_loop_size(Card);
	let door_loop_size = compute_loop_size(Door);

	let compute_encryption_key = |subject_number, loop_size|
		(0_usize..loop_size)
			.fold(1_u64, |acc_val, _|
				(acc_val * subject_number) % MAGIC_MOD);

	let encryption_key = compute_encryption_key(input_public_keys[Door], card_loop_size);
	assert_eq!(encryption_key, compute_encryption_key(input_public_keys[Card], door_loop_size));

	encryption_key
}

pub(crate) fn part1() -> u64 {
	part1_impl(&INPUT)
}


pub(crate) fn part2() -> &'static str {
	"Merry Christmas!"
}


#[cfg(test)]
const TEST_INPUT: [u64; 2] = [
	5764801,
	17807724,
];


#[test]
fn tests() {
	assert_eq!(part1_impl(&TEST_INPUT), 14897079);
	assert_eq!(part1(), 12285001);
}
