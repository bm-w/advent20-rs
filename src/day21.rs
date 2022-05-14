// Copyright (c) 2022 Bastiaan Marinus van de Weerd

use std::collections::{HashSet, HashMap, hash_map::Entry};


struct Food<'s> {
	ingredients: HashSet<&'s str>,
	allergens: HashSet<&'s str>,
}

trait Foods<'s>: IntoIterator<Item = &'s Food<'s>> {
	fn possible_allergen_ingredients(self) -> HashMap<&'s str, HashSet<&'s str>> where Self: Sized {
		let mut possible_allergen_ingredients = HashMap::new();
		for food in self.into_iter() {
			for &allergen in &food.allergens {
				match possible_allergen_ingredients.entry(allergen) {
					Entry::Vacant(entry) => {
						entry.insert(food.ingredients.clone());
					}
					Entry::Occupied(mut entry) => {
						let possible_ingredients = entry.get_mut();
						let intersection =  possible_ingredients.intersection(&food.ingredients);
						*possible_ingredients = intersection.copied().collect();
					}
				}
			}
		}
		possible_allergen_ingredients
	}
}

impl<'s, I> Foods<'s> for I where I: IntoIterator<Item = &'s Food<'s>> {}


fn input_foods_from_str(s: &str) -> Vec<Food> {
	parsing::try_foods_from_str(s).unwrap()
}

fn input_foods() -> Vec<Food<'static>> {
	input_foods_from_str(include_str!("day21.txt"))
}


fn part1_impl(input_foods: &[Food]) -> usize {
	let possibly_allergenic_ingredients = input_foods.possible_allergen_ingredients()
		.values().flatten().copied().collect::<HashSet<_>>();
	input_foods.iter()
		.flat_map(|food|
			food.ingredients.iter().filter(|&&ingredient|
				!possibly_allergenic_ingredients.contains(ingredient)))
		.count()
}

pub(crate) fn part1() -> usize {
	part1_impl(&input_foods())
}


fn part2_impl(input_foods: &[Food]) -> String {
	let mut allergen_ingredients = HashMap::new();
	let mut possible_allergen_ingredients = input_foods.possible_allergen_ingredients();
	while let Some((allergen, ingredient)) = possible_allergen_ingredients.iter()
		.filter_map(|(&allergen, ingredients)|
			if ingredients.len() == 1 { Some((allergen, *ingredients.iter().next().unwrap())) }
			else { None })
		.next()
	{
		allergen_ingredients.insert(allergen, ingredient);
		possible_allergen_ingredients.remove(allergen);
		for ingredients in possible_allergen_ingredients.values_mut() {
			ingredients.remove(ingredient);
		}
	}
	use itertools::Itertools;
	let sorted_ingredients = allergen_ingredients.into_iter().sorted_by_key(|&(a, _)| a).map(|(_, i)| i);
	Itertools::intersperse(sorted_ingredients, ",").collect()
}

pub(crate) fn part2() -> String {
	part2_impl(&input_foods())
}


mod parsing {
	use super::Food;

	#[derive(Debug)]
	pub(super) enum FoodError {
		Empty,
		ExpectedOpenParenContains,
		ExpectedCloseParen,
	}

	impl<'s> TryFrom<&'s str> for Food<'s> {
		type Error = FoodError;
		fn try_from(s: &'s str) -> Result<Self, Self::Error> {
			use {FoodError::*};

			if s.is_empty() { return Err(Empty) }
			let (ingredients, allergens) = s.split_once(" (contains ")
				.ok_or(ExpectedOpenParenContains)?;
			let allergens = allergens.strip_suffix(')')
				.ok_or(ExpectedCloseParen)?;

			let ingredients = ingredients.split(' ').collect();
			let allergens = allergens.split(", ").collect();

			Ok(Food { ingredients, allergens })
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct FoodsError {
		line: usize,
		source: FoodError
	}

	pub(super) fn try_foods_from_str(s: &str) -> Result<Vec<Food<'_>>, FoodsError> {
		s.lines().enumerate()
			.map(|(l, line)|
				line.try_into()
					.map_err(|e| FoodsError { line: l + 1, source: e }))
			.collect()
	}


	#[test]
	fn input() -> Result<(), FoodsError> {
		try_foods_from_str(super::TEST_INPUT).map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUT: &str = indoc::indoc! { "
	mxmxvkd kfcds sqjhc nhms (contains dairy, fish)
	trh fvjkl sbzzf mxmxvkd (contains dairy)
	sqjhc fvjkl (contains soy)
	sqjhc mxmxvkd sbzzf (contains fish)
" };

#[test]
fn tests() {
	assert_eq!(part1_impl(&input_foods_from_str(TEST_INPUT)), 5);
	assert_eq!(part1(), 2280);
	assert_eq!(&part2_impl(&input_foods_from_str(TEST_INPUT)), "mxmxvkd,sqjhc,fvjkl");
	assert_eq!(part2(), "vfvvnm,bvgm,rdksxt,xknb,hxntcz,bktzrz,srzqtccv,gbtmdb");
}
