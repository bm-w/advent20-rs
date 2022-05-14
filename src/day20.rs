// Copyright (c) 2022 Bastiaan Marinus van de Weerd


#[cfg_attr(test, derive(Debug, Clone))]
struct ImageTile {
	id: u64,
	pixels: Vec<bool>,
	width: usize,
}


mod transform {
	use std::{mem::MaybeUninit, ops::Mul};

	#[derive(Clone, Copy)]
	#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
	pub(super) enum Rotation { Right, Half, Left }

	impl Rotation {
		pub(super) fn all() -> [Option<Self>; 4] {
			use Rotation::*;
			[None, Some(Right), Some(Half), Some(Left)]
		}

		pub(super) fn all_flipped() -> [Option<Self>; 4] {
			use Rotation::*;
			[None, Some(Left), Some(Half), Some(Right)]
		}

		pub(super) fn inv(&self) -> Rotation {
			use Rotation::*;
			match self {
				Left => Right,
				Right => Left,
				_ => *self
			}
		}

		pub(super) fn flipped(&self) -> Rotation {
			self.inv()
		}
	}

	#[derive(Clone, Default)]
	/// Horizontal flip (if any) first, then rotation (if any).
	#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
	pub(super) struct Transform {
		pub(super) rotation: Option<Rotation>,
		pub(super) flipped_hor: bool,
	}

	impl Transform {

		#[cfg(test)]
		fn identity() -> Self {
			Self::default()
		}

		pub(super) fn all() -> [Transform; 8] {
			// SAFETY: `MaybeUninit` does not need initialization.
			let mut transforms: [MaybeUninit<Transform>; 8] = unsafe { MaybeUninit::uninit().assume_init() };

			for (offset, rotation) in Rotation::all().into_iter().enumerate() {
				(&mut transforms[offset]).write(Transform { rotation, flipped_hor: false });
			}

			for (offset, rotation) in Rotation::all_flipped().into_iter().enumerate() {
				(&mut transforms[4 + offset]).write(Transform { rotation, flipped_hor: true });
			}

			// SAFETY: Now properly initialized.
			unsafe { std::mem::transmute(transforms) }
		}

		pub(super) fn inv(&self) -> Transform {
			Transform {
				rotation: if self.flipped_hor { self.rotation } else { self.rotation.map(|r| r.inv()) },
				flipped_hor: self.flipped_hor,
			}
		}
	}

	impl Mul for &Transform {
		type Output = Transform;
		fn mul(self, rhs: Self) -> Self::Output {
			use Rotation::*;
			#[allow(clippy::suspicious_arithmetic_impl)]
			Transform {
				rotation: match (self.rotation, if self.flipped_hor { rhs.rotation.map(|r| r.flipped()) } else { rhs.rotation }) {
					(None, None) | (Some(Right), Some(Left)) | (Some(Half), Some(Half)) | (Some(Left), Some(Right)) => None,
					(None, Some(Right)) | (Some(Right), None) | (Some(Half), Some(Left)) | (Some(Left), Some(Half)) => Some(Right),
					(None, Some(Half)) | (Some(Right), Some(Right)) | (Some(Half), None) | (Some(Left), Some(Left)) => Some(Half),
					(None, Some(Left)) | (Some(Right), Some(Half)) | (Some(Half), Some(Right)) | (Some(Left), None) => Some(Left),
				},
				flipped_hor: self.flipped_hor ^ rhs.flipped_hor,
			}
		}
	}


	#[test]
	fn transform_mul() {
		use Rotation::*;
		assert_eq!(&Transform { rotation: Some(Left), flipped_hor: false } * &Transform { rotation: Some(Right), flipped_hor: false }, Transform { rotation: None, flipped_hor: false });
		assert_eq!(&Transform { rotation: Some(Left), flipped_hor: false } * &Transform { rotation: Some(Right), flipped_hor: true }, Transform { rotation: None, flipped_hor: true });
		assert_eq!(&Transform { rotation: Some(Left), flipped_hor: true } * &Transform { rotation: Some(Right), flipped_hor: false }, Transform { rotation: Some(Half), flipped_hor: true });
		assert_eq!(&Transform { rotation: Some(Left), flipped_hor: true } * &Transform { rotation: Some(Right), flipped_hor: true }, Transform { rotation: Some(Half), flipped_hor: false });
	}

	#[test]
	fn transform_inv() {
		use Rotation::*;
		assert_eq!(Transform { rotation: Some(Left), flipped_hor: true }.inv(), Transform { rotation: Some(Right), flipped_hor: true });
		for transform in Transform::all() {
			let transform_inv = transform.inv();
			assert_eq!(&transform * &transform_inv, Transform::identity());
			assert_eq!(&transform_inv * &transform, Transform::identity());
		}
	}
}


mod assembly {
	use std::{collections::HashMap, iter, ops::Mul};
	use itertools::Itertools as _;
	use super::{ImageTile, transform::{Rotation, Transform}};

	impl ImageTile {
		/// Clockwise starting from top left.
		fn edges(&self) -> [Vec<bool>; 4] {
			let mut edges = [vec![], vec![], vec![], vec![]];
			for i in 0..self.width { edges[0].push(self.pixels[i]) }
			for i in 0..self.width { edges[1].push(self.pixels[(i + 1) * self.width - 1]) }
			for i in 0..self.width { edges[2].push(self.pixels[self.pixels.len() - i - 1]) }
			for i in 0..self.width { edges[3].push(self.pixels[self.width * (self.width - i - 1)]) }
			edges
		}
	}

	impl Mul<&[Vec<bool>; 4]> for &Transform {
		type Output = [Vec<bool>; 4];
		fn mul(self, rhs: &[Vec<bool>; 4]) -> Self::Output {
			let mut out = rhs.clone();
			macro_rules! swaps {
				( $( $l:literal, $r: literal );+ ) => { {
					$( out.swap($l, $r); )+
				} }
			}
			if self.flipped_hor {
				for e in out.iter_mut() { e.reverse(); }
				swaps!(1, 3);
			}
			use Rotation::*;
			match self.rotation {
				None => (),
				Some(Right) => swaps!(2, 3; 1, 2; 0, 1), // 3, 0, 1, 2
				Some(Half) => swaps!(0, 2; 1, 3), // 2, 3, 0, 1
				Some(Left) => swaps!(0, 1; 1, 2; 2, 3), // 1, 2, 3, 0
			}
			out
		}
	}

	/// Edges & tiles, and tile transforms relative to the orientations where
	/// the edges would be tiles’ clockwise top edge (from left to right).
	fn edge_indexed_tiles<'a>(iter: impl Iterator<Item = &'a ImageTile>) -> HashMap<Vec<bool>, Vec<(Transform, &'a ImageTile)>> {
		iter
			.flat_map(|tile| {
				let edges = tile.edges();
				let mut rev_edges = edges.clone();
				for re in rev_edges.iter_mut() { re.reverse(); }
				let not_flipped = edges.into_iter().zip(
					Rotation::all().into_iter()
						.map(move |rotation| (Transform { rotation, flipped_hor: false }, tile)));
				let flipped = rev_edges.into_iter().zip(
					Rotation::all_flipped().into_iter()
						.map(move |rotation| (Transform { rotation: rotation.map(|r| r.flipped()), flipped_hor: true }, tile)));
				not_flipped.chain(flipped)
			})
			.into_group_map()
	}

	pub(super) trait Image<'a> {

		// TODO(bm-w): `AsSlice<[ImageTile]>`?
		type TilesIter: Iterator<Item = &'a ImageTile>;
		fn tiles_iter(&self) -> Self::TilesIter;

		/// Returns the row-major-ordered tiles and per tile the transform
		/// required to fit it into its position in the assembled image.
		fn assemble(&self) -> Result<Vec<(&'a ImageTile, Transform)>, ()> where Self: Sized {
			// TODO(bm-w): Optimize (e.g. using `ExactSizeIterator`)?
			let len = self.tiles_iter().count();
			let width = super::isqrt(len).expect("Image must be square");
			let edge_indexed_tiles = edge_indexed_tiles(self.tiles_iter());

			fn transform_tile_edges(tile: &ImageTile, transform: &Transform) -> [Vec<bool>; 4] {
				transform * &tile.edges()
			}

			fn transformed_tile_right_bottom_edges(tile: &ImageTile, transform: &Transform) -> [Vec<bool>; 2] {
				let [_, right_edge, bottom_edge, _] = transform_tile_edges(tile, transform);
				[right_edge, bottom_edge]
			}

			let mut stack = vec![(
				Box::new(itertools::iproduct!(self.tiles_iter(), Transform::all().into_iter()).map(|(tile, transform)| {
					let edges = transformed_tile_right_bottom_edges(tile, &transform);
					(tile, transform, edges)
				})) as Box<dyn Iterator<Item = (&ImageTile, Transform, [Vec<bool>;2])>>,
				None
			)];

			while let Some((
				(transforms_tiles, current),
				stack_below,
			)) = stack.split_last_mut().map(|(last, below)| (last, &*below)) {
				*current = transforms_tiles.next();

				let current = match current {
					None => {
						stack.pop();
						continue
					}
					Some(_) if stack_below.len() == width * width - 1 =>
						return Ok(stack.into_iter()
							.map(|(_, current)| current
								.map(|(tl, tr, _)| (tl, tr))
								.unwrap())
							.collect()),
					Some(ref current) => current
				};

				fn default_filter_map(transform: Transform, tile: &ImageTile) -> Option<(&ImageTile, Transform, [Vec<bool>; 2])> {
					let edges = transformed_tile_right_bottom_edges(tile, &transform);
					Some((tile, transform, edges))
				}

				type FilterMap<'a> = Box<dyn Fn(Transform, &'a ImageTile) -> Option<(&'a ImageTile, Transform, [Vec<bool>; 2])>>;
				let (edge, filter_map, transform): (_, FilterMap, _) = if (stack_below.len() + 1) % width == 0 {
					let (_, _, [_, bottom_edge]) = stack_below[stack_below.len() + 1 - width].1.as_ref().unwrap();
					(bottom_edge, Box::new(default_filter_map), Transform { rotation: None, flipped_hor: true })
				} else {
					let (_, _, [right_edge, _]) = current;
					let filter_map: FilterMap = if stack_below.len() >= width {
						let above_edge = stack_below[stack_below.len() + 1 - width].1
							.as_ref()
							.map(|(_, _, [_, bottom_edge])| {
								let mut edge = bottom_edge.clone();
								edge.reverse();
								edge
							})
							.unwrap();
						Box::new(move |transform, tile| {
							let [top_edge, right_edge, bottom_edge, _]
								= transform_tile_edges(tile, &transform);
							if top_edge != above_edge { None }
							else { Some((tile, transform, [right_edge, bottom_edge])) }
						})
					} else {
						Box::new(default_filter_map)
					};
					(right_edge, filter_map, Transform { rotation: Some(Rotation::Left), flipped_hor: true })
				};

				let tiles_below = stack_below.iter()
					.map(|(_, current)| current.as_ref().unwrap().0)
					.chain(iter::once(current.0))
					.map(|t| t as *const _)
					.collect::<Vec<_>>();

				let transforms_tiles = edge_indexed_tiles.get(edge)
					.into_iter()
					.flat_map(|v| v.iter())
					.filter(move |(_, t)|
						!tiles_below.contains(&((t as &ImageTile) as *const _)))
					.map(move |(tile_transform, &ref tile)|
						(&transform * &tile_transform.inv(), tile))
					.filter_map(move |(transform, tile)|
						filter_map(transform, tile));

				stack.push((Box::new(transforms_tiles), None));
			}

			Err(())
		}
	}

	impl<'a> Image<'a> for &'a [ImageTile] {
		type TilesIter = std::slice::Iter<'a, ImageTile>;
		fn tiles_iter(&self) -> Self::TilesIter {
			self.iter()
		}
	}

	#[cfg(test)]
	lazy_static! {
		static ref TEST_IMAGE_TILE: ImageTile = ImageTile {
			id: 1337,
			pixels: vec![
				true, true, true,
				false, true, false,
				false, false, true,
			],
			width: 3
		};
	}

	#[test]
	fn edges() {
		assert_eq!(TEST_IMAGE_TILE.edges(), [
			vec![true, true, true],
			vec![true, false, true],
			vec![true, false, false],
			vec![false, false, true],
		]);
	}
}


mod scanning {
	use std::{iter, marker::PhantomData, ops::{Index, Mul}};
	use super::{ImageTile, transform::{Rotation, Transform}};

	struct TranslatedTransform(Transform, usize);

	impl Mul<(usize, usize)> for &TranslatedTransform {
		type Output = (usize, usize);
		fn mul(self, (x, y): (usize, usize)) -> Self::Output {
			let w = self.1;
			use Rotation::*;
			let out_x = match (self.0.rotation, self.0.flipped_hor) {
				(None, false) | (Some(Half), true) => x,
				(Some(Right), _) => w - y - 1,
				(Some(Half), false) | (None, true) => w - x - 1,
				(Some(Left), _) => y,
			};
			let out_y = match (self.0.rotation, self.0.flipped_hor) {
				(None, _) => y,
				(Some(Right), false) | (Some(Left), true) => x,
				(Some(Half), _) => w - y - 1,
				(Some(Left), false) | (Some(Right), true) => w - x - 1,
			};
			(out_x, out_y)
		}
	}

	struct _Image<'t, T> {
		tiles: T,
		tiles_width: usize,
		/// Excluding borders.
		per_tile_width: usize,
		_pd: PhantomData<&'t ()>
	}

	impl<'t, T> Index<(usize, usize)> for _Image<'t, T> where T: AsRef<[(&'t ImageTile, Transform)]> {
		type Output = bool;
		fn index(&self, (x, y): (usize, usize)) -> &Self::Output {
			let (tile_x, tile_y) = (x / self.per_tile_width, y / self.per_tile_width);
			let tile_idx = tile_y * self.tiles_width + tile_x;
			let (tile, transform) = &self.tiles.as_ref()[tile_idx];
			let (tile_pixel_x, tile_pixel_y)
				= &TranslatedTransform(transform.inv(), tile.width)
					* (1 + x - tile_x * self.per_tile_width, 1 + y - tile_y * self.per_tile_width);
			let pixel_idx = (self.per_tile_width + 2) * tile_pixel_y + tile_pixel_x;
			tile.pixels.index(pixel_idx)
		}
	}

	impl<'t, T> Index<usize> for _Image<'t, T> where T: AsRef<[(&'t ImageTile, Transform)]> {
		type Output = bool;
		fn index(&self, index: usize) -> &Self::Output {
			let width = self.tiles_width * self.per_tile_width;
			&self[(index % width, index / width)]
		}
	}

	#[cfg(test)]
	struct Habitat<'i, I> {
		image: &'i I,
		sea_monster_origins: &'i [(usize, usize)],
	}

	#[cfg(test)]
	use std::fmt::{Display, Write as _};

	#[cfg(test)]
	impl<'t, T> Display for _Image<'t, T> where T: AsRef<[(&'t ImageTile, Transform)]> {
		fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
			let pixels_width = self.tiles_width * self.per_tile_width;
			for y in 0..pixels_width {
				for x in 0..pixels_width {
					f.write_char(if self[pixels_width * y + x] { '#' } else { '.' })?;
					if x == pixels_width - 1 { f.write_char('\n')?; }
				}
			}
			Ok(())
		}
	}

	const SEA_MONSTER_SIZE: (usize, usize) = (20, 3);
	const SEA_MONSTER_PIXELS: [(usize, usize); 15] = [
		(0, 1), (1, 2), // Tail
		(4, 2), (5, 1), (6, 1), (7, 2), // Back arc
		(10, 2), (11, 1), (12, 1), (13, 2), // Front arc
		(16, 2), (17, 1), (18, 0), (18, 1), (19, 1), // Neck & head
	];

	#[cfg(test)]
	impl<'t, T> Display for Habitat<'t, _Image<'t, T>> where T: AsRef<[(&'t ImageTile, Transform)]> {
		fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
			let pixels_width = self.image.tiles_width * self.image.per_tile_width;
			for y in 0..pixels_width {
				let sea_monster_origins: Vec<_> = self.sea_monster_origins.iter()
					.filter_map(|&(ox, oy)|
						if (oy..oy + SEA_MONSTER_SIZE.1).contains(&y) { Some((ox, oy)) } else { None })
					.collect();
				for x in 0..pixels_width {
					f.write_char(if self.image[pixels_width * y + x] {
						if sea_monster_origins.iter()
							.any(|&(ox, oy)|
								(ox..ox + SEA_MONSTER_SIZE.0).contains(&x)
								&& SEA_MONSTER_PIXELS.contains(&(x - ox, y - oy)))
							{ 'O' }
						else { '#' }
					} else { '.' })?;
					if x == pixels_width - 1 { f.write_char('\n')?; }
				}
			}
			Ok(())
		}
	}

	impl<'t, T> _Image<'t, T> where T: AsRef<[(&'t ImageTile, Transform)]> {
		fn try_from(tiles: T) -> Result<Self, ()> {
			let tiles_width = super::isqrt(tiles.as_ref().len()).ok_or(())?;
			let mut tiles_iter = tiles.as_ref().iter();
			let tile = tiles_iter.next().ok_or(())?.0;
			if tile.width <= 2 || tiles_iter.any(|(t, _)| t.width != tile.width) { return Err(()) }
			let per_tile_width = tile.width - 2;
			Ok(_Image { tiles, tiles_width, per_tile_width, _pd: PhantomData })
		}

		fn transformed_tiles(&self, transform: &Transform) -> Vec<(&'t ImageTile, Transform)> {
			let inv_translated_transform = TranslatedTransform(transform.inv(), self.tiles_width);
			let tiles_as_ref = self.tiles.as_ref();
			 (0..tiles_as_ref.len()).map(|i| {
				let (ix, iy) = (i % self.tiles_width, i / self.tiles_width);
				let (tix, tiy) = &inv_translated_transform * (ix, iy);
				let ti = self.tiles_width * tiy + tix;
				let (tile, ref tile_transform) = tiles_as_ref[ti];
				(tile, transform * tile_transform)
			}).collect()
		}

		fn scan_sea_monsters(&self) -> Result<(Transform, Vec<(usize, usize)>), ()> {
			let _Image { tiles_width, per_tile_width, .. } = *self;
			let pixels_width = tiles_width * per_tile_width;

			let all_transforms = Transform::all();
			let (no_transform, other_transforms) = all_transforms.split_first().unwrap();
			let transformed_tiles: Vec<_> = other_transforms.iter()
				.map(|t| (self.transformed_tiles(t), t))
				.collect();

			for (tiles, transform) in iter::once((self.tiles.as_ref(), no_transform))
				.chain(transformed_tiles.iter().map(|&(ref ts, t)| (ts.as_ref(), t)))
			{
				let image = _Image { tiles, tiles_width, per_tile_width, _pd: PhantomData };
				let mut origins = vec![];
				for (x0, y0) in itertools::iproduct!(
					0..pixels_width + 1 - SEA_MONSTER_SIZE.0,
					0..pixels_width + 1 - SEA_MONSTER_SIZE.1
				) {
					if SEA_MONSTER_PIXELS.into_iter().all(|(x, y)| image[(x0 + x, y0 + y)]) {
						origins.push((x0, y0))
					}
				}
				if !origins.is_empty() {
					return Ok((transform.clone(), origins))
				}
			}

			Err(())
		}

		fn scan_waters_roughness(&self) -> Result<(Transform, usize), ()> {
			let (transform, sea_monster_origins) = self.scan_sea_monsters()?;
			let &_Image { tiles_width, per_tile_width, .. } = self;
			let transformed_image = _Image {
				tiles: self.transformed_tiles(&transform),
				tiles_width, per_tile_width, _pd: PhantomData
			};
			let pixels_width = tiles_width * per_tile_width;
			let filled_pixels = itertools::iproduct!(0..pixels_width, 0..pixels_width)
				.filter(|&(x, y)| transformed_image[(x, y)])
				.count();
			let roughness = filled_pixels - sea_monster_origins.len() * SEA_MONSTER_PIXELS.len();

			#[cfg(test)]
			print!("Habitat ({} sea monster{}, waters roughness: {roughness}):\n{}",
				sea_monster_origins.len(),
				if sea_monster_origins.len() == 1 { "" } else { "s" },
				Habitat { image: &transformed_image, sea_monster_origins: sea_monster_origins.as_ref() });

			Ok((transform, roughness))
		}
	}

	pub(super) trait Image<'t>: AsRef<[(&'t ImageTile, Transform)]> {
		fn scan_waters_roughness(&self) -> Result<(Transform, usize), ()> {
			_Image::try_from(self)?.scan_waters_roughness()
		}
	}

	impl<'a, T> Image<'a> for T where T: AsRef<[(&'a ImageTile, Transform)]> {}


	#[test]
	fn index() -> Result<(), ()> {
		let tiles = vec![
			ImageTile { id: 1337, pixels: vec![false; 9], width: 3 },
			ImageTile { id: 1337, pixels: vec![false, false, false, false, true, false, false, false, false], width: 3 },
		];
		let transform = Transform { rotation: None, flipped_hor: false };
		let assembled_image = vec![
			(&tiles[1], transform.clone()),
			(&tiles[0], transform.clone()),
			(&tiles[0], transform.clone()),
			(&tiles[1], transform),
		];
		let img = _Image::try_from(assembled_image)?;
		assert!(img[(0, 0)]);
		assert!(!img[(0, 1)]);
		assert!(!img[(1, 0)]);
		assert!(img[(1, 1)]);
		Ok(())
	}
}


fn input_image_tiles_from_str(s: &str) -> Vec<ImageTile> {
	parsing::try_image_tiles_from_str(s).unwrap()
}

fn input_image_tiles() -> Vec<ImageTile> {
	input_image_tiles_from_str(include_str!("day20.txt"))
}


fn part1_impl(input_image_tiles: &[ImageTile]) -> u64 {
	use self::assembly::Image as _;
	let assembled_tiles = input_image_tiles.assemble().unwrap();
	let width = isqrt(assembled_tiles.len()).unwrap();
	[0, width - 1, width * (width - 1), width * width - 1]
		.into_iter()
		.map(|i| assembled_tiles[i].0.id)
		.product()
}

pub(crate) fn part1() -> u64 {
	part1_impl(&input_image_tiles())
}


fn part2_impl(input_image_tiles: &[ImageTile]) -> usize {
	use self::{assembly::Image as _, scanning::Image as _};
	input_image_tiles.assemble().unwrap().scan_waters_roughness().unwrap().1
}

pub(crate) fn part2() -> usize {
	part2_impl(&input_image_tiles())
}

#[test]
fn scratch() {
	part2_impl(&input_image_tiles_from_str(TEST_INPUT));
}


mod parsing {
	use std::{num::ParseIntError, iter, cmp::Ordering};
	use itertools::{Either, Itertools};
	use super::ImageTile;

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum ImageTileError {
		InvalidFormat { line: usize, column: usize},
		InvalidId { line: usize, source: ParseIntError },
		InvalidPixel { line: usize, column: usize, found: char },
		InvalidHeight { line: usize, width: usize, found_height: usize },
	}

	struct EnumeratedLines<'l, L>(L) where L: Iterator<Item = (usize, &'l str)>;

	impl<'l, L> TryFrom<EnumeratedLines<'l, L>> for ImageTile
	where L: Iterator<Item = (usize, &'l str)> {
		type Error = ImageTileError;
		fn try_from(EnumeratedLines(mut lines): EnumeratedLines<'l, L>) -> Result<Self, Self::Error> {
			use ImageTileError::*;
			let (l0, id): (usize, u64) = {
				let (l, line) = lines.next().ok_or(InvalidFormat { line: 1, column: 1 })?;
				let id = line.strip_prefix("Tile ").ok_or(InvalidFormat { line: l + 1, column: 1 })?;
				let id = id.strip_suffix(':').ok_or(InvalidFormat { line: l + 1, column: line.len() })?;
				(l, id.parse().map_err(|e| InvalidId { line: l + 1, source: e })?)
			};
			let mut lines = lines.peekable();
			let width = lines.peek().map(|(_, line)| line.len())
				.ok_or(InvalidFormat { line: l0 + 2, column: 1 })?;
			let pixels = lines
				.flat_map(|(l, line)|
					if line.len() != width {
						Either::Left(iter::once(Err(InvalidFormat { line: l + 1, column: line.len().min(width) + 1 })))
					} else {
						Either::Right(line.chars()
							.enumerate()
							.map(move |(c, chr)| match chr {
								'.' => Ok(false),
								'#' => Ok(true),
								found => Err(InvalidPixel { line: l + 1, column: c + 1, found })
							}))
					})
				.collect::<Result<Vec<_>, _>>()?;
			let height = pixels.len() / width;
			if height != width {
				return Err(InvalidHeight { line: 1 + height, width, found_height: height })
			}
			Ok(ImageTile { id, pixels, width })
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum ImageTilesError {
		InvalidImageTile(ImageTileError),
		MismatchedImageTiles { offset: usize, earlier_width: usize, found_width: usize },
		NonsquareLen(usize),
	}

	pub(super) fn try_image_tiles_from_str(s: &str) -> Result<Vec<ImageTile>, ImageTilesError> {
		use ImageTilesError::*;
		let image_tiles = s.lines().enumerate()
			.group_by(|(_, line)| line.is_empty())
			.into_iter()
			.filter_map(|(discard, lines)| if discard { None }
				else { Some(EnumeratedLines(lines).try_into()) })
			.collect::<Result<Vec<ImageTile>, _>>()
			.map_err(InvalidImageTile)?;
		for (earlier_offset, (earlier, current)) in image_tiles.iter().tuple_windows().enumerate() {
			if earlier.width != current.width {
				return Err(MismatchedImageTiles { offset: earlier_offset + 1, earlier_width: earlier.width, found_width: current.width });
			}
		}
		for i in 1.. {
			let isq = i * i;
			match isq.cmp(&image_tiles.len()) {
				Ordering::Equal => break,
				Ordering::Greater => return Err(NonsquareLen(image_tiles.len())),
				_ => (),
			}
		}
		Ok(image_tiles)
	}


	#[test]
	fn test_input() -> Result<(), ImageTilesError> {
		try_image_tiles_from_str(super::TEST_INPUT).map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUT: &str = indoc::indoc! { "
	Tile 2311:
	..##.#..#.
	##..#.....
	#...##..#.
	####.#...#
	##.##.###.
	##...#.###
	.#.#.#..##
	..#....#..
	###...#.#.
	..###..###

	Tile 1951:
	#.##...##.
	#.####...#
	.....#..##
	#...######
	.##.#....#
	.###.#####
	###.##.##.
	.###....#.
	..#.#..#.#
	#...##.#..

	Tile 1171:
	####...##.
	#..##.#..#
	##.#..#.#.
	.###.####.
	..###.####
	.##....##.
	.#...####.
	#.##.####.
	####..#...
	.....##...

	Tile 1427:
	###.##.#..
	.#..#.##..
	.#.##.#..#
	#.#.#.##.#
	....#...##
	...##..##.
	...#.#####
	.#.####.#.
	..#..###.#
	..##.#..#.

	Tile 1489:
	##.#.#....
	..##...#..
	.##..##...
	..#...#...
	#####...#.
	#..#.#.#.#
	...#.#.#..
	##.#...##.
	..##.##.##
	###.##.#..

	Tile 2473:
	#....####.
	#..#.##...
	#.##..#...
	######.#.#
	.#...#.#.#
	.#########
	.###.#..#.
	########.#
	##...##.#.
	..###.#.#.

	Tile 2971:
	..#.#....#
	#...###...
	#.#.###...
	##.##..#..
	.#####..##
	.#..####.#
	#..#.#..#.
	..####.###
	..#.#.###.
	...#.#.#.#

	Tile 2729:
	...#.#.#.#
	####.#....
	..#.#.....
	....#..#.#
	.##..##.#.
	.#.####...
	####.#.#..
	##.####...
	##..#.##..
	#.##...##.

	Tile 3079:
	#.#.#####.
	.#..######
	..#.......
	######....
	####.#..#.
	.#...#.##.
	#.#####.##
	..#.###...
	..#.......
	..#.###...
" };


#[test]
fn tests() {
	assert_eq!(part1_impl(&input_image_tiles_from_str(TEST_INPUT)[..]), 20899048083289);
	assert_eq!(part1(), 47213728755493);
	assert_eq!(part2_impl(&input_image_tiles_from_str(TEST_INPUT)[..]), 273);
	assert_eq!(part2(), 1599);
}


// Util

fn isqrt(n: usize) -> Option<usize> {
	(1..).find(|i| i * i == n)
}
