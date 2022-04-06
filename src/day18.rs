// Copyright (c) 2022 Bastiaan Marinus van de Weerd


enum Op { Plus, Times }

/// The const generic `PLUS_FIRST` is only used for parsing.
enum Arg<const PLUS_FIRST: bool> {
	Lit(u8),
	Expr(Box<Expr<PLUS_FIRST>>)
}

/// The const generic `PLUS_FIRST` is only used for parsing.
struct Expr<const PLUS_FIRST: bool>(Op, [Arg<PLUS_FIRST>; 2]);

impl Op {
	fn evaluate(&self, args: [u64; 2]) -> u64 {
		match self {
			Op::Plus => args[0] + args[1],
			Op::Times => args[0] * args[1],
		}
	}
}

impl<const PLUS_FIRST: bool> Arg<PLUS_FIRST> {
	fn evaluate(&self) -> u64 {
		match self {
			Arg::Lit(lit) => *lit as u64,
			Arg::Expr(expr) => expr.evaluate(),
		}
	}
}

impl<const PLUS_FIRST: bool> Expr<PLUS_FIRST> {
	fn evaluate(&self) -> u64 {
		self.0.evaluate([self.1[0].evaluate(), self.1[1].evaluate()])
	}
}


fn input_exprs_from_str<const PLUS_FIRST: bool>(s: &str) -> impl Iterator<Item = Expr<PLUS_FIRST>> + '_ {
	parsing::input_exprs_from_str(s).map(|r| r.unwrap())
}

fn input_exprs<const PLUS_FIRST: bool>() -> impl Iterator<Item = Expr<PLUS_FIRST>> {
	input_exprs_from_str(include_str!("day18.txt"))
}


fn part1and2_impl<const PLUS_FIRST: bool, I>(input_exprs: I) -> u64
where I: IntoIterator<Item = Expr<PLUS_FIRST>> {
	input_exprs.into_iter().map(|expr| expr.evaluate()).sum()
}

pub(crate) fn part1() -> u64 {
	part1and2_impl::<false, _>(input_exprs())
}

pub(crate) fn part2() -> u64 {
	part1and2_impl::<true, _>(input_exprs())
}


mod parsing {
	use std::str::FromStr;
	use super::{Op, Arg, Expr};

	pub(super) type InvalidOpError = char;

	impl TryFrom<char> for Op {
		type Error = InvalidOpError;
		fn try_from(chr: char) -> Result<Self, Self::Error> {
			match chr {
				'+' => Ok(Op::Plus),
				'*' => Ok(Op::Times),
				found => Err(found)
			}
		}
	}

	#[allow(dead_code, clippy::enum_variant_names)]
	#[derive(Debug)]
	pub(super) enum ExprExpectedError {
		LitOrOpenParen,
		Op,
		OpOrCloseParen,
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) enum ExprErrorKind {
		InvalidOp(InvalidOpError),
		InvalidLit(char),
		UnexpectedCloseParen(Option<ExprExpectedError>),
		UnexpectedEnd(ExprExpectedError)
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct ExprError {
		column: usize,
		kind: ExprErrorKind,
	}

	impl<const PLUS_FIRST: bool> FromStr for Expr<PLUS_FIRST> {
		type Err = ExprError;
		fn from_str(s: &str) -> Result<Self, Self::Err> {
			use {ExprErrorKind::*, ExprExpectedError as Expected};

			fn try_lit(c: usize, chr: char) -> Result<u8, ExprError> {
				Ok(chr.to_digit(10).ok_or(ExprError { column: c + 1, kind: InvalidLit(chr) })? as u8)
			}

			fn try_op(c: usize, chr: char) -> Result<Op, ExprError> {
				chr.try_into().map_err(|e| ExprError { column: c + 1, kind: InvalidOp(e) })
			}

			#[derive(Default)]
			struct IncompleteExpr<const PLUS_FIRST: bool>(Vec<(Arg<PLUS_FIRST>, Op)>, Option<Arg<PLUS_FIRST>>);

			fn try_into_expr<const PLUS_FIRST: bool>(
				plus_first: bool,
				incompl_expr: IncompleteExpr<PLUS_FIRST>
			) -> Result<Expr<PLUS_FIRST>, Expected> {
				let IncompleteExpr(head, tail_arg) = incompl_expr;
				let tail_arg = tail_arg.ok_or(Expected::LitOrOpenParen)?;
				if head.is_empty() { return Err(Expected::Op) }
				if !plus_first {
					let (acc_arg, acc_op) = head.into_iter()
						.fold(None, |acc, (arg, op)|
							Some(match acc {
								Some((acc_arg, acc_op)) =>
									(Arg::Expr(Box::new(Expr(acc_op, [acc_arg, arg]))), op),
								None => (arg, op)
							}))
						.unwrap();
					Ok(Expr(acc_op, [acc_arg, tail_arg]))
				} else {
					let into_acc_expr = |acc_arg, arg|
						Expr(Op::Plus, [acc_arg, arg]);
					let into_acc_expr_arg = |acc_arg, arg|
						Arg::Expr(Box::new(into_acc_expr(acc_arg, arg)));
					let into_incompl_plus_expr = |skipped_times_args: Vec<_>, tail_arg|
						IncompleteExpr(
							skipped_times_args.into_iter().map(|a| (a, Op::Times)).collect::<Vec<_>>(),
							Some(tail_arg));
					let (acc_arg, skipped_times_args) = head.into_iter()
						.fold((None, vec![]), |(acc_arg, mut skipped_times_args), (arg, op)|
							match (op, acc_arg) {
								(Op::Plus, None) =>
									(Some(arg), skipped_times_args),
								(Op::Plus, Some(some_acc_arg)) =>
									(Some(into_acc_expr_arg(some_acc_arg, arg)), skipped_times_args),
								(Op::Times, Some(acc_arg)) => {
									let tail_arg = into_acc_expr_arg(acc_arg, arg);
									let incompl_expr = into_incompl_plus_expr(
										std::mem::take(&mut skipped_times_args), tail_arg);
									skipped_times_args.push(try_into_arg(false, incompl_expr).unwrap());
									(None, skipped_times_args)
								}
								(Op::Times, None) => {
									skipped_times_args.push(arg);
									(None, skipped_times_args)
								}
							});
					match (acc_arg, skipped_times_args.is_empty()) {
						(Some(acc_arg), true) => Ok(into_acc_expr(acc_arg, tail_arg)),
						(acc_arg, false) => {
							let tail_arg = if let Some(acc_arg) = acc_arg
								{ into_acc_expr_arg(acc_arg, tail_arg) } else { tail_arg };
							let incompl_expr = into_incompl_plus_expr(skipped_times_args, tail_arg);
							try_into_expr(false, incompl_expr)
						}
						_ => unreachable!()
					}
				}
			}

			fn try_into_arg<const PLUS_FIRST: bool>(
				plus_first: bool,
				incompl_expr: IncompleteExpr<PLUS_FIRST>
			) -> Result<Arg<PLUS_FIRST>, Expected> {
				if incompl_expr.0.is_empty() {
					if let Some(tail_arg) = incompl_expr.1 {
						return Ok(tail_arg)
					}
				}
				Ok(Arg::Expr(Box::new(try_into_expr(plus_first, incompl_expr)?)))
			}

			let mut stack = vec![IncompleteExpr::default()];
			for (c, chr) in s.chars().enumerate() {
				match (chr, stack.last_mut()) {
					(ws, _) if ws.is_whitespace() =>
						continue,
					('(', _) =>
						stack.push(IncompleteExpr::default()),
					(')', Some(_)) => {
						let arg = try_into_arg(PLUS_FIRST, stack.pop().unwrap());
						let err = |e|
							ExprError { column: c + 1, kind: UnexpectedCloseParen(e) };
						match stack.last_mut() {
							None => return Err(err(arg.err())),
							Some(IncompleteExpr(_, none_arg @ None)) =>
								*none_arg = Some(arg.map_err(|e| err(Some(e)))?),
							_ => unreachable!()
						}
					}
					(chr, Some(IncompleteExpr(_, arg @ None))) =>
						*arg = Some(Arg::Lit(try_lit(c, chr)?)),
					(chr, Some(IncompleteExpr(left, arg @ Some(_)))) => {
						let op = try_op(c, chr)?;
						left.push((arg.take().unwrap(), op))
					}
					_ => unreachable!()
				}
			}

			let end_err = |err: ExprExpectedError| -> ExprError {
				ExprError { column: s.len() + 1, kind: UnexpectedEnd(err) }
			};

			let incompl_expr = stack.pop().unwrap();
			let expr = try_into_expr(PLUS_FIRST, incompl_expr).map_err(end_err)?;
			if !stack.is_empty() { return Err(end_err(Expected::OpOrCloseParen)) }
			Ok(expr)
		}
	}

	#[allow(dead_code)]
	#[derive(Debug)]
	pub(super) struct ExprsError { line: usize, source: ExprError }

	fn input_exprs_from_lines<'l, const PLUS_FIRST: bool>(
		lines: impl Iterator<Item = &'l str> + 'l
	) -> impl Iterator<Item = Result<Expr<PLUS_FIRST>, ExprsError>> + 'l {
		lines.enumerate()
			.map(|(l, line)| line.parse()
				.map_err(|e| ExprsError { line: l + 1, source: e }))
	}

	pub(super) fn input_exprs_from_str<const PLUS_FIRST: bool>(s: &str)
	-> impl Iterator<Item = Result<Expr<PLUS_FIRST>, ExprsError>> + '_ {
		input_exprs_from_lines(s.lines())
	}


	#[cfg(test)]
	pub(super) fn test_input_exprs_from_lines<'l, const PLUS_FIRST: bool>(
		lines: impl Iterator<Item = &'l str> + 'l
	) -> impl Iterator<Item = Result<Expr<PLUS_FIRST>, ExprsError>> + 'l {
		input_exprs_from_lines(lines)
	}

	#[test]
	fn expr() {
		use {ExprErrorKind::*, ExprExpectedError as Expected};
		assert!(matches!("".parse::<Expr<false>>(), Err(ExprError { column: 1, kind: UnexpectedEnd(Expected::LitOrOpenParen) })));
		assert!(matches!("x".parse::<Expr<false>>(), Err(ExprError { column: 1, kind: InvalidLit('x') })));
		assert!(matches!("1x".parse::<Expr<false>>(), Err(ExprError { column: 2, kind: InvalidOp('x') })));
		assert!(matches!("1 +x".parse::<Expr<false>>(), Err(ExprError { column: 4, kind: InvalidLit('x') })));
		assert!(matches!("1 + 2x".parse::<Expr<false>>(), Err(ExprError { column: 6, kind: InvalidOp('x') })));
		assert!(matches!("1".parse::<Expr<false>>(), Err(ExprError { column: 2, kind: UnexpectedEnd(Expected::Op) })));
		assert!(matches!("1 +".parse::<Expr<false>>(), Err(ExprError { column: 4, kind: UnexpectedEnd(Expected::LitOrOpenParen) })));
		assert!(matches!(")".parse::<Expr<false>>(), Err(ExprError { column: 1, kind: UnexpectedCloseParen(Some(Expected::LitOrOpenParen)) })));
		assert!(matches!("()".parse::<Expr<false>>(), Err(ExprError { column: 2, kind: UnexpectedCloseParen(Some(Expected::LitOrOpenParen)) })));
		assert!(matches!("1)".parse::<Expr<false>>(), Err(ExprError { column: 2, kind: UnexpectedCloseParen(None) })));
		assert!(matches!("(1)".parse::<Expr<false>>(), Err(ExprError { column: 4, kind: UnexpectedEnd(Expected::Op) })));
		assert!(matches!("1 + )".parse::<Expr<false>>(), Err(ExprError { column: 5, kind: UnexpectedCloseParen(Some(Expected::LitOrOpenParen)) })));
		assert!(matches!("(1 + )".parse::<Expr<false>>(), Err(ExprError { column: 6, kind: UnexpectedCloseParen(Some(Expected::LitOrOpenParen)) })));
		assert!(matches!("1 + 2)".parse::<Expr<false>>(), Err(ExprError { column: 6, kind: UnexpectedCloseParen(None) })));
		assert!(matches!("(1 + 2".parse::<Expr<false>>(), Err(ExprError { column: 7, kind: UnexpectedEnd(Expected::OpOrCloseParen) })));
	}

	#[test]
	fn inputs() -> Result<(), ExprsError> {
		input_exprs_from_lines(super::TEST_INPUTS.iter().map(|(s, _, _)| *s)).collect::<Result<Vec<Expr<false>>, _>>().map(|_| ())
	}
}


#[cfg(test)]
const TEST_INPUTS: [(&str, u64, u64); 6] = [
	("1 + 2 * 3 + 4 * 5 + 6", 71, 231),
	("1 + (2 * 3) + (4 * (5 + 6))", 51, 51),
	("2 * 3 + (4 * 5)", 26, 46),
	("5 + (8 * 3 + 9 + 3 * 4 * 3)" , 437, 1445),
	("5 * 9 * (7 * 3 * 3 + 9 * 3 + (8 + 6 * 4))" , 12240, 669060),
	("((2 + 4 * 9) * (6 + 9 * 8 + 6) + 6) + 2 + 4 * 2" , 13632, 23340),
];

#[test]
fn tests() {
	assert_eq!(
		part1and2_impl::<false, _>(parsing::test_input_exprs_from_lines(TEST_INPUTS.iter().map(|(s, _, _)| *s)).map(|r| r.unwrap())),
		TEST_INPUTS.iter().map(|(_, a, _)| *a).sum());
	assert_eq!(part1(), 14208061823964);
	assert_eq!(
		part1and2_impl::<true, _>(parsing::test_input_exprs_from_lines(TEST_INPUTS.iter().map(|(s, _, _)| *s)).map(|r| r.unwrap())),
		TEST_INPUTS.iter().map(|(_, _, a)| *a).sum());
	assert_eq!(part2(), 320536571743074);
}
