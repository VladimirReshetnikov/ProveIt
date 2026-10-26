# Literal nine-variable polynomial data for package 52

[`NativeNinePolynomial52.lean`](Lean/DiophantineConsistency/NativeNinePolynomial52.lean)
defines the full evaluator over any commutative ring. Its nine-coordinate
order is `b,g,h,s,w,phi,i,j,n`. The coefficient parameters are the fixed
four-port tuple and its chosen positive coefficient height.

The source radix is `4096*height*b^2`. Its kernel is the finite sum of the
136 supported weighted records from the literal 22-row, 31-input source.
The mask, dense padding, block sizes, cap, and central rank use ordinary
ring arithmetic. `ratioValue` then evaluates the actual package-52 Pell
registers and its margin-first finalizer. Integer evaluation is computable;
the data contain no natural truncation, division, or root selection.

`ratioValue_nat` identifies the arithmetic schedule with the checked
`NewVars.finalValue`. `value_eq_finalValue` connects the complete evaluator
once the supplied source rank, block size, and cap equal their natural
casts. These equalities are explicit proof hypotheses; they introduce no
truncation into the polynomial itself.

`polynomial ports height` is the actual `MvPolynomial (Fin 9) ℤ` obtained
by using coefficient constants and nine indeterminates in that evaluator.
`eval_polynomial` proves its evaluation equals `value` for every integer
assignment. Generic ring-homomorphism lemmas cover the literal coefficient
table, finite kernel, source code, and ratio schedule. The mathematical
polynomial constructor uses the library's noncomputable finite-support
operations, while the integer evaluator is executable.

The source/carry semantics and domain translations are separate bridge
theorems. Operation-count certification of a particular shared evaluator
also remains separate; this module does not assign the published 548-gate
count to its direct finite-sum recipe.

`NativeNineEquation52` now discharges the source cast hypotheses using
unconditional high-word positivity and exact mask/rank casts. Its shifted
polynomial is an actual nine-variable natural-domain equation, and
`exists_zero_iff_source_published` proves equivalence with the literal
positive source under the four published port-size bounds. Authentic
native calibration and the internal ZFC theorem remain open.
