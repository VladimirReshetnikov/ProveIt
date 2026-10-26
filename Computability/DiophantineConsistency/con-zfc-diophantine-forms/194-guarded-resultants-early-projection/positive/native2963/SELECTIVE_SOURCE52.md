# Literal package-52 source: checked stages

This checkpoint formalizes package 52's interior-regular nine-positive
equation: 548 binary operations and exact degree 15,502,748. Its finite
proposal audit is recorded in [PROPOSAL_REVIEW.md](PROPOSAL_REVIEW.md).
The modules here formalize its actual algebraic stages, with explicit
port bounds. They do not yet establish a new closed consistency equation
or a derivation of the equivalence inside ZFC.

## Literal source and exact coefficients

[`NativeQuadraticParent.lean`](Lean/DiophantineConsistency/NativeQuadraticParent.lean)
contains the source's 60 live arithmetic gates and 22 residuals on 31
positive inputs. Its four coefficient ports are `beta,K0,MC,MF`, in that
order. The copied [source JSON](data/native-quadratic52/source_system60.json)
has SHA-256
`ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48`.
The [generator](scripts/generate_native_quadratic_parent.py) independently
expands the gate expressions and compares all coefficients with the pinned
package-52 certificate. Lean checks the emitted identities over any
commutative ring and every port value; the generator is not trusted for
those identities.

Replace each positive source input by `x_i+1`, with `x_i` natural. Pad
coordinate zero with one, and move the guard residual to the last row.
The resulting 136 quadratic records use 71 distinct unordered pairs.
`rowValue_eq_shiftedRows` and `target_zeros_iff_source_zeros` prove exact
equality with the literal source predicate. They retain all four ports
uniformly; no native coefficient tuple is assumed correct by these theorems.

## Selective positions and coefficient bounds

The weights come from `SelectiveCertificate52`. The dummy weight is 81,
the maximum weight is 174, and an actual input occupies weight zero.
For row index `k` from 0 through 21, the target is `349*(k+1)`. The last
target is 7,678. Unused unordered pairs may collide; all used pairs are
isolated, including against the other rows' targets.

[`NativeQuadraticPositions.lean`](Lean/DiophantineConsistency/NativeQuadraticPositions.lean)
defines the complete kernel

```
E(X) = sum_(k,p in rowSupport(k))
         correction(p)*a(k,p)*X^(349*(k+1)-weight(p)),
correction(p) = 2 on diagonal pairs, 1 otherwise.
```

Its exact degree is 7,516 and its leading coefficient is 2. The product
`C(X)^2*E(X)`, with `C` the padded sparse input, has degree below 7,865.
Its coefficient at each target is twice the corresponding literal row.
These are complete polynomial statements: no higher terms are discarded.

[`NativeCoefficientBounds.lean`](Lean/DiophantineConsistency/NativeCoefficientBounds.lean)
checks every literal coefficient recipe. If `B0>=2`, `K>=16*B0`, and

```
0 <= beta,MC < B0,   0 <= MF < 2*B0,   0 <= K0 < K,
```

every corrected coefficient has magnitude below `4*B0*K`. In particular,
the published bounds `B0=2^590069`, `K=2^592884` give the exact height
`H=2^1182955`. The proof keeps `K0` linear, avoiding a larger bound from
squaring the transport port. This specialization is conditional on the
four port bounds; proving them for the actual native tuple remains separate.

`SelectiveCoefficientBounds` proves that distinct complementary exponents
give kernel coefficient height at most `H`, without multiplying by the
number of rows. Convolution then gives the bound
`H*(1+sum_i x_i)^2` for every product coefficient. For 31 coordinates
`x_i<b`, the power-of-two choice `B=4096*H*b^2` makes every product
coefficient strictly smaller than `B/2` in absolute value.

## Sparse decoding, ranges and final stages

[`LowMaskCoding.lean`](Lean/DiophantineConsistency/LowMaskCoding.lean)
proves that the low carry test encodes exactly the coordinates `x_i<b`.
It forces every unlisted digit to zero. The regressions use the actual
weight-zero input and show that digit 81 is zero before adding the dummy
term `B^81`, after which it is one.

`PolynomialRangeBounds` proves positivity and the full upper bound for
the high word before any binary decoding:

```
Jhigh = 2*(B^81+g)^2*E(B) + B*sum_(i<7865) B^i,
0 < Jhigh < 4*B^7865,
```

under the explicit coefficient, base and weak-cap assumptions
`0<=g<4*b*B^174`. The exact leading coefficient 2 supplies positivity.
`SelectiveCarry` proves the full shifted-polynomial identity, rowwise carry
equivalence and the central-binomial contract for two packed blocks.
The block sizes are `N0=B^175`, `N1=4*B^7865`, hence `N=4*B^8040`.
`NativeQuadraticSource52.source_contract` now proves the assembled exact
equivalence between central-binomial divisibility and all 22 literal
source rows at decoded bounded inputs. Its size bounds precede decoding.
The same file proves unconditional high-word positivity for every natural
`g`, without the cap, and exact integer casts for the masks, packed words
and rank. Its regression excludes the vacuous `b=1` case for every port tuple.

`NativeBaseBounds52` checks the weak soundness cap, stronger completeness
cap, exact power-of-two scale and an explicit arbitrarily large bound
`b=2^(lower+sum_i x_i+1)`. `NativeSparseBounds52` proves
`code<b*B^174` under `x_i<b<=B`, and shows that a literal source zero has
positive code: the all-zero shifted tuple makes the original fifth row 1.

The [ratio substitution](RATIO_REPARAMETERIZATION.md) preserves the actual
register `H` while eliminating the extra divisibility quotient. Its
`NativeNineRatio52` wrapper now checks soundness and completeness against
the existing Jones numerical ratio theorem with the actual register data.
The [margin-first finalizer](MARGIN_FINALIZER.md) proves exactly the
package-52 four-condition norm test, recovering positive margin before
extracting integer square roots. These are checked separately from the
source adapter.

`NativeNineSource52.natural_zero_iff_source` now joins the source contract,
cofinal bounds, new ratio variables and finalizer in both directions.
Its nine natural coordinates shift `b,g,h,s,w,i` by one and use `phi,j,n`
directly. `natural_zero_iff_source_published` discharges the coefficient
height using only the four explicit published port-size assumptions.
The numerical rank uses an exact `toNat`; its equality with the literal
polynomial rank is proved for arbitrary nonnegative candidate codes before
the weak cap is recovered. `NativeNinePolynomial52` supplies the literal
ring evaluator, and `NativeNineEquation52.polynomial` supplies an actual
`MvPolynomial (Fin 9) ℤ` with the six natural-coordinate shifts.
`exists_zero_iff_source_published` proves its natural-zero equivalence with
the literal 31-input source under only the four stated port-size bounds.
The direct finite-sum recipe does not yet have a Lean-certified identity
with the report's optimized 548-operation evaluator.

The remaining chain must calibrate the four authentic native coefficient
ports to ZFC refutations. The wave-eight review has since selected a
smaller numerical target, documented in
[PROPOSAL_REVIEW_WAVE8.md](PROPOSAL_REVIEW_WAVE8.md). This completed source
checkpoint and its generic components remain available for that work.
The separate object-language work is tracked in [OBJECT_ZFC.md](OBJECT_ZFC.md).

## Reproduction

From the repository root with Lean and Mathlib 4.32.0:

```sh
python3 Computability/DiophantineConsistency/scripts/generate_native_quadratic_parent.py
lake build DiophantineConsistency
lake env lean Computability/DiophantineConsistency/Lean/checks/NativeQuadraticParent.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/NativeQuadraticPositions.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/NativeQuadraticSource52.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/NativeNineSource52.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/NativeNineEquation52.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/LowMaskCoding.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/SelectiveCarry.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/RatioMarginFinalizer.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/RatioReparameterization.lean
```

Completed theorem audits report only `propext`, `Classical.choice` and
`Quot.sound`; no proof placeholders or additional axioms are introduced.
