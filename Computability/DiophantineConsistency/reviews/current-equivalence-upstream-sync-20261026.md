# Pinned upstream synchronization: independent source review

Reviewer: `controller_certificate`. Result: **PASS for source review; no blocking
mathematical or interface finding**. This is an independent review of incoming
proof changes, not a fresh Lean compilation or an acceptance of every research
proposal in the incoming packets.

The exact comparison is local
`c77fd6aca2a05e4da34a2b87d5f41a27666db316` against incoming
`3299f4aa4c9ae38b0f5a1c00a1f0d23f6cbdb114`. Their merge base is
`493d46d498af45840085ef8c170a9db6289157f9`. All eleven changed active modules
have identical local and merge-base bytes. Therefore their two-dot source
diffs are also the incoming changes from the merge base. Local additions
absent on the incoming branch are branch divergence, not incoming requests to
delete those files. In particular, the umbrella differs between the tips but
has no incoming change from the merge base.

I read the entire eleven-module active diff, the complete final sources, the
primary helper contracts described below, all five new placement records,
the adoption/index documentation diff, and the full final 211-line diff
continuation of `lean-proof-simplification-20261026-root.md`. I used only
read-only Git/source inspection and newly authored text-comparison/arithmetic
code. **No incoming Lean module, script, patch driver, or research executable
was run.** No Git state, existing source, prerequisite object or shared document
was changed. This receipt is the only new repository file from this review.

## Interface and data preservation

A text comparison of every old public theorem/lemma declaration, including
same-line attributes and allowing declaration reordering, found all **104**
old headers unchanged after whitespace normalization. This count classifies
theorems/lemmas only, rather than the broader result/record counts used in some
upstream axiom audits. The newly public declarations are the five existing
Jones evaluation bridges and the new `RefinedPair.core_eq` theorem. The Jones
bridge proofs themselves are unchanged. The selective coefficient theorem is
moved after its degree theorem; its statement is preserved.

All **56** existing definition/abbreviation regions were compared. **54** are
byte-identical after excluding surrounding comments/attributes. The only
changed regions are `RegisterNatPairing.leftRelation` and `rightRelation`:
their `correct` proof fields change, while every data field, witness count,
program input, output wire and graph expression remains unchanged. This source
review does not independently execute the reported whole-record `rfl` audit.

There is no added `axiom`, `sorry`, `admit`, `unsafe`, `native_decide`, or
`implemented_by` token in the active additions. No declaration statement is
weakened by a new desired-conclusion assumption. Existing imports are changed
only by adding `PellRatio90`, `SignedPellResidue`, polynomial big-operators and
ring list big-operators, and removing the direct complex-polynomial import in
`RefinedPair`. The primary project helper sources newly reused are unchanged
between the pinned tips. Transitive availability of complex arithmetic is not
claimed to have disappeared.

The eleven sources shrink from **1,978 to 1,741 physical lines**, a net 237-line
reduction including the three-line growth in `RefinedPair`.

## Arithmetic and semantic review

- **NativePellPower.** The reused `Ratio90.lower_key` is exactly the previous
  natural inequality. The full `lower_estimate` contract has the same shifted
  base `a+2`, odd index `2*r+1`, and hypotheses `X,Y,r >= 1`. Its undoubled
  ordinate satisfies `yn(P,r+1)*(X+1)^(2*r) < c*X^r`. Multiplication by positive
  two and the retained `k = 2*yn(P,r+1)` give precisely the old doubled bound.
  The new call discharges the two Pell-base inequalities from the existing
  hypotheses; it does not import a ratio or source-recovery conclusion as a
  premise. The subsequent power, congruence and source-recovery proof is
  unchanged.

- **NativePellStepDown.** Classification still produces
  `I*u = xn I s`. Divisibility by `I` follows directly from this equality.
  `SignedPellResidue.odd_index_of_base_dvd` reduces that divisibility to the
  existing Pell index congruence with index and modulus index both one,
  giving `s = 1 or 3 (mod 4)`, hence oddness. I read that complete helper and
  the underlying `Pell.modEq_of_xn_modEq` proof/contract. No positivity of the
  signed first-root quotient is added. Both residue alternatives and the
  absolute-value/sign recovery remain in the unchanged downstream proof.
  The now-unused `hy` premise is retained; removal of its dead positive-index
  intermediate does not remove a caller hypothesis.

- **NativeCyclicRotation.** With the existing definition
  `convolution a c k = sum_i a i*c(k-i)`, the impulse `Pi.single t 1` gives
  exactly `c(k-t)`, not the opposite rotation. Its word is `rho^t.val`.
  `word_convolution` therefore yields the unchanged word congruence modulo
  `rho^n-1` directly. I read the full convolution module and checked its
  `base_period`/`pow_mod_length` chain. The proof remains valid for arbitrary
  natural digits, `n=1`, and `rho=1` (where natural congruence modulo zero
  reduces to equality); it adds no Boolean, carry, or alignment premise.

- **RefinedPair.** `expand 2` doubles only the outer radical exponents, leaving
  coefficient variables fixed. Its injectivity requires only the positive
  exponent multiplier. The existing `expand_two_core` and
  `eval₂_rawProduct` identities, evaluated by the coefficient inclusion and
  outer variables, reduce the new formal statement to the already proved
  four-sign product formula. The eight arguments keep their original order:
  two radicands, two weights, then `n,B,C,D`. Integer evaluation then gives
  the old `value_eq` without selected complex roots. I read the actual
  formal-product/core/evaluation definitions and Mathlib expansion contract.

- **RegisterNatPairing.** The expanded two-element witness vector still lists
  the missing component first and inequality slack second. Eliminating the
  slack with `exists_certificate_iff`, then the missing component with
  `exists_pair_right_iff` or `exists_pair_left_iff`, proves the required
  projection equality with the correct orientation. The branch remains
  Mathlib max-square pairing, not the older Cantor pairing. All literal
  program nodes, ports and graph data are preserved.

- **SelectiveCarry / NativeQuadraticPositions.** Finite-sum monomial bounds
  prove the kernel degree without a nonzero-coefficient assumption; the
  square/product bounds give degree at most `2*W+D`. The strict bound and
  coefficient-vanishing conclusion follow with the original natural
  inequalities. Empty supports, zero polynomials and cancellation remain
  permitted. For position rows 0 through 20, `349*(k+1) <= 7329 < 7516`, so
  natural subtraction alone suffices. Row 21 is the actual five-entry set
  `{59,18,64,21,0}`. Independently reading its unchanged 71-pair and 32-weight
  literals gives complementary exponents **7407, 7474, 7411, 7478, 7516**,
  respectively. Thus the exceptional finite proof checks exactly the
  remaining frontier, including the attained top exponent.

- **JonesSyntax / ExecutableJones.** The five exposed proofs evaluate the
  same `RingVars` fields against the same `evalExprVars` record. The only
  executable proof-site change qualifies these existing bridges; the
  duplicate private proofs disappear. No syntax constructor, exponent,
  enumerator, coordinate or compiler expression changes.

- **SyntaxCoefficients.** The private bridge is a direct structural proof
  that the unchanged recursive interpretation equals a list sum of
  monomials. Append, negation and flat-map multiplication then use exact
  list/ring identities, and the coefficient map is additive. Multiplicity,
  order, zero terms, signed cancellation and empty lists remain represented.
  The exponent-vector equivalence supplies injectivity; no finite search or
  normalization of the executable list is silently introduced.

- **ObjectPolynomial.** The existential equation binder still shifts every
  input slot by one. Direct `evalForm_spec` simplification matches that
  binding. Injectivity of `Fin.val` makes restriction of infinite
  environments surjective onto every finite tuple; the existing `vempty H`
  provides the explicit extension default. The predicate retains its
  internal-natural guard and equation negation. This works also for zero
  variables and arbitrary nonstandard internal naturals. It does not replace
  internal tuples by standard numerals or add an extra model assumption.

## Upstream evidence and inert material

The complete upstream root receipt containing that continuation has SHA-256
`68a1431ce1b5b0a6908ef4f93861d6a6752ffa0f00abb71c6d8da70bc116feb1`.
I checked its claims against the corresponding adopted source commits and
the final source text. It reports successful target/client/focused compilations
and unchanged old axiom reports for all ten adoption groups. It explicitly
excludes the premature old-cache step-down audit, records the missing unchanged
prerequisite object and retry, preserves the unused-`hy` warning, and records
the object-environment motive-inference repair before final success. The
reported new formal-core audit uses only the standard axioms. These are
**upstream-reported compiler observations**, not fresh executions or direct
object authentication performed in this review. I found no conflict between
that receipt and the reviewed proof/interface changes.

The incoming merge-base diff contains 353 paths: eleven active modules,
338 files in the five new `2026-10-26zk` through `zo` research packet
directories, and four documentation files. The packet additions were reviewed
for placement/import scope, not all proposal mathematics. The complete active
source import scan finds no research-packet import, and `lakefile.toml`,
`lean-toolchain`, `lake-manifest.json`, and the active umbrella have no incoming
changes from the merge base. Proposed source copies and scripts in these
directories remain inert; this review neither executes nor adopts them.

The maintained equation artifacts are byte-identical between the pinned tips:
TeX `a48ac1f5bc498bfdbf300c7050332ecaa28af1fc43f27d86b0879a79bd38714e`,
PDF `417c2fa109cacf99d0e83af35d06cbdc8fed1179054d7245e07f3e51ebfff978`.
The incoming receipt separately reports the decimal-digit/render check; this
review verifies byte preservation, not a new render.

## Exact active-source binding

All paths below are beneath
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| Module | Incoming SHA-256 |
|---|---|
| ExecutableJones | `cfb042909f543bdb46853b08e9de389e84257f3b20a0b57e89124d3f479bc02b` |
| JonesSyntax | `9beb4143c9f824ec490fdffa59227036de8a2c68b44714728c4dcca5b5d6fd9b` |
| NativeCyclicRotation | `c99b77ade816ff64c0870899bd11b405220a36bb80f9b6fa7243a0d2f81e57a6` |
| NativePellPower | `0023e5b08860b86b147833810af60a138adfdae6bf9663a7e0c163eb6b9f3489` |
| NativePellStepDown | `8fc2fb01654786bf8d7a9e104e84593dc43f74f73de53862ff411433fb482814` |
| NativeQuadraticPositions | `9291a5ef09c8307a7c40fc1fb61f556cdddd460839cc4750b496b7fa3c8198fc` |
| ObjectPolynomial | `5fcc6433566013210491225b731f91f7063346078c53331ce3ba3505fc4eb641` |
| RefinedPair | `c06b1328baf3edb891ea3c92eda644e4bf4b13d535725b08a2dd5c4ea9ad1c36` |
| RegisterNatPairing | `f31c27c34f6711cde684c4fd560e1030a5c8fb5a8f6ed8cfd644fe15507259c4` |
| SelectiveCarry | `767c0d3166768c34664ec2fd89b0bfc0f30fcd62bfd8f5514736cd669dc0b4c3` |
| SyntaxCoefficients | `cad2c498522aca13bc656b25c5cfe466fea8c750a9626c8be17ca9e87e769dbb` |

The exact eleven-file Git diff has SHA-256
`f9f71477f12bdddb82c859de920b9801e821699e33ca07a873c4b14207d2ea45`.
The unchanged toolchain and manifest hashes are respectively
`2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e`
and `95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665`.

I authored none of these eleven incoming proof changes. I authored several
current-equation arithmetic, carry, word and source-map clients elsewhere in
this branch; that prior dependency role does not constitute independent
validation of their post-merge compilation. Root remains responsible for the
actual merge and any post-merge compilation/axiom checks. This review supplies
no new claim that the complete current equivalence endpoint has compiled.
