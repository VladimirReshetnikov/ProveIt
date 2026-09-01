# Documentation audit

`AGENTS.md` lists two documentation invariants for
`Analysis/FabiusFunction/Lean`:

- every source file carries a `/-! ... -/` module header; and
- every non-`private` declaration carries a `/-- ... -/` doc comment.

Neither held corpus-wide when this audit was first run.  This file records the
gap, and
[`scripts/doc_audit.py`](../scripts/doc_audit.py) makes it measurable, so that
a reviewer can check a change did not make it worse rather than re-deriving
the numbers by hand.  `AGENTS.md` asks for exactly this: a recorded, executable
scan rather than a number quoted from a vanished shell session.

## Running it

From the repository root:

```sh
python3 Analysis/FabiusFunction/scripts/doc_audit.py
python3 Analysis/FabiusFunction/scripts/doc_audit.py --list
```

The first form prints the totals and the twenty worst files.  The second adds
every undocumented declaration as `file:line  name`, which is the form to use
when clearing one file.

To use it as a gate:

```sh
python3 Analysis/FabiusFunction/scripts/doc_audit.py \
  --baseline Analysis/FabiusFunction/docs/doc_audit_baseline.json
```

This exits non-zero if the missing-doc total rises, if any individual file gets
worse, if a new file appears without a module header, or if the corpus inventory
changes without a reviewed baseline refresh.  The ratchet was originally
needed to make progress against a large inherited backlog.  As of 2026-08-29
that backlog is zero, so the checked baseline now enforces both invariants
without an exception.

Refresh the baseline with `--write-baseline` after genuinely reducing the
missing-doc count or after verifying a fully documented corpus addition.

## What the script does and does not check

It is a lexical scan, not Lean elaboration.  It tracks nested `/- -/` blocks,
`/-- -/` doc comments, `/-! -/` module comments, string literals and `--` line
comments, so a declaration keyword appearing inside a comment or a string is
never counted.  It accepts an attribute line (`@[simp]`, a multi-line
`@[...]`), an attribute on the same line as its declaration
(`@[simp] theorem foo`), a `set_option ... in` line, or blank lines between a
doc comment and the declaration it documents.  It also accepts the one-line
`/-- ... -/ theorem foo` form.

It does not see declarations produced by macros.  A `to_additive`-generated
name is invisible to it, exactly as it is to a reader of the source, so a
generated declaration is neither counted as present nor reported as
undocumented.

It says nothing about whether a doc comment is *correct*.  That is the more
expensive audit, and three defects it would have caught are recorded below.

## Findings

### Module headers

Twelve modules had no `/-! ... -/` header at all, verified by direct grep
(`/-!` occurring zero times in the file):

`PeriodicFourier`, `PeriodicMean`, `HalfQBinomial`, `ThueMorseGenerating`,
`ThueMorsePrefix`, `FabiusSaddleCentral`, `SaddleAllOrders`,
`FabiusSaddleExponentAllOrders`, `FabiusSaddleTailAllOrders`,
`FabiusSaddleReferenceTail`, `NegativeLaplaceVerticalOrdinaryJets`,
`GammaSecondOrder`.

Four more had a bare title with at most one line of prose, and one of those
described finished, downstream-consumed results as scratch development:

`FabiusLambertDerivativeBounds`, `FabiusSaddleCentralLambert`,
`NegativeLaplaceVerticalTaylor`, `NegativeLaplaceVerticalFourthBound`.

`SaddleLogExpansionAlgebra` called itself a scratch module in an otherwise
accurate header.

All of these have been written or rewritten.  Every header was drafted against
the whole file and then checked by a second reader against the same file,
because a header that is trusted and wrong is worse than one that is absent.

`PeriodicFourier` is the case that mattered most: 72 public declarations, the
entire Mellin and Fourier analysis of the regularized Bose kernel, and no
statement anywhere in the file of what it was for.

### Doc comments

The backlog began at 862 undocumented public declarations, 31% of the corpus.
Two documentation waves and a pass over the two root modules first brought it
to 176, or 6.2%, and the original 191-module corpus was subsequently cleared
according to the then-current checker.

That apparent zero exposed a checker defect: declarations written as
`@[simp] theorem foo` on one line were not counted at all.  After teaching the
auditor to remove balanced leading attribute blocks, and after the corpus grew
to 311 modules, the corrected 2026-08-27 inventory initially contained 4,803
public declarations with 105 missing comments in 40 files.  The old parser saw
only 4,606 declarations and
36 gaps on those same bytes; the correction therefore recovered 197 attributed
declarations, including 69 undocumented ones.  Run the script for the live
numbers rather than copying these historical values.

The post-merge 2026-09-01 inventory contains 623 modules and 8,476 lexically
visible public declarations, with zero missing module headers and zero missing
doc comments.  Relative to the 610/8,318 activation checkpoint, the exact
union adds thirteen modules and 158 declarations.  The branch-point geometry and
asymptotics leaves contribute 17 declarations for the one-sided vertical
tangents and leading signed square-root laws of both real Lambert branches.
The two Legendre--Gaunt modules contribute 25: four definitions and twelve
theorems in `LegendreGaunt.lean`, and one definition and eight theorems in
`FabiusLegendreGaunt.lean`.  They add the executable rational triple-product
and finite product-linearization core, then specialize it to full and even
Rvachev coefficient sums for rational and real Legendre Gram entries.  The
remaining twenty declarations are three generalized spectral q-Pochhammer
APIs, four density-diagnostic theorems, the locally uniform real-frequency
phase-prefix theorem and its compact-set uniform corollary in
`GeometricSincCharacteristicFunction.lean`, and eleven inverse-modulus
strictness and equality refinements.  `GeometricUniformMultisection.lean`
contributes two coordinate definitions and three fixed half/quarter
multisection theorems.  `GaussianBinomialAtNegOneDerivative.lean` supplies four
declarations: two first-derivative formulas at `q = -1` and two simple-root
multiplicity theorems.  Three signed-power moment theorems in
`RvachevDerivativeDistribution.lean` give the exact Boolean-cube formula and
its even-moment and positive-order odd-moment corollaries.  The same module's
two additional positive-order signed-distribution theorems give the sharply
normalized half-mixture law under exactly `0<n`:
`intervalIntegral_comp_normalized_iteratedDeriv_rvachev` is the continuous-test
half-mixture into any real Banach space, and
`map_normalized_iteratedDeriv_rvachev_restrict_Icc` is the corresponding Borel
pushforward identity for Lebesgue measure restricted to the closed interval
`[-1,1]`.  Order zero instead has the unsymmetrized original `rvachevUp` law.
The remaining declaration is the all-depth
`generalizedRvachevProduct_two_pow_mul` shift--refinement theorem in
`WeightLinearityProducts.lean`.  The final nine declarations are the two
definitions and seven theorems of `LagrangeRvachevSynthesis.lean`: the generic
finite-node decoder and atom coefficient, degree bounds, cardinal synthesis,
componentwise biorthogonality, linear coefficient identity, exact finite
interpolation loop, and unit row mass.  This inventory claim does not extend to
a geometric Gaussian closed-form decoder, a matrix wrapper, or an
optimal/minimum-variation decoder theorem.  The subsequent
`integral_polynomial_mul_rvachevUp_eq_dyadic_tsum` theorem in
`PolynomialCombExactness.lean` packages the polynomial-times-Rvachev integral
as the corresponding dyadic shifted-polynomial sum and contributes one further
declaration.  The subsequent centered Appell/deconvolution and arbitrary-phase
polynomial-reproduction tranche contributes four declarations: three in
`RvachevMomentAppell.lean` and one in `RvachevPolynomialSynthesis.lean`.
The new `QPochhammerEntire.lean` leaf contributes four further theorems:
locally uniform convergence of the defining products for every strict complex
contraction, complex differentiability in the free parameter, the exact
factor-zero classification (including the `q = 0` boundary), and simple zeros
expressed as analytic order one.  Together with the branch-only four-theorem
Gaussian `q = -1` first-jet leaf, both q-series modules remain facade-reachable.
The two subsequent general q-Pochhammer modules contribute thirty further
declarations.  `QPochhammerDissection.lean` adds two finite residue-class
dissection theorems over an arbitrary commutative ring: the exact-multiple form
is total in `r`, and the remainder form assumes exactly `u <= r`.
`QPochhammerInfinite.lean` adds the general infinite symbol and twenty-seven
theorems covering summability and convergence for a strict norm contraction,
finite-prefix and residue-class factorizations, exact factor-zero criteria,
locally uniform parameter convergence and continuity, complex entirety,
explicit derivatives at factor zeros, and nonvanishing of the displayed
derivative coefficient at every inverse-power zero for a nonzero nome.  Its
algebraic cofactor
identity needs only a field and a nonzero nome; its infinite dissection assumes
exactly `0 < r`, `[NormedCommRing R] [NormOneClass R] [CompleteSpace R]`, and
the strict contraction.  These are regularity statements in the free parameter
`a`, not a joint analyticity or continuation theorem in the nome `q`.
The valuation tranche's new leaf
`PrimePowerBinomialValuation.lean` contributes three theorems: the additive and
subtraction forms for an arbitrary prime-power Pascal row, and the strict-
interior dyadic-comb specialization.
Finally, `LegendreGauntClosedForm.lean` contributes two definitions and
twenty-five theorems: the total integer zero-row Wigner-square datum, its exact
central-binomial and factorial forms, the all-degree Gaunt identification,
sharp support, positivity and vanishing criteria, and the product-linearization
coefficient bridge.  It makes no signed-symbol, phase, half-integer,
nonzero-magnetic-index, or general Wigner recoupling claim.  The baseline
also includes the three finite rational-entry, rational-matrix, and real-matrix
Wigner-square sum corollaries in `FabiusLegendreGauntClosedForm.lean`.  These
two new leaves therefore contribute thirty declarations in total.  The
two definitions are `legendreGauntAdmissible` and
`legendreWignerThreeJZeroSqRat`.  In source order, the twenty-five core theorem
names are `legendreGauntAdmissible_iff_exists_pairwise_add`,
`legendreGauntAdmissible_pairwise_add`,
`legendreWignerThreeJZeroSqRat_pairwise_add`,
`legendreWignerThreeJZeroSqRat_pairwise_add_factorial`,
`legendreWignerThreeJZeroSqRat_eq_factorial_of_halfSum`,
`legendreWignerThreeJZeroSqRat_eq_zero_of_not_admissible`,
`legendreGauntRat_add_boundary`,
`legendreGauntRat_add_boundary_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreGauntRat_zero_left`,
`legendreGauntRat_zero_left_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreGauntRat_pairwise_add_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreGauntRat_eq_zero_of_not_admissible`,
`legendreGauntRat_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreGaunt_eq_two_mul_wignerThreeJZeroSqRat`,
`legendreWignerThreeJZeroSqRat_pos_iff_admissible`,
`legendreWignerThreeJZeroSqRat_nonneg`,
`legendreWignerThreeJZeroSqRat_eq_zero_iff_not_admissible`,
`legendreGauntRat_pos_iff_admissible`,
`legendreGauntRat_eq_zero_iff_not_admissible`,
`legendreGaunt_pos_iff_admissible`,
`legendreGaunt_eq_zero_iff_not_admissible`, `legendreGauntRat_nonneg`,
`legendreGaunt_nonneg`,
`legendreProductLinearizationCoeffRat_eq_mul_wignerThreeJZeroSqRat`, and
`legendreProductLinearizationCoeffRat_pos_iff_admissible`.  The three wrapper
names are `rvachevLegendreGramEntryRat_eq_two_mul_sum_wignerThreeJZeroSqRat`,
`rvachevLegendreGramMatrixRat_apply_eq_two_mul_sum_wignerThreeJZeroSqRat`, and
`upLegendreGramMatrix_apply_eq_two_mul_sum_wignerThreeJZeroSqRat`.

The audited formula contract is equally exact.  Admissibility is even total
degree plus the three weak triangle inequalities, equivalently
`i=b+c`, `j=a+c`, `k=a+b`.  If `C_n=choose (2*n) n` and `s=a+b+c`, then the
square datum is zero off support and
`W²(b+c,a+c,a+b)=C_a*C_b*C_c/((2*s+1)*C_s)`; factorially this is
`s!^2*(2*a)!*(2*b)!*(2*c)!/((2*s+1)!*a!^2*b!^2*c!^2)`.  The half-sum theorem
assumes exactly `i+j+k=2*s` and `i≤s`, `j≤s`, `k≤s`.  The two named boundaries
are `G_Q(i,j,i+j)=2*C_i*C_j/((2*(i+j)+1)*C_(i+j))=2*W²(i,j,i+j)` and
`G_Q(0,j,k)=(if j=k then 2/(2*j+1) else 0)=2*W²(0,j,k)`.  At every natural
triple `G_Q=2*W²`, its real counterpart is twice the real cast, positivity is
equivalent to admissibility, vanishing is equivalent to nonadmissibility, and
all three forms are nonnegative.  The rational product coefficient is
`(2*k+1)*W²` and is positive exactly on support.  Both rational finite-Gram
wrappers are the unconditional twice-sum
`2*∑ r∈range ((i+j)/2+1), c_r*W²(i,j,2*r)`; the real wrapper has the same finite
form and assumes exactly `F : BoundedFabius` and `hF : IsFabius F`.

This square datum is not a bridge to a separately implemented general Wigner
symbol.  No signed value or phase convention, half-integer or
nonzero-magnetic-index API, general `3j`/`6j`/`9j`, orthogonality, recoupling,
or named Wigner-symmetry theorem is present.  The Gaunt factorial identity and
product-coefficient nonnegativity/zero criteria are composable but do not have
separate named wrappers.  Infinite Legendre interchange, Christoffel
reconstruction, roots/quadrature, Padé/J-fractions, infinite Jacobi theory, and
asymptotics remain open.

The New Frontiers finite Gram--Legendre crosswalk consequently has eleven modules,
twenty definitions, and 109 theorems, hence 129 public declarations; its
predecessor nine-module subtotal was `18+81=99`, and the two closed-form leaves
contribute `2+25` and `0+3`.  The integer-index zero-row square datum and finite
Wigner-square Gram route are closed, while signed/phase, half-integer,
nonzero-magnetic-index, general Wigner/recoupling, and later infinite spectral
layers remain outside this tranche.  The baseline records zero missing headers
and zero missing doc comments, so every
future source addition must preserve the full invariant
rather than merely avoid worsening a historical backlog.  Run the script for
live numbers after merging concurrent source work.

The additional declaration in `PolynomialCombExactness.lean` is
`integral_polynomial_mul_rvachevUp_eq_dyadic_tsum`, the exact normalized
physical-coordinate self-sampling quadrature for every real polynomial whose
natural degree is at most the dyadic level and every real phase.

The retained comb-interpolation synthesis PDF is a validated 158-page A4
historical receipt: the current source includes a post-render update to its
additive-dyadic chapter, so a fresh parity build remains pending.  The rebuilt
Integration-and-Transform master is synchronized at 377 pages.  The canonical
q-series synthesis passed its complete publication
gate at 335 pages before this merge; adding the entire and general
finite/infinite q-Pochhammer crosswalks makes a final semantic-union rebuild
pending.  The retained
167-page primary, 126-page walkthrough, 237-page canonical frontier, 301-page
Representation Frontiers, 41-page New Frontiers, and 71-page notation-
catalogue artifacts all predate their current merged sources.  Their package
notices treat those PDFs as historical validation receipts, not parity claims,
until fresh uninterrupted three-pass builds complete.  The inverse-
computability receipt likewise requires refresh for the 623/8,476 census;
the canonical inverse-theory publication remains pending after its
Appell/deconvolution crosswalk update.

### What the review pass caught

Both waves paired each documenting agent with an independent auditor, and that
was not ceremony.  The recurring defect was never a wrong formula -- it was a
false claim about dependencies: "every coefficient computation below factors
through this" when one does not, "the denominator in every ratio bound here"
when it is the denominator of one, "used by X" when X re-derives it inline.
Prose asserting a dependency is much easier to get wrong than prose asserting a
statement, because the statement is on the next line and the dependency is not.

Two doc comments had silently dropped an ambient `IsFabius F`; one stated its
two interval inclusions in the wrong directions; one said an interval
restriction was necessary when the file proves no converse.

The second wave was told this in advance and instructed to write no "used by"
clause at all unless it had been grepped.  78 verified consumer clauses came
out of that, and the defect rate fell accordingly.

### Doc comments that contradicted their statements

A separate sampling pass read about 190 doc-comment/statement pairs looking
for prose that claims more, or less, than the Lean statement.  The corpus is in
good shape here; three defects were found and fixed.

1. `norm_iteratedDeriv_negativeLaplaceVerticalKernelLogFirst_le` was documented
   as holding "uniformly on every vertical strip center `|theta| <= 1`".  Its
   statement has no such hypothesis: `theta` is an arbitrary real and the
   constant does not mention it.  The prose *understated* the theorem, which
   would have sent a reader looking elsewhere for a bound this lemma already
   gives.

2. and 3. `legendrePolynomial_contDiff` and
   `contDiff_negativeLaplaceVerticalCurve` assert `ContDiff R (top)` with the
   exponent elaborated at `WithTop ℕ∞`.  In this Mathlib that is the *analytic*
   exponent `ω`, not `C^∞`:

   ```text
   Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:118
     scoped[ContDiff] notation3 "ω" => (⊤ : WithTop ℕ∞)
   Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:120
     scoped[ContDiff] notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)
   ```

   Both were documented as merely "smooth".  The corpus writes `ContDiff ℝ ∞`
   in 66 places and `ContDiff ℝ ⊤` in only these two, so the distinction is
   deliberate everywhere else.

   This distinction is worth policing in this corpus in particular.  Its
   central regularity result is that the Fabius function is `C^∞` everywhere
   and analytic exactly off `[0,1]`; a doc comment that says "smooth" over an
   `ω` statement is the one confusion the library exists to prevent.

## Suggested order of work

1. Any new file: header and doc comments at the time of writing.  The ratchet
   gate makes this cheap to enforce.
2. The five worst files.  Clearing them removes about a quarter of the
   backlog.
3. Doc comments on public declarations that appear in `PAPER_COVERAGE.md`,
   since those are the ones an outside reader reaches first.
4. The long interior estimate chains, one module at a time, ideally by the
   agent that most recently worked in the module and still has its structure
   in mind.

Adding a doc comment cannot change elaboration, so this work needs no build
slot.  On a machine where a full rebuild costs the better part of a day, that
makes it unusually good value.
