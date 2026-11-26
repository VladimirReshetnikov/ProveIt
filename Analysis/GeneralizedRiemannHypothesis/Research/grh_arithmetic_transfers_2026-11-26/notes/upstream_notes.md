# Upstream source audit and transfer interfaces

## Snapshot and level of verification

Repository: `https://github.com/lsernau/grh-lean`.
Pinned commit: `72fead102f663d5c7a407964a13dc0cf9d977207` (main, author date 2026-11-25).
The snapshot is the same one discussed in the incoming reports. It contains two editions.
The readable `grh/src` tree has 803 Lean files and 477,124 physical lines. The compact
`grh-compact/src` tree has 794 files and 112,827 physical lines. These physical line counts
include comments and blank lines; do not confuse them with the README's approximately
300,000 / 76,000 lines of code.

The attached `upstream_audit.py` was run against the pinned checkout. After removing nested
Lean comments and string literals, it found no token `sorry`, `admit`, `axiom`, `unsafe`,
`native_decide`, `implemented_by`, `ofReduceBool`, or `sorryAx` in either `src` tree.
It found no import of `Challenge` from either source tree. This is static evidence only.
It is not compilation, an axiom audit of compiled declarations, or a kernel replay.
The output `upstream_audit.json` also pins SHA-256 digests of the main files inspected.

`grh/Challenge.lean` deliberately contains five `sorry` statements for Comparator. The file
is outside `src`; default targets in `grh/lakefile.toml` are Lib, New, Main. A bare repository
search finding those five placeholders is not evidence of a hole in the target proofs.

The root README and `grh/README.md` report Lean 4.35.0, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, standard axioms `propext`, `Classical.choice`,
`Quot.sound`, exports accepted by nanoda/con-leche/con-ron, and Comparator acceptance.
These are the maintainers' reported checks. The parent agent separately located public
independent checks; those should be cited separately rather than conflated with our source scan.
GitHub API readout on 2026-11-26 returned zero workflow runs and zero check runs for the commit.
This merely means there is no GitHub Actions/check-run evidence to report; it is not evidence
against the published independent builds.

## Endpoint scope

`grh/src/Statements.lean` imports Mathlib and defines four auxiliary endpoint propositions
directly in terms of Mathlib's zeta and `DirichletCharacter.LFunction`. `src/Main.lean`
proves five endpoints, beginning with Mathlib's own `RiemannHypothesis`.

The strongest exported nonvanishing statement is

\[
\forall N\ge1\;\forall\chi\bmod N\;\forall s\in\mathbb C,
\quad \Re s>1/2,\quad(\chi\ne1\text{ or }s\ne1)
\Longrightarrow L(s,\chi)\ne0.
\]

All Dirichlet characters, including imprimitive characters, are included. This endpoint
does not assert RH for arbitrary nonabelian Artin L-functions, non-Dirichlet Hecke
characters of number fields, or automorphic L-functions. Internal use of those theories
does not broaden the exported theorem. The critical-line conclusions use the functional
equation in `New/Main.lean`.

Source anchors:

* `grh/src/Statements.lean:1-18`.
* `grh/src/Main.lean:4-22`.
* `grh/scripts/PrintAxioms.lean:1-7`.
* `grh/src/New/Reduction/OneSidedBound.lean:239` (`New.grh`).

## The reusable arithmetic mechanism, with quantifiers intact

The genuinely useful object is a family of arithmetic lattices and theta lifts, not only the
final theorem about Dirichlet zeros. The core comparison has three ingredients.

1. **Short integral inputs.** `span_short_integralRamified_eq_top` says that short integral
   source forms span; their normalized Poincare images have controlled archimedean squared
   norms for every conjugate. `indexLe_normalizedPoincare` controls a finite family of these
   images at every p-adic embedding by an index/colength bound. Divisibility of theta jets
   supplies weighted prime-power sums in the logarithm of the norm bound.
2. **Enough independent images.** `enough_forms` supplies a finite set of group translates
   whose total source dimension costs only a logarithmic multiple of target dimension and
   whose images span at least `(1-4/b^2)` of the target. This near-completeness matters: the
   auxiliary vectors used to complete a basis are individually expensive.
3. **Long integral families.** `integral_forms_long` bounds covolume plus twice the index from
   below. It uses a favorable twist for every p-adic embedding, together with one compatible
   height bound on the family of determinant ratios. Independent local selection without
   this height compatibility is not sufficient.

The general product-formula result is already abstracted:
`grh/src/New/Reduction/Lattices/TwistedLattice.lean:477`,
`New.TwistedLattice.covolume_add_index_nonneg`.
For a basis `(y_1,...,y_n,z_1,...,z_{n'})`, injective lifts, allowed twists, logarithmic
covolume `c`, index `delta`, auxiliary squared-norm cost `b_short`, scalar-height cost
`b_denom`, and determinant-ratio height cost `b_volume`, it gives

\[
0\le c+2\delta+n'(b_{\mathrm{short}}+b_{\mathrm{denom}})
 +b_{\mathrm{volume}}.
\]

The local integrality matrices entering the index bound must be uniform over twists allowed
at that prime; the proof uses the matrix at an embedding and its conjugate for the same chosen
twist. A transfer must preserve this uniformity as well as the final product formula.

In the RH application, the main amount cancels and the result is

\[
m\,\mathrm{totalRemainder}\le f a(\log b)^5.
\]

This is `star_inequality` at `New/Reduction/MainInequality.lean:87`. The final scale selection
has `m` between `sqrt(x)` and `2 sqrt(x)` and `log b <= 2 x^epsilon`, yielding an eventual
one-sided bound `R_q(x) <= x^{-1/2+epsilon}` (`OneSidedBound.lean:200`). For each putative
zero, the zero criterion chooses an auxiliary quadratic twist that does not vanish in the
relevant finite-height region, preventing pole cancellation. The quantifier is not one
globally fixed auxiliary quadratic twist for all zeros. See
`New/Reduction/Zeros/Criterion.lean:38-52` and its proof.

These facts justify regarding the proof as an arithmetic method that might transfer, but
they do not supply the new arithmetic objects or error budgets for a nonabelian target.

## A precise Euler-factor interface that should not be overlooked

The readable guide expressly says that some background theorems use weakened forms sufficient
for this proof. In particular:

* `GaloisRep.Attached` (`Lib/GaloisRep/Main/AttachedRepresentations.lean:62-74`) asks for
  coefficientwise p-adic approximation, for every positive tolerance, along the special
  `mostFrobenii` filter.
* `mostFrobenii` (`Lib/GaloisRep/Main/Defs.lean:209-231`) means that every nonempty open
  Galois set contains a nonempty open part on which all but finitely many relevant prime
  data satisfy the property. It is not a quantitative prime-density estimate.
* This interface is strong enough to prove uniqueness of attached characteristic-polynomial
  limits and traces: `Attached.tendsto_charpoly_coeff:230` and `Attached.trace_eq:248`.
  It should not be dismissed as merely a vague approximation.
* At one specified spherical place, however, `IsCompatibleAt` (`AttachedRepresentations.lean:83-87`)
  says that a Hecke polynomial **annihilates** the corresponding Frobenius action. It does
  not say that polynomial is the full characteristic polynomial with the correct multiplicities.

For a new Euler-product application, one must either use stronger existing compatibility
theorems or upgrade this interface. The upgrade is especially cheap in rank two.

### Rank-two determinant upgrade (elementary lemma)

Let `K` be a field, `A in GL_2(K)`, and
`Q(T)=T^2-tT+d`. Suppose `Q(A)=0` and `det(A)=d`. Then

\[
Q(T)=\det(TI-A),\qquad t=\operatorname{tr}A.
\]

**Proof.** Cayley--Hamilton gives
`A^2-(tr A)A+(det A)I=0`. Subtracting `Q(A)=0`, and using equality of determinants,
gives `(tr A-t)A=0`. Since `A` is invertible, `tr A=t`. Substitution proves the result.
The proof works in every characteristic.

**Application to a target interface.** At an unramified prime for the two-dimensional
standard `S_3` representation, determinant is the sign character. For the conductor-23
benchmark, a proposed local Hecke polynomial has the form
`Q_p(T)=T^2-a_p T+chi_{-23}(p)`. Once both its annihilation property and the determinant
identity are independently established for the desired representation, the exact Euler
factor follows. Thus full general-rank local-global compatibility is unnecessary for
this particular step. This removes an interface obligation, not the missing global
arithmetic prime-sum estimate. It is an elementary lemma, not a newly resolved conjecture.

### The rank restriction is real

Over `Q`, let `A=I_3` and let `B` be the permutation matrix of a 3-cycle:

\[
B=\begin{pmatrix}0&0&1\\1&0&0\\0&1&0\end{pmatrix}.
\]

Both matrices are orthogonal, have finite order dividing three, have determinant one,
and are killed by the squarefree polynomial `Q(T)=T^3-1`. Nevertheless

\[
\det(TI-A)=(T-1)^3,\quad\det(TI-B)=T^3-1,
\quad\operatorname{tr}A=3,\quad\operatorname{tr}B=0.
\]

Even finite image, semisimplicity, self-duality, purity of the eigenvalues, the right rank,
and an exact determinant cannot replace multiplicity control in rank three. This is a
counterexample only to an abstract inference, not to the upstream proof. The exact integer
calculation is reproduced in `euler_factor_check.py`; it also checks the rank-two identity
for 496 small invertible integer matrices and 8,432 candidate annihilators. The universal
rank-two proof is the algebraic argument above, not the finite test.

### A sufficient all-rank upgrade

If an `n x n` operator `A` has a cyclic vector `v`, meaning
`v,Av,...,A^(n-1)v` form a basis, its minimal polynomial has degree `n`. Therefore every
monic degree-`n` annihilator is its characteristic polynomial. This supplies a finite
certificate (a nonzero Krylov determinant) for computations where cyclicity is available.
One must not assume it for all Frobenius classes: the identity class in many finite-image
representations is scalar and has no cyclic vector in rank greater than one.

## A further proved arithmetic tool available for extraction

The following result is already established in the upstream formal development and has a
more direct arithmetic interpretation than another RH-equivalent analytic condition.

`New.Lift.KummerChart.dualDefect_le_of_few_low_weights`,
`grh/src/New/Congruences/Lifting/CupOrthogonalityBounds.lean:287-338`, gives an explicit
length bound in integral local p-adic Hodge theory. Its combined zero-defect version is
`dualDefect_eq_zero_and_dualDefect_le:351-372`.

Here `dualDefect(Q,L)` is the length over a p-adic integer coefficient ring `O` of
crystalline cocycles in `L`, modulo those annihilating every crystalline cocycle in every
lattice `Y` in a specified class `Q`, under every allowed pairing modulo `p^n`.
This is precisely the definition in
`Lib/ClassField/LocalDuality/CrystallineDuality.lean:152-200`.
An allowed pairing is not just an equivariant characteristic-zero pairing: its failure of
equivariance is `p^n` times a crystalline cocycle. This distinction is essential; do not
paraphrase the result as ordinary rational Bloch--Kato orthogonality, which is weaker.

Suppose the Kummer chart is unramified, `p>=5`, its residue-degree parameter is `f`, and
the Hodge--Tate jumps of the two classes at each letter lie in opposite two-window sets

\[
[-\eta,\eta]\cup \varepsilon_i[b_i,b_i+W],\quad
[-\eta,\eta]\cup -\varepsilon_i[b_i,b_i+W].
\]

Require `eta>=1`,

\[
b_i+W+\eta\le(p-3)a,\quad
6(a+\eta+W)<b_i,
\]

and no nonzero multiple of `p` within distance `6(a+eta+W)` of any of `0,b_i,-b_i`.
If `L` has at most `m` low jumps, with multiplicity, at each coefficient embedding, then

\[
\operatorname{dualDefect}(\mathcal Q,L)
\le 11 f\left(m(a+1)+\operatorname{rank}_O(L)(W+1)\right)
 \operatorname{length}_O(O/pO).
\]

The defect vanishes if both allowed jump sets avoid `[-a,0)`, or if the jump set on the
`L` side is wholly contained in `[-eta,0]`. These are alternatives in addition to the
preceding numerical/window hypotheses, not replacements for them.

The number `m` is the count of low jumps, not the total rank. This may be useful in
families where a few low jumps coexist with arbitrarily large multiplicity in the far
window. It provides controlled torsion loss for congruence arguments and potential
quantitative local Selmer comparisons. It does not assert vanishing of a global Selmer
group, a Tate--Shafarevich group, or a higher K-group.

A concrete permissible numerical regime outside the usual small-weight range is
`p=101`, `a=3`, `eta=1`, `W=0`, constant `b_i=151`. Indeed `152<=294`, `24<151`,
and no nonzero multiple of 101 lies within distance 24 of `0` or `+/-151`.
Then the defect bound becomes

\[
11f(4m+\operatorname{rank}L)\operatorname{length}_O(O/101O).
\]

For jump sets contained in `{0,151}` and `{0,-151}`, the no-small-negative-jump
alternative gives defect zero (assuming the chart and representation hypotheses).
This is a corollary obtained by substitution into an existing upstream theorem; novelty
and equivalence to other published formulations have not been established.

## Recommended prioritization

For a new global conjecture, the conductor-23 rank-two target remains a sensible first
test because the exact Euler-factor issue can be reduced to determinant compatibility.
The decisive unproved input remains a compatible integral lattice construction with a
Frobenius-sensitive divisibility gain, almost-spanning, and the requisite determinant-height
bound. It would be misleading to call the rank-two upgrade itself progress on that estimate.

For a completed arithmetic theorem that can be documented immediately, extract the local
dual-defect bound with its exact hypotheses and prove a specific application to a chosen
congruence module. This has a realistic route to useful research beyond standard RH/GRH
corollaries, while avoiding claims that a merely analogous global construction already exists.

## Reproducibility

Run `python3 upstream_audit.py /path/to/grh-lean --output upstream_audit.json`.
Run `python3 euler_factor_check.py > euler_factor_check.json`.
The upstream build itself, if independently desired, is described by its pinned README.
No upstream build was executed as part of this source audit.
