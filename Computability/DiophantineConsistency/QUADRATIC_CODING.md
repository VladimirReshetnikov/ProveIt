# Direct quadratic coding: checked components and remaining bridge

The closed equation in `ExplicitZFC.lean` still uses the proved quartic Jones
reduction. The results below do **not** yet produce a smaller closed equation.
They replace the exponential-position coefficient extraction by checked
quadratic and simultaneous arithmetic identities.

After the [wave-7 review](PROPOSAL_REVIEW.md), package 52's interior-regular
selective encoding is the next target, with package 53 retained for lower
degree. `SelectiveQuadraticCoding` now proves extraction under isolation of
only the used pairs, with arbitrary row targets and explicit cross-target
exclusion. `SelectiveCertificate52` checks the 71 active pairs at maximum
weight 174 and regular stride 349; `SelectiveCertificate46` checks its
62-pair support at maximum weight 175. Both allow unused collisions.
The literal native rows and source-to-refutation bridge remain separate.
`NearSquareFinalizer` also proves the sharp majorant and final one-witness
norm equivalence. The full-Sidon components below remain general reusable
foundations rather than the preferred numerical positions.

## Checked identities

Let `m` be the number of variable coordinates and reserve coordinate zero
for the constant value one. For `0 ≤ i ≤ m`, set

```
M = 2*m²+1,
w_i = M*i+i²,
L = 4*m³+2*m²+2*m,
H_j = L+j*(2*L+1).
```

[`SidonPositions.lean`](Lean/DiophantineConsistency/SidonPositions.lean)
proves that `w_i+w_j=w_k+w_l` determines the unordered pair, including
repeated indices. The maximum individual weight is exactly `2*m³+m²+m`.
Canonical sorted pairs receive distinct exponents at most `L`.

For a supplied quadratic coefficient family `a[j,p]`, define

```
C(X) = Σ_i u_i X^w_i,
Q_j(u) = Σ_(p=(i,k),i≤k) a[j,p]*u_i*u_k,
E(X) = Σ_j Σ_p correction(p)*a[j,p]*X^(H_j-w_i-w_k),
correction(i,k) = 2 if i=k, and 1 otherwise.
```

[`QuadraticCoding.lean`](Lean/DiophantineConsistency/QuadraticCoding.lean)
and [`MultiQuadraticCoding.lean`](Lean/DiophantineConsistency/MultiQuadraticCoding.lean)
prove, over every commutative coefficient ring,

```
coeff_(H_j) (C²*E) = 2*Q_j(u).
```

The product from row `j` is supported in `[H_j-L,H_j+L]`; these closed
intervals are disjoint. Every target is below
`r*(8*m³+4*m²+4*m+1)`. The requested spacing `2L+1` is conservative: the
wave-45 argument needs only target separation `L+1`, while the present
statement also separates complete product intervals.

[`MultiTargetCarry.lean`](Lean/DiophantineConsistency/MultiTargetCarry.lean)
adds an arithmetic test. Write `P=C²*E`, `n=targetBound m r`, and let `S` be
the finite set of targets. If `B=2^t`, `t≥1`, and

```
|coeff_i P| < B/2      for every i<n,
```

then the shifted digits `coeff_i P+B/2` are strictly between zero and `B`.
The file proves

```
τ₂(2*shiftedValue, (B-2)*Σ_(i∈S) B^i)=0
    ↔ ∀j, Q_j(u)=0.
```

`tau_quadratics_iff` states the equivalent version with twice the explicit
`selectedMask`; `doubledMask_eq` proves the displayed sparse-mask identity.
`shifted_rowProduct_cast` and `doubled_shifted_rowProduct_cast` identify the
finite digit value with `P(B)+(B/2)*Σ_(i<n)B^i` and its doubled form. No higher
coefficient was discarded: `coeff_rowProduct_eq_zero_of_bound` and
`rowProduct_degree_lt` prove the required finite support bound (`r>0` for
the degree statement).

For any supplied power `N=2^α` bounding both doubled numbers, define

```
R = (2*shiftedValue)*(N²-N)
      +(2*selectedMask+1)*(N²-1).
```

`central_quadratics_iff` proves

```
N² ∣ binomial(2R,R) ↔ ∀j, Q_j(u)=0.
```

Its half-base coefficient bound and the two numerical packing bounds are
explicit premises. They are proved hypotheses of a reusable theorem, not
new axioms or an assertion that the concrete source already satisfies them.
Ordinary `Polynomial` interpretations use Mathlib's noncomputable library
operations; all positions, correction factors, row values, masks, and finite
coefficient recipes are explicitly specified.

## Existing proof components that can be reused

| Component | Checked API and role |
|---|---|
| Actual source computation | `ExplicitZFC.program`, `ZFCFromProgram.refutationRep` supply the closed refutation predicate. |
| Quadratic gate system | `QuarticCompiler.residualSyntax`, `residual_degree`, `eval_sumSquares_zero_iff`, `exists_sumSquares_iff` already prove the gate residual interpretation. |
| Binary digit tests | `Jones1982.tau_ofDigits_iff`, `digit_iff`, `lemma_2_4_τ`, `lemma_2_16` supply the proofs used in `MultiTargetCarry`. |
| Sparse code decoding template | `code_of_tau1`/`tau1_of_code` in `Master2.lean` and `short_code_iff` in `ShortMask.lean`; their existing positions are `5^i`, so they need an explicit-weight variant. |
| Packing | `pack3_lt`, `pack3_carries_iff_dvd`, and `centralCode_ge_base` in `Packing.lean` are generic arithmetic results. Two blocks can instead use `lemma_2_10` before `lemma_2_16`. |
| Nine-variable Pell/ratio core | `Jones1982.Nine.ratio_sound` and `ratio_complete` accept ordinary `R,N,b,g,G` and numerical inequalities; they do not assume quartic coding. |
| Final relation combiner | `RefinedPair.value_eq` proves the literal two-radicand polynomial formula. |

`NineReduce.mem_of_reduced`, `reduced_of_mem`, the `Master3` source-system
interface, and `NineMain.wset_iff_nine` are currently tied to the quartic
index, `5^i` positions, fourth powers, and old masks. Replacing their `L`
constant does not establish a direct quadratic reduction.

## Minimal remaining construction

1. Supply the finite integer coefficients of each quadratic gate residual
   as canonical pairs and prove `Q_j(u)` equals that residual when `u_0=1`.
   The existing syntax coefficient reader supplies data, but the degree-two
   padding/pair reindexing theorem is still required. Reuse the existing gate
   completeness and soundness theorems for the exact refutation predicate.

2. Generalize sparse-code decoding to the explicit weights. A single
   natural code `g=Σ_(i>0)u_i B^w_i`, a size bound, and one mask must be
   equivalent to all decoded coordinates satisfying `u_i<b`. The proof must
   constrain every unused base-`B` digit to zero.

3. Prove concrete uniform magnitude bounds. Distinct complementary row
   positions bound each coefficient of `E` by the largest corrected source
   coefficient, without a factor `r`. The convolution bound is then
   `|coeff P|≤M*(Σ_i|u_i|)²`. Choose an explicit power-of-two base that makes
   this strictly less than `B/2`, and prove completeness by arbitrarily large
   allowed bases. This is the undisclosed-bound step that the new arithmetic
   theorem deliberately leaves as a premise.

4. Normalize a row with positive constant coefficient and place it last.
   The gate guard is `guard-1`, so its negative has constant coefficient one
   and excludes the all-zero witness tuple. Prove positivity of `E(B)` from
   its positive leading term and the coefficient bound, and hence positivity
   of the required numerical coding quantities.

5. Pack the source-decoding mask and the simultaneous-zero mask, prove
   their complete size bounds, and define explicit polynomial `N,R,G` with
   the inequalities required by `ratio_sound` and `ratio_complete`. For the
   closed source the coefficient family is fixed, so `E(B)` can be substituted
   as a literal polynomial: no extra test is needed merely to transfer an
   *unknown* coefficient-code value between bases. This proposed simplification
   still needs its own soundness, completeness, and cofinal-base proofs.
   A candidate bookkeeping choice is `B=b^5`, `W=max_i w_i`,
   `G=32*b*B^W`, and `N=B^(W+n+2)`: use a source-decoding block of length
   `W+1` followed by a doubled shifted-row block of length `n+1`.
   `centralCode N packedS packedT` then supplies the candidate `R`.
   The outstanding lemmas must show `B≥4b`, the signed coefficient bound,
   both block bounds, and the weak soundness margin versus the stronger
   completeness margin. These formulas are a proposed adapter, not a
   checked closed-equation construction.

6. Substitute the new explicit `R,N,b,g,G` into the existing ratio formulas
   and finalizer. Prove the nine-coordinate equivalence, preserve its shifted
   natural domains, and only then compare the resulting closed expression
   against `ExplicitZFC.expression`. A smaller positional bound by itself
   does not prove a smaller total equation.

The source of this route is the retained
[`MULTI_OUTPUT_EXTRACTION_PROOF.md`](con-zfc-diophantine-forms/45-multioutput/weights/MULTI_OUTPUT_EXTRACTION_PROOF.md).
Its coefficient/no-carry reasoning is now checked generically as described
above; the complete source adapter, numerical bounds, and nine-variable
specialization remain open. The separate internal object-language ZFC
formalization also remains open.
