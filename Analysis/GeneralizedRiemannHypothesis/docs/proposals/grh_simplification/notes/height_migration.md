# A determinant and scalar-height interface for the theta-lift argument

## Recommendation, provenance, and scope

The most defensible substantial simplification I found is to stop propagating an exact formula for every exchange scalar through the chain and auxiliary-form constructions. Retain each actual complex scalar, because the exact scalar is needed for the exchange and integrality identities, but propagate only the height bound for its **normalized squared absolute value**. Take determinants during the triangle induction, rather than first exposing a global product of Rallis operators and subsequently taking its determinant.

This is a source-grounded refactor, not a claim of a new proof of GRH. The readable edition already has a well-designed abstract triangle induction. There is no justification for claiming that all its square laws, adjoint laws, or finite-group boundary counts can be removed.

There is also an important provenance qualification. The compact edition of `lsernau/grh-lean` already implements both a `CostsSquares` interface and an existential mixed-Gram endomorphism whose determinant is the product of the first-arrow determinants. Thus both the scalar-cost architecture and the removal of a named global operator product have a compact precedent. The following files were read from upstream at revision `72fead102f663d5c7a407964a13dc0cf9d977207`:

* `grh-compact/src/New/Exchange/CostOfSquares.lean`, Git blob `3842be43cd82966d3398d9929f72dd7667a62f4d`;
* `grh-compact/src/New/Exchange/TriangleNorms.lean`, Git blob `7fbffde1546ee8fb2cf919567908a89a7c80de07`;
* `grh-compact/src/New/Rows/RowVolume.lean`, Git blob `925de9c592b40763516e70ddeae48b4ad1a35b88`.

Thus the broad ideas of assigning costs to squares and tracking a determinant through an existential mixed-Gram witness must be credited to that source. The proposed contribution beyond it is a clean port to the readable variables, generalization to arbitrary real per-square budgets with the exact triangular count, guarded treatment of zeros, the explicit adaptation of both determinant and auxiliary-form consumers, and an exact reverse-power height theorem that preserves the current unsquared end theorem and its negative main term. This is outside the subject matter of the 18 existing proposal directories inspected; it is not independent evidence for the mathematical correctness of the full claimed GRH proof.

All readable-source references below are to `VladimirReshetnikov/ProveIt` revision `9050b04000647d588d0c78d945180abcd3b0bcf7`, under `Analysis/GeneralizedRiemannHypothesis/Lean/grh/src/`. Stable URLs are obtained by prefixing the paths with `https://github.com/VladimirReshetnikov/ProveIt/blob/9050b04000647d588d0c78d945180abcd3b0bcf7/Analysis/GeneralizedRiemannHypothesis/Lean/grh/src/`.

## 1. The certificate, including its quantifiers

Fix the readable `D : Data P`. Write `T = D.MFoldTwist`, `J = New.PrimePadicIso`, and use `1 : T` as the reference twist. For `c : T -> C` and a family `theta : J -> T`, define

\[
 R_c(\theta)(\iota)
   =\left|\frac{c(1)}{c(\theta(\iota))}\right|^2\in\mathbb R_{\ge0}\subset\mathbb C.
\]

A suitable replacement for the modulus certificate is

\[
 \operatorname{Budget}_D(c,B):\Longleftrightarrow
 \forall\theta,\quad D.\mathrm{HasSmallRatios}(\theta)\Longrightarrow
 c(1)\ne0\Longrightarrow
 \mathrm{HeightLe}\bigl(B,R_c(\theta)\bigr).
 \tag{1}
\]

In Lean-style notation, its intended definition is:

```lean
def ScalarBudget (D : Data P) (c : D.MFoldTwist -> C) (B : R) : Prop :=
  forall theta : PrimePadicIso -> D.MFoldTwist,
    D.HasSmallRatios theta -> c 1 != 0 ->
    HeightLe B (fun iota => (norm (c 1 / c (theta iota)) : C) ^ 2)
```

This is schematic notation, not the delivered checked Lean file. Using a base-point guard is deliberate: `HasAbsUpToNormPower` currently permits its leading constant to be zero. A proof must not cancel that constant without deriving nonvanishing. Within this certificate only, division has Lean's totalized meaning, so `a/0=0`; the exact end-use as a ratio of nonzero volumes separately supplies nonvanishing at every sampled twist. One could add those sample-nonvanishing hypotheses to (1), obtaining a weaker certificate, but they are not necessary for the multiplicative calculus or the local proofs below.

The scalar calculus is small. It follows from `HeightLe.mul`, `HeightLe.prod`, and the multiplicativity of the complex norm that

\[
 \operatorname{Budget}(c,B),\ \operatorname{Budget}(c',B')
 \quad\Longrightarrow\quad\operatorname{Budget}(cc',B+B').
 \tag{2}
\]

The base-point guard for the product implies the base-point guards for both factors, and the ratio multiplication identity holds also for totalized division. The same reasoning gives finite products. Nonzero constant rescaling, conjugation, and replacing `c` by `c/c(1)` do not change `R_c` when `c(1) != 0`. There is a zero-cost certificate for the constant function one. A monotonicity rule can be added if a numerical upper bound is useful.

**There is no general inverse rule.** In particular, one must not infer `Budget(c^(-1), B)` from `Budget(c, B)`. A bound for a family and a bound for its inverse have different arithmetic meanings. Where an inverse of a conductor factor is required, prove zero cost for it separately, using the same conductor-norm identity with the exponent reversed.

The definition is uniform in the twist family. The final family `theta` is chosen once, by `exists_hasSmallRatios_heightLe_liftDeterminant_div`, and is used simultaneously for every scalar, every single lift, and the chain. Choosing an independent family at each square would not suffice.

## 2. Local height extraction: exactly what replaces the modulus formula

Suppose a local square-law scalar has, as in the existing sources, an identity

\[
 |c(\vartheta)|^2
 = A\,\operatorname{lValueProd}\bigl(\mathfrak m(\vartheta),
           (\nu\vartheta^n)^{-1},z\bigr),\qquad 1\le n\le m,
 \tag{3}
\]

where `p = (nu,z)` is a ramified critical pair and `z <= t`. The existing critical-pair identity, before introducing the named `lRatioProd`, writes the right side as

\[
 A' N(\vartheta)^e
       \prod_{s=1}^{z} r_{p,s,n}(\vartheta)^2,
 \qquad
 r_{p,s,n}(\vartheta)
   =(p.\mathrm{lowerPoint}(s)).\mathrm{ratio}(\vartheta^n,1).
 \tag{4}
\]

Here `N(vartheta) = vartheta.normQ`, and all terms `r` equal one at the reference twist. Under the guard `c(1) != 0`, the leading constant is nonzero and cancels. The existing nonvanishing of the critical-pair ratios also implies `c(vartheta) != 0` for these local scalars. Therefore

\[
 R_c(\theta)(\iota)
   =N(\theta\iota)^{-e}
      \prod_{s=1}^{z}r_{p,s,n}(\theta\iota)^{-2}.
 \tag{5}
\]

By `HasSmallRatios.height_le`, each inverse ratio has height at most `x_1`. Each square has height at most `2 x_1`, so the product costs `2 z x_1 <= 2 t x_1`. By `HasSmallRatios.coprime`, the conductor norm is a unit at the prime of `iota`; `HeightLe.rpow_mul` gives its rational powers cost zero. This proves

\[
 \operatorname{Budget}_D(c,2t x_1).
 \tag{6}
\]

The same argument applies to the signs already allowed by `HasSmallRatios`; it does not require a general inverse rule for height. For a scalar satisfying `|c(vartheta)|^2 = A N(vartheta)^e`, both `c` and `c^(-1)` have guarded budget zero, each proved directly. Nonzero constant factors also have zero normalized cost.

Relevant source anchors: `Twist/FitTwists.lean:218` defines the universally quantified `HasSmallRatios`; `Chain/Moduli.lean:202` is the current conversion from (3) to a global exact modulus certificate; `Chain/Moduli.lean:227` performs the eventual height conversion. The simplification performs that conversion locally and avoids carrying the exact product function through every later theorem.

The actual complex `c(vartheta)` is retained. Its phase cannot be recovered from (1), and its phase is used in period-transfer and integrality assertions. The change removes only the stronger metadata attached to this scalar.

## 3. The reverse-power height theorem

The readable `New.HeightLe` is a common-multiplier height: a single nonzero complex number `H`, real archimedean exponent `alpha`, and nonnegative finite exponents `h_l` work for every embedding and every member of the family. This matters when taking roots.

For every positive integer `n`,

\[
 \mathrm{HeightLe}(C,y^n)
 \quad\Longrightarrow\quad
 \mathrm{HeightLe}(C/n,y).
 \tag{7}
\]

Proof: take a witness `(H,alpha,h_l)` for the left side. Choose **one** complex `n`th root `K` of `H`. Since `H != 0`, `K != 0`. Use multiplier `K`, archimedean exponent `alpha/n`, and local exponents `h_l/n`. For every complex automorphism `sigma`,

\[
 |\sigma K|^n=|\sigma H|\le e^{\alpha},
\]

and for every `iota : C ~= Qbar_l`,

\[
 |\iota(Ky_\iota)|_l^n
   =|\iota(Hy_\iota^n)|_l\le l^{h_l}.
\]

Monotonicity of the positive `n`th power gives exactly the divided exponents. The common multiplier remains independent of `iota`, and the budget inequality divides by `n`. The argument works for negative `C` and does not require `y_iota != 0`. The case `n=0` is excluded.

Consequently a budget `B` for the squared scalar ratio gives the **unsquared** ratio height `B/2`. This avoids doubling the final theorem or weakening its negative main term. A standalone faithful generalization of this theorem was checked against Lean 4.35.0; that file is separate from the determinant-core file described below.

## 4. Determinants along the triangle

### 4.1 The ambient mixed Gram identity must be preserved

Let `V` be the ambient space of principal forms on `Y_0`, `U` the finite-dimensional target subspace, and `s : U -> V` its inclusion. Let `j_i` be the isometries used to identify the bottom of each row, and let `X_(i,n)` denote the existing weighted chain. Put

\[
 q_n(\vartheta)=\frac{w_0(\vartheta)w_1(\vartheta)^n}{w_n(\vartheta)}.
\]

The induction invariant is an endomorphism `K_(i,n)` of `U` such that

\[
 \langle X_{i,n}j_i x,\ X_{i,n}j_i(sy)\rangle
      =q_n\langle x,s(K_{i,n}y)\rangle
 \quad(x\in V,\ y\in U).
 \tag{8}
\]

It is not enough to define a Gram matrix only on `U` and forget the ambient quantifier. In the induction, the vector obtained by applying `d a` initially lies in `V`; the first-arrow formula is quantified over all of `V` precisely so that it can be paired against the next target endomorphism. Maintaining (8) gives the required invariance without assuming that the next vector lies in `U` in advance.

The zero chain has `K_(i,0) = I`. Let `beta_(i,n)` and `kappa_(i,n)` be the chain-commutation and chain-adjoint constants. The existing lemma `IsTriangle.inner_weightedChain_succ` gives the longer-chain Gram form in terms of the next-row one. The first-arrow relation is

\[
 w_0\langle a_i j_i x,a_i j_i(sy)\rangle
      =C_i\langle x,s(S_i y)\rangle.
 \tag{9}
\]

Using (8) in `inner_weightedChain_succ`, and then (9), gives

\[
 K_{i,n+1}=a_{i,n}S_iK_{i+1,n},\qquad
 a_{i,n}=\kappa_{i,n}\beta_{i,n}C_i.
 \tag{10}
\]

The ratio of the weights in `inner_weightedChain_succ` cancels to `q_(n+1)`. This is exactly the algebra in the current `TriangleNorms.lean:311` proof, with an existential endomorphism witness in place of the explicit `List.range'` product. The first-arrow relation includes `S_i = matrixCard^(-1) * Rallis_i` in the application.

### 4.2 Determinant-budget theorem

Let `d = dim U`. The source's `LinearMap.det` can be used directly; equivalently, choose any basis and apply the matrix theorem delivered below, since the determinant is independent of that choice. Taking determinants at each step of (10) gives

\[
 \det K_{i,n+1}
    =a_{i,n}^{d}\det S_i\det K_{i+1,n}.
 \tag{11}
\]

Define `c_(i,0)=1` and `c_(i,n+1)=a_(i,n)c_(i+1,n)`. Then induction yields

\[
 \det K_{i,n}=c_{i,n}^{d}\prod_{k=i}^{i+n-1}\det S_k.
 \tag{12}
\]

No pairwise commutativity of the operators `S_i` is needed. Their ordered composition is used only in the one-step relation; the determinant proof needs multiplicativity. There is no need for a public `rallisProduct` definition or for a theorem exposing the entire chain adjoint as a scalar times that product.

Allow a different local squared-ratio budget `E_(r,k)` for every square, `1 <= r < k <= m`. The chain-commutation/adjoint pair for row `i` crossing `n` squares has cost

\[
 e_{i,n}=\sum_{k=i+2}^{i+n+1} E_{i+1,k}.
\]

The constants `C_i` have normalized cost zero. The recursive accumulated budget is

\[
 B_{i,0}=0,\qquad B_{i,n+1}=e_{i,n}+B_{i+1,n},
\]

so, at the full triangle,

\[
 \operatorname{Budget}(c_{0,m},B_{0,m}),\qquad
 B_{0,m}=\sum_{1\le r<k\le m}E_{r,k}.
 \tag{13}
\]

Each square occurs exactly once: the outer recursion selects its first index `r`, and the row-commutation recursion selects its second index `k`. For uniform `E`, this becomes

\[
 B_{0,m}=\binom m2 E,
 \qquad 2\binom m2+m=m^2.
 \tag{14}
\]

The zero-dimensional case is immediate: every determinant is one, and no division by a scalar is needed; choose the auxiliary determinant scalar to be one. For positive dimension, the injectivity lemmas retained from the existing triangle prove positivity of chain Gram determinants. Together with the first-arrow determinants, (12) forces the accumulated scalar to be nonzero at each twist. The base-point guard in (1) may then be discharged, and the determinant ratios have nonzero denominators. Nonvanishing of any individual factor needed for a guard follows from nonvanishing of its product. The existing proof that the commutation scalars are nonzero is also retained wherever their inverses occur in the exact square identities.

### 4.3 What has actually been checked

`../lean/MatrixChainBudget.lean` is a new 154-line standalone file. It proves (12), the arbitrary additive scalar-cost propagation, the equality of accumulated row costs with the double sum over every pair `i < r < k <= i+n`, and the exact integer identity in (14). The squared-ratio multiplication identity, guarded certificate multiplication rule (2), and guarded accumulation along the chain are included. It compiles against Lean 4.35.0 and the pinned Mathlib environment with exit status zero. The printed axioms of the six main theorems are only `propext`, `Classical.choice`, and `Quot.sound`.

This file takes the matrix recurrence (10) as a hypothesis. It does **not** formalize the theta-lift adapter, replace the readable modules, or establish GRH. In particular, the mixed-Gram adapter just explained is a remaining integration obligation. The file's abstract `H` is meant to be instantiated by the existing `HeightLe`; a checked abstract multiplicative calculus is not a claim that the whole scalar-budget integration has been checked.

## 5. Exact normalization at the boundary

The raw weight factors are not pure conductor powers. Finite general-linear-group orders contain factors `1-q^(-j)`. Replacing all of them by height-zero errors would be wrong. The following exact cancellation must be retained.

Write

\[
 I(\vartheta)=[K_0:J(\vartheta)],\quad
 M(\vartheta)=\#\{Y_1\times\mathrm{RowIndex}\to
                    (\mathfrak m(\vartheta,1)).\mathrm{ResidueRing}\},
\]

and let `Wdim` be the fixed Weyl-index dimension. The two existing identities are

\[
 I(\vartheta)
   =\gamma N(\vartheta)^\ell
      \operatorname{gramFactor}(\vartheta)^m
      \frac{w_m}{w_0w_1^m},
 \tag{15}
\]

\[
 \frac{\operatorname{gramFactor}(\vartheta)}{M(\vartheta)}
     =g_0\,u(\vartheta),
 \qquad u(\vartheta)=\operatorname{twistFactor}(\vartheta).
 \tag{16}
\]

Here `gamma`, `ell`, and `g_0` are independent of `vartheta`; `g_0` is the chosen-place factor. Source anchors are `Chain/ChainNorms.lean:805` (`exists_stdLevelIndex_lastLevel_eq`) and `Norms/AdjointThetaLift.lean:665` (`DescentPair.gramFactor_div_card`). The conversion from weighted-chain Gram form to the actual chain has the exact factor `I * Wdim`, at `Chain/ChainNorms.lean:856`.

The determinant recurrence therefore gives

\[
 Z(\vartheta)
 =\left[
   c_{0,m}(\vartheta)
   \frac{I(\vartheta)\,Wdim\,w_0w_1^m}
        {w_m M(\vartheta)^m}
   \right]^d
   \prod_{j=1}^{m}\det R_j(\vartheta).
 \tag{17}
\]

By the retained single-lift determinant statement,

\[
 Z_j(\vartheta)
    =(A_j u(\vartheta))^d\det R_j(\vartheta),\qquad A_j\ne0.
 \tag{18}
\]

This is `Chain/NormOfChain.lean:122`, which uses the existing equality of good-form multiplicities and equality of the relevant Rallis determinants. Powers of an `MFoldTwist` have the same modulus, so the `u` in all `m` equations is the same. The common exponent is exactly `d = D.targetDim`. Neither this equality of dimensions nor the determinant transfer is replaced by an approximation.

Substituting (15), (16), and (18) into (17) cancels `u(vartheta)^m` **exactly**. The remaining boundary factor is

\[
 F(\vartheta)
  =\frac{\gamma\,Wdim\,g_0^m}{\prod_{j=1}^{m}A_j}
      N(\vartheta)^\ell.
 \tag{19}
\]

Only at this point is it valid to give the boundary factor budget zero. Put `c = c_(0,m) F`. Then

\[
 Z(\vartheta)=c(\vartheta)^d\prod_{j=1}^{m}Z_j(\vartheta).
 \tag{20}
\]

The determinants are positive real numbers, so taking complex norms gives the equally exact identity

\[
 Z(\vartheta)=|c(\vartheta)|^d\prod_{j=1}^{m}Z_j(\vartheta).
 \tag{21}
\]

This norm operation is used solely for the determinant ratio. It does not replace the complex scalar in period transfers or integral forms.

## 6. The existing long-forms bound is unchanged

Uniform square cost `E = 2 t x_1` gives, by (13), budget `2 binom(m,2) t x_1` for `c`. Applying (7) with `n=2` yields

\[
 \mathrm{HeightLe}\left(\binom m2t x_1,
        \iota\mapsto\frac{|c(1)|}{|c(\theta\iota)|}\right).
 \tag{22}
\]

Suppose the **same** family `theta` satisfies the existing single-lift bounds

\[
 \mathrm{HeightLe}\left(
 d\left(\frac{fa\log^4 b}{m}-k\,\mathrm{directionAmount}\right),
 \iota\mapsto\frac{Z_j(1)}{Z_j(\theta\iota)}\right)
 \quad(1\le j\le m).
 \tag{23}
\]

Dividing (21) at the reference twist and at `theta(iota)`, then applying product and power rules, gives

\[
 \mathrm{HeightLe}\left(
 d\left[\binom m2t x_1+fa\log^4 b-mk\,\mathrm{directionAmount}\right],
 \iota\mapsto\frac{Z(1)}{Z(\theta\iota)}\right).
 \tag{24}
\]

Because `binom(m,2) t x_1 <= m^2 t x_1 <= b`, this implies exactly

\[
 \mathrm{HeightLe}\left(
 d\left[b+fa\log^4b-\mathrm{mainAmount}\right],
 \iota\mapsto\frac{Z(1)}{Z(\theta\iota)}\right),
 \quad\mathrm{mainAmount}=mk\,\mathrm{directionAmount}.
 \tag{25}
\]

This is the existing statement `Twist/LongForms.lean:181`, `heightLe_chainDeterminant_one_div`. Its `-mainAmount` coefficient is unchanged. There is no additional `O(mfa)` term and no weakened coefficient hidden in the phrase “absorb the boundary cost.” The negative term survives because the boundary cancellation, the equality of determinant ranks, the common twist, and the reverse-power theorem are all exact.

## 7. All seven consumers, including the auxiliary denominators

The literal `HasAbsUpToNormPower`, `lRatioProd`, `quotientRatio`, or `turnRatio` definitions and uses occur in seven readable modules. A migration must cover the auxiliary branch as well as the determinant branch.

| Module | Required change | Retained substance |
|---|---|---|
| `Chain/Moduli.lean` | Replace global exact modulus metadata, named products of ratios, and eventual global height conversion by (1), its product calculus, and local extraction (3)-(6). | Critical-pair characters, ramification, tameness, residue-ring cardinality, and whatever local L-value identity proves (5). |
| `Chain/ChainNorms.lean` | Local square-law theorems return the same complex scalars with numerical budgets; adjoint and reversal scalars return separately proved zero budgets. `exists_isTriangle` supplies a budgeted-square structure. | Every exact square and adjoint relation; injectivity; group-index counts (15); the actual-chain inner product relation. |
| `Chain/NormOfChain.lean` | Replace public global operator product, exact aggregate quotient-ratio formulas, and ratio-height wrapper by the determinant-budget adapter and direct (25). | Definitions of `Theta`, `chainDeterminant`, `liftDeterminant`; their positivity; (18); final three good-eigenspace/range lemmas. |
| `AuxiliaryForms/Turns.lean` | `exists_squareLaw_grid_hasAbsUpToNormPower` returns `Budget(c, 2 t x_1)` with exactly the same `c : T -> C^*`; remove `turnRatio` and its two ramified-ratio wrappers. Off-diagonal period transfer carries this certificate. | `squarePair`, `isRamified_squarePair`, the exact `SquareLaw`, `TransfersPeriods`, tuple matching, Fourier and integrality arguments. |
| `AuxiliaryForms/DiagonalTurns.lean` | For scalar `c/c_line`, add the cost of `c` and a directly proved zero cost of `c_line^(-1)`. Sum all `m^2` turn costs in `exists_transfersPeriods_first_last`. | The line-kernel identity and nonvanishing of both unit-valued scalars; all exact period identities and their denominator cancellation. |
| `AuxiliaryForms/SpanningForms.lean` | Four certificates pass through the existing existence/spanning results; replace each exact product certificate by `Budget(c, 2 m^2 t x_1)`. | The actual `c : T -> C^*`, linear algebra, spanning, finite sums, integrality, and shortness of the lifted forms. |
| `Twist/LongForms.lean` | Normalize `gamma(vartheta)=c(vartheta)/c(1)` and return its scalar budget directly. Delete the two exact-product height/factorization wrappers. Feed (25) directly to `integral_forms_long`. | The same `IsAuxiliaryForm`, the same chosen regular twist family, basis completion, product-formula argument, and final theorem. |

`Chain/TriangleNorms.lean` is an eighth **adapter** module: it is generic in a relation `M`, so the named concrete modulus symbols do not occur there. Replace `HasSquareModuli` and the accumulating modulus proof by budgets, while preserving the triangle, injectivity and mixed-Gram machinery. Its current `exists_chainCommutes`, `ne_zero_of_chainCommutes`, `ne_zero_of_squareCommutes`, and `inner_weightedChain_succ` remain useful.

For the auxiliary denominator in particular, the source at `DiagonalTurns.lean:592` constructs `c/c_line`. The present `h_inv` is a modulus certificate for `c_line^(-1)`; it is not a height inverse rule. The port must replace it with the explicit conductor-power proof from Section 2, not delete the denominator. All these scalars are units, so nonvanishing is already part of their type.

At the end of the auxiliary branch, with `gamma = c/c(1)` and `gamma(1)=1`,

\[
 \operatorname{Budget}(c,2m^2t x_1)
 \quad\Longrightarrow\quad
 \mathrm{HeightLe}(2m^2t x_1,
    \iota\mapsto |\gamma(\theta\iota)|^{-2}).
 \tag{26}
\]

The exact existing inequality `2 m^2 t x_1 <= b` supplies `h_scalar : HeightLe b ...` at `LongForms.lean:230`. There is no need for an existential integer `e`, a formula for `norm gamma`, or a named `prod turnRatio`. The gamma-weighted lifts and their integrality are unchanged. Together with (25), the final proof still concludes

\[
 c+2\delta\ \ge\ d\bigl(\mathrm{mainAmount}-3fa\log^4b\bigr).
\]

## 8. Conservative accounting and named cut

Raw line counts at the pinned readable revision are: `Moduli` 430; `NormOfChain` 528; `ChainNorms` 892; `Turns` 1,002; `DiagonalTurns` 672; `SpanningForms` 796; `LongForms` 250; `TriangleNorms` 364. The seven concrete consumers total **4,570** lines; adding the generic adapter gives **4,934**. These figures are the **affected footprint**, not the number of deletable lines. Most of the 4,934 lines, especially exact square laws, Fourier calculations, spanning and integrality, must remain.

The strongest obvious retirement candidate in `NormOfChain` is the contiguous block beginning with `rallisProduct` (line 142) and ending with `HasSmallRatios.heightLe_inv_rpow_mul_prod_quotientRatio` (line 436, proof ending 446, following blank line 447). It contains 13 declarations, including the weighted and actual chain Gram adapters. These 13 names can be replaced by fewer determinant-budget adapters, but their mathematical boundary and single-lift content must be ported. They are:

1. `rallisProduct`;
2. `exists_inner_weightedChain_eq`;
3. `exists_inner_chain_eq`;
4. `isRamifiedRatio_of_mem_sigma`;
5. `card_sigma_Ioc_le`;
6. `prod_quotientRatio_one`;
7. `prod_quotientRatio_nonneg`;
8. `HasAbsUpToNormPower.exists_norm_div_eq_mul_prod_quotientRatio`;
9. `exists_adjoint_chain_comp_eq_smul_rallisProduct`;
10. `exists_chainDeterminant_eq_pow_mul_prod_liftDeterminant`;
11. `exists_div_chainDeterminant_one_eq`;
12. `exists_chainDeterminant_pos_and_div_chainDeterminant_one_eq`;
13. `HasSmallRatios.heightLe_inv_rpow_mul_prod_quotientRatio`.

In `Moduli`, retire the `HasAbsUpToNormPower` definition and its `.mul`, `.of_norm_sq_eq_mul_card_zpow`, `.one`, `.const`, `.inv`, `.prod`, `.exists_norm_div_eq` API; `IsRamifiedRatio` and its `.nonneg`, `.apply_one`; the `lRatioProd` definition and its exact aggregate-product wrappers; and the `quotientRatio` definition and wrappers. The critical-pair-to-height conversion replaces `hasAbsUpToNormPower_of_norm_sq_eq_lValueProd`. Statements `lValueProd_mul_inv_eq`, `lValueProd_mul_zpow_eq`, and `isTameFor_mul_and_lValueProd_eq` must either disappear in favor of the already earlier critical-pair identity or be restated locally with products of basic ratios. Their tameness consequences remain. Retain `quotientPair`, `quotientPair_character`, `isRamified_quotientPair`, `card_residueRing_twistModulus`, `isPrimitiveMulChar_of_isTameFor`, `isTameFor_mul`, and `isTameFor_mul_inv`; rewrite the last `isTameFor_inv_mul_pow` directly from `isTameFor_mul_inv`.

In `Turns`, only `turnRatio` and its two `isRamifiedRatio` wrappers are pure retirement candidates; the square-law theorem changes its certificate, not its exact scalar or identity. In `LongForms`, retire `HasSmallRatios.heightLe_inv_rpow_mul_prod_turnRatio` and `exists_chainDeterminant_one_div_eq`; replace the auxiliary-span output contract and the proof of `heightLe_chainDeterminant_one_div`. In `ChainNorms`, replace `HasAbsUpToNormPower.of_norm_sq_mul_card_pow_eq_one` by a zero-budget local lemma. In `SpanningForms`, the four relevant declarations are adapters, not deletion candidates.

An independent conservative audit isolates **27 declarations that serve only the old representation**, totaling **136 physical declaration/body lines** (134 nonblank, noncomment lines), or **198 lines including attached documentation**. The counts are: `Moduli` 18 declarations / 87 body lines / 120 documented lines; `NormOfChain` 5 / 33 / 52; `Turns` 3 / 8 / 13; `LongForms` 1 / 8 / 13. The exact names and ranges are in `work/lean_structure/metadata_only_audit.tsv`, with a reproduction script next to it. This narrow count deliberately excludes local L-value and conductor conversions, mixed-Gram and determinant adapters, generic counting, and exact boundary arithmetic.

The concrete structural gain is a smaller public interface: one scalar and one numerical budget replace a scalar, a separate product-valued function, an exponent witness, and their repeated exact-conversion wrappers. Larger gross replacement regions exist, including the 306-line `NormOfChain` block above, but the new adapters must be subtracted. **No net line saving is measured yet**, because no integrated readable-source patch has been compiled. The 154-line checked algebra file must not be compared with the entire 4,934-line affected footprint as though it replaced that footprint. A claim of several hundred net lines saved would require implementing and measuring the complete port; the present evidence does not establish that number.

## 9. Integration checklist and limitations

1. Add the exact reverse-power height theorem to readable `Heights.lean`; verify against the unchanged definition.
2. Implement (1) and local extraction (3)-(6) using the earlier critical-pair ratio identity. Ensure the guarded zero case is handled explicitly.
3. Replace `HasSquareModuli` with numerical local costs. Keep the actual scalars, exact square laws, adjoint laws, and commutation-scalar nonvanishing proof.
4. Prove the mixed-Gram adapter (8)-(10) and instantiate the checked determinant lemma, including the empty target case.
5. Port the exact boundary identities (15)-(19) unchanged; do not charge the uncancelled Euler factors zero cost.
6. Port all auxiliary scalar certificates, particularly `c_line^(-1)`, and keep the integral gamma-weighted forms unchanged.
7. Compile the unchanged end statements `heightLe_chainDeterminant_one_div` and `integral_forms_long` against the replacements. Only after that, remove unused public names and measure the net line/declaration reduction.

This proposal does not bypass the automorphic input, equal Hecke multiplicities, arithmetic deformation construction, or the final analytic reduction. It narrows an internal interface to what its consumers use. Its usefulness is local and testable: one can integrate it without changing the statements of the key final height theorems.

