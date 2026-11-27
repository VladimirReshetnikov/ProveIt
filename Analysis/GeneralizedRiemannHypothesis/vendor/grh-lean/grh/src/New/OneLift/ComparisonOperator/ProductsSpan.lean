import Lib.DiscreteSeries.Bruhat.ComplexPlace
import New.OneLift.ComparisonOperator.ThetaKernelEstimates
import New.OneLift.ComparisonOperator.ThreeExchanges

/-!
# Products span

For admissible data D (`New.Data`) and 1 ≤ j ≤ m, let 𝖥_i = `New.Data.choiceFn j i` be the functions
on the unitary group of W_j = `New.Data.spaceW j`, one for each choice i, and let θ° be the theta
kernel of (W_j, V°). A good form (`New.Data.goodForms`) is a form of principal level at the chosen
places in the image of the idempotent `New.Data.e₀`. We show that a good form y on W_j with
∫ y(g) 𝖥_i(g) θ°(g, ·) dg = 0 for all i is zero.

We write λ₁(g) for the first minimum `New.Space.firstMinimum` of the lattice at g, cut off at 1, |h|
for the largest operator norm `New.Rows.maxOpNorm` of a real point h, and m_u for the basic
holomorphic function `New.holMinorsPi` of a weight u, a quotient of products of minors. A peak
(`New.Rows.IsPeak`) of a bounded function is a point where its modulus exceeds half of the supremum.
Suppose y ≠ 0. The peaks of y are not deep in a cusp, and the proof has four steps.

1. The integral 𝖥^g of the carrier times a kernel on (S, W̃) times m_u₁ over the real group of S is
   a combination of the 𝖥_i (`New.Data.exists_sum_choiceFn_eq_integral`).
2. For every combination 𝖥 of the 𝖥_i, the integral of y 𝖥 m_u° over the real group at any point is
   zero (`New.Data.integral_mul_sum_choiceFn_eq_zero`).
3. At every peak g, 𝖥^g(g h) is close to 𝖥⁰(h), for one bounded function 𝖥⁰ with 𝖥⁰(1) ≠ 0
   (`New.Data.exists_choiceFn_approx`).
4. The mean over a circle of peaks makes 𝖥⁰(1) too small
   (`New.Data.norm_apply_one_le_of_forall_isPeak`).

Steps 1 and 3 do not involve y and come first in this file.

## Main definitions and results

* `New.Data.exists_datum_norm_modKernel_sub_polyMatrixCoeff_le` (sparse sums): for V, V' of ranks at
  most t and Q homogeneous of degree at most b^(3/2), if λ₁(g) λ₁(g') ≥ b^(−13), then for some datum
  Ψ the theta kernel `New.modKernel` at (g h, g' h') is close to the coefficient c_Q(h, h').
* `New.Data.exists_isPeak_carrierForm`: the carrier `New.Rows.carrierForm` has a peak g₁, and
  λ₁(g₁) ≥ (5 b √b)^(−1/2).
* `New.Data.exists_choiceFn_approx`: there is a bounded F₀ with F₀(1) ≠ 0 such that, when λ₁(g) ≥ (5
  b²⁴)^(−1/2), some combination F of the 𝖥_i satisfies |F(g h) − F₀(h)| ≤ 2 b^(−19 n_*) |F₀(1)|
  |h|^(6 n_*).
* `New.Data.thetaKernelPairing`: the pairing of a form on V°, given by its values at the classes,
  with the kernel θ°.
* `New.Data.eq_zero_of_integral_choiceFn_thetaKernelPairing`: products span.

Notions from other files:
* `New.Data.b`: The large scale b of the data, the weight at the b-places, as a real number.
* `New.Data.nStar`: The number n_* = 2ft³, where f is the number of infinite places of E and t = 5r.
* `New.Data.SecondFactorIndex`: The index set of V°: the r indices of W_j and t − 9m − 1 − r further
  ones.
* `New.Data.CarrierIndex`: The index set of the space S of signature (2m, m).
* `New.Data.conjHolomorphicWeight`, `New.Data.kernelWeight`: The weights u of the conjugate of y and
  u° of θ° on W_j. The 𝖥_i have the weight u − u°.

## Relation to the literature

For a finite family of choices with small integral data, a good form on U(W_j) orthogonal to all
products of the twist-free theta forms with theta kernels of the complementary block is zero. This
makes the map Θ° on good forms injective. It is a basis problem, the spanning of a space of forms by
theta series (Eichler, The basis problem for modular forms and the traces of the Hecke operators,
1973; Waldspurger, Engendrement par des séries thêta de certains espaces de formes modulaires,
1978/79; Böcherer, Siegel modular forms and theta series, 1989). It is known that stable-range theta
kernels reach all forms, that maxima of forms avoid the cusps, and that products span for GL(2).
Related work: J.-S. Li, Non-vanishing theorems for the cohomology of certain arithmetic quotients,
1992; Poor–Yuen, Linear dependence among Siegel modular forms, 2000; Khuri-Makdisi, Moduli
interpretation of Eisenstein series, 2012.
-/

namespace New.Data

/-!
## Approximation by combinations of the 𝖥_i away from the cusps

Here S is the space of signature (2m, m), W̃ = W_j ⊕ (E^j)⁻ ⊕ E^(3m−j) is `New.Data.paddedSpace`,
W♭ = E^(6m+1), and P = `New.Data.paddedMinorProd j` is the fixed polynomial on (S, W̃).
-/

section NaturalFormNear

open NumberField Matrix MvPolynomial Finset Norms.L2Operator Rows Fock WeilData Fintype Prod Sum

variable {P : Parameters} {D : Data P} (j : D.LiftIndex)

/-- Let `1 ≤ j ≤ m`, let `W_j` be the diagonal hermitian space of rank `r` with signs `D.signsW j`,
and pad it with `j` signs `-1` and `3 m - j` signs `1` to the space `W̃` with signs `padSigns j`.
The polynomial `paddedMinorProd j` is a product of minors whose rows are indices of `W̃`: one minor
has the `m` rows `negIndex j a`, and for each column height `h` one has the `2 m` rows
`posRowIndex j h a`, which start at the basis vector of number `h` of `W_j`. Each of these families
of rows is injective; the rows `negIndex j a` have sign `-1` and the rows `posRowIndex j h a` have
sign `1`. -/
theorem negIndex_posRowIndex_injective_and_padSigns :
    ((negIndex j).Injective ∧ ∀ h : ℕ, (posRowIndex j h).Injective) ∧
    (∀ a : Fin D.m, padSigns j (negIndex j a) = -1) ∧
    ∀ (h : ℕ) (a : Fin (2 * D.m)), padSigns j (posRowIndex j h a) = 1 := by
  -- Each value of these maps is either the index `D.rowIndexOfNumber i` of number `i` in `W_j` or
  -- a padding index, so the claims become inequalities between natural numbers.
  unfold Function.Injective negIndex posRowIndex
  refine ⟨⟨fun a b ↦ ?_, fun h a b ↦ ?_⟩, fun a ↦ ?_, fun h a ↦ ?_⟩
  all_goals split_ifs
  all_goals simp [signsW, rowIndexOfNumber] <;> grind

/-- Sparse sums. The data `D` give the CM field `E` with its `f` infinite places `D.Φ`, a large real
scale `b = D.b`, the numbers `t = D.t` and `n_* = nStar D = 2 f t ^ 3`, and the modulus
`untwistedModulus 2 = ϖ²`. Let `V`, `V'` be hermitian spaces of ranks at most `t`, let the
characters `χ`, `χ'` of `U(1)` have weights `γ`, `e` at the infinite places and residue characters
`ψ`, `ψ'`, and let the polynomial `Q` be homogeneous of degree `d ≤ b ^ (3 / 2)`. Write `λ₁(g)` for
the first minimum, cut off at `1`, of the lattice of `V` moved by the adelic point `g`, `|h|` for
the operator norm `maxOpNorm h`, and `c_Q = polyMatrixCoeff s s' γ e Q` for the matrix coefficient
of the real Weil representation at the Fock vector of `Q`. If `λ₁(g) λ₁(g') ≥ b ^ (-13)`, then for
some function `Ψ` on matrices modulo `ϖ²` the theta kernel `modKernel` with data `Ψ`, `Q` at
`(g h, g' h')` differs from `c_Q(h, h')` by at most
`b ^ (-20 n_*) (|h| |h'|) ^ (6 n_*) |c_Q(1, 1)|`, for all real points `h`, `h'`. -/
theorem exists_datum_norm_modKernel_sub_polyMatrixCoeff_le {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] [Nonempty n] [Nonempty n'] {s : n → ℤˣ} {s' : n' → ℤˣ}
    (V : Space D.E n s) (V' : Space D.E n' s') (h_rank : card n ≤ D.t) (h_rank' : card n' ≤ D.t)
    {χ χ' : AutChar D.E} {γ e : D.Φ → ℤ} {ψ ψ' : (w : FinPlace D.E) → MulChar (ResField w) ℂ}
    (hχ : χ.HasWeight γ ψ) (hχ' : χ'.HasWeight e ψ') {Q : MvPolynomial (D.Φ × n' × n) ℂ} {d : ℕ}
    (hQ : ∀ (r : ℝ) (y : D.Φ × n' × n → ℂ), Q.eval (r • y) = r ^ d * Q.eval y)
    (hd : d ≤ D.b * √D.b) {g : New.G D.E s} {g' : New.G D.E s'}
    (h_min : (D.b ^ 13)⁻¹ ≤ (V.move g).firstMinimum * (V'.move g').firstMinimum) :
    ∃ Ψ : Matrix n' n (D.untwistedModulus 2).ResidueRing → ℂ, ∀ (h : GInf D.E s) (h' : GInf D.E s'),
      ‖modKernel V V' χ χ' (D.untwistedModulus 2) Ψ Q (g * (h, 1)) (g' * (h', 1)) -
          polyMatrixCoeff s s' γ e Q h h'‖ ≤
        (D.b ^ (20 * nStar D))⁻¹ * (maxOpNorm h * maxOpNorm h') ^ (6 * nStar D) *
          ‖polyMatrixCoeff s s' γ e Q 1 1‖ := by
  -- The scale `c = q₁ / piM ^ 2` clears the denominators of `α` times the ideal of the modulus.
  let c : D.E := D.q₁ / algebraMap (𝓞 D.E) D.E (D.piM ^ 2)
  have piM_sq_ne_zero : algebraMap (𝓞 D.E) D.E (D.piM ^ 2) ≠ 0 := by simp
  have h_int : ∀ z : Ô D.E, (D.untwistedModulus 2).reduction z = 0 →
      algebraMap D.E (𝔸f D.E) c * (α.val * z.val) ∈ Ô D.E := by
    intro z hz
    rw [Modulus.reduction_eq_zero_iff, ideal_untwistedModulus_eq_span, Ideal.map_span,
      Set.image_singleton, Ideal.mem_span_singleton] at hz
    obtain ⟨y, rfl⟩ := hz
    have h_cancel : algebraMap D.E (𝔸f D.E) c *
        (algebraMap (𝓞 D.E) (Ô D.E) (D.piM ^ 2) : Ô D.E) = D.q₁ := by
      change _ * algebraMap D.E (𝔸f D.E) (algebraMap (𝓞 D.E) D.E (D.piM ^ 2)) = _
      rw [← map_mul, div_mul_cancel₀ _ piM_sq_ne_zero, map_natCast]
    rw [MulMemClass.coe_mul, mul_left_comm α.val, ← mul_assoc, h_cancel, ← mul_assoc]
    exact mul_mem P.q₁_mul_alpha_mem y.prop
  -- The points of the sparse lattice are `b ^ 6`-separated: the first minimum of the lattice of
  -- homomorphisms is at least `λ₁(g) λ₁(g')` over a constant, and `|Φ w c| = q₁ / M` is small.
  have h_sep (w : D.Φ) : D.b ^ 6 * ‖Φ w c‖ ≤
      √(2 * .pi * (Φ w WeilData.j).im) * ((V.move g).hom (V'.move g')).firstMinimum := by
    have h_norm : ‖Φ w c‖ = (D.q₁ : ℝ) / D.M := by
      simpa [c, sq, -Nat.cast_mul] using
        congrArg (fun x : 𝓞 D.E ↦ (D.q₁ : ℝ) / ‖Φ w (x : D.E)‖) D.piM_mul_star
    have h_cond : D.cyclotomicConductor ≠ 0 := NeZero.ne _
    have ht_pos : 0 < D.t := D.t_odd.pos
    have h_hom : (D.b ^ 13)⁻¹ / (6 * D.cyclotomicConductor * (D.f * D.t : ℝ) ^ 2 * D.t * D.t) ≤
        ((V.move g).hom (V'.move g')).firstMinimum := by
      grw [← firstMinimum_mul_le_hom _ P.conductor_mem_differentIdeal, Space.shortBasisConst,
        ← h_min, h_rank, h_rank', h_rank]
      simp [Data.f]
    grw [← h_hom, h_norm, P.phi_weilData_j]
    simpa using D.le_of_hasLogBound
  have h_dim : card (D.Φ × n' × n) < 2 * nStar D := by
    grw [card_prod, card_prod, h_rank, h_rank']
    exact D.nat_lt_of_hasLogBound
  -- The bound for the other terms of the lattice sum, to be raised to the power `2 n_*`.
  have h_ratio : 100 * (d + 2 * (2 * nStar D : ℕ)) / (D.b ^ 6) ^ 2 ≤ (D.b ^ 10)⁻¹ := by
    grw [hd]
    exact D.le_of_hasLogBound
  obtain ⟨Ψ, hΨ⟩ := exists_norm_modKernel_sub_fockInner_le (g := g) V' hχ hχ'
    (div_ne_zero (NeZero.ne (D.q₁ : D.E)) piM_sq_ne_zero) h_int g' (D.b ^ 6) (2 * nStar D)
    (by positivity) h_sep h_dim Q rfl d hQ
  refine ⟨Ψ, fun h h' ↦ (hΨ h h').trans ?_⟩
  grw [h_ratio]
  simp only [polyMatrixCoeff, Prod.mk_one_one, map_one, one_apply_eq_self]
  exact le_of_eq (by ring)

/-- Give a variable of `paddedMinorProd j` the sign `padSigns j` of its row times the sign `1 ⊕ᵥ -1`
of its column in `D.CarrierIndex`. Each of its variables has row and column of the same sign, so
`paddedMinorProd j` is a polynomial in the variables of sign `1`. -/
lemma paddedMinorProd_mem_supported :
    paddedMinorProd j ∈ supported ℂ
      {p | realSigns D.E (homSigns (n := D.CarrierIndex) (1 ⊕ᵥ -1) (padSigns j)) p = 1} := by
  simp (maxDischargeDepth := 9) [paddedMinorProd, variableMinor, det_apply', prod_mem, mul_mem,
    pow_mem,
    sum_mem, negIndex_posRowIndex_injective_and_padSigns j, pairSign]

/-- Extending a point of the group of `W_j` by the identity on the padding does not increase its
norm. -/
lemma maxOpNorm_sum_one_le (y : GInf D.E (D.signsW j)) :
    maxOpNorm (G.sum ((y, 1), (1 : New.G D.E (-1 ⊕ᵥ 1 : PadIndex j → ℤˣ)))).1 ≤ maxOpNorm y := by
  simp [G.sum, U.sum, pi_norm_le_iff_of_nonempty, one_le_maxOpNorm,
    norm_le_pi_norm (fun w ↦ (y w).1.1)]

/-- Let `S` be the space of signature `(2 m, m)`, with index set `D.CarrierIndex` and signs
`1 ⊕ᵥ -1`, and let `W̃` be the space `W_j` (`1 ≤ j ≤ m`) padded to the signs `padSigns j`. Let
`P = paddedMinorProd j` be the fixed product of minors in the variables of `(S, W̃)`. For characters
of any weights `γ`, `e`, the matrix coefficient `polyMatrixCoeff` of the real Weil representation at
the Fock vector of `P` does not vanish at the identity, and it is bounded on the product of the real
unitary groups of `S` and `W̃`. -/
lemma polyMatrixCoeff_paddedMinorProd_ne_zero_and_bounded (γ e : D.Φ → ℤ) :
    polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ e (paddedMinorProd j) 1 1 ≠ 0 ∧
    ∃ B : ℝ, ∀ (h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) (h' : GInf D.E (padSigns j)),
      ‖polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ e (paddedMinorProd j) h h'‖ ≤ B := by
  -- The Fock representation is unitary: `l` carries `fockInner` to an inner product and the action
  -- to isometries.
  let ε := realSigns D.E (homSigns (n := D.CarrierIndex) (1 ⊕ᵥ -1) (padSigns j))
  let v := polyVector ε (paddedMinorProd j)
  obtain ⟨_, _, _, l, h_inner, h_unitary⟩ :=
    (isUnitaryRep_detTwist (ε := ε) (f := .id _) (γ := 0) (one_mul _).ge).exists_innerProductSpace
  refine ⟨?_, ‖l v‖ * ‖l v‖, fun h h' ↦ ?_⟩
  · -- Each minor in `paddedMinorProd` has distinct rows and distinct columns.
    simp [polyMatrixCoeff, ε, ← h_inner, paddedMinorProd, prod_eq_zero_iff,
      negIndex_posRowIndex_injective_and_padSigns j,
      inl_injective, inr_injective, mk_one_one]
  · -- Up to factors of modulus one this is an inner product; apply Cauchy–Schwarz.
    have h_phase : ‖polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ e (paddedMinorProd j) h h'‖ =
        ‖inner ℂ (l v) (l (realWeil (pairHomInf (h, h')) v))‖ := by
      simp [polyMatrixCoeff, realPairWeil, v, ε, ← h_inner]
    have h_iso : ‖l (realWeil (pairHomInf (h, h')) v)‖ = ‖l v‖ := by
      simpa [ε] using h_unitary (pairHomInf (h, h')) v
    grw [h_phase, norm_inner_le_norm, h_iso]

/-- The product of minors `paddedMinorProd j` is homogeneous of degree at most `b ^ (3 / 2)`, where
`b = D.b` is the large scale of the data. Its variables are indexed by an infinite place, a basis
vector of `W_j` (`D.RowIndex`) or of its padding (`PadIndex j`), and a basis vector of the space of
signature `(2 m, m)` (`D.CarrierIndex`). -/
lemma exists_eval_smul_paddedMinorProd : ∃ d : ℕ, d ≤ D.b * √D.b ∧
    ∀ (r : ℝ) (y : D.Φ × (D.RowIndex ⊕ PadIndex j) × D.CarrierIndex → ℂ),
      (paddedMinorProd j).eval (r • y) = r ^ d * (paddedMinorProd j).eval y := by
  let deg (w : D.Φ) : ℕ := ∑ h : Fin (D.posRank j),
    2 * D.m * (untwistedDescentPair j).colsPlus w h +
    D.m * (card (DetIndex j w) + card (FirstFactorIndex j) + D.m)
  have h_deg (w : D.Φ) : (deg w : ℝ) ≤ 2 * D.m * (5 * D.b) := by
    have h_cols : ∑ h : Fin (D.posRank j), (untwistedDescentPair j).colsPlus w h ≤
        card (DetIndex j w) := by simp
    grw [← two_mul_card_detIndex_add_le j w]
    norm_cast
    simp only [deg, ← mul_sum]
    grw [h_cols]
    lia
  refine ⟨∑ w, deg w, ?_, fun r y ↦ ?_⟩
  · grw [Nat.cast_sum, sum_le_card_nsmul _ _ _ fun w _ ↦ h_deg w]
    simpa using D.le_of_hasLogBound
  · have h_minor {p : Type} [Fintype p] [DecidableEq p] (τ : D.Φ)
        (row : p → D.RowIndex ⊕ PadIndex j) (col : p → D.CarrierIndex) :
        (variableMinor τ row col).eval (r • y) =
          r ^ card p * (variableMinor τ row col).eval y := by
      simp [variableMinor, det_apply', mul_sum, prod_mul_distrib, mul_left_comm]
    simp only [paddedMinorProd, map_prod, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    refine prod_congr rfl fun w _ ↦ ?_
    simp only [deg, map_mul, map_pow, map_prod, h_minor, Fintype.card_fin, mul_pow,
      prod_mul_distrib, pow_add, ← pow_mul, prod_pow_eq_pow_sum]
    ring

variable (D) in
/-- The weight `u₁ = (-Δ'; 6 m + 1)` of the kernels on `(S, W♭)`, the same at every place. Here
`Δ' = reducedHalfGap` is `Δ / 2 - (t + 1) / 2`, where the gap `Δ = 2 r ^ 8` is the difference of the
weights of consecutive lifts, and `6 m + 1` is the rank of `W♭`. Here and below `(a; b)` has the
entry `a` at the signs `+1` and `b` at the signs `-1` of `S`. -/
def flatKernelWeight (_ : D.Φ) : D.CarrierIndex → ℤ :=
  (fun _ ↦ -D.reducedHalfGap) ⊕ᵥ fun _ ↦ 6 * D.m + 1

/-- The weight `(Δ'; μ₁⁺ + r + 2 m)` of the holomorphic factor in the coefficient of
`paddedMinorProd`. Here `Δ' = reducedHalfGap` is `Δ / 2 - (t + 1) / 2` for the gap `Δ`, and
`μ₁⁺ = #(DetIndex j w)` is the number of columns of the diagram `μ⁺` at the place `w`: the sum of
the column counts `colsPlus` of `untwistedDescentPair j`, plus `Δ'`. The weight is `u₂ + μ₁⁺`, where
`u₂ = (Δ' - μ₁⁺; r + 2 m)` is the weight for the standard character `υ ^ m`. The shift by `μ₁⁺` in
every entry arises because the character `carrierChar j` of the kernel has weight `m - μ₁⁺` instead
of `m`. -/
noncomputable def holomorphicWeight (w : D.Φ) : D.CarrierIndex → ℤ :=
  (fun _ ↦ D.reducedHalfGap) ⊕ᵥ fun _ ↦ card (DetIndex j w) + D.r + 2 * D.m

/-- The weight `u₃ = (0; μ₁⁺ + n'' + 2 m)` of the antiholomorphic factor in the coefficient of
`paddedMinorProd`. Here `μ₁⁺ = #(DetIndex j w)` is the number of columns of the diagram `μ⁺` at the
place `w` (the sum of the column counts `colsPlus` of `untwistedDescentPair j`, plus
`reducedHalfGap`), and `n'' = #(FirstFactorIndex j) = r + 9 m + 1` is the rank of `W̃ ⊕ W♭`. -/
noncomputable def antiholomorphicWeight (w : D.Φ) : D.CarrierIndex → ℤ :=
  (fun _ ↦ 0) ⊕ᵥ fun _ ↦ card (DetIndex j w) + card (FirstFactorIndex j) + 2 * D.m

/-- Let `S` be the space of signature `(2 m, m)`, with signs `1 ⊕ᵥ -1`, and let `W̃` be the padded
space of rank `r + 3 m` with signs `padSigns j`. Let `c_P` be the matrix coefficient
`polyMatrixCoeff` of the Fock vector of the product of minors `P = paddedMinorProd j` on `(S, W̃)`;
the weight `γ` of the first character is arbitrary, and that of the second is `m - μ₁⁺`, where
`μ₁⁺ = #(DetIndex j w)` is the number of columns of the partition `μ⁺` of the `j`-th lift at the
place `w`. Then for every real point `h` of the group of `S`,
`c_P(h, 1) = c_P(1, 1) m₂(h) conj(m₃(h))`. Here `m₂`, `m₃` are the quotients of minors `holMinorsPi`
of the weights `holomorphicWeight j = (Δ'; μ₁⁺ + r + 2 m)` and
`antiholomorphicWeight j = (0; μ₁⁺ + r + 11 m + 1)`, with `Δ' = D.reducedHalfGap` and with the
entries at the signs `+1`, `-1` before and after the semicolon. -/
lemma polyMatrixCoeff_paddedMinorProd (γ : D.Φ → ℤ) (h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) :
    polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ (fun w : D.Φ ↦ D.m - card (DetIndex j w))
      (paddedMinorProd j)
      h 1 =
    polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ (fun w : D.Φ ↦ D.m - card (DetIndex j w))
      (paddedMinorProd j)
      1 1 * holMinorsPi (1 ⊕ᵥ -1) (holomorphicWeight j) h *
        starRingEnd ℂ (holMinorsPi (1 ⊕ᵥ -1) (antiholomorphicWeight j) h) := by
  obtain ⟨-, h_neg_rows, h_pos_rows⟩ := negIndex_posRowIndex_injective_and_padSigns j
  have h_neg : Exchange.negCount (padSigns j) = D.m := by simp [negCount_signsW, j.2.2]
  let ν (w : D.Φ) : ℕ := ∑ k : Fin (D.posRank j), (untwistedDescentPair j).colsPlus w k
  let κ (w : D.Φ) : ℕ := card (DetIndex j w) + card (FirstFactorIndex j) + D.m
  -- Each minor in `paddedMinorProd` uses all columns of one sign, so a substitution multiplies it
  -- by a principal minor.
  have h_scale (u : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) :
      linSubst (complexLinearPart (pairHomInf (s' := padSigns j) (u⁻¹, 1))) (paddedMinorProd j) =
        (∏ w, principalMinor (u w).1.1 (fun k ↦ (1 ⊕ᵥ -1 : _ → ℤˣ) k = 1) ^ ν w *
          principalMinor (u w).1.1 (fun k ↦ (1 ⊕ᵥ -1 : _ → ℤˣ) k = -1) ^ κ w) • paddedMinorProd
            j := by
    simp [ν, κ, paddedMinorProd, prod_pow_eq_pow_sum, -card_sum,
      linSubst_variableMinor (h_pos_rows _) inl_injective,
      linSubst_variableMinor h_neg_rows inr_injective, smul_pow, prod_smul, smul_smul]
  -- Entry by entry, `holomorphicWeight j` is the weight `(-ν; rank W̃ - m) + μ₁⁺` and
  -- `antiholomorphicWeight j` is the weight `(0; κ + m)`.
  have holomorphicWeight_eq : holomorphicWeight j = fun (w : D.Φ) (i : D.CarrierIndex) ↦
      if (1 ⊕ᵥ -1 : _ → ℤˣ) i = 1 then (-ν w + (D.m - (D.m - card (DetIndex j w))) : ℤ)
      else (card (D.RowIndex ⊕ PadIndex j) - D.m : ℕ) + (D.m - (D.m - card (DetIndex j w))) := by
    ext w (_ | _)
    · simp [ν, holomorphicWeight]
    · simp [holomorphicWeight, ↓card_rowIndex]
      grind
  have antiholomorphicWeight_eq : antiholomorphicWeight j = fun (w : D.Φ) (i : D.CarrierIndex) ↦
      if (1 ⊕ᵥ -1 : _ → ℤˣ) i = 1 then (0 : ℤ) else κ w + D.m := by
    ext w (_ | _)
    · simp [antiholomorphicWeight]
    · simp [κ, antiholomorphicWeight]
      ring
  rw [holomorphicWeight_eq, antiholomorphicWeight_eq,
    polyMatrixCoeff_eq_holMinorsPi_mul_conj (1 ⊕ᵥ -1) (padSigns j) (paddedMinorProd j)
      (paddedMinorProd_mem_supported j) γ _ h_scale h, h_neg]

/-- Let `S` be the space of signature `(2 m, m)`, with index set `D.CarrierIndex` and signs
`1 ⊕ᵥ -1`. The weights `u₁ = flatKernelWeight D` and `u₃ = antiholomorphicWeight j` are integer
vectors on the indices of `S`, one for each infinite place. For every order `o` on the indices they
are `K`-dominant and have gap `300 n_*`, and `u₃` has entries of modulus at most `5 b`. Here
`b = D.b` is the large scale of the data and `n_* = nStar D = 2 f t ^ 3`, with `f` the number of
infinite places and `t = 5 r`. -/
lemma flatKernelWeight_antiholomorphicWeight_bounds (o : D.CarrierIndex → ℤ) :
    (∀ w : D.Φ, IsKDominant (1 ⊕ᵥ -1) o (flatKernelWeight D w)) ∧
    (∀ w : D.Φ, HasHolGap (1 ⊕ᵥ -1) (flatKernelWeight D w) (300 * nStar D)) ∧
    (∀ w : D.Φ, IsKDominant (1 ⊕ᵥ -1) o (antiholomorphicWeight j w)) ∧
    (∀ w : D.Φ, HasHolGap (1 ⊕ᵥ -1) (antiholomorphicWeight j w) (300 * nStar D)) ∧
    ∀ (w : D.Φ) (i : D.CarrierIndex), |(antiholomorphicWeight j w i : ℝ)| ≤ 5 * D.b := by
  have h_gap : 300 * nStar D + D.t ≤ D.halfGap := D.mul_nStar_add_t_le_halfGap
  refine ⟨by simp [flatKernelWeight, IsKDominant], ?_,
    by simp [antiholomorphicWeight, IsKDominant], ?_, fun w i ↦ ?_⟩
  · simp [flatKernelWeight, reducedHalfGap, HasHolGap]
    lia
  · simp [antiholomorphicWeight, -Nat.cast_sum, HasHolGap]
    grind [reducedHalfGap]
  · have h_le : D.m ≤ card (FirstFactorIndex j) := by grind [card_firstFactorIndex j]
    grw [← two_mul_card_detIndex_add_le j w]
    norm_cast
    cases i <;> simp [antiholomorphicWeight, -card_sum] <;> grind

/-- The character `carrierChar j` of the kernels on `(S, W̃)` and `(S, W̃ ⊕ W♭)` has weight
`m - μ₁⁺`, with `μ₁⁺ = #(DetIndex j w)` at the place `w`, and trivial tame part. -/
lemma carrierChar_hasWeight_sub_card :
    (carrierChar j).HasWeight (fun w : D.Φ ↦ D.m - card (DetIndex j w)) 1 := by
  have h_weight (w : D.Φ) :
      (D.m : ℤ) - card (DetIndex j w) = (D.m + firstFactorCharExp j : ℕ) - D.liftWeight j w := by
    grind [card_detIndex_add_firstFactorCharExp j w]
  simpa only [h_weight] using carrierChar_hasWeight j

variable (D) in
/-- Let `S = signedSpace D.E (1 ⊕ᵥ -1)` be the space of signature `(2 m, m)`, and let
`φ° = carrierForm D.E D.m` be the carrier, the theta lift of the constant function `1` from the
negative definite space of rank `m` to `S`. Assume that `φ°` is automorphic of every level and
rapidly decreasing (`rapidOfLevel`), and holomorphic in the real variable of weight `(0; 3 m)` for
an order `o` with the signs `+1` first. Then `φ°` has a peak `g₁`, and the first minimum of the
lattice of `S` at `g₁`, cut off at `1`, is at least `(5 b √b) ^ (-1 / 2)`, where `b = D.b` is the
large scale of the data. -/
lemma exists_isPeak_carrierForm {o : D.CarrierIndex → ℤ} (ho : IsPosFirstOrder (1 ⊕ᵥ -1) o)
    (h_level : ∀ N : 𝓞 D.E, carrierForm D.E D.m ∈ rapidOfLevel (signedSpace D.E (1 ⊕ᵥ -1)) N)
    (h_hol : IsAdelicHol o (fun _ : D.Φ ↦ 0 ⊕ᵥ 3 * D.m) (carrierForm D.E D.m)) :
    ∃ g₁ : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ), IsPeak (carrierForm D.E D.m) g₁ ∧
      (√(5 * D.b * √D.b))⁻¹ ≤ ((signedSpace D.E (1 ⊕ᵥ -1)).move g₁).firstMinimum := by
  obtain ⟨g₁, hg₁⟩ := exists_isPeak_of_mem_rapidOfLevel (h_level 1) carrierForm_ne_zero
  have h_gap (w : D.Φ) : HasHolGap (1 ⊕ᵥ -1) (0 ⊕ᵥ 3 * D.m : D.CarrierIndex → ℤ) 1 := by
    simp [HasHolGap]
    grind
  have h_wt (w : D.Φ) :
      ∀ i : D.CarrierIndex, |((0 ⊕ᵥ 3 * D.m : D.CarrierIndex → ℤ) i : ℝ)| ≤ 5 * D.b := by
    simpa [Real.exp_nonneg] using D.le_of_hasLogBound
  obtain ⟨⟨h_autom, -⟩, -⟩ := h_level 1
  refine ⟨g₁, hg₁, hg₁.le_firstMinimum _ _ ho h_gap h_wt D.le_of_hasLogBound D.le_of_hasLogBound
    P.star_sqrtNegDInE ?_ h_autom.rat_mul (apply_mul_of_mem_rapidOfLevel (h_level _)) h_hol⟩
  -- The level used is `√(-d)`, with `d = P.d` and `K = ℚ(√(-d))`; its norm `√d` is at most `√b`.
  simpa [P.d_prime.pos] using D.le_of_hasLogBound

/-- The space `W̃ = W_j ⊕ (E^j)⁻ ⊕ E^(3 m - j)`. -/
noncomputable abbrev paddedSpace : Space D.E (D.RowIndex ⊕ PadIndex j) (padSigns j) :=
  (D.spaceW j).sum ((stdSpace D.E (Fin j)).neg.sum (stdSpace D.E (Fin (2 * D.m + (D.m - j)))))

/-- For `g` in the group of `W_j = D.spaceW j`, the first minimum (cut off at `1`) of `W_j` moved by
`g` is at most that of the padded space `W̃ = paddedSpace j` moved by `G.sum (g, 1)`. So extending
`g` by `1` to `W̃` does not lower the first minimum. -/
lemma firstMinimum_le_paddedSpace (g : New.G D.E (D.signsW j)) :
    ((D.spaceW j).move g).firstMinimum ≤ ((paddedSpace j).move (G.sum (g, 1))).firstMinimum := by
  have h_pad : 1 ≤ (((stdSpace D.E (Fin j)).neg.sum
      (stdSpace D.E (Fin (2 * D.m + (D.m - j))))).move 1).firstMinimum := by
    rw [← G.sum.map_one]
    -- Both summands are definite, so both have first minimum at least `1`.
    exact (le_inf (Space.one_le_firstMinimum fun _ _ ↦ rfl)
      (Space.one_le_firstMinimum fun _ _ ↦ rfl)).trans inf_le_firstMinimum_sum
  grw [← inf_le_firstMinimum_sum, ← h_pad, inf_of_le_left Space.firstMinimum_le_one]

/-- Step 1 of the proof that products span. Let `1 ≤ j ≤ m`, let `W_j` be the diagonal space with
signs `D.signsW j`, let `W̃ = paddedSpace j` be its sum with a definite space of each sign, and let
`S = signedSpace D.E (1 ⊕ᵥ -1)` be the space of signature `(2 m, m)`. Assume that the order `o` puts
the signs `+1` of `S` first, that the carrier `φ° = carrierForm D.E D.m` is automorphic of every
level and rapidly decreasing (`rapidOfLevel`), and that the quotient of minors
`m_u₁ = holMinorsPi _ u₁` is integrable on the real group of `S`, where `u₁ = flatKernelWeight D` is
the weight of the kernels on `S` and `W♭ = E^(6 m + 1)`. Let `g₁` be a point of the group of `S`,
let `Ψ` be a function on matrices modulo `ϖ²` (`untwistedModulus 2`, with `ϖ` the product of the
chosen places above the level primes), and let `θ[Ψ, P]` be the theta kernel `modKernel` of
`(S, W̃)` with datum `Ψ`, polynomial the product of minors `P = paddedMinorProd j`, and characters
`υ ^ m` and `carrierChar j` of `U(1)`, where `υ = upsilonU1` has weight `1`. Then, as a function of
the point `g` of the group of `W_j`, the integral of `φ°(g₁ h) θ[Ψ, P](g₁ h, (g, 1)) m_u₁(h)` over
the real points `h` is a linear combination of the functions `choiceFn j i`. These are the integrals
of `φ°` against theta kernels of `(S, W̃ ⊕ W♭)`, one for each choice `i` of an additive character
of the matrices modulo `ϖ²`, a class of `U(W♭)` at level `ϖ²` and rows of determinants. -/
lemma exists_sum_choiceFn_eq_integral {o : D.CarrierIndex → ℤ} (ho : IsPosFirstOrder (1 ⊕ᵥ -1) o)
    (h_level : ∀ N : 𝓞 D.E, carrierForm D.E D.m ∈ rapidOfLevel (signedSpace D.E (1 ⊕ᵥ -1)) N)
    (h_int : MeasureTheory.Integrable (holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D)))
    (g₁ : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ))
    (Ψ : Matrix (D.RowIndex ⊕ PadIndex j) D.CarrierIndex (D.untwistedModulus 2).ResidueRing → ℂ) :
    ∃ c : ChoiceIndex j → ℂ, ∀ g : New.G D.E (D.signsW j),
      ∑ i : ChoiceIndex j, c i * choiceFn j i g =
      ∫ h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ), carrierForm D.E D.m (g₁ * (h, 1)) *
        modKernel (signedSpace D.E (1 ⊕ᵥ -1)) (paddedSpace j) (upsilonU1 ^ D.m) (carrierChar j)
          (D.untwistedModulus 2) Ψ (paddedMinorProd j) (g₁ * (h, 1)) (G.sum (g, 1)) *
        holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D) h := by
  -- The reproducing formula on `(S, W♭)` turns the real integral into pairings with kernels `θ₂ r`.
  -- The product of `θ[Ψ, P]` with `θ₂ r` is a kernel on `W̃ ⊕ W♭`, and Fourier expansion of its
  -- datum writes it as a combination of the kernels that define `choiceFn`.
  let S : Space D.E D.CarrierIndex (1 ⊕ᵥ -1) := signedSpace D.E (1 ⊕ᵥ -1)
  let φ : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ) → ℂ := carrierForm D.E D.m
  let 𝔪 : Modulus D.E := D.untwistedModulus 2
  have h_card : 2 * card D.CarrierIndex < card D.FlatIndex := by
    simp only [card_sum, Fintype.card_fin]
    omega
  obtain ⟨e⟩ : Nonempty (D.CarrierIndex ↪ D.FlatIndex) :=
    Function.Embedding.nonempty_of_card_le (by omega)
  let δ : Matrix D.FlatIndex D.CarrierIndex 𝔪.ResidueRing → ℂ :=
    Pi.single (inclMatrix 𝔪.ResidueRing e) 1
  let Q (r : D.RowChoice) : MvPolynomial (D.Φ × D.FlatIndex × D.CarrierIndex) ℂ :=
    pairedDetProd (fun τ a b ↦ .X (τ, a, inl b)) fun w k ↦
      ((D.shortRows r).map (Φ w)).submatrix (r.rows w k) id
  -- The kernels on `(S, W̃)`, on `(S, W♭)` and on `(S, W̃ ⊕ W♭)`.
  let θ₁ (g : New.G D.E (D.signsW j)) (x : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) : ℂ :=
    modKernel S (paddedSpace j) (upsilonU1 ^ D.m) (carrierChar j) 𝔪 Ψ (paddedMinorProd j) x
      (G.sum (g, 1))
  let θ₂ (r : D.RowChoice) (x : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) : ℂ :=
    modKernelStdSpace S (upsilonU1 ^ D.m) 1 𝔪 δ (Q r) x r.classRep
  let θ (i : ChoiceIndex j) (g : New.G D.E (D.signsW j))
      (x : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) : ℂ :=
    modKernel S ((paddedSpace j).sum (stdSpace D.E D.FlatIndex)) (upsilonU1 ^ D.m) (carrierChar j)
      𝔪 (traceChar i.matrix)
      (renameRowsCols inl id (paddedMinorProd j) * renameRowsCols inr id (Q i.rowChoice)) x
      (G.sum (G.sum (g, 1), (1, i.rowChoice.classRep)))
  have h_choiceFn (i : ChoiceIndex j) (g : New.G D.E (D.signsW j)) :
      choiceFn j i g = ∫ x, φ x * θ i g x ∂S.quotMeasure := rfl
  -- Reproduction on `(S, W♭)`: the translates of the power of one minor lie in the span of the
  -- products of determinants formed with the short basis `shortRows` of each class.
  obtain ⟨c, h_repro⟩ : ∃ c : D.RowChoice → ℂ, ∀ ψ ∈ rapidOfLevel S (D.piM ^ 2),
      ∫ h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ),
        ψ (g₁ * (h, 1)) * holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D) h =
      ∑ r, c r * ∫ x, ψ x * θ₂ r x ∂S.quotMeasure := by
    have h_weight : flatKernelWeight D =
        fun _ ↦ (-D.reducedHalfGap ⊕ᵥ card D.FlatIndex : D.CarrierIndex → ℤ) := by
      ext w (_ | _) <;> simp [flatKernelWeight]
    rw [h_weight] at h_int ⊢
    obtain ⟨minor_ne, minor_hol⟩ := prod_variableMinor_mem_holomorphicData (E := D.E) ho
      (Function.Embedding.inl.trans e) D.reducedHalfGap fun _ ↦ D.m
    have h_unit (r : D.RowChoice) : IsUnit (D.shortRows r) := by simp [shortRows]
    exact reproducing_formula_modKernel ho D.ideal_untwistedModulus_eq_span
      nonempty_modulus_places S (hasWeight_upsilonU1_pow D.m) .one (by simp [IsKDominant]) h_int
      h_card e minor_ne minor_hol (fun p rows ↦ Q (p, rows))
      (fun p ↦ realPairWeil_mem_span_pairedDetProd _ (h_unit (p, 0)) _ _) g₁
  -- The product of `Ψ` with the datum `δ` is a combination of additive characters.
  obtain ⟨f, h_fourier⟩ : ∃ f : Matrix D.CarrierIndex (FirstFactorIndex j) 𝔪.ResidueRing → ℂ,
      ∑ Λ, f Λ • traceChar Λ = fun z ↦ Ψ z.toRows₁ * δ z.toRows₂ :=
    exists_sum_smul_addChar_trace_eq 𝔪.isPrimitive_primAddChar _
  -- The two kernels multiply to the kernel of the sum of the spaces, which is linear in its datum.
  have h_seesaw (r : D.RowChoice) (g : New.G D.E (D.signsW j))
      (x : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) :
      θ₁ g x * θ₂ r x = ∑ Λ, f Λ * θ (Λ, r) g x := by
    simp only [θ₁, θ₂, θ]
    rw [← modKernel_sum_right, ← h_fourier, mul_one]
    simp only [← modKernelBilin_apply, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
  -- The products of `φ` with the kernels are rapidly decreasing of level `ϖ²`.
  have θ₁_level (g : New.G D.E (D.signsW j)) : φ * θ₁ g ∈ rapidOfLevel S (D.piM ^ 2) :=
    mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span (hb := carrierChar_hasWeight j)
      (fun _ _ ↦ rfl) (h_level (D.piM ^ 2)) ..
  have θ_level (i : ChoiceIndex j) (g : New.G D.E (D.signsW j)) :
      φ * θ i g ∈ rapidOfLevel S (D.piM ^ 2) :=
    mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span (hb := carrierChar_hasWeight j)
      (fun _ _ ↦ rfl) (h_level (D.piM ^ 2)) ..
  have h_pairing (r : D.RowChoice) (g : New.G D.E (D.signsW j)) :
      ∫ x, (φ * θ₁ g) x * θ₂ r x ∂S.quotMeasure = ∑ Λ, f Λ * choiceFn j (Λ, r) g := by
    simp only [Pi.mul_apply, mul_assoc, h_seesaw, h_choiceFn]
    exact integral_mul_sum_const_mul fun Λ ↦ θ_level (Λ, r) g
  refine ⟨fun i ↦ c i.rowChoice * f i.matrix, fun g ↦ ?_⟩
  calc ∑ i : ChoiceIndex j, c i.rowChoice * f i.matrix * choiceFn j i g
    _ = ∑ r, c r * ∑ Λ, f Λ * choiceFn j (Λ, r) g := by
      simp only [mul_sum, ← mul_assoc]
      exact sum_prod_type_right _
    _ = ∑ r, c r * ∫ x, (φ * θ₁ g) x * θ₂ r x ∂S.quotMeasure := by simp only [h_pairing]
    _ = ∫ h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ),
        (φ * θ₁ g) (g₁ * (h, 1)) * holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D) h :=
      (h_repro (φ * θ₁ g) (θ₁_level g)).symm

variable (D) in
/-- The identity `b ^ (-20 n_*) b ^ n_* = b ^ (-19 n_*)` for `n_* = nStar D`. -/
lemma inv_pow_twenty_mul_pow_nStar :
    (D.b ^ (20 * nStar D))⁻¹ * D.b ^ nStar D = (D.b ^ (19 * nStar D))⁻¹ := by
  field_simp
  ring

/-- Let `S = signedSpace D.E (1 ⊕ᵥ -1)`. Suppose the first minimum of `S` moved by `g₁` is at least
`(5 b √b) ^ (-1 / 2)`. Suppose that of `D.spaceW j` moved by `g` is at least
`(5 b ^ 24) ^ (-1 / 2)`. Then the first minimum of `S` moved by `g₁`, times that of `paddedSpace j`
moved by `G.sum (g, 1)`, is at least `b ^ (-13)`. Here `b = D.b` is the large scale of the data. -/
lemma inv_pow_le_firstMinimum_mul {g₁ : New.G D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)}
    {g : New.G D.E (D.signsW j)}
    (h_g₁ : (√(5 * D.b * √D.b))⁻¹ ≤ ((signedSpace D.E (1 ⊕ᵥ -1)).move g₁).firstMinimum)
    (h_g : (√(5 * D.b * D.b ^ 23))⁻¹ ≤ ((D.spaceW j).move g).firstMinimum) :
    (D.b ^ 13)⁻¹ ≤ ((signedSpace D.E (1 ⊕ᵥ -1)).move g₁).firstMinimum *
      ((paddedSpace j).move (G.sum (g, 1))).firstMinimum := by
  have h_pos : 0 < ((signedSpace D.E (1 ⊕ᵥ -1)).move g₁).firstMinimum := Space.firstMinimum_pos
  grw [← firstMinimum_le_paddedSpace, ← h_g, ← h_g₁]
  exact D.le_of_hasLogBound

/-- Let `S` be the space with index set `D.CarrierIndex` of `3 m` elements, and let `W̃` be the
padded space `W_j ⊕ (E^j)⁻ ⊕ E^(3 m - j)`: `j` signs `-1`, then `3 m - j` signs `1`. Both have rank
at most `t = 5 r`. The index set of `W̃` is `D.RowIndex ⊕ PadIndex j`: the `r` indices of `W_j` and
the `3 m` indices of the padding. -/
lemma card_carrierIndex_le_and_card_sum_padIndex_le :
    card D.CarrierIndex ≤ D.t ∧ card (D.RowIndex ⊕ PadIndex j) ≤ D.t := by
  simp [↓card_rowIndex]
  grind

/-- Let `f` be holomorphic of weight `(0; 3 m)` on the real group of the space `S` of signature
`(2 m, m)`, for an order `o` with the signs `+1` first. Let `1 ≤ j ≤ m` and let `W̃` be the padded
space of rank `r + 3 m` with signs `padSigns j`. Let `c_P` be the matrix coefficient
`polyMatrixCoeff` of the Fock vector of the product of minors `P = paddedMinorProd j` on `(S, W̃)`;
the weight `γ` of the first character is arbitrary, and that of the second is `m - μ₁⁺`, with
`μ₁⁺ = #(DetIndex j w)` the number of columns of the partition `μ⁺` of the `j`-th lift at the place
`w`. Let `m₁`, `m₃` be the quotients of minors `holMinorsPi` of the weights
`u₁ = flatKernelWeight D`, that of the kernels on `S` and `E^(6 m + 1)`, and
`u₃ = antiholomorphicWeight j`, that of the antiholomorphic factor of `c_P(·, 1)`. If
`f c_P(·, 1) m₁` is integrable, its integral is `f(1) c_P(1, 1)` times the integral of
`|m₃| ^ 2`. -/
lemma integral_mul_polyMatrixCoeff_paddedMinorProd {o : D.CarrierIndex → ℤ}
    (ho : IsPosFirstOrder (1 ⊕ᵥ -1) o)
    {f : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ) → ℂ}
    (hf : IsHolOfWeight (1 ⊕ᵥ -1) o (fun _ : D.Φ ↦ (0 ⊕ᵥ 3 * D.m : D.CarrierIndex → ℤ)) f)
    (γ : D.Φ → ℤ)
    (h_int : MeasureTheory.Integrable fun h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ) ↦ f h *
      polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ (fun w : D.Φ ↦ D.m - card (DetIndex j w))
        (paddedMinorProd j) h 1 *
      holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D) h) :
    ∫ h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ), f h *
      polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ (fun w : D.Φ ↦ D.m - card (DetIndex j w))
        (paddedMinorProd j) h 1 *
      holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D) h =
    (∫ h, ‖holMinorsPi (1 ⊕ᵥ -1) (antiholomorphicWeight j) h‖ ^ 2 : ℝ) * (f 1 *
      polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ (fun w : D.Φ ↦ D.m - card (DetIndex j w))
        (paddedMinorProd j) 1 1) := by
  -- The holomorphic factor of `c_P(·, 1)` times `f m₁` is holomorphic of the weight of `m₃`.
  set m₁ := holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D)
  let m₂ := holMinorsPi (1 ⊕ᵥ -1) (holomorphicWeight j)
  let m₃ := holMinorsPi (1 ⊕ᵥ -1) (antiholomorphicWeight j)
  set cP := polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) γ (fun w ↦ D.m - card (DetIndex j w))
    (paddedMinorProd j)
  obtain ⟨h_dom₁, -, h_dom₃, -⟩ := flatKernelWeight_antiholomorphicWeight_bounds j o
  have h_dom₂ (w : D.Φ) : IsKDominant (1 ⊕ᵥ -1) o (holomorphicWeight j w) := by
    simp [holomorphicWeight, IsKDominant]
  have h_weight : antiholomorphicWeight j =
      (fun _ ↦ (0 ⊕ᵥ 3 * D.m : D.CarrierIndex → ℤ)) + flatKernelWeight D +
        holomorphicWeight j := by
    ext w (_ | _) <;> simp [antiholomorphicWeight, flatKernelWeight, holomorphicWeight, -card_sum]
    grind [card_firstFactorIndex j]
  have h_const : IsHolOfWeight (1 ⊕ᵥ -1) o (holomorphicWeight j) fun h ↦ cP 1 1 * m₂ h := by
    simpa using IsHolOfWeight.sum (T := {()}) (fun _ : Unit ↦ cP 1 1)
      fun _ ↦ isHolOfWeight_holMinorsPi ho h_dom₂
  have h_hol : IsHolOfWeight (1 ⊕ᵥ -1) o (antiholomorphicWeight j)
      fun h ↦ f h * m₁ h * (cP 1 1 * m₂ h) := by
    rw [h_weight]
    exact (hf.mul ho.1 (isHolOfWeight_holMinorsPi ho h_dom₁)).mul ho.1 h_const
  have h_integrand (h : GInf D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)) :
      f h * cP h 1 * m₁ h = f h * m₁ h * (cP 1 1 * m₂ h) * starRingEnd ℂ (m₃ h) := by
    simp only [cP, polyMatrixCoeff_paddedMinorProd j γ h]
    ring
  simp only [h_integrand] at h_int ⊢
  simpa [m₁, m₂, m₃] using h_hol.integral_mul_conj_holMinorsPi ho h_dom₃ h_int

/-- There is a bounded function `F₀` on the real group of `W_j` with `F₀ 1 ≠ 0` such that, at every
adelic `g` off the cusps, in the sense that the lattice of `W_j` moved by `g` has first minimum at
least `(5 b ^ 24) ^ (-1 / 2)`, some combination `F` of the `choiceFn j i` has `|F (g h) - F₀ h| ≤ 2
b ^ (-19 n_*) |F₀ 1| |h| ^ (6 n_*)` for all real `h`. Here `|h| = maxOpNorm h`, `b = D.b` is the
large scale of the data, and `n_* = nStar D = 2 f t ^ 3`, with `f` the number of infinite places and
`t = 5 r`. -/
theorem exists_choiceFn_approx : ∃ (F₀ : GInf D.E (D.signsW j) → ℂ) (C : ℝ),
    F₀ 1 ≠ 0 ∧
    (∀ h : GInf D.E (D.signsW j), ‖F₀ h‖ ≤ C) ∧
    ∀ g : New.G D.E (D.signsW j), (√(5 * D.b * D.b ^ 23))⁻¹ ≤ ((D.spaceW j).move g).firstMinimum →
      ∃ c : ChoiceIndex j → ℂ, ∀ h : GInf D.E (D.signsW j),
        ‖∑ i : ChoiceIndex j, c i * choiceFn j i (g * (h, 1)) - F₀ h‖ ≤
          2 * (D.b ^ (19 * nStar D))⁻¹ * ‖F₀ 1‖ * maxOpNorm h ^ (6 * nStar D) := by
  -- With a peak `g₁` of `φ°` put `F₀ h = ∫ φ°(g₁ h') c_P(h', h) m_u₁(h') dh'`. Its value at `1` is
  -- `c_P(1, 1) φ°(g₁) J` with `J = ∫ |m_u₃|²`. Away from the cusps a theta kernel is close to `c_P`
  -- (`exists_datum_norm_modKernel_sub_polyMatrixCoeff_le`), and the same integral with the kernel
  -- in place of `c_P` is a combination of the `choiceFn j i`. The bound `h_bound` for the integral
  -- of the difference has the same factors `|φ°(g₁)|` and `J`, so it is small against `|F₀ 1|`.
  let φ := carrierForm D.E D.m
  let S := signedSpace D.E (1 ⊕ᵥ -1 : D.CarrierIndex → ℤˣ)
  obtain ⟨φ_level, o, ho, φ_hol⟩ : (∀ N, φ ∈ rapidOfLevel S N) ∧
      ∃ o, IsPosFirstOrder (1 ⊕ᵥ -1) o ∧ IsAdelicHol o (fun _ ↦ 0 ⊕ᵥ 3 * D.m) φ :=
    carrierForm_mem_rapidOfLevel_and_isAdelicHol D.m_even (isTameFor_twistedChiMPow (c := 2) j 1)
  obtain ⟨g₁, g₁_peak, g₁_min⟩ :
      ∃ g₁, IsPeak φ g₁ ∧ (√(5 * D.b * √D.b))⁻¹ ≤ (S.move g₁).firstMinimum :=
    exists_isPeak_carrierForm D ho φ_level φ_hol
  let cP := polyMatrixCoeff (1 ⊕ᵥ -1) (padSigns j) (fun _ ↦ D.m) (fun w ↦ D.m - card (DetIndex j w))
    (paddedMinorProd j)
  obtain ⟨cP_ne, B, cP_le⟩ : cP 1 1 ≠ 0 ∧ ∃ B : ℝ, ∀ h h', ‖cP h h'‖ ≤ B :=
    polyMatrixCoeff_paddedMinorProd_ne_zero_and_bounded j _ _
  let m₁ := holMinorsPi (1 ⊕ᵥ -1) (flatKernelWeight D)
  let J : ℝ := ∫ h, ‖holMinorsPi (1 ⊕ᵥ -1) (antiholomorphicWeight j) h‖ ^ 2
  let ι (h : GInf D.E (D.signsW j)) : GInf D.E (padSigns j) := (G.sum ((h, 1), 1)).1
  let F₀ (h : GInf D.E (D.signsW j)) : ℂ := ∫ h', φ (g₁ * (h', 1)) * cP h' (ι h) * m₁ h'
  -- The weights `u₁`, `u₃` satisfy the hypotheses of `integrable_mul_holMinorsPi`.
  obtain ⟨h_rank, h_rank'⟩ := card_carrierIndex_le_and_card_sum_padIndex_le j
  obtain ⟨u₁_dom, u₁_gap, u₃_dom, u₃_gap, u₃_le⟩ :=
    flatKernelWeight_antiholomorphicWeight_bounds j o
  have J_pos : 0 < J := integral_norm_holMinorsPi_sq_pos h_rank ho u₃_dom u₃_gap
  have h_bound {A : GInf D.E (1 ⊕ᵥ -1) → ℂ} {c : ℝ} (hA : Continuous A)
      (hA_le : ∀ h', ‖A h'‖ ≤ c * maxOpNorm h' ^ (6 * nStar D)) :
      MeasureTheory.Integrable (fun h' ↦ φ (g₁ * (h', 1)) * A h' * m₁ h') ∧
      ‖∫ h', φ (g₁ * (h', 1)) * A h' * m₁ h'‖ ≤ 2 * ‖φ g₁‖ * c * D.b ^ nStar D * J := by
    have prod_le (h' : GInf D.E (1 ⊕ᵥ -1)) :
        ‖φ (g₁ * (h', 1)) * A h'‖ ≤ 2 * ‖φ g₁‖ * c * maxOpNorm h' ^ (6 * nStar D) := by
      grw [norm_mul, g₁_peak.norm_le, hA_le, ← mul_assoc]
    exact integrable_mul_holMinorsPi h_rank ho u₃_dom u₁_dom u₃_gap u₁_gap u₃_le
      ((φ_hol g₁).continuous.fun_mul hA) prod_le
  have F₀_bound (h : GInf D.E (padSigns j)) :
      MeasureTheory.Integrable (fun h' ↦ φ (g₁ * (h', 1)) * cP h' h * m₁ h') ∧
      ‖∫ h', φ (g₁ * (h', 1)) * cP h' h * m₁ h'‖ ≤ 2 * ‖φ g₁‖ * B * D.b ^ nStar D * J :=
    h_bound (by fun_prop [polyMatrixCoeff]) fun h' ↦ (cP_le h' h).trans
      (le_mul_of_one_le_right ((norm_nonneg _).trans (cP_le 1 1))
        (one_le_pow₀ (one_le_maxOpNorm h')))
  have F₀_one : F₀ 1 = J * (φ g₁ * cP 1 1) := by
    simpa [F₀, ι, J, cP, m₁, φ, mk_one_one] using
      integral_mul_polyMatrixCoeff_paddedMinorProd j ho (φ_hol g₁) (fun _ ↦ D.m) (F₀_bound 1).1
  refine ⟨F₀, 2 * ‖φ g₁‖ * B * D.b ^ nStar D * J,
    by simp [F₀_one, J_pos.ne', g₁_peak.ne_zero, cP_ne, φ], fun h ↦ (F₀_bound (ι h)).2,
    fun g hg ↦ ?_⟩
  -- Away from the cusps the kernel `θ Ψ` of some datum `Ψ` is close to `c_P`.
  let θ (Ψ : Matrix (D.RowIndex ⊕ PadIndex j) D.CarrierIndex (D.untwistedModulus 2).ResidueRing →
    ℂ) :=
    modKernel S (paddedSpace j) (upsilonU1 ^ D.m) (carrierChar j) (D.untwistedModulus 2) Ψ
      (paddedMinorProd j)
  obtain ⟨d, hd, h_homog⟩ := exists_eval_smul_paddedMinorProd j
  obtain ⟨Ψ, θ_near⟩ : ∃ Ψ, ∀ h' h, ‖θ Ψ (g₁ * (h', 1)) (G.sum (g, 1) * (h, 1)) - cP h' h‖ ≤
      (D.b ^ (20 * nStar D))⁻¹ * (maxOpNorm h' * maxOpNorm h) ^ (6 * nStar D) * ‖cP 1 1‖ :=
    exists_datum_norm_modKernel_sub_polyMatrixCoeff_le S (paddedSpace j) h_rank h_rank'
      (hasWeight_upsilonU1_pow D.m) (carrierChar_hasWeight_sub_card j) h_homog hd
      (inv_pow_le_firstMinimum_mul j g₁_min hg)
  obtain ⟨c, sum_eq⟩ : ∃ c : ChoiceIndex j → ℂ, ∀ x, ∑ i, c i * choiceFn j i x =
      ∫ h', φ (g₁ * (h', 1)) * θ Ψ (g₁ * (h', 1)) (G.sum (x, 1)) * m₁ h' :=
    exists_sum_choiceFn_eq_integral j ho φ_level
      (integrable_holMinorsPi h_rank ho u₁_dom u₁_gap) g₁ Ψ
  refine ⟨c, fun h ↦ ?_⟩
  -- The difference is the integral of `φ° (θ Ψ - c_P) m_u₁`, to which `h_bound` applies.
  let A (h' : GInf D.E (1 ⊕ᵥ -1)) : ℂ :=
    θ Ψ (g₁ * (h', 1)) (G.sum (g, 1) * (ι h, 1)) - cP h' (ι h)
  let ε : ℝ := (D.b ^ (20 * nStar D))⁻¹ * maxOpNorm (ι h) ^ (6 * nStar D) * ‖cP 1 1‖
  have A_le (h' : GInf D.E (1 ⊕ᵥ -1)) : ‖A h'‖ ≤ ε * maxOpNorm h' ^ (6 * nStar D) :=
    (θ_near h' (ι h)).trans_eq (by ring)
  obtain ⟨diff_int, diff_le⟩ := h_bound (by fun_prop [polyMatrixCoeff, modKernel]) A_le
  have h_diff : ∑ i, c i * choiceFn j i (g * (h, 1)) - F₀ h =
      ∫ h', φ (g₁ * (h', 1)) * A h' * m₁ h' := by
    have h_point : G.sum (g * (h, 1), 1) = G.sum (g, 1) * (ι h, 1) := by
      simp [ι, G.sum, Pi.mul_def, ← map_mul]
    rw [sum_eq, h_point, sub_eq_iff_eq_add,
      ← MeasureTheory.integral_add diff_int (F₀_bound (ι h)).1]
    simp [A, ← add_mul, ← mul_add]
  have norm_one : ‖F₀ 1‖ = J * (‖φ g₁‖ * ‖cP 1 1‖) := by simp [F₀_one, abs_of_pos J_pos]
  calc ‖∑ i, c i * choiceFn j i (g * (h, 1)) - F₀ h‖
    _ ≤ 2 * ‖φ g₁‖ * ε * D.b ^ nStar D * J := by rwa [h_diff]
    _ ≤ 2 * ‖φ g₁‖ * ((D.b ^ (20 * nStar D))⁻¹ * maxOpNorm h ^ (6 * nStar D) * ‖cP 1 1‖) *
        D.b ^ nStar D * J := by
      unfold ε
      grw [maxOpNorm_sum_one_le j h]
    _ = 2 * (D.b ^ (19 * nStar D))⁻¹ * ‖F₀ 1‖ * maxOpNorm h ^ (6 * nStar D) := by
      rw [norm_one, ← inv_pow_twenty_mul_pow_nStar D]
      ring

end NaturalFormNear

/-!
## The proof that products span

The good form is called `F`. By the reproducing formula `New.Rows.reproducing_formula_modKernel`,
the vanishing pairings give a vanishing integral over the real group.
-/

section Separation

open ComplexConjugate Parameters Rows Submodule WeilData Finset Fintype Fock DescentPair

variable {P : Parameters} {D : Data P} (j : D.LiftIndex)

/-- The pairing `⟨ζ, θ°(g, ·)⟩` of a form `ζ` on the definite space `V°` with the theta kernel `θ°`
of `(W_j, V°)`; it is conjugate-linear in `ζ`. The form is given by its values at the classes
`SecondFactorClasses` of `U(V°)` at principal level `ϖ²`, where `untwistedModulus 2` is the modulus
`ϖ²`. The values lie in the Weyl module, written in the basis `WeylIndexFamily`, of the diagrams
`μ⁻` with the column counts `colsMinus` of `untwistedDescentPair j`, the `j`-th descent pair at the
trivial twist. The term of a class `c` is the kernel `modKernelStdSpace` at `(g, c)` whose datum is
the indicator of the inclusion matrix of `W_j` in `V°` modulo `ϖ²` and whose polynomial is that of
the conjugate of `ζ c` in the variables of the negative basis vectors of `W_j` (`letterPoly`). -/
noncomputable def thetaKernelPairing (ζ : D.SecondFactorClasses →
      WeylIndexFamily (fun _ ↦ D.SecondFactorIndex) (untwistedDescentPair j).colsMinus → ℂ)
    (g : New.G D.E (D.signsW j)) : ℂ :=
  ∑ c : D.SecondFactorClasses,
    modKernelStdSpace (D.spaceW j) (untwistedDescentPair j).charW (upsilonU1 ^ (D.m / 2 - j : ℤ))
    (D.untwistedModulus 2) (Pi.single (inclMatrix (D.untwistedModulus 2).ResidueRing .inl) 1)
    (letterPoly (D.signsW j) (untwistedDescentPair j).numbering (-1)
      (untwistedDescentPair j).colsMinus
      (star (ζ c))) g c.out

variable {j}

/-- Let `1 ≤ j ≤ m`, let `W_j = D.spaceW j` be the diagonal hermitian space with signs `D.signsW j`,
and let `F` be a good form on `W_j`: an automorphic form whose real type is the discrete series of
doubled parameter `paramW`, fixed by the principal congruence subgroup at the chosen places above
the level primes, and in the image of the idempotent `e₀` of the group algebra of the finite groups
`GL_r` over their residue fields. Then for every adelic `g` the function `h ↦ conj F(g h)` on the
real group is holomorphic (`IsAdelicHol`). -/
lemma isAdelicHol_star_goodForms (F : D.goodForms (D.spaceW j)) :
    IsAdelicHol (orderW j) (conjHolomorphicWeight j) fun g : New.G D.E (D.signsW j) ↦
      star ((F : New.G D.E (D.signsW j) → ℂ) g) := by
  -- The lift `L` is injective, so its adjoint composed with it is injective, hence onto in finite
  -- dimension: `F` is a descent.
  let L : D.principalForms (D.spaceW j) →ₗ[ℂ] (D.descentPair .one j).FormV := D.singleLift .one j
  obtain ⟨y, lift⟩ : ∃ y : D.principalForms (D.spaceW j), L.adjoint (L y) = F.val :=
    (L.adjoint ∘ₗ L).surjective_of_injective
      ((LinearMap.adjoint_comp_self_injective_iff L).mpr (D.singleLift_injective .one)) F.val
  have h_descent :
      (F : New.G D.E (D.signsW j) → ℂ) = (D.descentPair .one j).normalizedDescent (L y) := by
    rw [← lift, D.coe_adjoint_singleLift]
  -- The polynomial of the highest vector is a product of joint harmonics, hence holomorphic; by
  -- equivariance so is the polynomial of every vector.
  obtain ⟨⟨harm, joint, pol_top⟩, -⟩ := (D.fitsParams_descentPair .one j).exists_isJointHarmonic
  let pol := polyVector (realSigns D.E (homSigns (D.signsW j) 1)) ∘ₗ
    (untwistedDescentPair j).fockPoly
  have hol ξ : pol ξ ∈ holomorphicData (D.signsW j) 1 (orderW j) (conjHolomorphicWeight j)
      (fun _ ↦ Exchange.negCount (untwistedDescentPair j).signs)
      (fun w ↦ (card (D.RowIndex ⊕ Fin D.t) / 2 : ℕ) + (D.descentPair .one j).weight w) :=
    mem_holomorphicData_of_highestVector pol (fun w ↦ (joint w).hasGap_row.injective)
      (realPairWeil_fockPoly _)
      (prod_mem_holomorphicData isPosFirstOrder_orderW paramW_lt_of_orderW_lt
        (fun w ↦ (joint w).isJointHighest) pol_top).2
  -- The conjugate of the descent is a finite combination of theta kernels with such polynomials.
  rw [h_descent]
  simpa [normalizedDescent, DescentPair.conjKernel, classSum, Rat.smul_def,
    ↓ finsum_eq_sum_of_fintype]
    using!
    fun g ↦ .sum _ fun _ ↦ isAdelicHol_pairTheta (hol _) g

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `1 ≤ j ≤ m`, let `F` be a good form on `W_j = D.spaceW j`, and write `F_i = choiceFn j i`
for the functions on the adelic group of `W_j` attached to the choices `i`. Let `V°` be the definite
space with index set `D.SecondFactorIndex`. A form `ζ` on `V°` assigns to each class at level `ϖ²` a
vector of the Weyl module of the diagrams with column counts `colsMinus`, in the basis
`WeylIndexFamily`, and `thetaKernelPairing j ζ g` pairs it with the theta kernel of `(W_j, V°)` at
`g`. Assume that the integrals of `F F_i` against these pairings, over the adelic group modulo its
rational points (`quotMeasure`), vanish for all `i` and `ζ`, and that the quotient of minors
`m_u° = holMinorsPi _ u°` is integrable, where `u° = kernelWeight j` is the weight of that kernel on
`W_j`. Then the integral of `F(g h) (∑ c_i F_i(g h)) m_u°(h)` over the real points `h` is zero for
every adelic `g`. -/
lemma integral_mul_sum_choiceFn_eq_zero (F : D.goodForms (D.spaceW j))
    (h_orth : ∀ (i : ChoiceIndex j) (ζ : D.SecondFactorClasses →
        WeylIndexFamily (fun _ : D.Φ ↦ D.SecondFactorIndex) (untwistedDescentPair j).colsMinus → ℂ),
      ∫ g : New.G D.E (D.signsW j), (F : New.G D.E (D.signsW j) → ℂ) g * choiceFn j i g *
        thetaKernelPairing j ζ g ∂(D.spaceW j).quotMeasure = 0)
    (h_int : MeasureTheory.Integrable (holMinorsPi (D.signsW j) (kernelWeight j)))
    (c : ChoiceIndex j → ℂ) (g : New.G D.E (D.signsW j)) :
    ∫ h : GInf D.E (D.signsW j), (F : New.G D.E (D.signsW j) → ℂ) (g * (h, 1)) *
      (∑ i : ChoiceIndex j, c i * choiceFn j i (g * (h, 1))) *
      holMinorsPi (D.signsW j) (kernelWeight j) h = 0 := by
  classical
  have fit : (D.descentPair .one j).FitsParams D.paramW := D.fitsParams_descentPair .one j
  have prod_level (i : ChoiceIndex j) :
      F.1.1.1 * choiceFn j i ∈ rapidOfLevel (D.spaceW j) (D.piM ^ 2) :=
    mul_choiceFn_mem_rapidOfLevel F i
  have rank_lt : 2 * card D.RowIndex < card D.SecondFactorIndex := by
    rw [D.card_rowIndex, card_sum, D.card_rowIndex, Fintype.card_fin, D.t_eq_five_mul_r]
    grind [D.hundred_mul_m_add_nine_lt_k, D.r_add_one]
  -- Reproduction on `(W_j, V°)`, for the basis polynomials `Q` in the negative letters; their span
  -- holds the translates of the highest vector.
  let Q := fockLetters (D.signsW j) (untwistedDescentPair j).numbering (-1) ∘
    nablaBasis ℂ (fun _ : D.Φ ↦ D.SecondFactorIndex) (untwistedDescentPair j).colsMinus
  obtain ⟨top_ne, top_hol⟩ := letterPoly_highestVector_mem_holomorphicData
    (n' := D.SecondFactorIndex)
    (γ := fun _ ↦ Exchange.negCount (D.signsW j)) (w := fun _ ↦ D.m / 2 - j) isPosFirstOrder_orderW
    (paramW_lt_of_orderW_lt 1) (fit.paramsCorrespond 1).hasGap_left.injective (fit.numbering_eq 1) _
    fit.colsMinus_eq_zero
  obtain ⟨a, repro⟩ := reproducing_formula_modKernel isPosFirstOrder_orderW
    (D.ideal_untwistedModulus_eq_span (c := 2)) nonempty_modulus_places (D.spaceW j)
    (hasWeight_upsilonU1_pow _) (hasWeight_upsilonU1_zpow (D.m / 2 - j))
    (isKDominant_kernelWeight j) h_int rank_lt .inl top_ne top_hol (fun _ ↦ Q)
    (fun _ _ ↦ by
      -- `erw` is needed: the first weight is `negCount` only after unfolding.
      erw [realPairWeil_fockLetters]
      -- The translate of a `toPoly` is a combination of the `Q`; `clear` keeps the search short.
      clear * -
      aesop (add safe sum_mem, simp [Q, toPoly, linearCombination_apply])) g
  refine (repro _ (mul_sum_mem_rapidOfLevel prod_level)).trans
    (sum_eq_zero fun p _ ↦ mul_eq_zero_of_right _ ?_)
  -- The pairing of `F ∑ c_i F_i` with a kernel is a combination of the pairings of the `F F_i`,
  -- and each of these is that of `h_orth` for `ζ` supported at one class, where its value is the
  -- conjugate of a vector `v` whose polynomial is the basis polynomial.
  let K (x : New.G D.E (D.signsW j)) : ℂ :=
    modKernelStdSpace (D.spaceW j) (upsilonU1 ^ Exchange.negCount (D.signsW j))
      (upsilonU1 ^ (D.m / 2 - j : ℤ)) (D.untwistedModulus 2)
      (Pi.single (inclMatrix (D.untwistedModulus 2).ResidueRing .inl) 1) (Q p.2) x p.1.out
  obtain ⟨v, hv⟩ : ∃ v, toPoly _ (untwistedDescentPair j).colsMinus v = nablaBasis ℂ _ _ p.2 :=
    range_toPoly.ge prod_tableauPoly_mem_nabla
  have h_theta (x : New.G D.E (D.signsW j)) :
    thetaKernelPairing j (Pi.single p.1 (star v)) x = K x := by
    simp [thetaKernelPairing, K, Q, ← modKernelBilin_apply, apply_ite, letterPoly, hv, nablaBasis,
      Pi.single_apply]
    rfl
  have h_pair (i : ChoiceIndex j) :
      ∫ x, F.1.1 x * (choiceFn j i * K) x ∂(D.spaceW j).quotMeasure = 0 := by
    simpa [h_theta, mul_assoc] using! h_orth i (Pi.single p.1 (star v))
  calc ∫ x, (F.1.1.1 * fun y ↦ ∑ i, c i * choiceFn j i y) x * K x ∂(D.spaceW j).quotMeasure
    _ = ∫ x, F.1.1 x * ∑ i, c i * (choiceFn j i * K) x ∂(D.spaceW j).quotMeasure := by
      simp [mul_assoc, sum_mul]
    _ = ∑ i, c i * ∫ x, F.1.1 x * (choiceFn j i * K) x ∂(D.spaceW j).quotMeasure := by
      refine integral_mul_sum_const_mul (a := D.piM ^ 2) fun i ↦ ?_
      rw [← mul_assoc]
      exact mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span (fun _ _ ↦ rfl)
        (prod_level i) ..
    _ = 0 := by simp only [h_pair, mul_zero, sum_const_zero]

/-- Products span. For admissible data `D` and `1 ≤ j ≤ m`, let `W_j = D.spaceW j` be the diagonal
hermitian space with signs `D.signsW j` and let `V°` be the definite space with index set
`D.SecondFactorIndex`. Let `F` be a good form on `W_j`: a form of principal level at the chosen
places in the image of the idempotent `e₀` of the group algebra of the finite groups at these
places. If `∫ F(g) F_i(g) θ°(g, ·) dg = 0` for all `i`, then `F = 0`. Here the `F_i = choiceFn j i`
are integrals of the carrier `carrierForm` against theta kernels, one for each of the finitely many
choices `i` of kernel data; the integral is over the adelic group modulo its rational points
(`quotMeasure`); and `thetaKernelPairing j ζ g` is the pairing of the theta kernel `θ°(g, ·)` of
`(W_j, V°)` with a form `ζ` on `V°`. Such a form assigns to each class at level `ϖ²` a vector of the
Weyl module, in the basis `WeylIndexFamily` indexed by the infinite places `D.Φ`, of the diagrams
whose column counts `colsMinus` belong to the data `untwistedDescentPair j` of the `j`-th lift. -/
theorem eq_zero_of_integral_choiceFn_thetaKernelPairing (F : D.goodForms (D.spaceW j))
    (h_orth : ∀ (i : ChoiceIndex j) (ζ : D.SecondFactorClasses →
        WeylIndexFamily (fun _ : D.Φ ↦ D.SecondFactorIndex) (untwistedDescentPair j).colsMinus → ℂ),
      ∫ g : New.G D.E (D.signsW j), (F : New.G D.E (D.signsW j) → ℂ) g * choiceFn j i g *
        thetaKernelPairing j ζ g ∂(D.spaceW j).quotMeasure = 0) :
    F = 0 := by
  -- Suppose `F ≠ 0`. The peaks of `conj F` lie away from the cusp, where a combination of the
  -- `F_i` is close to a fixed `F₀`. Then `norm_apply_one_le_of_forall_isPeak` makes `F₀ 1` too
  -- small.
  have h_rank : card D.RowIndex ≤ D.t := by grind [D.card_rowIndex, D.t_eq_five_mul_r]
  obtain ⟨F₀, C, F₀_ne, F₀_le, near⟩ := exists_choiceFn_approx j
  suffices h_star : star (F : New.G D.E (D.signsW j) → ℂ) = 0 from
    Subtype.ext (Subtype.ext (Subtype.ext (star_eq_zero.1 h_star)))
  by_contra F_ne
  -- `conj F` has level `M √(-d)`, so its peaks are not deep in a cusp.
  have F_level : star (F : New.G D.E (D.signsW j) → ℂ) ∈
      rapidOfLevel (D.spaceW j) (D.M * sqrtNegDInE P D.towerExp) :=
    star_mem_rapidOfLevel
      (goodForms_mem_rapidOfLevel F (.mul_right ⟨_, D.piM_mul_star.symm⟩ _))
  have gap_one (τ : D.Φ) : HasHolGap (D.signsW j) (conjHolomorphicWeight j τ) 1 := fun a b ha hb ↦
    by
    have h_one : 1 ≤ 300 * nStar D := by linarith [D.nStar_pos]
    exact le_trans (by gcongr) (hasHolGap_conjHolomorphicWeight j τ a b ha hb)
  have peak_min {g : New.G D.E (D.signsW j)} (hg : IsPeak (fun g ↦ star (F.1.1 g)) g) :
      (√(5 * D.b * D.b ^ 23))⁻¹ ≤ ((D.spaceW j).move g).firstMinimum :=
    hg.le_firstMinimum _ _ isPosFirstOrder_orderW gap_one (abs_conjHolomorphicWeight_le j)
      D.le_of_hasLogBound D.le_of_hasLogBound (by simp [star_sqrtNegDInE])
      (by simpa [NeZero.pos] using D.le_of_hasLogBound) F_level.1.1.rat_mul
      (apply_mul_of_mem_rapidOfLevel F_level) (isAdelicHol_star_goodForms F)
  obtain ⟨g, g_peak⟩ := exists_isPeak_of_mem_rapidOfLevel F_level F_ne
  have F₀_small : ‖F₀ 1‖ ≤
      (4 * D.b ^ nStar D + 1) * (2 * (D.b ^ (19 * nStar D))⁻¹ * ‖F₀ 1‖) := by
    refine norm_apply_one_le_of_forall_isPeak h_rank isPosFirstOrder_orderW
      (isKDominant_conjHolomorphicWeight j)
      (isKDominant_kernelWeight j) (hasHolGap_conjHolomorphicWeight j) (hasHolGap_kernelWeight j)
      (abs_conjHolomorphicWeight_le j) F.1.1.2.continuous.star (isAdelicHol_star_goodForms F) g_peak
        F₀_le
      fun x hx ↦ ?_
    obtain ⟨c, close⟩ := near x (peak_min hx)
    refine ⟨fun h ↦ ∑ i, c i * choiceFn j i (x * (h, 1)),
      .sum _ fun i ↦ isAdelicHol_choiceFn i x, close, ?_⟩
    simpa only [star_star] using integral_mul_sum_choiceFn_eq_zero F h_orth
      (integrable_holMinorsPi h_rank isPosFirstOrder_orderW (isKDominant_kernelWeight j)
        (hasHolGap_kernelWeight j)) c x
  -- This is absurd: with `B = b ^ n_* > 10` we have `(4 B + 1) 2 < B ^ 2 ≤ B ^ 19`.
  have h_pow : 10 < D.b ^ nStar D :=
    have hb : 10 < D.b := D.lt_of_hasLogBound
    hb.trans_le (le_self_pow₀ (by linarith) D.nStar_pos.ne')
  have h_lt : (4 * D.b ^ nStar D + 1) * (2 * (D.b ^ (19 * nStar D))⁻¹) < 1 := by
    rw [← mul_assoc, mul_inv_lt_iff₀ (by positivity), one_mul, mul_comm 19, pow_mul D.b (nStar D)]
    calc (4 * D.b ^ nStar D + 1) * 2 < (D.b ^ nStar D) ^ 2 := by nlinarith
      _ ≤ (D.b ^ nStar D) ^ 19 := pow_le_pow_right₀ (by linarith) (by norm_num)
  nlinarith [norm_pos_iff.2 F₀_ne]

end Separation

end New.Data
