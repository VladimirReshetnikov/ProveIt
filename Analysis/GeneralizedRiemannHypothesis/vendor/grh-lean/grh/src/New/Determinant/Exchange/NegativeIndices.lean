import Lib.Weil.Periods.DescentVanishing

/-!
# Theta coefficients vanish off negative forms

This file finds a unit vector, supported on the negative signs, that kills the columns of a
frame. The rotations of its line lie in the maximal compact subgroup of `U (signMatrix s)`. It
shows that a polynomial whose Fock vector is fixed by the compact stabiliser of the frame is zero.
It proves that right translation by an element of a compact subgroup preserves the left Haar
measure. Here `New.Exchange.negCount s` is the number of signs `-1`.

## Main definitions and results

* `New.Exchange.centreCoeff_eq_zero_of_not_representedBy`: a Fourier coefficient of the theta
  integral `New.Exchange.thetaIntegral` vanishes, under conditions on weights, signs and
  integrability, at an invertible form that fails to be negative definite at some real place. After
  unfolding, the coefficient is an integral modulo the stabiliser of a frame, and the mean of the
  integrand over a compact subgroup is an invariant functional on Fock space, which is zero.
* `New.Exchange.apply_eq_zero_of_forall_fixed_eq_zero`: let a compact group act by bounded operators
  `ρ g` on a Banach space, and let `W` be a stable subspace of finite dimension in which only `0` is
  fixed. Then an invariant bounded functional `l` vanishes at every vector of `W` with continuous
  orbit: the mean of the orbit is a fixed vector of `W`.

Notions from other files:
* `thetaIntegral S T α β f`: the integral over `[U(T)]` of the theta kernel of the datum `f`.
* `PairFock E s t`, `realPairWeil`: the Fock space of the pair and its real Weil representation.

## Relation to the literature

See `New.Determinant.Exchange.TheoremForPartners` for related work.
-/

section NonnegativeVanishing

open New Matrix MeasureTheory Measure Space Pointwise Pi Fintype MulAction ComplexConjugate
  ComplexOrder MatrixOrder Fock Heisenberg.IsVacuum Finset CStarAlgebra Exchange DiscreteSeries

section Rotation

open MvPolynomial hiding funext_iff

variable {E : Type} [Field E] [NumberField E] {a b n : Type} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n] {s : n → ℤˣ} {t : a → ℤˣ}
  {μ : NumberField.InfinitePlace E → ℤ}

/-- Let `s` be a vector of signs and `U (signMatrix s)` the unitary group of the diagonal Hermitian
form with entries `s` (`u.val.val` is the matrix of `u`). If the Gram matrix of the columns of `x`
for this form is not of the form `-cᴴ * c` for any `c`, then some element of the group carries a
vector in the span of the columns to the positive basis vector `i`. -/
lemma New.Exchange.exists_unitary_mulVec_eq_single {i : n} (hs_pos : s i = 1) {x : Matrix n b ℂ}
    (hx : ¬∃ c : Matrix b b ℂ, cᴴ * signMatrix (-1 : b → ℤˣ) * c = xᴴ * signMatrix s * x) :
    ∃ (u : U (signMatrix s)) (v : b → ℂ), (u.val.val * x) *ᵥ v = Pi.single i 1 := by
  have hs_herm : (signMatrix s)ᴴ = signMatrix s := Fock.conjTranspose_signMatrix
  have h_herm : (xᴴ * signMatrix s * x).IsHermitian := isHermitian_conjTranspose_mul_mul x hs_herm
  -- the Gram form is not negative semidefinite, so it represents `1`
  have h_not_nsd : ¬(-(xᴴ * signMatrix s * x)).PosSemidef := fun h_psd ↦ by
    obtain ⟨c, hc⟩ := nonneg_iff_eq_star_mul_self.mp h_psd.nonneg
    exact hx ⟨c, by simpa [neg_eq_iff_eq_neg, star_eq_conjTranspose] using hc.symm⟩
  obtain ⟨v, -, hv⟩ := exists_mem_dotProduct_mulVec_eq_one h_herm ⊤ fun h_nonpos ↦ h_not_nsd <|
    .of_dotProduct_mulVec_nonneg h_herm.neg fun v ↦ by simpa [neg_mulVec] using h_nonpos v trivial
  -- `x v` and the basis vector `i` both have length `1`, so Witt's theorem maps one to the other
  have x_length : star (x *ᵥ v) ⬝ᵥ signMatrix s *ᵥ x *ᵥ v = 1 := by
    rw [← hv, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have i_length : star (basisFun ℂ n i) ⬝ᵥ signMatrix s *ᵥ basisFun ℂ n i = 1 := by
    simp [signMatrix, hs_pos]
  obtain ⟨u, hu⟩ : ∃ u : U (signMatrix s),
      u.val.val * replicateCol Unit (x *ᵥ v) = replicateCol Unit (basisFun ℂ n i) := by
    refine witt ⟨.I, by simp⟩ hs_herm IsHermitianInvolution.isUnit
      (.of_ne_zero fun h ↦ by simp [h] at x_length) (.of_ne_zero ((basisFun ℂ n).ne_zero i)) ?_
    ext
    simp only [conjTranspose_replicateCol, ← replicateRow_vecMul,
      replicateRow_mul_replicateCol_apply, ← dotProduct_mulVec, x_length, i_length]
  exact ⟨u, v, by simpa [← replicateCol_mulVec] using hu⟩

/-- Let `s` have `card b` more negative signs than `t`, and let the positive basis vector `i` be in
the span of the columns of `x`. There is a unit vector `r`, supported on the negative signs of `s`,
that kills the columns of `x` and the columns `j` of `y` with `t j = -1`. -/
lemma New.Exchange.exists_unit_dotProduct_col_eq_zero {a b n : Type} [Fintype a] [Fintype b]
    [Fintype n] [DecidableEq n] {s : n → ℤˣ} {t : a → ℤˣ} {i : n} (hs_pos : s i = 1)
    (h_negCount : Fintype.card b + negCount t = negCount s) {x : Matrix n b ℂ} {v : b → ℂ}
    (hv : x *ᵥ v = Pi.single i 1) (y : n → a → ℂ) :
    ∃ r : n → ℂ, (∀ j : b, (r ⬝ᵥ fun k : n ↦ x k j) = 0) ∧
      (∀ j : a, t j = -1 → (r ⬝ᵥ fun k : n ↦ y k j) = 0) ∧
      (∀ k : n, s k ≠ -1 → r k = 0) ∧ r ⬝ᵥ star r = 1 := by
  -- the kernel of `f` is cut out by the three linear conditions
  let f : (n → ℂ) →ₗ[ℂ] ((b → ℂ) × ({j // t j = -1} → ℂ)) × ({k // s k ≠ -1} → ℂ) :=
    (x.vecMulLinear.prod (of fun k (j : {j // t j = -1}) ↦ y k j).vecMulLinear).prod
      (.funLeft ℂ ℂ Subtype.val)
  suffices h_ker : ∃ r ∈ f.ker, star r ⬝ᵥ (1 : Matrix n n ℂ) *ᵥ r = 1 by
    simpa [f, funext_iff, dotProduct_comm (star _), and_assoc, vecMul] using h_ker
  -- otherwise `f` is injective, so onto by `h_negCount`; but `hv` ties two of its coordinates
  refine exists_mem_dotProduct_mulVec_eq_one isHermitian_one f.ker fun h_nonpos ↦ ?_
  have f_inj : Function.Injective f := (injective_iff_map_eq_zero f).2 fun r hr ↦ by
    simpa [(dotProduct_star_self_nonneg r).ge_iff_eq'] using h_nonpos r hr
  have h_rank : Module.finrank ℂ (n → ℂ) =
      Module.finrank ℂ (((b → ℂ) × ({j // t j = -1} → ℂ)) × ({k // s k ≠ -1} → ℂ)) := by
    have h_count : card b + card {j // t j = -1} = card {k // s k = -1} := h_negCount
    simp [h_count, Nat.add_sub_cancel' (card_subtype_le _)]
  obtain ⟨r, hr⟩ : ∃ r : n → ℂ, f r = (0, 1) := (f.linearEquivOfInjective f_inj h_rank).surjective _
  obtain ⟨⟨r_x, -⟩, r_eq_one⟩ : (r ᵥ* x = 0 ∧ ∀ j : a, t j = -1 → (r ⬝ᵥ fun k ↦ y k j) = 0) ∧
      ∀ k : n, s k ≠ -1 → r k = 1 := by
    simpa [f, funext_iff, vecMul] using hr
  have h_coord : r i = r ᵥ* x ⬝ᵥ v := by simp [← dotProduct_mulVec, hv]
  simp [r_x, r_eq_one i (by simp [hs_pos])] at h_coord

/-- Let `s` be a vector of signs and `U (signMatrix s)` the unitary group of the diagonal Hermitian
form with entries `s`; its maximal compact subgroup `maxCompactU s` consists of its elements that
are also unitary for the standard form. Let `r` be a unit vector supported on the negative signs,
and `|η| = 1`. The rotation by `conj η` of the line of `star r` lies in `maxCompactU s`. -/
lemma New.Exchange.exists_mem_maxCompactU_eq_rotation {r : n → ℂ}
    (r_supp : ∀ k : n, s k ≠ -1 → r k = 0) (r_unit : r ⬝ᵥ star r = 1) {η : ℂ}
    (hη : η * conj η = 1) :
    ∃ c ∈ maxCompactU s, c.val.val = 1 + (conj η - 1) • vecMulVec (star r) r := by
  set P : Matrix n n ℂ := vecMulVec (star r) r with hP
  have P_herm : Pᴴ = P := by simp [hP]
  have P_sq : P * P = P := by simp [hP, vecMulVec_mul_vecMulVec, r_unit]
  have sign_P : signMatrix s * P = -P := by
    ext j k
    by_cases hj : s j = -1 <;> simp [hP, signMatrix, vecMulVec_apply, hj, r_supp j]
  have P_sign : P * signMatrix s = -P := by simpa [P_herm] using congrArg conjTranspose sign_P
  have h_adjoint : (1 + (conj η - 1) • P)ᴴ = 1 + (η - 1) • P := by simp [P_herm]
  -- the rotation preserves every form `J` with `J * P = P * J = ε • P`, as `η * conj η = 1`
  have h_form {J : Matrix n n ℂ} (ε : ℂ) (h_left : J * P = ε • P) (h_right : P * J = ε • P) :
      (1 + (conj η - 1) • P)ᴴ * J * (1 + (conj η - 1) • P) = J := by
    simp only [h_adjoint, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      h_left, h_right, P_sq]
    linear_combination (norm := module) hη • ε • P
  exact ⟨U.of IsHermitianInvolution.isUnit _ (h_form (-1) (by simp [sign_P]) (by simp [P_sign])),
    h_form 1 (by simp) (by simp), rfl⟩

open NumberField (InfinitePlace)

omit [NumberField E] in
/-- An element of the maximal compact subgroup, placed at `τ`, is block diagonal at every place. -/
lemma New.Exchange.mulSingle_mem_blockDiagAlg (τ : InfinitePlace E) {c : U (signMatrix s)}
    (c_mem : c ∈ maxCompactU s) (w : InfinitePlace E) :
    ((mulSingle τ c : GInf E s) w).val.val ∈ blockDiagAlg s := by
  obtain rfl | hw := eq_or_ne w τ <;> simp [mem_maxCompactU.mp c_mem, *]

/-- Let `c` be the rotation by `conj η`, `|η| = 1`, of the line of `star r`, for a unit vector `r`
supported on the negative signs of `s`. Placed at `τ`, it acts on the vector of `P` by a
substitution times `η ^ N`, where `N` is the number of positive signs of `t` minus `μ τ`. For each
`j` the substitution multiplies `∑ i, conj (r i) • X (τ, i, j)` by `conj η` if `t j = -1`, and
`∑ i, r i • X (τ, i, j)` by `η` if `t j = 1`. It fixes the combinations of the `X (τ, i, j)`
orthogonal to these, and all variables at other places. -/
lemma New.Exchange.realPairWeil_rotation_polyVector {τ : InfinitePlace E} {N : ℕ}
    (hN : μ τ + N = negCount (-t)) {r : n → ℂ} (r_supp : ∀ k : n, s k ≠ -1 → r k = 0)
    (r_unit : r ⬝ᵥ star r = 1) {η : ℂ} (hη : η * conj η = 1) {c : U (signMatrix s)}
    (c_mem : c ∈ maxCompactU s) (hc : c.val.val = 1 + (conj η - 1) • vecMulVec (star r) r)
    (P : MvPolynomial (InfinitePlace E × n × a) ℂ) :
    realPairWeil μ 0 (1, mulSingle τ c) (polyVector (realSigns E (homSigns t s)) P) =
      η ^ N • polyVector (realSigns E (homSigns t s)) (aeval (fun (w, k, j) ↦ X (w, k, j) +
        if w ≠ τ then 0
        else if t j = -1 then ((conj η - 1) * r k) • ∑ i : n, conj (r i) • X (τ, i, j)
        else ((η - 1) * conj (r k)) • ∑ i : n, r i • X (τ, i, j)) P) := by
  have c_inv : c⁻¹.val.val = 1 + (η - 1) • vecMulVec (star r) r :=
    ((coe_units_inv c.val).trans (maxCompactU.coe_inv ⟨c, c_mem⟩)).trans (by simp [hc])
  -- the positive block of `c` is `1`, and the negative block has determinant `η⁻¹`
  have pos_det : principalMinor c.val.val (s · = 1) = 1 := by
    have proj_r : posProj s *ᵥ star r = 0 := by
      simp +contextual [funext_iff, posProj, r_supp, mulVec]
    simp [hc, principalMinor_eq_det, ← posProj.eq_1, mul_vecMulVec, proj_r]
  have neg_det : principalMinor c.val.val (s · = -1) = η⁻¹ := by
    have neg_r : (diagonal fun k : n ↦ if s k = -1 then (1 : ℂ) else 0) *ᵥ star r = star r :=
      funext fun k ↦ by simpa [mulVec_diagonal, eq_comm (a := (0 : ℂ))] using r_supp k
    -- a rank one update of the identity
    have c_det : (1 + (conj η - 1) • vecMulVec (star r) r).det = η⁻¹ := by
      rw [← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_mul_comm]
      simp [r_unit, eq_inv_of_mul_eq_one_right hη]
    simp [hc, principalMinor_eq_det, mul_vecMulVec, neg_r, c_det]
  rw [realPairWeil_polyVector (hx := by simp) (hy := mulSingle_mem_blockDiagAlg τ c_mem),
    Fintype.prod_eq_single τ fun w hw ↦ by simp [hw]]
  congr 1
  · simp [pos_det, neg_det, eq_sub_of_add_eq hN, negCount]
  -- a variable is moved by a column of `c` if `s k = t j`, and by a row of `c⁻¹` otherwise
  refine congrArg (fun σ ↦ polyVector _ (aeval σ P)) (funext fun ⟨w, k, j⟩ ↦ ?_)
  obtain rfl | hw := eq_or_ne w τ
  · simp only [mulSingle_eq_same, c_inv, hc]
    by_cases hk : s k = -1
    · by_cases hj : t j = -1 <;>
        simp [hk, hj, eq_comm (a := (-1 : ℤˣ)), Matrix.one_apply, vecMulVec_apply, add_smul,
          sum_add_distrib, smul_sum, smul_smul, mul_assoc, mul_comm (r k)]
    · simp [r_supp k hk, Matrix.one_apply, vecMulVec_apply]
  · simp [hw, Matrix.one_apply]

/-- Let `μ τ` be less than the number `negCount (-t)` of positive signs of `t`, and let `r` be a
unit vector supported on the negative signs of `s`. If the elements `1 + δ • star r rᵀ` of the
maximal compact subgroup `maxCompactU s`, placed at `τ` (`mulSingle`) and `1` elsewhere, fix the
vector of `P`, then `P` vanishes at every point `z` at which the variables
`∑ k, conj (r k) • X (τ, k, j)` with `t j = -1` vanish. -/
lemma New.Exchange.eval_eq_zero_of_rotation_fixed {τ : InfinitePlace E}
    (hμ : μ τ < negCount (-t)) {r : n → ℂ} (r_supp : ∀ k : n, s k ≠ -1 → r k = 0)
    (r_unit : r ⬝ᵥ star r = 1) {P : MvPolynomial (InfinitePlace E × n × a) ℂ}
    (h_fixed : ∀ c ∈ maxCompactU s, ∀ δ : ℂ, c.val.val = 1 + δ • vecMulVec (star r) r →
      realPairWeil μ 0 (1, mulSingle τ c) (polyVector (realSigns E (homSigns t s)) P) =
        polyVector (realSigns E (homSigns t s)) P)
    {z : InfinitePlace E × n × a → ℂ}
    (hz : ∀ j : a, t j = -1 → ∑ k : n, conj (r k) * z (τ, k, j) = 0) : eval z P = 0 := by
  -- At `z` the rotation by `conj η` brings in only nonnegative powers of `η`, and the vacuum a
  -- positive power. So `eval z P` is the value on the unit circle of a polynomial `g` with
  -- `g 0 = 0`, which is zero by the mean value property.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, μ τ + M.succ = negCount (-t) := hμ.dest
  -- the substitution moves `z` to `z + (η - 1) • z'`
  let z' : InfinitePlace E × n × a → ℂ := fun (w, k, j) ↦
    if w ≠ τ ∨ t j = -1 then 0 else conj (r k) * ∑ i : n, r i * z (τ, i, j)
  let g (η : ℂ) : ℂ := η ^ M.succ * eval (z + (η - 1) • z') P
  have h_circle (η : ℂ) (hη : η * conj η = 1) : g η = eval z P := by
    obtain ⟨c, c_mem, hc⟩ := exists_mem_maxCompactU_eq_rotation r_supp r_unit hη
    let σ : InfinitePlace E × n × a → MvPolynomial (InfinitePlace E × n × a) ℂ :=
      fun (w, k, j) ↦ X (w, k, j) + if w ≠ τ then 0
        else if t j = -1 then ((conj η - 1) * r k) • ∑ i : n, conj (r i) • X (τ, i, j)
        else ((η - 1) * conj (r k)) • ∑ i : n, r i • X (τ, i, j)
    have h_poly : η ^ M.succ • aeval σ P = P :=
      polyVector_injective (ε := realSigns E (homSigns t s)) <| by
        rw [map_smul, ← realPairWeil_rotation_polyVector hM r_supp r_unit hη c_mem hc,
          h_fixed c c_mem _ hc]
    have h_point : (fun p ↦ aeval z (σ p)) = z + (η - 1) • z' := by
      funext ⟨w, k, j⟩
      by_cases hw : w = τ <;> by_cases hj : t j = -1 <;> simp [σ, z', hw, hj, hz j, mul_assoc]
    calc g η = η ^ M.succ * aeval z (aeval σ P) := by rw [comp_aeval_apply, h_point, aeval_eq_eval]
      _ = eval z P := by rw [aeval_eq_eval, ← smul_eval, h_poly]
  have g_diff : Differentiable ℂ g := by simpa only [g, eval_eq'] using by fun_prop
  calc eval z P = ∫ θ : UnitAddCircle, g θ.toCircle := by
        simp [h_circle, Circle.norm_coe, RCLike.mul_conj, Measure.real]
    _ = 0 := by simp [integral_comp_toCircle_eq_apply_zero g_diff.differentiableOn, g]

/-- Let a compact group act by bounded operators `ρ g` on a Banach space, and let `W` be a stable
subspace of finite dimension in which only `0` is fixed. Then an invariant bounded functional `l`
vanishes at every vector of `W` with continuous orbit: the mean of the orbit is a fixed vector of
`W`. -/
lemma New.Exchange.apply_eq_zero_of_forall_fixed_eq_zero {G V : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] (ρ : G →* V →L[ℂ] V) {W : Submodule ℂ V}
    [FiniteDimensional ℂ W] (h_stable : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W)
    (h_fixed : ∀ w ∈ W, (∀ g : G, ρ g w = w) → w = 0) {l : V →L[ℂ] ℂ}
    (l_inv : ∀ (g : G) (v : V), l (ρ g v) = l v) {v : V} (hv : v ∈ W)
    (h_cont : Continuous fun g : G ↦ ρ g v) : l v = 0 := by
  borelize G
  let κ : Measure G := haarMeasure ⊤
  have : IsProbabilityMeasure κ := ⟨haarMeasure_self⟩
  have h_int : Integrable (fun g : G ↦ ρ g v) κ := integrable_of_compactSpace h_cont
  have mean_mem : ∫ g : G, ρ g v ∂κ ∈ W :=
    (W.restrictScalars ℝ).convex.integral_mem W.closed_of_finiteDimensional
      (.of_forall fun g ↦ h_stable g v hv) h_int
  have mean_fixed (k : G) : ρ k (∫ g : G, ρ g v ∂κ) = ∫ g : G, ρ g v ∂κ := by
    simpa [← (ρ k).integral_comp_comm h_int] using integral_mul_left_eq_self (ρ · v) k
  calc l v = l (∫ g : G, ρ g v ∂κ) := by simp [← l.integral_comp_comm h_int, l_inv]
    _ = 0 := by rw [h_fixed _ mean_mem mean_fixed, map_zero]

omit [DecidableEq b] in
/-- Let the weight `μ τ` be less than the number `negCount (-t)` of positive signs of `t`. Let `s`
have `card b` more negative signs than `t`, and let the positive basis vector `i` be in the span of
the columns of `x`. Suppose every `c` in `maxCompactU s` with `c * x = x`, placed at `τ` and acting
by `realPairWeil μ 0`, fixes the Fock vector `polyVector` of a polynomial `P`. Then `P = 0`. -/
lemma New.Exchange.eq_zero_of_stabilizer_fixes_polyVector {τ : InfinitePlace E}
    (hμ : μ τ < negCount (-t)) {i : n} (hs_pos : s i = 1)
    (h_negCount : Fintype.card b + negCount t = negCount s) {x : Matrix n b ℂ} {v : b → ℂ}
    (hv : x *ᵥ v = Pi.single i 1) {P : MvPolynomial (InfinitePlace E × n × a) ℂ}
    (h_fixed : ∀ c ∈ maxCompactU s, c.val.val * x = x →
      realPairWeil μ 0 (1, mulSingle τ c) (polyVector (realSigns E (homSigns t s)) P) =
        polyVector (realSigns E (homSigns t s)) P) : P = 0 := by
  -- For each point `z`, counting dimensions gives a line in the span of the negative basis vectors,
  -- spanned by `star r`, that is orthogonal to `x` and whose variables with `t j = -1` vanish at
  -- `z`. The rotations of this line fix `x`.
  refine MvPolynomial.funext fun z ↦ ?_
  obtain ⟨r, r_x, r_z, r_supp, r_unit⟩ :=
    exists_unit_dotProduct_col_eq_zero hs_pos h_negCount hv fun k j ↦ conj (z (τ, k, j))
  have rotation_fixes (δ : ℂ) : (1 + δ • vecMulVec (star r) r) * x = x := by
    simp [← Matrix.ext_iff, r_x, Matrix.add_mul, vecMulVec_mul, vecMulVec_apply, vecMul]
  have hz (j : a) (hj : t j = -1) : ∑ k : n, conj (r k) * z (τ, k, j) = 0 := by
    simpa [dotProduct] using congrArg conj (r_z j hj)
  refine eval_eq_zero_of_rotation_fixed hμ r_supp r_unit (fun c c_mem δ hc ↦ ?_) hz
  exact h_fixed c c_mem (by rw [hc, rotation_fixes])

/-- An element `c` of the maximal compact subgroup, placed at `τ`, maps the Fock vector of a
homogeneous polynomial of degree `d` to the Fock vector of another such polynomial. -/
lemma New.Exchange.realPairWeil_mulSingle_mem_map_homogeneousSubmodule (τ : InfinitePlace E)
    {c : U (signMatrix s)} (c_mem : c ∈ maxCompactU s) {d : ℕ}
    {P : MvPolynomial (InfinitePlace E × n × a) ℂ} (hP : P.IsHomogeneous d) :
    realPairWeil μ 0 (1, mulSingle τ c) (polyVector (realSigns E (homSigns t s)) P) ∈
      (homogeneousSubmodule (InfinitePlace E × n × a) ℂ d).map
        (polyVector (realSigns E (homSigns t s))) := by
  -- `c` acts by a scalar times a linear substitution, which keeps the degree
  rw [realPairWeil_polyVector (hx := by simp) (hy := mulSingle_mem_blockDiagAlg τ c_mem)]
  refine Submodule.smul_mem _ _ (Submodule.mem_map_of_mem ?_)
  rw [mem_homogeneousSubmodule, ← one_mul d]
  refine hP.aeval _ fun p ↦ ?_
  -- each variable goes to a linear form
  exact IsHomogeneous.sum _ _ 1 fun i _ ↦ IsHomogeneous.sum _ _ 1 fun j _ ↦
    (homogeneousSubmodule _ ℂ 1).smul_mem _ (isHomogeneous_X ℂ _)

/-- Let the weight `μ τ` be less than the number `negCount (-t)` of positive signs of `t`. Let `s`
have a positive sign, and `card b` more negative signs than `t`. Let the Gram matrix of the columns
of `x` not be of the form `-cᴴ * c`. For some isometry `u` at the place `τ`, a functional on Fock
space that is invariant under the compact stabiliser of `u * x`, acting by the real Weil
representation of weight `μ` (`realPairWeil`), is zero. -/
lemma New.Exchange.exists_isometry_fock_functional_eq_zero (τ : InfinitePlace E)
    (hμ : μ τ < negCount (-t)) {i : n} (hs_pos : s i = 1)
    (h_negCount : Fintype.card b + negCount t = negCount s) {x : Matrix n b ℂ}
    (hx : ¬∃ c : Matrix b b ℂ, cᴴ * signMatrix (-1 : b → ℤˣ) * c = xᴴ * signMatrix s * x) :
    ∃ u : U (signMatrix s), ∀ l : PairFock E t s →L[ℂ] ℂ,
      (∀ c ∈ maxCompactU s, c.val.val * (u.val.val * x) = u.val.val * x →
        ∀ v : PairFock E t s, l (realPairWeil μ 0 (1, mulSingle τ c) v) = l v) → l = 0 := by
  -- By Witt's theorem choose `u` with the positive basis vector `i` in the span of `u x`. The
  -- compact stabiliser `C` of `u x` acts on the polynomial vectors of each degree, and these span
  -- a dense subspace, so it suffices that `C` fixes no nonzero polynomial vector.
  obtain ⟨u, v, hu⟩ := exists_unitary_mulVec_eq_single hs_pos hx
  refine ⟨u, fun l l_inv ↦ ?_⟩
  let C : Subgroup (maxCompactU s) := stabilizer (maxCompactU s) (u.val.val * x)
  have hC : IsClosed (C : Set (maxCompactU s)) := isClosed_singleton.preimage
    (f := fun c : maxCompactU s ↦ c.val.val.val * (u.val.val * x)) (by fun_prop)
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  let ρ : C →* PairFock E t s →L[ℂ] PairFock E t s := (realPairWeil μ 0).comp <|
    (MonoidHom.inr _ _).comp <| (MonoidHom.mulSingle _ τ).comp <|
      (maxCompactU s).subtype.comp C.subtype
  let ε : InfinitePlace E × n × a → ℤˣ := realSigns E (homSigns t s)
  have homogeneous_zero (d : ℕ) (P : MvPolynomial (InfinitePlace E × n × a) ℂ)
      (hP : P.IsHomogeneous d) : l (polyVector ε P) = 0 := by
    let W : Submodule ℂ (PairFock E t s) := (homogeneousSubmodule _ ℂ d).map (polyVector ε)
    have : FiniteDimensional ℂ W := Module.Finite.of_fg ((homogeneousSubmodule_fg _ ℂ d).map _)
    have h_stable (c : C) : ∀ w ∈ W, ρ c w ∈ W := by
      rintro _ ⟨Q, hQ, rfl⟩
      exact realPairWeil_mulSingle_mem_map_homogeneousSubmodule τ c.val.prop hQ
    have h_fixed : ∀ w ∈ W, (∀ c : C, ρ c w = w) → w = 0 := by
      rintro _ ⟨Q, -, rfl⟩ hQ
      rw [eq_zero_of_stabilizer_fixes_polyVector (P := Q) hμ hs_pos h_negCount hu
        fun c c_mem c_fix ↦ hQ ⟨⟨c, c_mem⟩, c_fix⟩, map_zero]
    have h_cont : Continuous fun c : C ↦
        realPairWeil μ 0 (1, mulSingle τ c.val.val) (polyVector ε P) := by
      have := continuous_mulSingle (A := fun _ : InfinitePlace E ↦ U (signMatrix s)) τ
      fun_prop
    exact apply_eq_zero_of_forall_fixed_eq_zero ρ h_stable h_fixed
      (fun ⟨⟨c, c_mem⟩, c_fix⟩ ↦ l_inv c c_mem c_fix) (Submodule.mem_map_of_mem hP) h_cont
  -- a polynomial is the sum of its homogeneous components, and polynomial vectors are dense
  refine ContinuousLinearMap.ext (isClosed_property denseRange_polyVector l.isClosed_ker fun P ↦ ?_)
  rw [← P.sum_homogeneousComponent, _root_.map_sum]
  exact l.ker.sum_mem fun d _ ↦ homogeneous_zero d _ (homogeneousComponent_isHomogeneous d P)

end Rotation

open NumberField (InfinitePlace)

/-- Right translation by an element of a compact subgroup preserves the left Haar measure of a
locally compact group: the modular function is `1` on compact subgroups. -/
lemma New.Exchange.haar_map_mul_right_of_isCompact {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] {C : Subgroup H} (hC : IsCompact (C : Set H)) (k : C) :
    (haar : Measure H).map (· * (k : H)) = haar := by
  -- both sides are Haar measures, and they agree on the compact neighbourhood `A * C`, which is
  -- stable under right translation by `k`
  obtain ⟨A, hA, hCA⟩ := exists_compact_superset hC
  let K : TopologicalSpace.PositiveCompacts H := ⟨⟨A * C, hA.mul hC⟩,
    (k : H) * k, subset_interior_mul_left (Set.mul_mem_mul (hCA k.prop) k.prop)⟩
  have h_eq : (haar : Measure H).map (· * (k : H)) K = haar (K : Set H) := by
    simp [K, Set.preimage, (measurableEmbedding_mulRight _).map_apply,
      ← QuotientGroup.preimage_image_mk_eq_mul]
  rw [haarMeasure_unique (map _ _) K, h_eq, ← haarMeasure_unique]

variable {E : Type} [Field E] [CMType E] [H : WeilData E] {a b m n : Type} [Fintype a]
  [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m] [Fintype n]
  [DecidableEq n]

omit [DecidableEq b] in
/-- Let `C` be the elements of the stabiliser of an adelic frame `x'` that lie in the conjugate of
`maxCompact E s` by `u⁻¹` at the real place `τ`, with an invariant probability measure `κ`. Suppose
that only the zero functional on Fock space is invariant, for the weight `μ` of `ν`, under the
compact stabiliser of `u x'` at `τ`. Then the theta functional `θ` of the Weil representation with
characters `ν`, `δ` has mean zero over `k C u⁻¹`. -/
lemma New.Exchange.integral_theta_pairWeil_stabilizer_eq_zero {s : n → ℤˣ} {t : a → ℤˣ}
    {Y : Space E n s} {Z : Space E a t} {μ : InfinitePlace E → ℤ}
    {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ} (ν δ : AutChar E) [AutChar.HasWeight ν μ ψ]
    {x' : Matrix n b (𝔸 E)} {τ : InfinitePlace E} {u : U (signMatrix s)}
    (h_no_invariant_functional : ∀ l : PairFock E t s →L[ℂ] ℂ, (∀ c ∈ maxCompactU s,
      c.val.val * (u.val.val * atRealPlace x' τ) = u.val.val * atRealPlace x' τ →
        ∀ v : PairFock E t s, l (realPairWeil μ 0 (1, mulSingle τ c) v) = l v) → l = 0)
    (κ : Measure ((ConjAct.toConjAct ((mulSingle τ u⁻¹, 1) : G E s) • maxCompact E s).subgroupOf
      (stabilizer (G E s) x')))
    [IsProbabilityMeasure κ] [κ.IsMulRightInvariant] (k : stabilizer (G E s) x') (φ : 𝒮 (Z.hom Y)) :
    ∫ c, θ (Z.hom Y) (pairWeil Z Y ν δ (1, (k : G E s) *
      (((c : stabilizer (G E s) x') : G E s) * ((mulSingle τ u⁻¹, 1) : G E s))) φ) ∂κ = 0 := by
  -- The mean is a bounded functional. On data with a fixed finite part it is invariant under the
  -- compact stabiliser at `τ`, so it is zero by `h_no_invariant_functional`; such data determine
  -- it.
  let S : Subgroup (G E s) := stabilizer (G E s) x'
  let w : G E s := (mulSingle τ u⁻¹, 1)
  let C : Subgroup S := (ConjAct.toConjAct w • maxCompact E s).subgroupOf S
  have hS : IsClosed (S : Set (G E s)) :=
    isClosed_singleton.preimage (f := fun h : G E s ↦ G.adeleMatrix h * x') (by fun_prop)
  have hC : IsCompact (C : Set S) := (isCompact_maxCompact.smul _).preimage_val
  have : CompactSpace C := isCompact_iff_compactSpace.1 hC
  let A (c : C) : 𝒮 (Z.hom Y) →L[ℂ] ℂ := θ (Z.hom Y) ∘L pairWeil Z Y ν δ (1, k * (c * w))
  have hA (f : 𝒮 (Z.hom Y)) : Continuous fun c : C ↦ A c f := by
    simp only [A, ContinuousLinearMap.comp_apply]
    fun_prop
  have h_apply (f : 𝒮 (Z.hom Y)) : strongIntegral κ A f = ∫ c : C, A c f ∂κ :=
    strongIntegral_apply κ A (fun f' ↦ integrable_of_compactSpace (hA f')) f
  -- the functional `v ↦ mean (v ⊗ f)` on Fock space is zero
  have h_fock_zero (f : 𝒮 (Z.hom Y)) : strongIntegral κ A ∘L (Z.hom Y).integrated.flip f = 0 := by
    refine h_no_invariant_functional _ fun c hc hcx v ↦ ?_
    let p : G E s := w * (mulSingle τ c, 1) * w⁻¹
    have hpS : p ∈ S := by
      refine matrix_ext_𝔸 (fun τ' ↦ Matrix.map_mul.trans ?_) (Matrix.map_mul.trans ?_)
      · change (p.1 τ' : Matrix n n ℂ) * atRealPlace x' τ' = atRealPlace x' τ'
        obtain rfl | h_ne := eq_or_ne τ' τ
        · simp [p, w, hcx, Matrix.mul_assoc]
        · simp [p, w, h_ne]
      · have hp_fin : (G.adeleMatrix p).map Prod.snd = 1 := by ext; simp [p, w, mul_assoc]
        exact (congrArg (· * x'.map Prod.snd) hp_fin).trans (Matrix.one_mul _)
    have hpC : (⟨p, hpS⟩ : S) ∈ C := ⟨(mulSingle τ c, 1), ⟨by simpa, by simp⟩, rfl⟩
    -- the integral is unchanged when `c'` is replaced by `c' * p`
    have h_translate (f' : 𝒮 (Z.hom Y)) :
        ∫ c' : C, A (c' * ⟨⟨p, hpS⟩, hpC⟩) f' ∂κ = ∫ c' : C, A c' f' ∂κ :=
      integral_mul_right_eq_self (A · f') _
    simpa [← pairWeil_integrated_right ν δ, h_apply, A, p, rep_apply_apply, mul_assoc] using
      h_translate _
  have h_zero : strongIntegral κ A φ = 0 :=
    Space.map_eq_zero_of_map_integrated_eq_zero (Z.hom Y) (Space.projOn_empty _ φ) fun P y _ ↦
      DFunLike.congr_fun (h_fock_zero ((Z.hom Y).finHeisenbergOp y (Z.hom Y).vacElem))
        (polyVector _ P)
  simpa [h_apply, A] using h_zero

/-- Let the splitting `D` write `X` as the sum of two dual isotropic subspaces of rank `#b` and of
`Z`, orthogonal to both. The slice at `x'` (`D.homSlice`) is the map from data on `Hom(X, Y)` to
data on `Hom(Z, Y)` that takes the value `x'` on one of the two subspaces. An element `k` of the
stabiliser of `x'` in `U(Y)` commutes with it: on the slice it acts by the Weil representation of
the smaller pair `(Z, Y)`, with the character `ν` if `δ = ν υ ^ #b`, for `υ` the character
`upsilonU1` of the Weil data. -/
lemma New.Exchange.homSlice_pairWeil_stabilizer_mul {r : m → ℤˣ} {s : n → ℤˣ} {t : a → ℤˣ}
    {X : Space E m r} {Y : Space E n s} {Z : Space E a t} (D : X.Splitting Z b) {ν δ : AutChar E}
    (hδ : δ = ν * H.upsilonU1 ^ Fintype.card b) {x' : Matrix n b (𝔸 E)}
    (k : stabilizer (G E s) x') (g : G E r) (h : G E s) (f : 𝒮 (X.hom Y)) :
    D.homSlice Y x' (pairWeil X Y δ δ (g, k * h) f) =
      pairWeil Z Y ν δ (1, k) (D.homSlice Y x' (pairWeil X Y δ δ (g, h) f)) := by
  have hk : k.1⁻¹.adeleMatrix * x' = x' := k⁻¹.2
  simpa [← hδ, -coe_units_inv, hk, Prod.mk_one_one, rep_apply_apply] using
    D.homSlice_levi Y ν δ 1 1 k x' (pairWeil X Y δ δ (g, h) f)

/-- The spaces `X`, `Y`, `Z` are Hermitian over `E` with Weil data `H`: a splitting Hecke character
`υ`, whose restriction to the norm-one ideles is `H.upsilonU1`, and a scalar `H.j` of `E` with
`conj j = -j`. Let the splitting `D` write `X` as the sum of two dual isotropic subspaces of rank
`#b` and of `Z`, orthogonal to both. (a) The weights `μ τ` are less than the number of positive
signs of `Z`; `Y` has a positive sign, and `#b` more negative signs than `Z`. (b) `ν` has weight
`μ`, with any tame part `ψ`, and `δ = ν H.upsilonU1 ^ #b`. (c) `T` is invertible and, at some real
place, not of the form `-cᴴ c` (`RepresentedBy` fails). (d) The sum over the rational frames of the
absolute values of the terms of the unfolded theta integral is integrable (`HasIntegrableTerms`).
The theta integral `thetaIntegral X Y δ δ f` integrates the kernel of `f` over `[U(Y)]`, in the Weil
representation of `(X, Y)` in which `δ` is the character of `U(1)` for both spaces: the first fixes
the action of `U(Y)`, the second that of `U(X)`. Then `centreCoeff` at `H.j • T` of this function on
`U(X)`, its Fourier coefficient along the centre of the unipotent radical of `D`, vanishes at `g`.
-/
lemma New.Exchange.centreCoeff_eq_zero_of_not_representedBy {r : m → ℤˣ} {ν : AutChar E}
    {X : Space E m r} {s : n → ℤˣ} {Y : Space E n s} {t : a → ℤˣ} {Z : Space E a t}
    {D : X.Splitting Z b} {μ : InfinitePlace E → ℤ} {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}
    {δ : AutChar E} {f : 𝒮 (X.hom Y)} {g : G E r} {T : Matrix b b E} [AutChar.HasWeight ν μ ψ]
    (i : n) (hμ : ∀ τ : InfinitePlace E, μ τ < negCount (-t)) (hs_pos : s i = 1)
    (h_negCount : Fintype.card b + negCount t = negCount s)
    (hδ : δ = ν * H.upsilonU1 ^ Fintype.card b) (hT_unit : IsUnit T)
    (hT_not_neg : ¬RepresentedBy (-1) (T.map toAdele)) (h_int : D.HasIntegrableTerms Y δ δ f g) :
    D.centreCoeff (H.j • T) (thetaIntegral X Y δ δ f) g = 0 := by
  -- If no rational frame has Gram matrix `T` the coefficient is an empty sum. Otherwise it is the
  -- integral of the term of one frame `x` modulo the rational stabiliser of `x`. The mean of the
  -- term over a compact subgroup `C` of the adelic stabiliser `S` gives an invariant functional
  -- on Fock space at a place `τ`, which is zero; so the integral vanishes.
  have h_integral : thetaIntegral X Y δ δ f =
      fun k ↦ ∫ h, pairTheta X Y δ δ f (k, h) * 1 ∂Y.quotMeasure := funext (by simp [thetaIntegral])
  rw [h_integral]
  obtain h_empty | ⟨x, rfl⟩ := isEmpty_or_nonempty {x : Matrix n b E | xᴴ * Y.J * x = T}
  · rw [D.centreCoeff_integral_eq_tsum h_int continuous_const T, tsum_empty]
  let x' : Matrix n b (𝔸 E) := Y.x⁻¹.val * x.map toAdele
  let S : Subgroup (G E s) := stabilizer (G E s) x'
  have hS : IsClosed (S : Set (G E s)) :=
    isClosed_singleton.preimage (f := fun h : G E s ↦ G.adeleMatrix h * x') (by fun_prop)
  have hΓS : Y.ratStabilizer x ≤ S := by
    rintro _ ⟨γ, hγ : (γ : Matrix n n E) * x = x, rfl⟩
    exact (Y.ratMap_mul_toAdele Y γ x).trans (by simp [x', hγ])
  have h_fixesLeft_one : Y.Γ.FixesLeft fun _ ↦ (1 : ℂ) := by simp
  -- a real place `τ` at which the Gram matrix is not negative, and the isometry `u` there
  obtain ⟨τ, hτ⟩ : ∃ τ : InfinitePlace E, ¬∃ c : Matrix b b ℂ,
      cᴴ * signMatrix (-1 : b → ℤˣ) * c = atRealPlace ((xᴴ * Y.J * x).map toAdele) τ :=
    not_forall.1 hT_not_neg
  rw [← gram_at_point_eq_map, ← gram_atRealPlace] at hτ
  obtain ⟨u, hu⟩ := exists_isometry_fock_functional_eq_zero τ (hμ τ) hs_pos h_negCount hτ
  -- `C` is the intersection of `S` with a conjugate of the maximal compact subgroup
  let w : G E s := (mulSingle τ u⁻¹, 1)
  let C : Subgroup S := (ConjAct.toConjAct w • maxCompact E s).subgroupOf S
  have hC : IsCompact (C : Set S) := (isCompact_maxCompact.smul _).preimage_val
  have : CompactSpace C := isCompact_iff_compactSpace.1 hC
  have : IsClosed (C : Set S) := hC.isClosed
  let κ : Measure C := (haar (Set.univ : Set C))⁻¹ • haar
  have : κ.IsMulRightInvariant := isMulRightInvariant_smul _
  -- as right translation by `C` keeps the Haar measure of `S`, it suffices that the term has mean
  -- zero over `C`
  have h_mean (k : S) (h : G E s) : ∫ c : C, D.thetaTerm Y δ δ f g x (↑(k * c) * h) ∂κ = 0 := by
    change ∫ c : C, θ _ (D.homSlice Y x' (pairWeil X Y δ δ (g, ↑(k * c) * h) f)) ∂κ = 0
    simp only [homSlice_pairWeil_stabilizer_mul D hδ]
    -- apply the vanishing of the mean over `k C w` to the datum transformed by `w⁻¹` and `h`
    simpa [w, rep_apply_apply, mul_assoc, Prod.mk_one_one] using
      integral_theta_pairWeil_stabilizer_eq_zero ν δ hu κ k
        (pairWeil Z Y ν δ (1, w⁻¹) (D.homSlice Y x' (pairWeil X Y δ δ (g, h) f)))
  have h_scale (k : C) : (haar : Measure S).map (· * (k : S)) = (1 : NNReal) • haar := by
    simp [haar_map_mul_right_of_isCompact hC]
  -- unfolding: the coefficient is the integral of the term modulo the rational stabiliser
  have h_unfold : D.centreCoeff (H.j • (xᴴ * Y.J * x))
        (fun k ↦ ∫ h, pairTheta X Y δ δ f (k, h) * 1 ∂Y.quotMeasure) g =
      ∫ h, D.thetaTerm Y δ δ f g x h * 1 ∂(Y.ratStabilizer x).quotMeasure :=
    (D.centreCoeff_eq_integral_ratStabilizer h_int continuous_const h_fixesLeft_one hT_unit).right
  rw [h_unfold]
  -- translation by `C` scales the measure by `d = 1`, while the mean is `a = 0` times the term
  exact integral_quotMeasure_eq_zero_of_mean volume
    (D.fixesLeft_thetaTerm_mul h_fixesLeft_one x) (by fun_prop [Splitting.thetaTerm]) hΓS κ
    (translator := fun _ c ↦ (c : S)) (fun _ ↦ measurable_subtype_coe) (d := 1) (a := 0)
    (h_scale := fun _ ↦ h_scale) zero_ne_one (h_mean := by simpa using h_mean)

end NonnegativeVanishing
