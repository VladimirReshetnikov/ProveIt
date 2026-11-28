import Lib.DiscreteSeries.FlenstedJensen.CasimirEigenfunction
import Lib.General.NumberTheory.FrobeniusOrbits

/-!
# First properties of c_λ and its K-types

We study the function c_λ = `New.HCParam.dsCoeff` on U(diag ε). Here l = 2λ is a parameter, usually
assumed to satisfy `New.HCParam.HasGap`; K = `New.maxCompactU` has its Haar measure `New.haarK` of
mass one. We write m_w = `New.weightMinors` w for the product of principal minors that is the
coefficient of a highest vector for dominant w, and Λ = `New.HCParam.lowestKType` for the lowest
K-type; λ + ρ = `New.paramAddRho` l, with ρ half the sum of the roots positive for l. The first
properties of c_λ are read off from Flensted-Jensen's integral `New.HCParam.flenstedJensen` over K.
Then we compute ∫_K conj(m_ν(k)) c_λ(xkb) dk for a weight ν that is K-dominant for the order −l: it
is a constant times c_λ(x) c_λ(b) for ν = Λ, and 0 if ν − Λ is outside the cone
`New.HCParam.rootCone` of positive roots.

## Main definitions and results

* `New.dsCoeff_one`, `New.dsCoeff_of_mem_blockDiagAlg`, `New.dsCoeff_of_mem_maxCompactU`:
  c_λ(1) = 1, and c_λ = m_Λ on invertible block diagonal matrices, in particular on K.
* `New.dsCoeff_polar`: the formula for c_λ(p z q⁻¹) with p, q in K and z positive definite.
* `New.dsCoeff_inv`, `New.dsCoeff_neg`: inversion of g and λ ↦ −λ both conjugate c_λ(g).
* `New.integral_conj_weightMinors_lowestKType_mul_dsCoeff`,
  `New.integral_conj_weightMinors_mul_dsCoeff_eq_zero`: the projections of c_λ to its K-types.

Notions from other files:
* `New.USign`: for a vector of signs ε, the unitary group U(J) of the diagonal matrix J = diag(ε);
  `New.maxCompactU ε` is its compact subgroup K = U(diag ε) ∩ U(n).
* `New.HCParam.HasGap`: the entries of `l = 2λ` are distinct and congruent to #n − 1 mod 2, and
  `|λ_i − λ_j| ≥ h` whenever `ε_i ≠ ε_j`.
* `New.IsKDominant`: the weight w is K-dominant for the order o if w_j ≤ w_i whenever ε_i = ε_j and
  o_i < o_j.
* `New.HCParam.rootCone`: the integer vectors β with o · β ≤ 0 for every vector o that strictly
  reverses the order of l: the polar cone of these vectors o.

## Relation to the literature

Known result: Flensted-Jensen's function c_λ on U(p,q), classically the coefficient of the lowest
K-type of a discrete series, its first properties and its projections to K-types.

It is treated for U(p,q) and parameters with a gap, with the integrand written by principal minors;
existence of the discrete series is not assumed. Source: M. Flensted-Jensen, Discrete series for
semisimple symmetric spaces, Ann. of Math. 111 (1980) 253-311; B. Sun, Matrix coefficients of
cohomologically induced representations, Compositio Math. 143 (2007), Thm 1.1 (arXiv math/0403440);
A. Knapp, Representation Theory of Semisimple Groups (1986), ch. IX.
-/

/-! ## Value at one, polar formula and symmetries of c_λ -/

namespace New

open Matrix MeasureTheory ComplexConjugate ComplexOrder U


variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {l : HCParam ε} {h : ℕ}

/-- For g in U(diag ε) and a weight w, the product of principal minors m_w = `New.weightMinors` w
takes conjugate values at g and at g⁻¹. -/
theorem weightMinors_unitary_inv (g : USign ε) (w : n → ℤ) :
    weightMinors w (g : Matrix n n ℂ)⁻¹ = conj (weightMinors w g) := by
  -- Each principal minor of `g⁻¹` is the conjugate of that of `g` (`principalMinor_coe_inv`).
  have h_minor (p : n → Prop) [DecidablePred p] :
      principalMinor (g : Matrix n n ℂ)⁻¹ p = conj (principalMinor (g : Matrix n n ℂ) p) := by
    simpa using U.principalMinor_coe_inv (p := p) g
  have h_det : (g : Matrix n n ℂ)⁻¹.det = conj (g : Matrix n n ℂ).det := by
    simpa [principalMinor_of_forall] using h_minor ⊤
  rw [conj_weightMinors]
  simp [weightMinors, h_minor, h_det]

/-- For g in U(diag ε) and a weight w, negating w conjugates the product of minors m_w(g). -/
theorem weightMinors_unitary_neg (g : USign ε) (w : n → ℤ) :
    weightMinors (-w) g = conj (weightMinors w g) := by
  rw [weightMinors_neg, weightMinors_unitary_inv]; simp [GeneralLinearGroup.det_ne_zero]

/-- The group U(J) of a matrix J is σ-compact. -/
instance {J : Matrix n n ℂ} : SigmaCompactSpace (U J) := inferInstance

/-- The function c_λ = `l.dsCoeff` takes the value 1 at the identity. -/
@[simp]
theorem dsCoeff_one : l.dsCoeff 1 = 1 := by
  -- At the identity the integrand of `flenstedJensen` is `|m_Λ(k)|²`, with integral `kTypeNormSq`.
  have h_norm : ∫ k : maxCompactU ε, weightMinors l.lowestKType k *
      conj (weightMinors l.lowestKType k) ∂haarK ε = (l.lowestKType.kTypeNormSq : ℂ) := by
    simp [RCLike.mul_conj, kTypeNormSq, ← integral_complex_ofReal]
  simp [dsCoeff, flenstedJensen, ← maxCompactU.coe_inv, h_norm, ne_of_gt]

/-- For a parameter l = 2λ of gap h (`l.HasGap h`), p, q in K = U(diag ε)∩U(n) and z in U(diag ε)
positive definite, c_λ(pzq⁻¹) equals ∫_K m_Λ(pu) conj(m_Λ(qu)) / m_{−λ−ρ}(uᴴzu) du divided by ∫_K
|m_Λ|², where du is the Haar measure of mass one. Here c_λ = `l.dsCoeff` is the function g ↦ Ξ(a,
a⁻¹g), with a the block diagonal part of g and Ξ the normalised integral
`New.HCParam.flenstedJensen`. The function m_w(g) = `New.weightMinors w` is the product over all
integers t of the principal minor of g on {i | t ≤ w i}, each factor with t ≤ 0 divided by det g,
and Λ = `l.lowestKType` and λ + ρ = `paramAddRho l`. -/
theorem dsCoeff_polar (hg : l.HasGap h) (p q : maxCompactU ε) {z : USign ε}
    (hz : (z : Matrix n n ℂ).PosDef) :
    l.dsCoeff ((p * z * q⁻¹ : USign ε) : Matrix n n ℂ) =
      (∫ u : maxCompactU ε, weightMinors l.lowestKType (p * u.val) *
          conj (weightMinors l.lowestKType (q * u)) /
          weightMinors (-paramAddRho l) ((u : Matrix n n ℂ)ᴴ * z * u) ∂haarK ε) /
        l.lowestKType.kTypeNormSq :=
  dsCoeff_eq_integral_of_eq_mul_mul_conjTranspose hg (mem_maxCompactU.1 p.property)
    (mem_maxCompactU.1 q.property) hz.isAccretive (by simp [← maxCompactU.coe_inv])

/-- For a parameter λ of gap h and g in U(diag ε), c_λ(g⁻¹) is the complex conjugate of c_λ(g). -/
theorem dsCoeff_inv (hg : l.HasGap h) (g : USign ε) : l.dsCoeff ↑g⁻¹ = conj (l.dsCoeff g) := by
  -- Write `g = k z` with `z > 0`. Then `g⁻¹ = z⁻¹ k⁻¹`, and the integrands of `dsCoeff_polar` for
  -- the two are conjugate, because `weightMinors` is conjugated by inversion.
  obtain ⟨k, z, hz, rfl, -⟩ := exists_polar g
  let F (u : maxCompactU ε) : ℂ := weightMinors l.lowestKType (k * u.val) *
    conj (weightMinors l.lowestKType u) /
    weightMinors (-paramAddRho l) ((u : Matrix n n ℂ)ᴴ * z * u)
  have h_denom (u : maxCompactU ε) (w : n → ℤ) :
      weightMinors w ((u : Matrix n n ℂ)⁻¹ * ((z : Matrix n n ℂ)⁻¹ * u)) =
        conj (weightMinors w ((u : Matrix n n ℂ)⁻¹ * (z * u))) := by
    simpa [mul_assoc, Matrix.mul_inv_rev, GeneralLinearGroup.det_ne_zero] using
      weightMinors_unitary_inv ((u : USign ε)⁻¹ * z * (u : USign ε)) w
  have h_self : l.dsCoeff ↑(k * z) = (∫ u, F u ∂haarK ε) / l.lowestKType.kTypeNormSq := by
    simpa [F] using dsCoeff_polar hg k 1 hz
  have h_inv : l.dsCoeff ↑(k * z)⁻¹ = (∫ u, conj (F u) ∂haarK ε) / l.lowestKType.kTypeNormSq := by
    simpa [F, mul_assoc, mul_comm, ← maxCompactU.coe_inv, Matrix.mul_inv_rev, h_denom] using
      dsCoeff_polar hg 1 k (z := z⁻¹) (by simpa using hz)
  rw [h_inv, h_self, integral_conj, map_div₀, Complex.conj_ofReal]

/-- Let `l = 2λ` be a parameter of gap `h`: its entries are distinct and congruent to `card n - 1`
mod 2, and `|λ i - λ j| ≥ h` whenever `ε i ≠ ε j`. Let c_λ = `l.dsCoeff` be the function
c_λ(g) = Ξ(a, a⁻¹g), where a is the block diagonal part of g and Ξ is the normalised integral
`New.HCParam.flenstedJensen`. Then for every g in U(diag ε), c_{−λ}(g) is the complex conjugate of
c_λ(g). -/
@[simp]
theorem dsCoeff_neg (hg : l.HasGap h) (g : USign ε) : (-l).dsCoeff g = conj (l.dsCoeff g) := by
  -- `lowestKType` and `paramAddRho` change sign with `l`, and this conjugates the integrand of
  -- `dsCoeff_polar`.
  have h_mu : paramAddRho (-l) = -paramAddRho l := by
    grind [two_mul_paramAddRho, hg.neg, twoRho_neg, Pi.neg_def]
  obtain ⟨k, z, hz, rfl, -⟩ := exists_polar g
  let F (u : maxCompactU ε) : ℂ := weightMinors l.lowestKType (k * u.val) *
    conj (weightMinors l.lowestKType u) /
    weightMinors (-paramAddRho l) ((u : Matrix n n ℂ)ᴴ * z * u)
  have h_pos : l.dsCoeff ↑(k * z) = (∫ u, F u ∂haarK ε) / l.lowestKType.kTypeNormSq := by
    simpa [F] using dsCoeff_polar hg k 1 hz
  have h_conj (u : maxCompactU ε) :
      weightMinors (paramAddRho l) ((u : Matrix n n ℂ)⁻¹ * z * u) =
        conj (weightMinors (-paramAddRho l) ((u : Matrix n n ℂ)⁻¹ * z * u)) := by
    simpa using weightMinors_unitary_neg (u⁻¹ * z * u : USign ε) (-paramAddRho l)
  have h_num (u : maxCompactU ε) : weightMinors (-l.lowestKType) (k * u.val) =
      conj (weightMinors l.lowestKType (k * u.val)) := by
    simpa using weightMinors_unitary_neg (k * u : USign ε) l.lowestKType
  have h_neg : (-l).dsCoeff ↑(k * z) = (∫ u, conj (F u) ∂haarK ε) / l.lowestKType.kTypeNormSq := by
    simpa [F, h_mu, h_num, h_conj, ← maxCompactU.coe_inv, kTypeNormSq,
      weightMinors_unitary_neg] using dsCoeff_polar hg.neg k 1 hz
  rw [h_neg, h_pos, integral_conj, map_div₀, Complex.conj_ofReal]

/-- Let `l = 2λ` be a parameter of gap `h` (distinct entries congruent to `card n - 1` mod 2, with
`|λ i - λ j| ≥ h` whenever `ε i ≠ ε j`), and let c_λ = `l.dsCoeff`, c_λ(g) = Ξ(a, a⁻¹g) with a the
block diagonal part of g. For an invertible a in `blockDiagAlg ε` (matrices commuting with diag ε),
c_λ(a) = `weightMinors Λ a`, where Λ = `l.lowestKType` = λ + ρ − 2ρ_c, with 2ρ_c the sum of the
compact roots positive for `l`. Here `weightMinors Λ a` is the product over integers t of the
principal minor of a on {i | t ≤ Λ i}, with each factor for t ≤ 0 divided by det a. -/
theorem dsCoeff_of_mem_blockDiagAlg (hg : l.HasGap h) {a : Matrix n n ℂ} (ha : a ∈ blockDiagAlg ε)
    (ha_det : a.det ≠ 0) : l.dsCoeff a = weightMinors l.lowestKType a := by
  -- In the splitting `a = a * 1` the denominator of the integrand is `1`. By Schur's relation
  -- (`IsHolOfWeight.integral_mul_conj_weightMinors`, stated for functions of `Unit`-indexed tuples)
  -- the integral of `weightMinors Λ (a * u) * conj (weightMinors Λ u)` is `kTypeNormSq` times
  -- `weightMinors Λ a`.
  have h_int : ∫ u : maxCompactU ε, weightMinors l.lowestKType (a * u.val) *
      conj (weightMinors l.lowestKType u) ∂haarK ε =
        l.lowestKType.kTypeNormSq * weightMinors l.lowestKType a := by
    simpa using (isHolOfWeight_weightMinors hg.neg.injective a
      (fun _ : Unit ↦ hg.isKDominant_lowestKType) ha_det).integral_mul_conj_weightMinors
        hg.neg.injective hg.isKDominant_lowestKType
        (by fun_prop (disch := simp [ha_det, GeneralLinearGroup.det_ne_zero]))
  rw [dsCoeff, blockDiagPart_of_mem ha, nonsing_inv_mul a ha_det.isUnit, flenstedJensen]
  simp [h_int, ← maxCompactU.coe_inv, ne_of_gt, GeneralLinearGroup.det_ne_zero]

/-- For a parameter λ of gap h and k in K = U(diag ε) ∩ U(n), c_λ(k) = m_Λ(k), the product of
principal minors of weight Λ = λ + ρ − 2ρ_c. -/
theorem dsCoeff_of_mem_maxCompactU (hg : l.HasGap h) {k : U (signMatrix ε)}
    (hk : k ∈ maxCompactU ε) : l.dsCoeff k = weightMinors l.lowestKType k :=
  dsCoeff_of_mem_blockDiagAlg hg (mem_maxCompactU.1 hk) (GeneralLinearGroup.det_ne_zero _)

end New

/-!
## The lowest K-type of c_λ and vanishing outside Λ + cone

The projection formula for c_λ(x k b) is proved for b near 1, by writing c_λ as Flensted-Jensen's
integral and averaging over a circle in K, and is continued analytically to every b in U(diag ε).
-/

section KTypeProjection

open Matrix MeasureTheory ComplexConjugate Norms.L2Operator ComplexOrder New DiscreteSeries

variable {n : Type} [Fintype n] {ε : n → ℤˣ} {l : HCParam ε} {h : ℕ}

/-- If `β` is `0` or lies outside `l.rootCone`, there is an order `o` opposite to `l` for which
`o ⬝ᵥ β` is a natural number that vanishes only for `β = 0`. -/
theorem New.exists_order_dotProduct_eq_natCast {β : n → ℤ} (h_cone : β ≠ 0 → β ∉ l.rootCone) :
    ∃ (o : n → ℤ) (N : ℕ),
      (∀ i j : n, l j < l i → o i < o j) ∧ (N : ℤ) = o ⬝ᵥ β ∧ (N = 0 ↔ β = 0) := by
  by_cases hβ : β = 0
  · exact ⟨-l, 0, by simp [hβ]⟩
  · obtain ⟨o, ho, h_not_le⟩ := not_forall₂.1 (h_cone hβ)
    have h_pos : 0 < o ⬝ᵥ β := not_le.1 h_not_le
    exact ⟨o, (o ⬝ᵥ β).toNat, ho, Int.toNat_of_nonneg h_pos.le, by simp [hβ, h_pos]⟩

/-- An integer vector `o` that strictly reverses the order of a parameter `l` with a gap is
injective, and `o i < o j` holds only if `l j < l i`. -/
private theorem New.injective_and_lt_of_reverses_order (hg : l.HasGap h) {o : n → ℤ}
    (ho : ∀ i j : n, l j < l i → o i < o j) :
    o.Injective ∧ ∀ i j : n, o i < o j → l j < l i := by
  have h_order (i j : n) (hij : o i < o j) : l j < l i := by
    by_contra! h_le
    rcases h_le.lt_or_eq with h_lt | h_eq
    exacts [(ho j i h_lt).not_gt hij, hij.ne (congrArg o (hg.injective h_eq))]
  refine ⟨fun i j hij ↦ hg.injective ?_, h_order⟩
  exact le_antisymm (not_lt.1 fun h_lt ↦ (ho i j h_lt).ne hij)
    (not_lt.1 fun h_lt ↦ (ho j i h_lt).ne' hij)

variable [DecidableEq n]

/-- The integral ∫_K conj(m_ν(k)) c_λ(x k z) dk, with m_ν = `weightMinors ν` and
c_λ = `l.dsCoeff`, is analytic in the matrix `z` at every point of U(diag ε). -/
theorem New.analyticAt_integral_conj_weightMinors_mul_dsCoeff (ν : n → ℤ) (x b : USign ε) :
    AnalyticAt ℂ
      (fun z : Matrix n n ℂ ↦ ∫ k : maxCompactU ε,
        conj (weightMinors ν k) * l.dsCoeff (x * k * z) ∂haarK ε) b := by
  -- The integrand is an analytic family in `z`, with parameter `(conj (m_ν k), x k)` continuous on
  -- the compact group `K`.
  let param (k : maxCompactU ε) : ℂ × Matrix n n ℂ :=
    (conj (weightMinors ν k), (x * k : Matrix n n ℂ))
  have h_param : Continuous param := by fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero])
  exact (IsAnalyticFamily.of_analyticAt (ι := param) (p := (b : Matrix n n ℂ)) h_param
    (fun (z, y, g) ↦ y * l.dsCoeff (g * z)) fun (k : maxCompactU ε) ↦ by
      have h_coeff := l.analyticAt_dsCoeff (x * k * b)
      fun_prop).analyticAt_integral (haarK ε)

/-- For θ in ℝ/ℤ let s = `θ.toCircle` and t = diag(s ^ o) in K. Let ν be K-dominant for injective
`o`, μ dominant for `-o`, let `y` factor as t⁻¹ y = A(s) t⁻¹ C with `A` entire, `A 0 = 1`, `C`
triangular (`IsCircleFactorization`), with `w * A s` accretive (Hermitian part positive definite) on
the unit disc (w is a matrix), let N = o · (ν − Λ) be a natural number that vanishes only for ν = Λ.
Then the mean over θ of m_ν(k t j⁻¹) · u · conj(m_Λ(k t)) / m_μ(w t* y t) is u conj(m_Λ(j)) / m_μ(w)
times
|m_Λ(k)|² / m_μ(y) if ν = Λ, and 0 otherwise. Here m_ν = `weightMinors ν` for each weight, and
dominance for the signs `1` compares all pairs of indices. -/
private theorem New.integral_circle_weightMinors_div {o ν Λ μ : n → ℤ} {N : ℕ} (ho : o.Injective)
    (hν : IsKDominant ε o ν) (hμ : IsKDominant 1 (-o) μ) (hN : (N : ℤ) = o ⬝ᵥ (ν - Λ))
    (hN_zero : N = 0 ↔ ν = Λ) (j k : maxCompactU ε) (u : ℂ) {w y C : Matrix n n ℂ}
    {A : ℂ → Matrix n n ℂ} (hy : IsCircleFactorization 1 (-o) μ y A C)
    (hA_acc : ∀ s : ℂ, ‖s‖ ≤ 1 → (w * A s).IsAccretive) :
    ∫ θ : UnitAddCircle,
        (let t : maxCompactU ε := diagTorusK fun i : n ↦ θ.toCircle ^ o i
        weightMinors ν (k * t * j⁻¹).val * (u * conj (weightMinors Λ (k * t).val) /
          weightMinors μ (w * ((t : Matrix n n ℂ)ᴴ * y * t)))) =
      u * conj (weightMinors Λ j) / weightMinors μ w *
        (weightMinors Λ k * conj (weightMinors Λ k) / weightMinors μ y) *
          if ν = Λ then 1 else 0 := by
  -- On the circle the integrand is `m_ν(k t_s j⁻¹) / s ^ (o · ν)` times `q s`, with `q` analytic
  -- on the disc, so the mean is `q 0 * m_ν(j⁻¹) * m_ν(k)`.
  have hA := hy.analyticAt
  let T (s : Circle) : Matrix n n ℂ := diagonal fun i ↦ (s : ℂ) ^ o i
  let q (s : ℂ) : ℂ :=
    s ^ N * (u * conj (weightMinors Λ k) / weightMinors μ (w * A s)) / diagChar μ C
  have hq : AnalyticOnNhd ℂ q (Metric.closedBall 0 1) := fun s hs ↦ by
    have := hA_acc s (by simpa using hs)
    fun_prop (disch := simp [*, -det_mul, IsAccretive.det_ne_zero])
  have h_hol : IsHolOfWeight ε o (fun _ : Unit ↦ ν) (fun g ↦ ∏ τ, weightMinors ν (k * g τ)) ε :=
    isHolOfWeight_weightMinors ho k (fun _ ↦ hν) (GeneralLinearGroup.det_ne_zero _)
  have h_circle : ∫ θ : UnitAddCircle,
      weightMinors ν ((k : Matrix n n ℂ) * (T θ.toCircle * (j : Matrix n n ℂ)⁻¹)) *
        (((θ.toCircle : ℂ) ^ (o ⬝ᵥ ν))⁻¹ * q θ.toCircle) =
      q 0 * weightMinors ν (j : Matrix n n ℂ)⁻¹ * weightMinors ν k := by
    simpa [T, diagTorus, dotProduct, ← _root_.zpow_mul, ← zpow_sum_of_ne_zero] using
      h_hol.circle_mean_weightMinors ho (.inr rfl) (fun _ ↦ hν)
        (fun _ ↦ mem_maxCompactU.1 j⁻¹.property) q hq
  -- `h_circle` evaluates the mean; it remains to match its two sides with those of the goal.
  refine .trans ?_ (h_circle.trans ?_)
  · -- The triangular factor `t_s⁻¹ C t_s` comes out of the denominator as `diagChar`.
    congr with θ
    set s : Circle := θ.toCircle
    let t : Matrix n n ℂ := T s
    let t' : Matrix n n ℂ := T s⁻¹
    have h_factor : t' * y = A s * (t' * C) := by simpa [t', T] using hy.diagonal_mul_eq s
    have h_diag : diagChar μ (t' * C * t) = diagChar μ C := by
      simp [t, t', T, diagChar, zpow_ne_zero, mul_comm]
    have h_denom : weightMinors μ (w * (t' * y * t)) =
        weightMinors μ (w * A s) * diagChar μ C := by
      rw [h_factor, mul_assoc (A s), ← mul_assoc w, ← h_diag]
      simpa [t, t', T] using hμ.weightMinors_mul_borel (neg_injective.comp ho)
        (hA_acc s s.norm_coe.le).det_ne_zero (by simp)
        (((isBorelMatrix_diagonal s).mul hy.isBorelMatrix).mul (isBorelMatrix_diagonal s⁻¹))
    have h_num : conj (weightMinors Λ ((k : Matrix n n ℂ) * t)) =
        conj (weightMinors Λ k) / (s : ℂ) ^ (o ⬝ᵥ Λ) := by
      simp [t, T, conj_weightMinors, dotProduct, ← _root_.zpow_mul, ← zpow_sum_of_ne_zero,
        ← s.coe_inv_eq_conj, Pi.star_def, GeneralLinearGroup.det_ne_zero, zpow_ne_zero,
        div_eq_mul_inv, mul_comm]
    have h_integrand : u * conj (weightMinors Λ ((k : Matrix n n ℂ) * t)) /
        weightMinors μ (w * (t' * y * t)) = ((s : ℂ) ^ (o ⬝ᵥ ν))⁻¹ * q s := by
      have h_power : (s : ℂ) ^ N = (s : ℂ) ^ (o ⬝ᵥ ν) / (s : ℂ) ^ (o ⬝ᵥ Λ) := by
        rw [← zpow_natCast, hN, dotProduct_sub, zpow_sub₀ s.coe_ne_zero]
      simp only [q, h_num, h_denom, h_power]
      field_simp [zpow_ne_zero, s.coe_ne_zero]
    rw [← h_integrand]
    simp [t, t', T, diagTorus, Pi.star_def, ← s.coe_inv_eq_conj, mul_assoc]
  · -- At `s = 0`, `A 0 = 1`; either `ν = Λ` or both sides vanish.
    by_cases h_eq : ν = Λ
    · simp [q, hN_zero.2 h_eq, h_eq, hy.apply_zero, hy.weightMinors_eq, weightMinors_unitary_inv]
      ring
    · simp [q, mt hN_zero.1 h_eq, h_eq]

/-- For `-o` injective, μ dominant for `-o` and `x` in U(diag ε), every `b` near 1 has, for all `k`
in K, the following properties, where a_x = `blockDiagPart ε x` (the entries of x with ε_i = ε_j,
the others replaced by 0) and y = k* b k. The matrix y and its products with each j* a_x⁻¹ x j, j in
K, are accretive (Hermitian part positive definite), and y has a circle factorisation
(`New.IsCircleFactorization`) t⁻¹ y = A(s) t⁻¹ C for |s| = 1, t = diag(s ^ o), A entire, A 0 = 1, C
triangular, such that every product j* a_x⁻¹ x j * A(s),
|s| ≤ 1, is accretive. -/
private theorem New.eventually_forall_accretive_circleFactorization {o μ : n → ℤ}
    (ho : (-o).Injective) (hμ : IsKDominant 1 (-o) μ) (x : USign ε) :
    let S (y : Matrix n n ℂ) (k : maxCompactU ε) : Matrix n n ℂ := (k : Matrix n n ℂ)ᴴ * y * k
    ∀ᶠ b : USign ε in nhds 1, ∀ k : maxCompactU ε,
      (∀ j : maxCompactU ε, (S ((blockDiagPart ε x)⁻¹ * x) j * S b k).IsAccretive) ∧
      (S b k).IsAccretive ∧
      ∃ (A : ℂ → Matrix n n ℂ) (C : Matrix n n ℂ),
        IsCircleFactorization 1 (-o) μ (S b k) A C ∧
          ∀ s : ℂ, ‖s‖ ≤ 1 → ∀ j : maxCompactU ε,
            (S ((blockDiagPart ε x)⁻¹ * x) j * A s).IsAccretive := by
  intro S
  -- By compactness of `K`, what holds near `1` holds at every `k* b k` for `b` near `1`.
  have h_transfer {P : Matrix n n ℂ → Prop} (hP : ∀ᶠ y : Matrix n n ℂ in nhds 1, P y) :
      ∀ᶠ b : USign ε in nhds 1, ∀ k : maxCompactU ε, P (S b k) := by
    simpa using ((show Continuous fun b : USign ε ↦ (b : Matrix n n ℂ) by fun_prop).tendsto' 1 1
      rfl).eventually <| isCompact_univ.eventually_forall_mem
        S {z | P z} fun k _ ↦ hP.filter_mono (by simp [S, ← maxCompactU.coe_inv])
  have h_acc_near : ∀ᶠ y : Matrix n n ℂ in nhds 1, ∀ j ∈ Set.univ,
      S ((blockDiagPart ε x)⁻¹ * x) j * y ∈ {z : Matrix n n ℂ | z.IsAccretive} :=
    isCompact_univ.eventually_forall_mem _ _ (by
      simp [S, IsAccretive.setOf_mem_nhds, GeneralLinearGroup.det_ne_zero])
  filter_upwards [h_transfer h_acc_near, h_transfer PosDef.one.isAccretive.setOf_mem_nhds,
    h_transfer (eventually_exists_isCircleFactorization ho hμ h_acc_near)] with b hb_acc hb
      hb_factor
  intro k
  obtain ⟨A, C, hAC, hA_acc⟩ := hb_factor k (by simp)
  exact ⟨fun j ↦ hb_acc k j trivial, hb k, A, C, hAC,
    fun s hs j ↦ hA_acc s (by simpa using hs) j trivial⟩

omit [DecidableEq n] in
/-- If ν is `K`-dominant for `-l` and is Λ or has ν − Λ outside `l.rootCone`, there is an injective
`o`, with ν `K`-dominant for `o` and −λ − ρ = `-paramAddRho l` dominant for `-o`, such that
N = o · (ν − Λ) is a natural number that vanishes only for ν = Λ. -/
private theorem New.exists_order_isKDominant_dotProduct_eq_natCast (hg : l.HasGap h) {ν : n → ℤ}
    (hν : IsKDominant ε (-l) ν) (h_cone : ν ≠ l.lowestKType → ν - l.lowestKType ∉ l.rootCone) :
    ∃ (o : n → ℤ) (N : ℕ), o.Injective ∧ IsKDominant ε o ν ∧
      IsKDominant 1 (-o) (-paramAddRho l) ∧ (N : ℤ) = o ⬝ᵥ (ν - l.lowestKType) ∧
      (N = 0 ↔ ν = l.lowestKType) := by
  obtain ⟨o, N, ho, hN, hN_zero⟩ :=
    exists_order_dotProduct_eq_natCast fun h_ne ↦ h_cone (sub_ne_zero.1 h_ne)
  obtain ⟨ho_inj, h_order⟩ := injective_and_lt_of_reverses_order hg ho
  -- `o` orders the indices as `-l` does, so dominance carries over.
  have hν_dom : IsKDominant ε o ν := fun i j h_sign hij ↦
    hν i j h_sign (neg_lt_neg (h_order i j hij))
  have hμ_dom : IsKDominant 1 (-o) (-paramAddRho l) := fun i j h_sign hij ↦
    hg.isKDominant_neg_paramAddRho i j h_sign (h_order j i (neg_lt_neg_iff.1 hij))
  exact ⟨o, N, ho_inj, hν_dom, hμ_dom, hN, by simpa [sub_eq_zero] using hN_zero⟩

/-- The projection formula for `b` near `1`. Let `l = 2λ` have a gap and ν be a weight, `K`-dominant
for the order `-l`, that is the lowest `K`-type Λ or has ν − Λ outside `l.rootCone`. Then
∫_K conj(m_ν(k)) c_λ(x k b) dk is ∫_K |m_Λ|² · c_λ(x) c_λ(b) if ν = Λ, and `0` otherwise, where
c_λ = `l.dsCoeff` and m_w = `weightMinors w`. -/
private theorem New.eventually_integral_conj_weightMinors_mul_dsCoeff (hg : l.HasGap h)
    (x : USign ε) {ν : n → ℤ} (hν : IsKDominant ε (-l) ν)
    (h_cone : ν ≠ l.lowestKType → ν - l.lowestKType ∉ l.rootCone) :
    ∀ᶠ b : USign ε in nhds 1,
      ∫ k : maxCompactU ε, conj (weightMinors ν k) * l.dsCoeff ↑(x * k * b) ∂haarK ε =
        l.lowestKType.kTypeNormSq * (l.dsCoeff x * l.dsCoeff b) *
          if ν = l.lowestKType then 1 else 0 := by
  -- The left side is a double integral over `K × K`, and averaging over a circle in `K` splits it.
  -- The circle is `diag (s ^ o)` for an order `o` such that `N = o · (ν - Λ)` is a natural number
  -- that vanishes only for `ν = Λ`.
  obtain ⟨o, N, ho_inj, hν_dom, hμ_dom, hN, hN_zero⟩ :=
    exists_order_isKDominant_dotProduct_eq_natCast hg hν h_cone
  let S (y : Matrix n n ℂ) (k : maxCompactU ε) : Matrix n n ℂ := (k : Matrix n n ℂ)ᴴ * y * k
  -- For `b` near 1, uniformly in `k`, `y = k* b k` satisfies `t_s⁻¹ y = A k s * t_s⁻¹ * C k` for
  -- `|s| = 1`, `t_s = diag (s ^ o)`, with `A k` entire, `A k 0 = 1` and `C k` triangular.
  filter_upwards [eventually_forall_accretive_circleFactorization (neg_injective.comp ho_inj)
    hμ_dom x] with b hb
  choose h_acc hb_acc A C h_factor hA_acc using hb
  -- With `j = a * k`, `H j k` is `conj (weightMinors ν a)` times the integrand at `k` of
  -- Flensted-Jensen's integral for `l.dsCoeff (x * a * b)`.
  let G (j k : maxCompactU ε) (y : Matrix n n ℂ) : ℂ :=
    weightMinors l.lowestKType (blockDiagPart ε x * j) * conj (weightMinors l.lowestKType k) /
      weightMinors (-paramAddRho l) (S ((blockDiagPart ε x)⁻¹ * x) j * y)
  let H (j k : maxCompactU ε) : ℂ := weightMinors ν (k * j⁻¹).val * G j k (S b k)
  have hH_int : Integrable H.uncurry ((haarK ε).prod (haarK ε)) := integrable_of_compactSpace <| by
    unfold H G S
    fun_prop (disch := simp [h_acc, GeneralLinearGroup.det_ne_zero])
  let F (k : maxCompactU ε) : ℂ := weightMinors l.lowestKType k *
    conj (weightMinors l.lowestKType k) / weightMinors (-paramAddRho l) (S b k)
  -- The mean of `H j (k t_s)` over the circle.
  let τ (θ : UnitAddCircle) : maxCompactU ε := diagTorusK fun i ↦ θ.toCircle ^ o i
  have h_mean (j k : maxCompactU ε) :
      ∫ θ, H j (k * τ θ) = G j j 1 * F k * if ν = l.lowestKType then 1 else 0 := by
    simpa [H, G, F, S, τ, mul_assoc] using integral_circle_weightMinors_div ho_inj hν_dom hμ_dom hN
      hN_zero j k (weightMinors l.lowestKType (blockDiagPart ε x * j)) (h_factor k)
      fun s hs ↦ hA_acc k s hs j
  let c : ℂ := l.lowestKType.kTypeNormSq
  have h_x : l.dsCoeff x = (∫ j, G j j 1 ∂haarK ε) / c := by
    simp [HCParam.dsCoeff, HCParam.flenstedJensen, G, S, c, mul_assoc]
  have h_b : l.dsCoeff b = (∫ k, F k ∂haarK ε) / c := by
    simp [dsCoeff_eq_flenstedJensen hg (one_mem _) (by simpa using hb_acc 1),
      HCParam.flenstedJensen, F, S, c]
  -- Use `dsCoeff_eq_flenstedJensen` for `x * a * b` with the factor `blockDiagPart ε x * a`.
  have h_left (a : maxCompactU ε) : conj (weightMinors ν a) * l.dsCoeff ↑(x * a * b) * c =
      ∫ k, H (a * k) k ∂haarK ε := by
    rw [dsCoeff_eq_flenstedJensen hg
      (mul_mem (blockDiagPart_mem x) (mem_maxCompactU.1 a.property)), HCParam.flenstedJensen]
    · simp [H, G, S, c, mul_assoc, ← maxCompactU.coe_inv, Matrix.mul_inv_rev, ne_of_gt,
        weightMinors_unitary_inv, integral_const_mul]
    · simpa [mul_assoc, ← maxCompactU.coe_inv, Matrix.mul_inv_rev] using h_acc 1 a
  -- After averaging over right multiplication by `(1, τ θ)` on `K × K`, the integrand is a function
  -- of `j` times a function of `k`.
  have h_average : ∫ p, H.uncurry p ∂(haarK ε).prod (haarK ε) =
      ∫ p, G p.1 p.1 1 * F p.2 * (if ν = l.lowestKType then 1 else 0) ∂(haarK ε).prod (haarK ε) :=
    integral_eq_of_circle_mean (T := fun θ p ↦ p * (1, τ θ)) (Continuous.measurable (by fun_prop))
      (fun θ ↦ measurePreserving_mul_right _ (1, τ θ))
      hH_int fun (j, k) ↦ by simpa using h_mean j k
  have hc : c ≠ 0 := by simp [c, ne_of_gt]
  apply mul_right_cancel₀ hc
  calc (∫ a : maxCompactU ε, conj (weightMinors ν a) * l.dsCoeff ↑(x * a * b) ∂haarK ε) * c
    _ = ∫ a, ∫ k, H (a * k) k ∂haarK ε ∂haarK ε := by simp_rw [← integral_mul_const, h_left]
    _ = ∫ p, H.uncurry p ∂(haarK ε).prod (haarK ε) :=
      ((measurePreserving_mul_prod ..).fubini hH_int).2
    _ = (∫ j, G j j 1 ∂haarK ε) * (∫ k, F k ∂haarK ε) * (if ν = l.lowestKType then 1 else 0) := by
      rw [h_average, integral_mul_const, integral_prod_mul (fun j ↦ G j j 1) F]
    _ = c * (l.dsCoeff x * l.dsCoeff b) * (if ν = l.lowestKType then 1 else 0) * c := by
      rw [h_x, h_b]
      field_simp

/-- The two cases of the projection formula in one identity, for every `b` in U(diag ε): for
`l = 2λ` with a gap and a weight ν that is `K`-dominant for `-l` and is Λ or has ν − Λ outside
`l.rootCone`, with c_λ = `l.dsCoeff` and m_w = `weightMinors w`, ∫_K conj(m_ν(k)) c_λ(x k b) dk is
∫_K |m_Λ|² · c_λ(x) c_λ(b) if ν = Λ, and `0` otherwise. -/
private theorem New.integral_conj_weightMinors_mul_dsCoeff_eq_mul_ite (hg : l.HasGap h)
    (x b : USign ε) {ν : n → ℤ} (hν : IsKDominant ε (-l) ν)
    (h_cone : ν ≠ l.lowestKType → ν - l.lowestKType ∉ l.rootCone) :
    ∫ k : maxCompactU ε, conj (weightMinors ν k) * l.dsCoeff ↑(x * k * b) ∂haarK ε =
      l.lowestKType.kTypeNormSq * (l.dsCoeff x * l.dsCoeff b) *
        if ν = l.lowestKType then 1 else 0 := by
  -- Both sides are analytic along a path `c` from 1 to `b` and agree near 1. Being block diagonal
  -- for the trivial signs `1`, as `exists_analytic_path` asks, is no condition.
  obtain ⟨c, hc_zero, rfl, hc, -⟩ := exists_analytic_path (.inl rfl) b (by simp)
  let P (s : ℝ) : ℂ :=
    ∫ k : maxCompactU ε, conj (weightMinors ν k) * l.dsCoeff ↑(x * k * c s) ∂haarK ε
  let Q (s : ℝ) : ℂ := l.lowestKType.kTypeNormSq * (l.dsCoeff x * l.dsCoeff (c s)) *
    if ν = l.lowestKType then 1 else 0
  have hP (t : ℝ) : AnalyticAt ℝ P t :=
    (analyticAt_integral_conj_weightMinors_mul_dsCoeff ν x (c t)).restrictScalars.comp_of_eq (hc t)
      rfl
  have hQ (t : ℝ) : AnalyticAt ℝ Q t := by
    have h_coeff := (l.analyticAt_dsCoeff (c t)).restrictScalars.comp_of_eq (hc t) rfl
    fun_prop
  have h_near : ∀ᶠ s : ℝ in nhds 0, P s = Q s :=
    ((continuous_U_iff_matrix.2 (continuous_iff_continuousAt.2 fun t ↦ (hc t).continuousAt)
      ).tendsto' 0 1 hc_zero).eventually
        (eventually_integral_conj_weightMinors_mul_dsCoeff hg x hν h_cone)
  exact congrFun (AnalyticOnNhd.eq_of_eventuallyEq (fun t _ ↦ hP t) (fun t _ ↦ hQ t) h_near) 1

/-- Projection of c_λ to its lowest `K`-type Λ. For a parameter `l = 2λ` of gap h and `x`, `b` in
U(diag ε), ∫_K conj(m_Λ(k)) c_λ(x k b) dk = ∫_K |m_Λ|² · c_λ(x) c_λ(b), with K = U(diag ε)∩U(n)
carrying its Haar measure of mass one. Here c_λ = `l.dsCoeff`, Λ = `l.lowestKType`, and
m_Λ = `weightMinors Λ` is the function sending g to the product over all integers t of the principal
minor of g on {i | t ≤ Λ i}, each factor with t ≤ 0 divided by det g.

For the matrix coefficient of a unit highest weight vector this identity expresses, by Schur's
orthogonality relations for `K`, that the lowest `K`-type of the discrete series occurs once. -/
theorem New.integral_conj_weightMinors_lowestKType_mul_dsCoeff (hg : l.HasGap h) (x b : USign ε) :
    ∫ k : maxCompactU ε, conj (weightMinors l.lowestKType k) * l.dsCoeff ↑(x * k * b) ∂haarK ε =
      l.lowestKType.kTypeNormSq * (l.dsCoeff x * l.dsCoeff b) := by
  simpa using integral_conj_weightMinors_mul_dsCoeff_eq_mul_ite hg x b
    hg.isKDominant_lowestKType (absurd rfl)

/-- c_λ has no `K`-type outside Λ + `l.rootCone`: for a parameter `l = 2λ` with a gap, `x`, `b` in
U(diag ε) and a weight ν that is `K`-dominant for the order `-l`, with ν − Λ outside the cone, ∫_K
conj(m_ν(k)) c_λ(x k b) dk = 0.

This is the form, for the one coefficient c_λ, of the fact that the `K`-types of the discrete series
lie in the cone above the lowest one (a consequence of Blattner's formula). -/
theorem New.integral_conj_weightMinors_mul_dsCoeff_eq_zero (hg : l.HasGap h) (x b : USign ε)
    {ν : n → ℤ} (hν : IsKDominant ε (-l) ν) (h_cone : ν - l.lowestKType ∉ l.rootCone) :
    ∫ k : maxCompactU ε, conj (weightMinors ν k) * l.dsCoeff ↑(x * k * b) ∂haarK ε = 0 := by
  -- `ν ≠ Λ`, since `0` lies in the cone.
  rw [integral_conj_weightMinors_mul_dsCoeff_eq_mul_ite hg x b hν fun _ ↦ h_cone,
    ite_eq_right fun h_eq ↦ h_cone (by simp [h_eq, HCParam.rootCone]), mul_zero]

end KTypeProjection
