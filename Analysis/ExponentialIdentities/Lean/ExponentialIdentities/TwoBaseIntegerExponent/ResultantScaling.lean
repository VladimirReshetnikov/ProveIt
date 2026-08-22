import Mathlib.RingTheory.Polynomial.Resultant.Basic

namespace Polynomial

noncomputable section

variable {K : Type*} [Field K]

theorem comp_C_mul_X_eq_C_pow_mul_scaleRoots_inv
    (f : K[X]) (s : K) (hs : s ≠ 0) :
    f.comp (C s * X) = C (s ^ f.natDegree) * f.scaleRoots s⁻¹ := by
  ext i
  rw [comp_C_mul_X_coeff, coeff_C_mul, coeff_scaleRoots]
  by_cases hfi : f.coeff i = 0
  · simp [hfi]
  have hi : i ≤ f.natDegree := le_natDegree_of_ne_zero hfi
  have hscale : s ^ i = s ^ f.natDegree * (s⁻¹) ^ (f.natDegree - i) := by
    rw [inv_pow]
    apply (eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hs)).2
    exact pow_mul_pow_sub s hi
  rw [hscale]
  ring

theorem resultant_comp_C_mul_X_explicit (f g : K[X]) (s : K) (hs : s ≠ 0) :
    resultant (f.comp (C s * X)) (g.comp (C s * X)) f.natDegree g.natDegree =
      s ^ (f.natDegree * g.natDegree) * f.resultant g := by
  rw [comp_C_mul_X_eq_C_pow_mul_scaleRoots_inv f s hs,
    comp_C_mul_X_eq_C_pow_mul_scaleRoots_inv g s hs]
  rw [resultant_C_mul_left, resultant_C_mul_right]
  have hres := resultant_scaleRoots f g s⁻¹
  simp only [natDegree_scaleRoots] at hres
  rw [hres]
  rw [← pow_mul, ← pow_mul, mul_comm g.natDegree f.natDegree]
  let N := f.natDegree * g.natDegree
  change s ^ N * (s ^ N * (s⁻¹ ^ N * f.resultant g)) =
    s ^ N * f.resultant g
  rw [inv_pow]
  field_simp

theorem resultant_comp_C_mul_X (f g : K[X]) (s : K) (hs : s ≠ 0) :
    (f.comp (C s * X)).resultant (g.comp (C s * X)) =
      s ^ (f.natDegree * g.natDegree) * f.resultant g := by
  have hfdeg : (f.comp (C s * X)).natDegree = f.natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X s hs, mul_one]
  have hgdeg : (g.comp (C s * X)).natDegree = g.natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X s hs, mul_one]
  change resultant (f.comp (C s * X)) (g.comp (C s * X))
      (f.comp (C s * X)).natDegree (g.comp (C s * X)).natDegree = _
  rw [hfdeg, hgdeg]
  exact resultant_comp_C_mul_X_explicit f g s hs

end

theorem int_resultant_comp_C_mul_X_explicit (f g : ℤ[X]) (s : ℤ) (hs : s ≠ 0) :
    resultant (f.comp (C s * X)) (g.comp (C s * X)) f.natDegree g.natDegree =
      s ^ (f.natDegree * g.natDegree) * f.resultant g := by
  let φ : ℤ →+* ℚ := Int.castRingHom ℚ
  apply (Int.cast_injective : Function.Injective (fun z : ℤ ↦ (z : ℚ)))
  have hφ : Function.Injective φ :=
    (Int.cast_injective : Function.Injective (fun z : ℤ ↦ (z : ℚ)))
  have hsQ : φ s ≠ 0 := by
    intro h
    apply hs
    apply hφ
    simpa using h
  have h := resultant_comp_C_mul_X_explicit
    (f.map φ) (g.map φ) (φ s) hsQ
  change φ (resultant (f.comp (C s * X)) (g.comp (C s * X))
      f.natDegree g.natDegree) =
    φ (s ^ (f.natDegree * g.natDegree) * f.resultant g)
  rw [← resultant_map_map (f.comp (C s * X)) (g.comp (C s * X))
    f.natDegree g.natDegree φ]
  rw [map_mul, map_pow]
  rw [← resultant_map_map f g f.natDegree g.natDegree φ]
  rw [Polynomial.map_comp]
  rw [Polynomial.map_comp]
  rw [Polynomial.map_mul]
  rw [Polynomial.map_C]
  rw [Polynomial.map_X]
  simpa only [natDegree_map_eq_of_injective hφ] using h

theorem int_resultant_comp_C_mul_X (f g : ℤ[X]) (s : ℤ) (hs : s ≠ 0) :
    (f.comp (C s * X)).resultant (g.comp (C s * X)) =
      s ^ (f.natDegree * g.natDegree) * f.resultant g := by
  have hfdeg : (f.comp (C s * X)).natDegree = f.natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X s hs, mul_one]
  have hgdeg : (g.comp (C s * X)).natDegree = g.natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X s hs, mul_one]
  change resultant (f.comp (C s * X)) (g.comp (C s * X))
      (f.comp (C s * X)).natDegree (g.comp (C s * X)).natDegree = _
  rw [hfdeg, hgdeg]
  exact int_resultant_comp_C_mul_X_explicit f g s hs

/-- Exact scalar normalization at a nonzero dilation preserves natural degree. -/
theorem natDegree_of_comp_eq_C_mul
    (f f₀ : ℤ[X]) (s q : ℤ) (a n : ℕ)
    (hs : s ≠ 0) (hq : q ≠ 0) (hfdeg : f.natDegree = n)
    (hscale : f.comp (C s * X) = C (q ^ a) * f₀) :
    f₀.natDegree = n := by
  calc
    f₀.natDegree = (C (q ^ a) * f₀).natDegree :=
      (natDegree_C_mul (pow_ne_zero _ hq)).symm
    _ = (f.comp (C s * X)).natDegree := congrArg natDegree hscale.symm
    _ = f.natDegree := by
      rw [natDegree_comp, natDegree_C_mul_X s hs, mul_one]
    _ = n := hfdeg

/-- Exact cancellation form of the two normalized residual scalings. -/
theorem resultant_eq_pow_mul_of_cross_normalizations
    (f g f₀ g₀ : ℤ[X]) (q : ℤ) (n e : ℕ) (hq : q ≠ 0)
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hf₀deg : f₀.natDegree = n) (hg₀deg : g₀.natDegree = n)
    (hfscale : f.comp (C (q ^ n) * X) = C (q ^ (n * n)) * f₀)
    (hgscale : g.comp (C (q ^ n) * X) = C (q ^ e) * g₀) :
    f.resultant g = q ^ (n * e) * f₀.resultant g₀ := by
  have hs : q ^ n ≠ 0 := pow_ne_zero _ hq
  have hres := int_resultant_comp_C_mul_X_explicit f g (q ^ n) hs
  rw [hfscale, hgscale, resultant_C_mul_left, resultant_C_mul_right] at hres
  have hres' :
      q ^ (n * (n * n)) * (q ^ (n * e) * f₀.resultant g₀) =
        q ^ (n * (n * n)) * f.resultant g := by
    simpa [hfdeg, hgdeg, hf₀deg, hg₀deg, ← pow_mul,
      Nat.mul_add, mul_comm, mul_left_comm, mul_assoc] using hres
  exact (mul_left_cancel₀ (pow_ne_zero (n * (n * n)) hq) hres').symm

/-- Symmetric exact cancellation, with the full `q^(n²)` normalization on
the second polynomial and the cross `q^e` normalization on the first. -/
theorem resultant_eq_pow_mul_of_cross_normalizations_right
    (f g f₀ g₀ : ℤ[X]) (q : ℤ) (n e : ℕ) (hq : q ≠ 0)
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hf₀deg : f₀.natDegree = n) (hg₀deg : g₀.natDegree = n)
    (hfscale : f.comp (C (q ^ n) * X) = C (q ^ e) * f₀)
    (hgscale : g.comp (C (q ^ n) * X) = C (q ^ (n * n)) * g₀) :
    f.resultant g = q ^ (n * e) * f₀.resultant g₀ := by
  have hs : q ^ n ≠ 0 := pow_ne_zero _ hq
  have hres := int_resultant_comp_C_mul_X_explicit f g (q ^ n) hs
  rw [hfscale, hgscale, resultant_C_mul_left, resultant_C_mul_right] at hres
  have hres' :
      q ^ (n * (n * n)) * (q ^ (n * e) * f₀.resultant g₀) =
        q ^ (n * (n * n)) * f.resultant g := by
    simpa [hfdeg, hgdeg, hf₀deg, hg₀deg, ← pow_mul,
      Nat.mul_add, mul_comm, mul_left_comm, mul_assoc] using hres
  exact (mul_left_cancel₀ (pow_ne_zero (n * (n * n)) hq) hres').symm

/-- A constant nonzero reduction of the secondary normalized residual makes
the normalized resultant nonzero. -/
theorem int_resultant_ne_zero_of_map_right_eq_C
    {k : Type*} [Field k] (f g : ℤ[X]) (n : ℕ) (φ : ℤ →+* k) (u : k)
    (hfcoeff : (f.map φ).coeff n ≠ 0) (hu : u ≠ 0)
    (hgmap : g.map φ = C u) :
    resultant f g n n ≠ 0 := by
  intro hzero
  have hmap : resultant (f.map φ) (g.map φ) n n = 0 := by
    rw [resultant_map_map, hzero, map_zero]
  rw [hgmap, resultant_C_right] at hmap
  exact mul_ne_zero (pow_ne_zero _ hfcoeff) (pow_ne_zero _ hu) hmap

/-- Left-handed constant-reduction criterion. -/
theorem int_resultant_ne_zero_of_map_left_eq_C
    {k : Type*} [Field k] (f g : ℤ[X]) (n : ℕ) (φ : ℤ →+* k) (u : k)
    (hgcoeff : (g.map φ).coeff n ≠ 0) (hu : u ≠ 0)
    (hfmap : f.map φ = C u) :
    resultant f g n n ≠ 0 := by
  intro hzero
  have hmap : resultant (f.map φ) (g.map φ) n n = 0 := by
    rw [resultant_map_map, hzero, map_zero]
  rw [hfmap, resultant_C_left] at hmap
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (pow_ne_zero _ hgcoeff))
    (pow_ne_zero _ hu) hmap

/-- The residue of the normalized resultant is explicit when the secondary
normalized polynomial becomes a nonzero constant. -/
theorem map_int_resultant_of_map_right_eq_C
    {k : Type*} [Field k] (f g : ℤ[X]) (n : ℕ) (φ : ℤ →+* k) (u : k)
    (hgmap : g.map φ = C u) :
    φ (resultant f g n n) = (f.map φ).coeff n ^ n * u ^ n := by
  rw [← resultant_map_map, hgmap, resultant_C_right]

/-- Explicit left-handed residue of a normalized resultant. -/
theorem map_int_resultant_of_map_left_eq_C
    {k : Type*} [Field k] (f g : ℤ[X]) (n : ℕ) (φ : ℤ →+* k) (u : k)
    (hfmap : f.map φ = C u) :
    φ (resultant f g n n) =
      (-1 : k) ^ (n * n) * (g.map φ).coeff n ^ n * u ^ n := by
  rw [← resultant_map_map, hfmap, resultant_C_left]

/-- Combining an exact cross normalization with a constant nonzero residue proves
the original cross resultant is nonzero, and identifies its entire forced `q`-power. -/
theorem resultant_cross_normalization_ne_zero
    {k : Type*} [Field k]
    (f g f₀ g₀ : ℤ[X]) (q : ℤ) (n e : ℕ) (hq : q ≠ 0)
    (φ : ℤ →+* k) (u : k)
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hf₀deg : f₀.natDegree = n) (hg₀deg : g₀.natDegree = n)
    (hfscale : f.comp (C (q ^ n) * X) = C (q ^ (n * n)) * f₀)
    (hgscale : g.comp (C (q ^ n) * X) = C (q ^ e) * g₀)
    (hfcoeff : (f₀.map φ).coeff n ≠ 0) (hu : u ≠ 0)
    (hgmap : g₀.map φ = C u) :
    f.resultant g ≠ 0 := by
  rw [resultant_eq_pow_mul_of_cross_normalizations
    f g f₀ g₀ q n e hq hfdeg hgdeg hf₀deg hg₀deg hfscale hgscale]
  exact mul_ne_zero (pow_ne_zero _ hq)
    (by
      change resultant f₀ g₀ f₀.natDegree g₀.natDegree ≠ 0
      simpa only [hf₀deg, hg₀deg] using
        int_resultant_ne_zero_of_map_right_eq_C f₀ g₀ n φ u hfcoeff hu hgmap)

/-- Symmetric nonvanishing package for a constant reduction of the first
cross-normalized polynomial. -/
theorem resultant_cross_normalization_right_ne_zero
    {k : Type*} [Field k]
    (f g f₀ g₀ : ℤ[X]) (q : ℤ) (n e : ℕ) (hq : q ≠ 0)
    (φ : ℤ →+* k) (u : k)
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hf₀deg : f₀.natDegree = n) (hg₀deg : g₀.natDegree = n)
    (hfscale : f.comp (C (q ^ n) * X) = C (q ^ e) * f₀)
    (hgscale : g.comp (C (q ^ n) * X) = C (q ^ (n * n)) * g₀)
    (hgcoeff : (g₀.map φ).coeff n ≠ 0) (hu : u ≠ 0)
    (hfmap : f₀.map φ = C u) :
    f.resultant g ≠ 0 := by
  rw [resultant_eq_pow_mul_of_cross_normalizations_right
    f g f₀ g₀ q n e hq hfdeg hgdeg hf₀deg hg₀deg hfscale hgscale]
  exact mul_ne_zero (pow_ne_zero _ hq)
    (by
      change resultant f₀ g₀ f₀.natDegree g₀.natDegree ≠ 0
      simpa only [hf₀deg, hg₀deg] using
        int_resultant_ne_zero_of_map_left_eq_C f₀ g₀ n φ u hgcoeff hu hfmap)

/-- Sharp quotient form: the entire forced `q^(n e)` factor is split off, and
the remaining integer has an explicit nonzero residue. -/
theorem exists_residue_unit_quotient_of_cross_normalization
    {k : Type*} [Field k]
    (f g f₀ g₀ : ℤ[X]) (q : ℤ) (n e : ℕ) (hq : q ≠ 0)
    (φ : ℤ →+* k) (u : k)
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hf₀deg : f₀.natDegree = n) (hg₀deg : g₀.natDegree = n)
    (hfscale : f.comp (C (q ^ n) * X) = C (q ^ (n * n)) * f₀)
    (hgscale : g.comp (C (q ^ n) * X) = C (q ^ e) * g₀)
    (hfcoeff : (f₀.map φ).coeff n ≠ 0) (hu : u ≠ 0)
    (hgmap : g₀.map φ = C u) :
    ∃ r : ℤ, f.resultant g = q ^ (n * e) * r ∧
      φ r = (f₀.map φ).coeff n ^ n * u ^ n ∧ φ r ≠ 0 := by
  refine ⟨f₀.resultant g₀, ?_, ?_, ?_⟩
  · exact resultant_eq_pow_mul_of_cross_normalizations
      f g f₀ g₀ q n e hq hfdeg hgdeg hf₀deg hg₀deg hfscale hgscale
  · change φ (resultant f₀ g₀ f₀.natDegree g₀.natDegree) = _
    simpa only [hf₀deg, hg₀deg] using
      map_int_resultant_of_map_right_eq_C f₀ g₀ n φ u hgmap
  · change φ (resultant f₀ g₀ f₀.natDegree g₀.natDegree) ≠ 0
    rw [hf₀deg, hg₀deg,
      map_int_resultant_of_map_right_eq_C f₀ g₀ n φ u hgmap]
    exact mul_ne_zero (pow_ne_zero _ hfcoeff) (pow_ne_zero _ hu)

/-- Symmetric quotient form, recording the explicit nonzero residue when the
first normalized polynomial becomes constant. -/
theorem exists_residue_unit_quotient_of_cross_normalization_right
    {k : Type*} [Field k]
    (f g f₀ g₀ : ℤ[X]) (q : ℤ) (n e : ℕ) (hq : q ≠ 0)
    (φ : ℤ →+* k) (u : k)
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hf₀deg : f₀.natDegree = n) (hg₀deg : g₀.natDegree = n)
    (hfscale : f.comp (C (q ^ n) * X) = C (q ^ e) * f₀)
    (hgscale : g.comp (C (q ^ n) * X) = C (q ^ (n * n)) * g₀)
    (hgcoeff : (g₀.map φ).coeff n ≠ 0) (hu : u ≠ 0)
    (hfmap : f₀.map φ = C u) :
    ∃ r : ℤ, f.resultant g = q ^ (n * e) * r ∧
      φ r = (-1 : k) ^ (n * n) * (g₀.map φ).coeff n ^ n * u ^ n ∧
      φ r ≠ 0 := by
  refine ⟨f₀.resultant g₀, ?_, ?_, ?_⟩
  · exact resultant_eq_pow_mul_of_cross_normalizations_right
      f g f₀ g₀ q n e hq hfdeg hgdeg hf₀deg hg₀deg hfscale hgscale
  · change φ (resultant f₀ g₀ f₀.natDegree g₀.natDegree) = _
    simpa only [hf₀deg, hg₀deg] using
      map_int_resultant_of_map_left_eq_C f₀ g₀ n φ u hfmap
  · change φ (resultant f₀ g₀ f₀.natDegree g₀.natDegree) ≠ 0
    rw [hf₀deg, hg₀deg,
      map_int_resultant_of_map_left_eq_C f₀ g₀ n φ u hfmap]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (pow_ne_zero _ hgcoeff))
      (pow_ne_zero _ hu)

/-- Coefficientwise content in two simultaneously dilated polynomials transfers to their
resultant, before cancelling the determinant's change-of-variable factor. -/
theorem pow_dvd_scaled_resultant_of_comp_content
    (f g : ℤ[X]) (s q : ℤ) (a b : ℕ) (hs : s ≠ 0)
    (hf : C (q ^ a) ∣ f.comp (C s * X))
    (hg : C (q ^ b) ∣ g.comp (C s * X)) :
    q ^ (a * g.natDegree + b * f.natDegree) ∣
      s ^ (f.natDegree * g.natDegree) * f.resultant g := by
  obtain ⟨f₁, hf₁⟩ := hf
  obtain ⟨g₁, hg₁⟩ := hg
  have hres := int_resultant_comp_C_mul_X_explicit f g s hs
  rw [hf₁, hg₁, resultant_C_mul_left, resultant_C_mul_right] at hres
  refine ⟨resultant f₁ g₁ f.natDegree g.natDegree, ?_⟩
  calc
    s ^ (f.natDegree * g.natDegree) * f.resultant g =
        (q ^ a) ^ g.natDegree *
          ((q ^ b) ^ f.natDegree *
            resultant f₁ g₁ f.natDegree g.natDegree) := hres.symm
    _ = q ^ (a * g.natDegree + b * f.natDegree) *
          resultant f₁ g₁ f.natDegree g.natDegree := by
      rw [← pow_mul, ← pow_mul, pow_add]
      ring

/-- After cancelling `q^(k n²)`, simultaneous contents `q^a` and `q^b` in
`f(q^k X)` and `g(q^k X)` leave `q^(n(a+b)-kn²)` in `Res(f,g)`. -/
theorem pow_sub_dvd_resultant_of_comp_content
    (f g : ℤ[X]) (q : ℤ) (k a b n : ℕ) (hq : q ≠ 0)
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hf : C (q ^ a) ∣ f.comp (C (q ^ k) * X))
    (hg : C (q ^ b) ∣ g.comp (C (q ^ k) * X))
    (hbudget : k * (n * n) ≤ n * (a + b)) :
    q ^ (n * (a + b) - k * (n * n)) ∣ f.resultant g := by
  have hs : q ^ k ≠ 0 := pow_ne_zero _ hq
  have hraw := pow_dvd_scaled_resultant_of_comp_content
    f g (q ^ k) q a b hs hf hg
  have hraw' : q ^ (n * (a + b)) ∣
      q ^ (k * (n * n)) * f.resultant g := by
    simpa [hfdeg, hgdeg, ← pow_mul, Nat.mul_add, Nat.add_mul,
      mul_comm, mul_left_comm, mul_assoc] using hraw
  let E := n * (a + b) - k * (n * n)
  let B := k * (n * n)
  have hsum : E + B = n * (a + b) := by
    dsimp [E, B]
    exact Nat.sub_add_cancel hbudget
  have hraw'' : q ^ B * q ^ E ∣ q ^ B * f.resultant g := by
    rw [← pow_add, Nat.add_comm B E, hsum]
    exact hraw'
  exact (mul_dvd_mul_iff_left (pow_ne_zero B hq)).mp hraw''

/-- The cross-residual specialization: a full `q^(n²)` residual together with a
secondary `q^e` residual at dilation `q^n` contributes exactly `q^(n e)` to the
undilated resultant. -/
theorem pow_mul_dvd_resultant_of_cross_residuals
    (f g : ℤ[X]) (q : ℤ) (n e : ℕ) (hq : q ≠ 0)
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hf : C (q ^ (n * n)) ∣ f.comp (C (q ^ n) * X))
    (hg : C (q ^ e) ∣ g.comp (C (q ^ n) * X)) :
    q ^ (n * e) ∣ f.resultant g := by
  have hbudget : n * (n * n) ≤ n * (n * n + e) :=
    Nat.mul_le_mul_left n (Nat.le_add_right (n * n) e)
  have h := pow_sub_dvd_resultant_of_comp_content
    f g q n (n * n) e n hq hfdeg hgdeg hf hg hbudget
  simpa only [Nat.mul_add, Nat.add_sub_cancel_left] using h

/-- Symmetric version of `pow_mul_dvd_resultant_of_cross_residuals`, with the
secondary residual on the first polynomial. -/
theorem pow_mul_dvd_resultant_of_cross_residuals_right
    (f g : ℤ[X]) (q : ℤ) (n e : ℕ) (hq : q ≠ 0)
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hf : C (q ^ e) ∣ f.comp (C (q ^ n) * X))
    (hg : C (q ^ (n * n)) ∣ g.comp (C (q ^ n) * X)) :
    q ^ (n * e) ∣ f.resultant g := by
  have hbudget : n * (n * n) ≤ n * (e + n * n) :=
    Nat.mul_le_mul_left n (Nat.le_add_left (n * n) e)
  have h := pow_sub_dvd_resultant_of_comp_content
    f g q n e (n * n) n hq hfdeg hgdeg hf hg hbudget
  have hexp : n * (e + n * n) - n * (n * n) = n * e := by
    rw [Nat.mul_add, Nat.add_sub_cancel_right]
  simpa only [hexp] using h

/-- The exact two-prime cross-resultant package arising from the synchronized
dyadic/triadic residuals. -/
theorem two_three_cross_residuals_dvd_resultant
    (f g : ℤ[X]) (n e : ℕ)
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hf2 : C ((2 : ℤ) ^ (n * n)) ∣ f.comp (C ((2 : ℤ) ^ n) * X))
    (hg2 : C ((2 : ℤ) ^ e) ∣ g.comp (C ((2 : ℤ) ^ n) * X))
    (hf3 : C ((3 : ℤ) ^ e) ∣ f.comp (C ((3 : ℤ) ^ n) * X))
    (hg3 : C ((3 : ℤ) ^ (n * n)) ∣ g.comp (C ((3 : ℤ) ^ n) * X)) :
    (2 : ℤ) ^ (n * e) * 3 ^ (n * e) ∣ f.resultant g := by
  have h2 : (2 : ℤ) ^ (n * e) ∣ f.resultant g :=
    pow_mul_dvd_resultant_of_cross_residuals
      f g 2 n e (by norm_num) hfdeg hgdeg hf2 hg2
  have h3 : (3 : ℤ) ^ (n * e) ∣ f.resultant g :=
    pow_mul_dvd_resultant_of_cross_residuals_right
      f g 3 n e (by norm_num) hfdeg hgdeg hf3 hg3
  have hcop : IsCoprime ((2 : ℤ) ^ (n * e)) ((3 : ℤ) ^ (n * e)) :=
    (show IsCoprime (2 : ℤ) 3 from
      Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)).pow
  exact hcop.mul_dvd h2 h3

/-- Report-14/15 exponent, with `e = n(n-1)/2`: the common cross resultant is
divisible by both structural-prime powers, hence by their product. -/
theorem two_three_triangular_cross_residuals_dvd_resultant
    (f g : ℤ[X]) (n : ℕ)
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hf2 : C ((2 : ℤ) ^ (n * n)) ∣ f.comp (C ((2 : ℤ) ^ n) * X))
    (hg2 : C ((2 : ℤ) ^ (n * (n - 1) / 2)) ∣
      g.comp (C ((2 : ℤ) ^ n) * X))
    (hf3 : C ((3 : ℤ) ^ (n * (n - 1) / 2)) ∣
      f.comp (C ((3 : ℤ) ^ n) * X))
    (hg3 : C ((3 : ℤ) ^ (n * n)) ∣ g.comp (C ((3 : ℤ) ^ n) * X)) :
    (2 : ℤ) ^ (n * (n * (n - 1) / 2)) *
        3 ^ (n * (n * (n - 1) / 2)) ∣ f.resultant g := by
  exact two_three_cross_residuals_dvd_resultant
    f g n (n * (n - 1) / 2) hfdeg hgdeg hf2 hg2 hf3 hg3

end Polynomial
