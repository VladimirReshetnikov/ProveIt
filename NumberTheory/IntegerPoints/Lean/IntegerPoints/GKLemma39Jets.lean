import IntegerPoints.GKLemma39Local
import IntegerPoints.InverseJet
import IntegerPoints.InverseJetStability

/-!
# Graham--Kolesnik, Lemma 3.9: normalized analytic jets

This module connects the local inverse supplied by `GK39` with the finite
inverse-jet stability theorem in `InverseJet`.  At a frequency `nu` with
inverse point `X = x nu`, the forward and inverse jets are normalized by

`u_m = (deriv f)^(m)(X) X^m / nu`,
`z_m = x^(m)(nu) nu^m / X`.

Faà di Bruno applied to `(deriv f) ∘ x = id` gives exactly
`InverseJet.normalizedRecurrenceAt u z m`.  The Graham--Kolesnik class
inequalities make `u_m` an `O(eps)` perturbation of the power-model jet, and
the first forward jet stays uniformly away from zero.  The abstract finite
stability theorem therefore controls every normalized inverse jet through
order `P - 1`.

The final section isolates the other analytic ingredient needed when the
normalization is removed: comparison of the inverse point `X` with the power
scale `y^(1/s) nu^(-1/s)`.
-/

open Real Finset Set Filter
open scoped BigOperators Topology ContDiff

namespace LeanProofs.IntegerPoints

namespace GK39Jets

/-! ### Normalized jets and their algebra -/

/-- The normalized derivatives of the forward map `f'` at the inverse point. -/
noncomputable def normalizedForwardJet (f x : ℝ → ℝ) (nu : ℝ) (m : ℕ) : ℝ :=
  iteratedDeriv m (deriv f) (x nu) * (x nu) ^ m / nu

/-- The normalized derivatives of the inverse map. -/
noncomputable def normalizedInverseJet (x : ℝ → ℝ) (nu : ℝ) (m : ℕ) : ℝ :=
  iteratedDeriv m x nu * nu ^ m / x nu

/-- The ratio between the power-model value for `f'` and its actual value
`nu = f'(X)`. -/
noncomputable def phaseRatio (s y X nu : ℝ) : ℝ :=
  y * X ^ (-s) / nu

/-- Multiplication by the natural power cancels the corresponding part of a
negative real exponent. -/
theorem rpow_neg_sub_mul_pow {X : ℝ} (hX : 0 < X) (s : ℝ) (m : ℕ) :
    X ^ (-s - (m : ℝ)) * X ^ m = X ^ (-s) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_add hX]
  congr 1
  ring

/-- Normalizing every factor in one Faà di Bruno monomial leaves the common
factor `nu^m / nu`. -/
theorem partitionTerm_normalized {g x : ℝ → ℝ} {X nu : ℝ}
    (hX : X ≠ 0) (hnu : nu ≠ 0) {m : ℕ}
    (c : OrderedFinpartition m) :
    InverseJet.partitionTerm
        (fun q => iteratedDeriv q g X * X ^ q / nu)
        (fun q => iteratedDeriv q x nu * nu ^ q / X) c =
      (iteratedDeriv c.length g X *
          ∏ j, iteratedDeriv (c.partSize j) x nu) * nu ^ m / nu := by
  unfold InverseJet.partitionTerm
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, InverseJet.sum_partSize, Fin.prod_const]
  field_simp

/-- The class regularity makes `f'` globally `C^(P-1)`. -/
theorem contDiff_deriv_pred {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hP : 2 ≤ P) (hf : InGKClass N P s y eps a b f) :
    ContDiff ℝ (P - 1) (deriv f) := by
  have hfP : ContDiff ℝ ((P - 1 : ℕ) + 1) f := by
    exact hf.2.2.2.1.of_le (by
      exact_mod_cast (show P - 1 + 1 ≤ P by omega))
  exact (contDiff_succ_iff_deriv.mp hfP).2.2

/-! ### The normalized Faà di Bruno recurrence -/

/-- At every interior frequency, the actual normalized jets obey exactly the
same triangular recurrence as the power model. -/
theorem normalizedRecurrenceAt {N s y eps a b : ℝ} {P : ℕ}
    {f x : ℝ → ℝ} (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 2 ≤ P) (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f) (hab : a < b)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    {nu : ℝ} (hnu : nu ∈ Ioo (deriv f b) (deriv f a))
    {m : ℕ} (hm0 : 0 < m) (hmP : m ≤ P - 1) :
    InverseJet.normalizedRecurrenceAt
      (normalizedForwardJet f x nu) (normalizedInverseJet x nu) m := by
  have hnu_closed : nu ∈ Icc (deriv f b) (deriv f a) :=
    ⟨hnu.1.le, hnu.2.le⟩
  have hxnu := hx nu hnu_closed
  have hX0 : 0 < x nu := GK39.point_pos hN hf hxnu.1
  have hnu0 : 0 < nu := by
    rw [← hxnu.2]
    exact GK39.deriv_pos_of_mem_Icc hN hs hy hP heps heps_half hf hxnu.1
  have hg : ContDiffAt ℝ (P - 1) (deriv f) (x nu) :=
    (contDiff_deriv_pred hP hf).contDiffAt
  have hx_cd : ContDiffAt ℝ (P - 1) x nu :=
    GK39.inverse_contDiffAt hN hs hy hP heps heps_half hf hab hx hnu
  have hfaa := iteratedDeriv_comp_eq_sum_orderedFinpartition
    (g := deriv f) (f := x) (x := nu) (i := m) hg hx_cd
    (by
      change ((m : ℕ∞) : ℕ∞ω) ≤
        ((P : ℕ∞) : ℕ∞ω) - (((1 : ℕ) : ℕ∞) : ℕ∞ω)
      rw [← WithTop.coe_sub]
      exact_mod_cast hmP)
  have hIoo : ∀ᶠ v in nhds nu, v ∈ Ioo (deriv f b) (deriv f a) :=
    Ioo_mem_nhds hnu.1 hnu.2
  have hcomp : (deriv f ∘ x) =ᶠ[nhds nu] id := by
    filter_upwards [hIoo] with v hv
    simpa only [Function.comp_apply, id_eq] using
      (hx v ⟨hv.1.le, hv.2.le⟩).2
  have hcomp_deriv :
      iteratedDeriv m (deriv f ∘ x) nu = if m = 1 then 1 else 0 := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq m hcomp]
    simp [iteratedDeriv_id, hm0.ne']
  have hraw :
      (∑ c : OrderedFinpartition m,
        iteratedDeriv c.length (deriv f) (x nu) *
          ∏ j, iteratedDeriv (c.partSize j) x nu) =
        if m = 1 then 1 else 0 := by
    rw [← hfaa]
    exact hcomp_deriv
  rw [InverseJet.normalizedRecurrenceAt]
  have hterm (c : OrderedFinpartition m) :
      InverseJet.partitionTerm
          (normalizedForwardJet f x nu) (normalizedInverseJet x nu) c =
        (iteratedDeriv c.length (deriv f) (x nu) *
            ∏ j, iteratedDeriv (c.partSize j) x nu) * nu ^ m / nu := by
    change InverseJet.partitionTerm
        (fun q => iteratedDeriv q (deriv f) (x nu) * (x nu) ^ q / nu)
        (fun q => iteratedDeriv q x nu * nu ^ q / x nu) c = _
    exact partitionTerm_normalized hX0.ne' hnu0.ne' c
  simp_rw [hterm]
  rw [← Finset.sum_div, ← Finset.sum_mul, hraw]
  split_ifs with hm1
  · subst m
    simp [hnu0.ne']
  · simp

/-! ### The phase ratio -/

/-- The model-to-actual first-derivative ratio lies in `(2/3,2)` and is
`2eps`-close to one. -/
theorem phaseRatio_bounds {N s y eps a b : ℝ} {P : ℕ}
    {f x : ℝ → ℝ} (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 2 ≤ P) (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    {nu : ℝ} (hnu : nu ∈ Ioo (deriv f b) (deriv f a)) :
    0 < phaseRatio s y (x nu) nu ∧
      2 / 3 < phaseRatio s y (x nu) nu ∧
      phaseRatio s y (x nu) nu < 2 ∧
      |phaseRatio s y (x nu) nu - 1| < 2 * eps := by
  have hnu_closed : nu ∈ Icc (deriv f b) (deriv f a) :=
    ⟨hnu.1.le, hnu.2.le⟩
  have hxnu := hx nu hnu_closed
  have hX0 : 0 < x nu := GK39.point_pos hN hf hxnu.1
  have hnu0 : 0 < nu := by
    rw [← hxnu.2]
    exact GK39.deriv_pos_of_mem_Icc hN hs hy hP heps heps_half hf hxnu.1
  let M : ℝ := y * (x nu) ^ (-s)
  have hM0 : 0 < M := by dsimp [M]; positivity
  have happ : |nu - M| < eps * M := by
    have h := GK39.abs_deriv_sub_model_lt hP hf hxnu.1
    rw [hxnu.2] at h
    simpa only [M] using h
  have hepsM : eps * M < (1 / 2) * M :=
    mul_lt_mul_of_pos_right heps_half hM0
  have hhalf : (1 / 2) * M < nu := by
    have := (abs_lt.mp happ).1
    linarith
  have hthreehalf : nu < (3 / 2) * M := by
    have := (abs_lt.mp happ).2
    linarith
  have hq0 : 0 < phaseRatio s y (x nu) nu := by
    unfold phaseRatio
    positivity
  have hq_lower : 2 / 3 < phaseRatio s y (x nu) nu := by
    rw [phaseRatio, show y * (x nu) ^ (-s) = M by rfl,
      lt_div_iff₀ hnu0]
    linarith
  have hq_upper : phaseRatio s y (x nu) nu < 2 := by
    rw [phaseRatio, show y * (x nu) ^ (-s) = M by rfl,
      div_lt_iff₀ hnu0]
    linarith
  have hdiff : |M - nu| < eps * M := by
    simpa only [abs_sub_comm] using happ
  have hq_close : |phaseRatio s y (x nu) nu - 1| < 2 * eps := by
    have hrewrite : M / nu - 1 = (M - nu) / nu := by
      field_simp
    rw [phaseRatio, show y * (x nu) ^ (-s) = M by rfl, hrewrite,
      abs_div, abs_of_pos hnu0]
    calc
      |M - nu| / nu < eps * M / nu :=
        (div_lt_div_iff_of_pos_right hnu0).2 hdiff
      _ = eps * (M / nu) := by ring
      _ < eps * 2 := mul_lt_mul_of_pos_left hq_upper heps
      _ = 2 * eps := by ring
  exact ⟨hq0, hq_lower, hq_upper, hq_close⟩

/-! ### Forward-jet perturbation bounds -/

/-- Before replacing the phase ratio by one, the normalized class inequality
has this exact form. -/
theorem normalizedForwardJet_sub_scaled_model_lt
    {N s y eps a b : ℝ} {P : ℕ} {f x : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) (hP : 2 ≤ P)
    (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    {nu : ℝ} (hnu : nu ∈ Ioo (deriv f b) (deriv f a))
    {m : ℕ} (_hm1 : 1 ≤ m) (hmP : m ≤ P - 1) :
    |normalizedForwardJet f x nu m -
        InverseJet.forwardCoeff s m * phaseRatio s y (x nu) nu| <
      eps * InverseJet.risingCoeff s m * phaseRatio s y (x nu) nu := by
  have hnu_closed : nu ∈ Icc (deriv f b) (deriv f a) :=
    ⟨hnu.1.le, hnu.2.le⟩
  have hxnu := hx nu hnu_closed
  have hX0 : 0 < x nu := GK39.point_pos hN hf hxnu.1
  have hnu0 : 0 < nu := by
    rw [← hxnu.2]
    exact GK39.deriv_pos_of_mem_Icc hN hs hy hP heps heps_half hf hxnu.1
  have hm_lt : m < P := by omega
  have hclass := hf.2.2.2.2 m hm_lt (x nu) hxnu.1
  rw [iteratedDeriv_succ'] at hclass
  let D : ℝ := iteratedDeriv m (deriv f) (x nu)
  let R : ℝ := InverseJet.risingCoeff s m
  let C : ℝ := InverseJet.forwardCoeff s m
  let q : ℝ := phaseRatio s y (x nu) nu
  have hclass' :
      |D - C * y * (x nu) ^ (-s - (m : ℝ))| <
        eps * R * y * (x nu) ^ (-s - (m : ℝ)) := by
    simpa only [D, C, R, InverseJet.forwardCoeff,
      InverseJet.risingCoeff] using hclass
  have hpow0 : 0 < (x nu) ^ m := pow_pos hX0 m
  have hcancel :
      (x nu) ^ (-s - (m : ℝ)) * (x nu) ^ m = (x nu) ^ (-s) :=
    rpow_neg_sub_mul_pow hX0 s m
  have hnormalized :
      |(D - C * y * (x nu) ^ (-s - (m : ℝ))) * (x nu) ^ m / nu| <
        eps * R * q := by
    rw [abs_div, abs_mul, abs_of_pos hpow0, abs_of_pos hnu0]
    have hmul := mul_lt_mul_of_pos_right hclass' hpow0
    have hdiv := (div_lt_div_iff_of_pos_right hnu0).2 hmul
    calc
      |D - C * y * (x nu) ^ (-s - (m : ℝ))| * (x nu) ^ m / nu <
          (eps * R * y * (x nu) ^ (-s - (m : ℝ))) *
            (x nu) ^ m / nu := hdiv
      _ = eps * R * q := by
        dsimp [q, phaseRatio]
        calc
          eps * R * y * (x nu) ^ (-s - (m : ℝ)) * (x nu) ^ m / nu =
              eps * R * y *
                ((x nu) ^ (-s - (m : ℝ)) * (x nu) ^ m) / nu := by ring
          _ = eps * R * y * (x nu) ^ (-s) / nu := by rw [hcancel]
          _ = eps * R * (y * (x nu) ^ (-s) / nu) := by ring
  have hsplit :
      normalizedForwardJet f x nu m - C * q =
        (D - C * y * (x nu) ^ (-s - (m : ℝ))) * (x nu) ^ m / nu := by
    dsimp [normalizedForwardJet, D, q, phaseRatio]
    rw [← hcancel]
    ring
  change |normalizedForwardJet f x nu m - C * q| < eps * R * q
  rw [hsplit]
  exact hnormalized

/-- The normalized forward jets are within
`4 eps (s)_m` of the exact forward power-model coefficients. -/
theorem normalizedForwardJet_sub_model_le
    {N s y eps a b : ℝ} {P : ℕ} {f x : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) (hP : 2 ≤ P)
    (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    {nu : ℝ} (hnu : nu ∈ Ioo (deriv f b) (deriv f a))
    {m : ℕ} (hm1 : 1 ≤ m) (hmP : m ≤ P - 1) :
    |normalizedForwardJet f x nu m - InverseJet.forwardCoeff s m| ≤
      4 * eps * InverseJet.risingCoeff s m := by
  let q : ℝ := phaseRatio s y (x nu) nu
  let R : ℝ := InverseJet.risingCoeff s m
  let C : ℝ := InverseJet.forwardCoeff s m
  have hR0 : 0 < R := InverseJet.risingCoeff_pos hs m
  have hratio := phaseRatio_bounds hN hs hy hP heps heps_half hf hx hnu
  have hq0 : 0 < q := by simpa only [q] using hratio.1
  have hq2 : q < 2 := by simpa only [q] using hratio.2.2.1
  have hq_close : |q - 1| < 2 * eps := by
    simpa only [q] using hratio.2.2.2
  have hscaled := normalizedForwardJet_sub_scaled_model_lt
    hN hs hy hP heps heps_half hf hx hnu hm1 hmP
  have hscaled' :
      |normalizedForwardJet f x nu m - C * q| < eps * R * q := by
    simpa only [C, q, R] using hscaled
  have hcoeff : |C| = R := by
    dsimp [C, R, InverseJet.forwardCoeff]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hR0]
  have hfirst : eps * R * q < 2 * eps * R := by
    calc
      eps * R * q < eps * R * 2 :=
        mul_lt_mul_of_pos_left hq2 (mul_pos heps hR0)
      _ = 2 * eps * R := by ring
  have hsecond : |C * (q - 1)| < 2 * eps * R := by
    rw [abs_mul, hcoeff]
    calc
      R * |q - 1| < R * (2 * eps) :=
        mul_lt_mul_of_pos_left hq_close hR0
      _ = 2 * eps * R := by ring
  have hsplit :
      normalizedForwardJet f x nu m - C =
        (normalizedForwardJet f x nu m - C * q) + C * (q - 1) := by ring
  change |normalizedForwardJet f x nu m - C| ≤ 4 * eps * R
  rw [hsplit]
  calc
    |(normalizedForwardJet f x nu m - C * q) + C * (q - 1)| ≤
        |normalizedForwardJet f x nu m - C * q| + |C * (q - 1)| :=
      abs_add_le _ _
    _ ≤ 2 * eps * R + 2 * eps * R :=
      (add_lt_add (hscaled'.trans hfirst) hsecond).le
    _ = 4 * eps * R := by ring

/-- The first forward jet is uniformly nonzero; this is the denominator bound
required by inverse-jet stability. -/
theorem one_third_s_le_abs_normalizedForwardJet_one
    {N s y eps a b : ℝ} {P : ℕ} {f x : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) (hP : 2 ≤ P)
    (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    {nu : ℝ} (hnu : nu ∈ Ioo (deriv f b) (deriv f a)) :
    s / 3 ≤ |normalizedForwardJet f x nu 1| := by
  let q : ℝ := phaseRatio s y (x nu) nu
  let u : ℝ := normalizedForwardJet f x nu 1
  have hratio := phaseRatio_bounds hN hs hy hP heps heps_half hf hx hnu
  have hq : 2 / 3 < q := by simpa only [q] using hratio.2.1
  have hq0 : 0 < q := by simpa only [q] using hratio.1
  have hscaled := normalizedForwardJet_sub_scaled_model_lt
    hN hs hy hP heps heps_half hf hx hnu (m := 1) le_rfl (by omega)
  have happ : |u + s * q| < eps * s * q := by
    simpa [u, q, InverseJet.forwardCoeff, InverseJet.risingCoeff] using hscaled
  have hsq0 : 0 < s * q := mul_pos hs hq0
  have heps_one : eps < 1 := heps_half.trans (by norm_num)
  have hu_neg : u < 0 := by
    have hu_upper := (abs_lt.mp happ).2
    calc
      u < -(s * q) + eps * (s * q) := by linarith
      _ = -(1 - eps) * (s * q) := by ring
      _ < 0 :=
        mul_neg_of_neg_of_pos (neg_neg_of_pos (sub_pos.mpr heps_one)) hsq0
  rw [abs_of_neg hu_neg]
  have hlower : (1 - eps) * s * q < -u := by
    have hu_upper := (abs_lt.mp happ).2
    linarith
  have hone : 1 / 2 < 1 - eps := by linarith
  have hproduct : s / 3 < (1 - eps) * s * q := by
    calc
      s / 3 = (1 / 2) * s * (2 / 3) := by ring
      _ < (1 - eps) * s * (2 / 3) := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hone hs) (by norm_num)
      _ < (1 - eps) * s * q := by
        exact mul_lt_mul_of_pos_left hq (mul_pos (sub_pos.mpr heps_one) hs)
  exact (hproduct.trans hlower).le

/-! ### Applying finite inverse-jet stability -/

/-- For fixed `s` and `P`, all normalized inverse jets through order `P-1`
are uniformly `O(eps)`-close to the inverse-power coefficients. -/
theorem exists_normalizedInverseJet_bound (s : ℝ) (P : ℕ) (hs : 0 < s) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N y eps a b : ℝ) (f x : ℝ → ℝ),
        0 < N → 0 < y → 0 < eps → eps < 1 / 2 → 2 ≤ P →
        InGKClass N P s y eps a b f → a < b →
        (∀ nu ∈ Icc (deriv f b) (deriv f a),
          x nu ∈ Icc a b ∧ deriv f (x nu) = nu) →
        ∀ nu ∈ Ioo (deriv f b) (deriv f a),
          ∀ p : ℕ, 1 ≤ p → p ≤ P - 1 →
            |normalizedInverseJet x nu p - InverseJet.inverseCoeff s p| ≤
              K * eps := by
  let A : ℕ → ℝ := fun m => 4 * InverseJet.risingCoeff s m
  have hA : ∀ m, 0 ≤ A m := fun m => by
    dsimp [A]
    exact mul_nonneg (by norm_num) (InverseJet.risingCoeff_pos hs m).le
  obtain ⟨K, hK, hstable⟩ :=
    InverseJet.exists_finite_stability_constant A hs (show 0 < s / 3 by positivity)
      hA (P - 1)
  refine ⟨K, hK, ?_⟩
  intro N y eps a b f x hN hy heps heps_half hP hf hab hx nu hnu p hp1 hpP
  apply hstable eps (normalizedForwardJet f x nu) (normalizedInverseJet x nu)
    heps.le heps_half.le
  · exact one_third_s_le_abs_normalizedForwardJet_one
      hN hs hy hP heps heps_half hf hx hnu
  · intro m hm1 hmP
    have h := normalizedForwardJet_sub_model_le
      hN hs hy hP heps heps_half hf hx hnu hm1 hmP
    simpa only [A, mul_assoc, mul_comm, mul_left_comm] using h
  · intro m hm1 hmP
    exact normalizedRecurrenceAt hN hs hy hP heps heps_half hf hab hx hnu
      (Nat.zero_lt_of_lt hm1) hmP
  · exact hp1
  · exact hpP

/-! ### Removing the normalization: the inverse-point scale -/

/-- The inverse-power map is Lipschitz on the fixed compact ratio interval.
The existential constant depends only on `s`. -/
theorem exists_ratio_rpow_lipschitz_constant (s : ℝ) (_hs : 0 < s) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ q ∈ Icc (1 / 2 : ℝ) 2,
      |q ^ (-(1 / s)) - 1| ≤ L * |q - 1| := by
  let psi : ℝ → ℝ := fun q => q ^ (-(1 / s))
  have hpsi : ContDiffOn ℝ 1 psi (Icc (1 / 2 : ℝ) 2) := by
    intro q hq
    have hq0 : 0 < q := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hq.1
    exact (Real.contDiffAt_rpow_const_of_ne hq0.ne').contDiffWithinAt
  obtain ⟨L, hL⟩ :=
    hpsi.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  refine ⟨(L : ℝ), L.2, ?_⟩
  intro q hq
  have h1 : (1 : ℝ) ∈ Icc (1 / 2 : ℝ) 2 := by norm_num
  have h := hL.dist_le_mul q hq 1 h1
  simpa only [psi, Real.dist_eq, one_rpow] using h

/-- Exact algebraic relation between the inverse point, the model scale, and
the first-derivative ratio. -/
theorem inverseScale_mul_ratio_rpow {s y X nu : ℝ}
    (hs : 0 < s) (hy : 0 < y) (hX : 0 < X) (hnu : 0 < nu) :
    y ^ (1 / s) * nu ^ (-(1 / s)) *
        phaseRatio s y X nu ^ (-(1 / s)) = X := by
  have hs_ne : s ≠ 0 := hs.ne'
  have hnu_rpow : 0 < nu ^ (-(1 / s)) := Real.rpow_pos_of_pos hnu _
  unfold phaseRatio
  rw [Real.div_rpow (mul_nonneg hy.le (Real.rpow_nonneg hX.le _)) hnu.le,
    Real.mul_rpow hy.le (Real.rpow_nonneg hX.le _)]
  have hX_cancel : (X ^ (-s)) ^ (-(1 / s)) = X := by
    rw [← Real.rpow_mul hX.le]
    have : (-s) * (-(1 / s)) = 1 := by field_simp
    rw [this, Real.rpow_one]
  rw [hX_cancel]
  have hy_cancel : y ^ (1 / s) * y ^ (-(1 / s)) = 1 := by
    rw [← Real.rpow_add hy]
    simp
  calc
    y ^ (1 / s) * nu ^ (-(1 / s)) *
          (y ^ (-(1 / s)) * X / nu ^ (-(1 / s))) =
        (y ^ (1 / s) * y ^ (-(1 / s))) * X := by
      field_simp [hnu_rpow.ne']
    _ = X := by rw [hy_cancel, one_mul]

/-- The inverse point is `O(eps)`-close, relatively to the model scale, to
`y^(1/s) nu^(-1/s)`.  This is the scaling comparison needed to turn normalized
inverse-jet stability into the derivative estimate of Lemma 3.9. -/
theorem exists_inverseScale_comparison_constant (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N y eps a b : ℝ) (P : ℕ) (f x : ℝ → ℝ),
        0 < N → 0 < y → 0 < eps → eps < 1 / 2 → 2 ≤ P →
        InGKClass N P s y eps a b f →
        (∀ nu ∈ Icc (deriv f b) (deriv f a),
          x nu ∈ Icc a b ∧ deriv f (x nu) = nu) →
        ∀ nu ∈ Ioo (deriv f b) (deriv f a),
          |x nu - y ^ (1 / s) * nu ^ (-(1 / s))| ≤
            C * eps * (y ^ (1 / s) * nu ^ (-(1 / s))) := by
  obtain ⟨L, hL0, hL⟩ := exists_ratio_rpow_lipschitz_constant s hs
  refine ⟨2 * L, mul_nonneg (by norm_num) hL0, ?_⟩
  intro N y eps a b P f x hN hy heps heps_half hP hf hx nu hnu
  have hnu_closed : nu ∈ Icc (deriv f b) (deriv f a) :=
    ⟨hnu.1.le, hnu.2.le⟩
  have hxnu := hx nu hnu_closed
  have hX0 : 0 < x nu := GK39.point_pos hN hf hxnu.1
  have hnu0 : 0 < nu := by
    rw [← hxnu.2]
    exact GK39.deriv_pos_of_mem_Icc hN hs hy hP heps heps_half hf hxnu.1
  let q : ℝ := phaseRatio s y (x nu) nu
  let Y : ℝ := y ^ (1 / s) * nu ^ (-(1 / s))
  have hY0 : 0 < Y := by dsimp [Y]; positivity
  have hratio := phaseRatio_bounds hN hs hy hP heps heps_half hf hx hnu
  have hq_mem : q ∈ Icc (1 / 2 : ℝ) 2 := by
    constructor
    · exact (show (1 / 2 : ℝ) < 2 / 3 by norm_num).le.trans
        (by simpa only [q] using hratio.2.1.le)
    · exact (by simpa only [q] using hratio.2.2.1.le)
  have hq_close : |q - 1| < 2 * eps := by
    simpa only [q] using hratio.2.2.2
  have hscale : Y * q ^ (-(1 / s)) = x nu := by
    simpa only [Y, q] using inverseScale_mul_ratio_rpow hs hy hX0 hnu0
  calc
    |x nu - Y| = Y * |q ^ (-(1 / s)) - 1| := by
      rw [← hscale, show Y * q ^ (-(1 / s)) - Y =
        Y * (q ^ (-(1 / s)) - 1) by ring, abs_mul, abs_of_pos hY0]
    _ ≤ Y * (L * |q - 1|) :=
      mul_le_mul_of_nonneg_left (hL q hq_mem) hY0.le
    _ ≤ Y * (L * (2 * eps)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hq_close.le hL0) hY0.le
    _ = (2 * L) * eps * Y := by ring

end GK39Jets

end LeanProofs.IntegerPoints
