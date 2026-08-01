import PolynomialFormulas.Quartic
import PolynomialFormulas.AbelRuffini

/-!
# Solvability by radicals through degree four

This file connects the verified quadratic, Cardano, and Ferrari formulas to
mathlib's semantic field `solvableByRad ℚ ℂ`.  The coefficient-generic root
lemmas work whenever all coefficients already belong to that field.  Their
branch constructions supply the compatibility hypotheses required by the
formula APIs, including Cardano's zero-radicand case and Ferrari's `s = 0`
case.

The final theorem proves that every complex root of every rational polynomial
of degree at most four belongs to `solvableByRad ℚ ℂ`.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.LowDegreeRadicals

noncomputable section

/-- The intermediate field of complex numbers solvable by radicals over `ℚ`. -/
abbrev RField := solvableByRad ℚ ℂ

/-- Every rational constant belongs to the radical field. -/
theorem rat_mem (q : ℚ) : (q : ℂ) ∈ RField := by
  exact IntermediateField.algebraMap_mem _ q

/-- Every positive-order radical of an element of the radical field exists in
`ℂ` and again belongs to the radical field. -/
theorem exists_radical_mem (z : ℂ) (hz : z ∈ RField) (n : ℕ) (hn : n ≠ 0) :
    ∃ w : ℂ, w ^ n = z ∧ w ∈ RField := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z (Nat.pos_of_ne_zero hn)
  refine ⟨w, hw, solvableByRad.rad_mem hn ?_⟩
  rwa [hw]

/-- A root of a genuine quadratic whose coefficients belong to the radical
field also belongs to the radical field. -/
theorem quadratic_root_mem
    {a b c x : ℂ}
    (haR : a ∈ RField) (hbR : b ∈ RField) (hcR : c ∈ RField)
    (ha : a ≠ 0) (hx : quadratic a b c x = 0) :
    x ∈ RField := by
  have hdisc : b ^ 2 - 4 * a * c ∈ RField := by
    exact sub_mem (pow_mem hbR 2) (mul_mem (mul_mem (rat_mem 4) haR) hcR)
  obtain ⟨s, hs, hsR⟩ := exists_radical_mem _ hdisc 2 (by decide)
  rcases (quadratic_eq_zero_iff ha hs).mp hx with rfl | rfl
  · exact div_mem (add_mem (neg_mem hbR) hsR) (mul_mem (rat_mem 2) haR)
  · exact div_mem (sub_mem (neg_mem hbR) hsR) (mul_mem (rat_mem 2) haR)

/-- A root of a genuine linear equation over the radical field belongs to the
radical field. -/
theorem linear_root_mem
    {a b x : ℂ} (haR : a ∈ RField) (hbR : b ∈ RField)
    (ha : a ≠ 0) (hx : linear a b x = 0) : x ∈ RField := by
  rw [linear_eq_zero_iff ha] at hx
  rw [hx]
  exact div_mem (neg_mem hbR) haR

theorem cubicP_mem {A B : ℂ} (hA : A ∈ RField) (hB : B ∈ RField) :
    cubicP A B ∈ RField := by
  exact sub_mem hB (mul_mem (rat_mem 3) (pow_mem (div_mem hA (rat_mem 3)) 2))

theorem cubicQ_mem {A B C : ℂ}
    (hA : A ∈ RField) (hB : B ∈ RField) (hC : C ∈ RField) :
    cubicQ A B C ∈ RField := by
  exact add_mem
    (sub_mem hC (mul_mem hB (div_mem hA (rat_mem 3))))
    (mul_mem (rat_mem 2) (pow_mem (div_mem hA (rat_mem 3)) 3))

theorem cubicDelta_mem {p q : ℂ} (hp : p ∈ RField) (hq : q ∈ RField) :
    cubicDelta p q ∈ RField := by
  exact add_mem (pow_mem (div_mem hq (rat_mem 2)) 2)
    (pow_mem (div_mem hp (rat_mem 3)) 3)

/-- A root of a genuine cubic whose coefficients belong to the radical field
also belongs to the radical field.

The proof constructs a compatible Cardano pair.  If the first cube radicand
vanishes, the discriminant identity forces `p = 0`; otherwise the second cube
root is chosen as `(-p / 3) / u`. -/
theorem cubic_root_mem
    {a b c d x : ℂ}
    (haR : a ∈ RField) (hbR : b ∈ RField) (hcR : c ∈ RField)
    (hdR : d ∈ RField) (ha : a ≠ 0) (hx : cubic a b c d x = 0) :
    x ∈ RField := by
  let A := b / a
  let B := c / a
  let C := d / a
  let p := cubicP A B
  let q := cubicQ A B C
  have hAR : A ∈ RField := div_mem hbR haR
  have hBR : B ∈ RField := div_mem hcR haR
  have hCR : C ∈ RField := div_mem hdR haR
  have hpR : p ∈ RField := cubicP_mem hAR hBR
  have hqR : q ∈ RField := cubicQ_mem hAR hBR hCR
  obtain ⟨s, hs, hsR⟩ :=
    exists_radical_mem (cubicDelta p q) (cubicDelta_mem hpR hqR) 2 (by decide)
  let U := -q / 2 + s
  let V := -q / 2 - s
  have hUR : U ∈ RField := add_mem (div_mem (neg_mem hqR) (rat_mem 2)) hsR
  have hVR : V ∈ RField := sub_mem (div_mem (neg_mem hqR) (rat_mem 2)) hsR
  have hUV : U * V = (-p / 3) ^ 3 := by
    have h := cardano_discriminant_equation hs
    dsimp [U, V]
    calc
      (-q / 2 + s) * (-q / 2 - s) = -(p / 3) ^ 3 := h
      _ = (-p / 3) ^ 3 := by ring
  obtain ⟨w, hw, hwR⟩ :=
    exists_radical_mem (-3 : ℂ) (neg_mem (rat_mem 3)) 2 (by decide)
  let ω := (-1 + w) / 2
  have hωR : ω ∈ RField :=
    div_mem (add_mem (neg_mem (one_mem RField)) hwR) (rat_mem 2)
  have hω : ω ^ 2 + ω + 1 = 0 := by
    dsimp [ω]
    calc
      ((-1 + w) / 2) ^ 2 + (-1 + w) / 2 + 1 = (w ^ 2 + 3) / 4 := by ring
      _ = 0 := by rw [hw]; norm_num
  have finish (u v : ℂ)
      (hu : u ^ 3 = U) (hv : v ^ 3 = V) (huv : u * v = -p / 3)
      (huR : u ∈ RField) (hvR : v ∈ RField) : x ∈ RField := by
    obtain ⟨i, hi⟩ := solveCubic_exhaustive ha hu hv huv hω hx
    subst x
    have hshift : (b / a) / 3 ∈ RField := div_mem (div_mem hbR haR) (rat_mem 3)
    fin_cases i
    · exact sub_mem (add_mem huR hvR) hshift
    · exact sub_mem
        (add_mem (mul_mem hωR huR) (mul_mem (pow_mem hωR 2) hvR)) hshift
    · exact sub_mem
        (add_mem (mul_mem (pow_mem hωR 2) huR) (mul_mem hωR hvR)) hshift
  by_cases hU : U = 0
  · have hp : p = 0 := by
      have hp3 : (-p / 3) ^ 3 = 0 := by rw [← hUV, hU, zero_mul]
      have hpdiv : -p / 3 = 0 := by
        by_contra hne
        exact (pow_ne_zero 3 hne) hp3
      simpa using hpdiv
    obtain ⟨v, hv, hvR⟩ := exists_radical_mem V hVR 3 (by decide)
    exact finish 0 v (by simp [hU]) hv (by simp [hp]) (zero_mem _) hvR
  · obtain ⟨u, hu, huR⟩ := exists_radical_mem U hUR 3 (by decide)
    have hu0 : u ≠ 0 := by
      intro hu0
      apply hU
      rw [← hu, hu0]
      norm_num
    let v := (-p / 3) / u
    have hvR : v ∈ RField := div_mem (div_mem (neg_mem hpR) (rat_mem 3)) huR
    have huv : u * v = -p / 3 := by
      dsimp [v]
      field_simp
    have hv : v ^ 3 = V := by
      dsimp [v]
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero 3 hu0)).2
      rw [hu]
      simpa [mul_comm] using hUV.symm
    exact finish u v hu hv huv huR hvR

theorem quarticP_mem {A B : ℂ} (hA : A ∈ RField) (hB : B ∈ RField) :
    quarticP A B ∈ RField := by
  exact sub_mem hB (mul_mem (rat_mem 6) (pow_mem (div_mem hA (rat_mem 4)) 2))

theorem quarticQ_mem {A B C : ℂ}
    (hA : A ∈ RField) (hB : B ∈ RField) (hC : C ∈ RField) :
    quarticQ A B C ∈ RField := by
  exact add_mem
    (sub_mem hC (mul_mem (mul_mem (rat_mem 2) hB) (div_mem hA (rat_mem 4))))
    (mul_mem (rat_mem 8) (pow_mem (div_mem hA (rat_mem 4)) 3))

theorem quarticR_mem {A B C D : ℂ}
    (hA : A ∈ RField) (hB : B ∈ RField) (hC : C ∈ RField)
    (hD : D ∈ RField) : quarticR A B C D ∈ RField := by
  exact sub_mem
    (add_mem
      (sub_mem hD (mul_mem hC (div_mem hA (rat_mem 4))))
      (mul_mem hB (pow_mem (div_mem hA (rat_mem 4)) 2)))
    (mul_mem (rat_mem 3) (pow_mem (div_mem hA (rat_mem 4)) 4))

/-- A root of a genuine quartic whose coefficients belong to the radical field
also belongs to the radical field.

The cubic resolvent root belongs to the radical field by `cubic_root_mem`.  If
Ferrari's square radical `s` vanishes, the resolvent identity forces `q = 0`
and `t` is chosen independently as a square root; otherwise
`ferrari_parameters_of_resolvent` supplies `t`. -/
theorem quartic_root_mem
    {a b c d e x : ℂ}
    (haR : a ∈ RField) (hbR : b ∈ RField) (hcR : c ∈ RField)
    (hdR : d ∈ RField) (heR : e ∈ RField)
    (ha : a ≠ 0) (hx : quartic a b c d e x = 0) :
    x ∈ RField := by
  let A := b / a
  let B := c / a
  let C := d / a
  let D := e / a
  let p := quarticP A B
  let q := quarticQ A B C
  let r := quarticR A B C D
  have hAR : A ∈ RField := div_mem hbR haR
  have hBR : B ∈ RField := div_mem hcR haR
  have hCR : C ∈ RField := div_mem hdR haR
  have hDR : D ∈ RField := div_mem heR haR
  have hpR : p ∈ RField := quarticP_mem hAR hBR
  have hqR : q ∈ RField := quarticQ_mem hAR hBR hCR
  have hrR : r ∈ RField := quarticR_mem hAR hBR hCR hDR
  let resolventCubic : ℂ[X] :=
    Polynomial.C (-8) * X ^ 3 + Polynomial.C (4 * p) * X ^ 2 +
      Polynomial.C (8 * r) * X + Polynomial.C (q ^ 2 - 4 * p * r)
  have hresDegree : resolventCubic.degree ≠ 0 := by
    rw [show resolventCubic.degree = 3 by
      dsimp [resolventCubic]
      exact Polynomial.degree_cubic (by norm_num : (-8 : ℂ) ≠ 0)]
    norm_num
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_root resolventCubic hresDegree
  have hmcubic : cubic (-8) (4 * p) (8 * r) (q ^ 2 - 4 * p * r) m = 0 := by
    simpa [resolventCubic, Polynomial.IsRoot, cubic] using hm
  have hmR : m ∈ RField := by
    apply cubic_root_mem (neg_mem (rat_mem 8))
      (mul_mem (rat_mem 4) hpR) (mul_mem (rat_mem 8) hrR)
      (sub_mem (pow_mem hqR 2) (mul_mem (mul_mem (rat_mem 4) hpR) hrR))
      (by norm_num : (-8 : ℂ) ≠ 0)
    exact hmcubic
  have hres : ferrariResolvent p q r m = 0 := by
    unfold ferrariResolvent cubic at *
    linear_combination hmcubic
  have hsRadicand : 2 * m - p ∈ RField :=
    sub_mem (mul_mem (rat_mem 2) hmR) hpR
  obtain ⟨s, hs, hsR⟩ := exists_radical_mem (2 * m - p) hsRadicand 2 (by decide)
  have finish (t : ℂ)
      (hst : 2 * s * t = -q) (ht : t ^ 2 = m ^ 2 - r)
      (htR : t ∈ RField) : x ∈ RField := by
    have hρRadicand : s ^ 2 - 4 * (m - t) ∈ RField :=
      sub_mem (pow_mem hsR 2)
        (mul_mem (rat_mem 4) (sub_mem hmR htR))
    have hσRadicand : s ^ 2 - 4 * (m + t) ∈ RField :=
      sub_mem (pow_mem hsR 2)
        (mul_mem (rat_mem 4) (add_mem hmR htR))
    obtain ⟨ρ, hρ, hρR⟩ :=
      exists_radical_mem _ hρRadicand 2 (by decide)
    obtain ⟨σ, hσ, hσR⟩ :=
      exists_radical_mem _ hσRadicand 2 (by decide)
    obtain ⟨i, hi⟩ := solveQuartic_exhaustive ha hs hst ht hρ hσ hx
    subst x
    have hshift : (b / a) / 4 ∈ RField := div_mem (div_mem hbR haR) (rat_mem 4)
    fin_cases i
    · exact sub_mem (div_mem (add_mem hsR hρR) (rat_mem 2)) hshift
    · exact sub_mem (div_mem (sub_mem hsR hρR) (rat_mem 2)) hshift
    · exact sub_mem (div_mem (add_mem (neg_mem hsR) hσR) (rat_mem 2)) hshift
    · exact sub_mem (div_mem (sub_mem (neg_mem hsR) hσR) (rat_mem 2)) hshift
  by_cases hs0 : s = 0
  · have hmp : 2 * m - p = 0 := by rw [← hs, hs0]; norm_num
    have hq2 : q ^ 2 = 0 := by
      unfold ferrariResolvent at hres
      rw [hmp] at hres
      simpa using hres
    have hq0 : q = 0 := by
      by_contra hne
      exact (pow_ne_zero 2 hne) hq2
    obtain ⟨t, ht, htR⟩ :=
      exists_radical_mem (m ^ 2 - r) (sub_mem (pow_mem hmR 2) hrR) 2 (by decide)
    exact finish t (by simp [hs0, hq0]) ht htR
  · let t := -q / (2 * s)
    obtain ⟨hst, ht⟩ := ferrari_parameters_of_resolvent hres hs hs0
    have htR : t ∈ RField :=
      div_mem (neg_mem hqR) (mul_mem (rat_mem 2) hsR)
    exact finish t hst ht htR

/-- Every complex root of a rational polynomial of degree at most four is
contained in the field of elements solvable by radicals over `ℚ`. -/
theorem root_mem_of_natDegree_le_four
    {P : ℚ[X]} (hdeg : P.natDegree ≤ 4) (x : P.rootSet ℂ) :
    (x : ℂ) ∈ RField := by
  have hroot : P.aeval (x : ℂ) = 0 := aeval_eq_zero_of_mem_rootSet x.property
  have hlt : P.natDegree < 5 := hdeg.trans_lt (by decide)
  have heval :
      quartic (P.coeff 4 : ℂ) (P.coeff 3 : ℂ) (P.coeff 2 : ℂ)
        (P.coeff 1 : ℂ) (P.coeff 0 : ℂ) (x : ℂ) = 0 := by
    rw [aeval_eq_sum_range' hlt] at hroot
    simp [Finset.sum_range_succ, Algebra.smul_def] at hroot
    unfold quartic
    linear_combination hroot
  by_cases h4 : P.coeff 4 = 0
  · have hcubic :
        cubic (P.coeff 3 : ℂ) (P.coeff 2 : ℂ) (P.coeff 1 : ℂ)
          (P.coeff 0 : ℂ) (x : ℂ) = 0 := by
      simpa [quartic, cubic, h4] using heval
    by_cases h3 : P.coeff 3 = 0
    · have hquadratic :
          quadratic (P.coeff 2 : ℂ) (P.coeff 1 : ℂ) (P.coeff 0 : ℂ) (x : ℂ) = 0 := by
        simpa [cubic, quadratic, h3] using hcubic
      by_cases h2 : P.coeff 2 = 0
      · have hlinear :
            linear (P.coeff 1 : ℂ) (P.coeff 0 : ℂ) (x : ℂ) = 0 := by
          simpa [quadratic, linear, h2] using hquadratic
        by_cases h1 : P.coeff 1 = 0
        · have h0C : (P.coeff 0 : ℂ) = 0 := by
            simpa [linear, h1] using hlinear
          have h0 : P.coeff 0 = 0 := by exact_mod_cast h0C
          have hPzero : P = 0 := by
            ext n
            by_cases hn : n ≤ 4
            · interval_cases n <;> simp [h0, h1, h2, h3, h4]
            · exact (natDegree_le_iff_coeff_eq_zero.mp hdeg n
                (Nat.lt_of_not_ge hn)).trans (coeff_zero n).symm
          exact (ne_zero_of_mem_rootSet x.property hPzero).elim
        · apply linear_root_mem (rat_mem _) (rat_mem _)
            (by exact_mod_cast h1)
          exact hlinear
      · apply quadratic_root_mem (rat_mem _) (rat_mem _) (rat_mem _)
          (by exact_mod_cast h2)
        exact hquadratic
    · apply cubic_root_mem (rat_mem _) (rat_mem _) (rat_mem _) (rat_mem _)
        (by exact_mod_cast h3)
      exact hcubic
  · apply quartic_root_mem (rat_mem _) (rat_mem _) (rat_mem _) (rat_mem _) (rat_mem _)
      (by exact_mod_cast h4)
    exact heval

/-- Every rational polynomial of degree at most four is completely solvable
by radicals in the semantic sense used by the Abel--Ruffini development. -/
theorem completelySolvableByRadicals_of_natDegree_le_four
    {P : ℚ[X]} (hdeg : P.natDegree ≤ 4) :
    CompletelySolvableByRadicals P := by
  intro x
  exact root_mem_of_natDegree_le_four hdeg x

end

end LeanProofs.PolynomialFormulas.LowDegreeRadicals
