import GRHArticle.SingularModuli.QuarticIrreducibility
import GRHArticle.SingularModuli.RootCertificates

/-!
# Exact minimum support for two explicit quartics

The relative p-adic disks in smd:ex:hand and the factorial threshold
criterion certify minimum support five for each root.
-/

namespace GRHArticle.SingularModuli

open Polynomial

/-- Every root of the quartic at discriminant -55 has minimum support five. -/
theorem quartic55_minimumSupport
    {L : Type*} [Field L] [Algebra ℚ L]
    (x : L) (hx : aeval x quartic55 = 0) :
    minimumSupport (K := ℚ) (x := x) ⟨quartic55, quartic55_monic, hx⟩ = 5 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h := minimumSupport_eq_of_threshold_disk (p := 3) quartic55 quartic55_monic
    quartic55_irreducible x hx (27 : ℂ_[3]) (by norm_num) (κ := 1) (by norm_num)
    (by
      intro i hi d hd
      rw [quartic55_natDegree] at hi
      have hv := factorialIntervalValuation_three_le (i := i) (d := d) (by omega) hd
      simpa using (show (factorialIntervalValuation 3 i d : ℚ) ≤ (d : ℚ) by exact_mod_cast hv))
    (by
      intro y hy
      simpa only [Nat.cast_ofNat, Rat.cast_one] using quartic55_root_in_disk hy)
  simpa only [quartic55_natDegree] using h

/-- Every root of the quartic at discriminant -68 has minimum support five. -/
theorem quartic68_minimumSupport
    {L : Type*} [Field L] [Algebra ℚ L]
    (x : L) (hx : aeval x quartic68 = 0) :
    minimumSupport (K := ℚ) (x := x) ⟨quartic68, quartic68_monic, hx⟩ = 5 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h := minimumSupport_eq_of_threshold_disk (p := 2) quartic68 quartic68_monic
    quartic68_irreducible x hx (192 : ℂ_[2]) (by norm_num) (κ := 5 / 2) (by norm_num)
    (by
      intro i hi d hd
      rw [quartic68_natDegree] at hi
      have hv := factorialIntervalValuation_two_le (i := i) (d := d) (by omega) hd
      have hv' : (factorialIntervalValuation 2 i d : ℚ) ≤ 2 * (d : ℚ) := by
        exact_mod_cast hv
      have hmul : 2 * (d : ℚ) ≤ (d : ℚ) * (5 / 2) := by
        have hdn : (0 : ℚ) ≤ d := Nat.cast_nonneg _
        linarith
      exact hv'.trans hmul)
    (by
      intro y hy
      simpa only [Nat.cast_ofNat, Rat.cast_div, Rat.cast_ofNat] using quartic68_root_in_disk hy)
  simpa only [quartic68_natDegree] using h

end GRHArticle.SingularModuli
