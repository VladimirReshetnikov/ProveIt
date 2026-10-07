import GowersSzemeredi.Proofs05Downstream
import GowersSzemeredi.Proofs05ModularApproximation
import GowersSzemeredi.Proofs05QuadraticLocalizationBudget

/-! Uniform phase control for the leading quadratic term on a short chunk. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem centeredAbs_mul_natCast_pow_le {N : Nat} [NeZero N]
    (b : ZMod N) (t k : Nat) :
    centeredAbs (b * (t : ZMod N) ^ k) ≤ centeredAbs b * t ^ k := by
  have heq : (((b.valMinAbs * (t : Int) ^ k) : Int) : ZMod N) = b * (t : ZMod N) ^ k := by
    push_cast
    rfl
  calc
    _ ≤ (b.valMinAbs * (t : Int) ^ k).natAbs := by
      rw [← heq]
      exact recurrence_centeredAbs_intCast_le _
    _ = _ := by rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]; rfl

theorem exponential_neg_add_distance {N : Nat} [NeZero N] (b y : ZMod N) :
    ‖exponential (-(b + y)) - exponential (-y)‖ = ‖exponential (-b) - 1‖ := by
  have heq : exponential (-(b + y)) - exponential (-y) =
      exponential (-y) * (exponential (-b) - 1) := by
    rw [show -(b + y) = -y + -b by ring]
    simp only [exponential, AddChar.map_add_eq_mul]
    ring
  rw [heq, norm_mul]
  rw [show ‖exponential (-y)‖ = 1 from AddChar.norm_apply (ZMod.stdAddChar (N := N)) _, one_mul]

theorem quadratic_leading_phase_error {N L t : Nat} [NeZero N]
    (b y : ZMod N) (hL : 2 ≤ L)
    (hb : (centeredAbs b : Real) ≤ (N : Real) / quadraticLocalizationPrecision L)
    (ht : t ≤ 2 * quadraticLocalizationChunk L) :
    ‖exponential (-(b * (t : ZMod N) ^ 2 + y)) - exponential (-y)‖ ≤
      1 / (8 * L) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hR : (0 : Real) < quadraticLocalizationPrecision L := by
    exact_mod_cast (show 0 < quadraticLocalizationPrecision L by
      have := quadraticLocalization_precision_ge_two hL; omega)
  have htR : (t : Real) ≤ 2 * (quadraticLocalizationChunk L : Real) := by exact_mod_cast ht
  have hbmul : (centeredAbs (b * (t : ZMod N) ^ 2) : Real) ≤
      (centeredAbs b : Real) * (t : Real) ^ 2 := by
    exact_mod_cast centeredAbs_mul_natCast_pow_le b t 2
  rw [exponential_neg_add_distance]
  calc
    _ ≤ 2 * Real.pi * centeredAbs (-(b * (t : ZMod N) ^ 2)) / N :=
      downstream_norm_exponential_sub_one_le _
    _ = 2 * Real.pi * centeredAbs (b * (t : ZMod N) ^ 2) / N := by
      simp only [centeredAbs, ZMod.natAbs_valMinAbs_neg]
    _ ≤ 2 * Real.pi * ((N : Real) / quadraticLocalizationPrecision L *
          (2 * (quadraticLocalizationChunk L : Real)) ^ 2) / N := by
      gcongr
      exact hbmul.trans (mul_le_mul hb (pow_le_pow_left₀ (by positivity) htR 2)
        (by positivity) (by positivity))
    _ = 2 * Real.pi * (2 * (quadraticLocalizationChunk L : Real)) ^ 2 /
        quadraticLocalizationPrecision L := by field_simp
    _ ≤ _ := quadraticLocalization_leading_error hL

end LeanProofs.GowersSzemeredi
