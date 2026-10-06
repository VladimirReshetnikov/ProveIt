import GowersSzemeredi.Proofs02Partition

/-! # Linear recurrence at a prescribed denominator cutoff -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Dirichlet approximation supplies a short multiplier with small centered
residue. This covers degree one, outside the Weyl recurrence's degree range. -/
theorem linear_small_multiplier {N : Nat} [NeZero N] (t : Nat) (ht : 2 ≤ t)
    (a : ZMod N) :
    ∃ u : Nat, 0 < u ∧ u ≤ t ∧
      (centeredAbs ((u : ZMod N) * a) : Real) ≤ (N : Real) / (t + 1) := by
  have hNreal : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let xi : Real := (a.val : Real) / N
  obtain ⟨j, k, hkpos, hkt, happ⟩ :=
    Real.exists_int_int_abs_mul_sub_le xi (by omega : 0 < t)
  let u : Nat := k.toNat
  have hku : (u : Int) = k := Int.toNat_of_nonneg hkpos.le
  have hu : 0 < u := by
    have hkupos : (0 : Int) < (u : Int) := by simpa only [hku] using hkpos
    exact_mod_cast hkupos
  have hut : u ≤ t := by
    have : (u : Int) ≤ (t : Int) := by simpa only [hku] using hkt
    exact_mod_cast this
  let z : Int := k * (a.val : Int) - j * (N : Int)
  have hzcast : (z : ZMod N) = (u : ZMod N) * a := by
    dsimp only [z]
    rw [Int.cast_sub, Int.cast_mul, Int.cast_mul]
    simp only [hku.symm, Int.cast_natCast, ZMod.natCast_self, mul_zero, sub_zero]
    rw [ZMod.natCast_zmod_val]
  have hzdiv : (z : Real) / N = (k : Real) * xi - j := by
    dsimp only [z, xi]
    push_cast
    field_simp
  have hzabs : |(z : Real)| ≤ (N : Real) / (t + 1) := by
    rw [← hzdiv, abs_div, abs_of_pos hNreal] at happ
    rw [div_le_iff₀ hNreal] at happ
    calc
      |(z : Real)| ≤ 1 / ((t : Real) + 1) * N := happ
      _ = (N : Real) / (t + 1) := by ring
  have hzhalf : |(z : Real)| < (N : Real) / 2 := by
    refine hzabs.trans_lt ?_
    exact div_lt_div_of_pos_left hNreal (by norm_num) (by exact_mod_cast (show 2 < t + 1 by omega))
  have hzinterval : z * 2 ∈ Set.Ioc (-(N : Int)) N := by
    have hzreal := (abs_lt.mp hzhalf)
    have hlow : -(N : Real) < (z : Real) * 2 := by nlinarith [hzreal.1]
    have hupp : (z : Real) * 2 ≤ N := by nlinarith [hzreal.2]
    constructor
    · exact_mod_cast hlow
    · exact_mod_cast hupp
  have hzmin : ((u : ZMod N) * a).valMinAbs = z :=
    (ZMod.valMinAbs_spec _ _).2 ⟨hzcast.symm, hzinterval⟩
  refine ⟨u, hu, hut, ?_⟩
  rw [centeredAbs, hzmin]
  simpa only [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast] using hzabs

end LeanProofs.GowersSzemeredi
