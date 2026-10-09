import GowersSzemeredi.Proofs16GlobalProgressionGeometry

/-! Uniform ambient density for the initial proper-progression geometry.
Finite rank and tuple caps remove the dependence on selected witnesses. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def progressionGeometryDensity (beta epsilon width : Real) (ell M t : Nat) : Real :=
  ((beta^4 - epsilon) / ((M + 1 : Nat)^(4 * ell) : Real)) *
    Real.exp (-(((t : Real) + 1) * width + 10 * ((t : Real) + 1)^2))

theorem progressionGeometryDensity_pos {beta epsilon width : Real} (h : epsilon < beta^4)
    (ell M t : Nat) : 0 < progressionGeometryDensity beta epsilon width ell M t := by
  unfold progressionGeometryDensity
  exact mul_pos (div_pos (sub_pos.mpr h) (by positivity)) (Real.exp_pos _)

/-- Increasing the tuple and rank caps only weakens the guaranteed density. -/
theorem progressionGeometryDensity_antitone_caps {beta epsilon width : Real}
    (heps : epsilon ≤ beta^4) (hw : 0 ≤ width) (ell M t m s : Nat)
    (hm : m ≤ M) (hs : s ≤ t) :
    progressionGeometryDensity beta epsilon width ell M t ≤
      progressionGeometryDensity beta epsilon width ell m s := by
  unfold progressionGeometryDensity
  apply mul_le_mul
  · apply div_le_div_of_nonneg_left (sub_nonneg.mpr heps) (by positivity)
    exact_mod_cast Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) (4 * ell)
  · apply Real.exp_le_exp.mpr
    have hst : (s : Real) ≤ t := by exact_mod_cast hs
    have hs0 : (0 : Real) ≤ s := Nat.cast_nonneg _
    have ht0 : (0 : Real) ≤ t := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right (add_le_add_right hst 1) hw
    nlinarith
  · positivity
  · positivity

/-- The extraction scale is at most one for epsilon in [0,1]. -/
theorem corollary20Kappa_le_one {epsilon : Real} (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (K : Nat) (hK : 0 < K) : corollary20Kappa epsilon K ≤ 1 := by
  have hK1 : (1 : Real) ≤ K := by exact_mod_cast hK
  have hden : (1 : Real) ≤ 1024 * (K : Real)^4 := by nlinarith [one_le_pow₀ hK1 (n := 4)]
  have he : epsilon / (1024 * (K : Real)^4) ≤ 1 := (div_le_one (by positivity)).mpr (heps1.trans hden)
  have he0 : 0 ≤ epsilon / (1024 * (K : Real)^4) := by positivity
  have hpow : ((epsilon / (1024 * (K : Real)^4))^2)^1164 ≤ 1 := by
    have hsq : (epsilon / (1024 * (K : Real)^4))^2 ≤ 1 := by simpa using pow_le_pow_left₀ he0 he 2
    simpa using pow_le_pow_left₀ (sq_nonneg _) hsq 1164
  have htwo : (2 : Real)^(-(1882 : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  unfold corollary20Kappa
  exact (mul_le_mul htwo hpow (by positivity) (by norm_num)).trans (by norm_num)

end LeanProofs.GowersSzemeredi
