import Surreal.Surcomplex.PolarNormalization

/-!
# Recovering an exact angle sum from its half-turn phase

A finite angle strictly between zero and three pi whose phase is minus
one equals pi exactly. The ordinary integral period kernel excludes all
other possibilities, supplying the final prerequisite for
`trigonometry:thm:anglesum`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

/-- In the interval `(0, 3*pi)`, a half-turn phase forces the exact finite angle `pi`. -/
theorem finiteAngle_eq_pi_of_phase_eq_neg_one (θ : SignSequence.FiniteElement.{u})
    (hlo : 0 < θ.val) (hhi : θ.val < 3 * SignSequence.ofReal Real.pi)
    (hp : finitePhase θ = -1) : θ = SignSequence.finiteOfReal Real.pi := by
  obtain ⟨n, hn⟩ := (finitePhase_eq_iff θ (SignSequence.finiteOfReal Real.pi)).mp
    (hp.trans finitePhase_pi.symm)
  have hpi : (0 : SignSequence.{u}) < SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono Real.pi_pos
  have hneg : SignSequence.ofReal (-(2 * Real.pi)) <
      θ.val - SignSequence.ofReal Real.pi := by
    rw [map_neg, map_mul, map_ofNat]
    linarith only [hlo, hpi]
  have hpos : θ.val - SignSequence.ofReal Real.pi < SignSequence.ofReal (2 * Real.pi) := by
    rw [map_mul, map_ofNat]
    linarith only [hhi]
  change θ.val - SignSequence.ofReal Real.pi = _ at hn
  rw [hn] at hneg hpos
  have hneg' := SignSequence.ofReal_strictMono.lt_iff_lt.mp hneg
  have hpos' := SignSequence.ofReal_strictMono.lt_iff_lt.mp hpos
  have hnlo : (-1 : ℝ) < n := by nlinarith only [hneg', Real.pi_pos]
  have hnhi : (n : ℝ) < 1 := by nlinarith only [hpos', Real.pi_pos]
  have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
  have hnhi' : n < (1 : ℤ) := by exact_mod_cast hnhi
  have hnzero : n = 0 := by omega
  apply ArchimedeanClass.FiniteElement.ext
  change θ.val = SignSequence.ofReal Real.pi
  apply sub_eq_zero.mp
  simpa only [hnzero, Int.cast_zero, zero_mul, map_zero] using hn

end Surreal.Surcomplex
