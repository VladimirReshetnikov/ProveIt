import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.Terminal.GaussianGammaNegativeIntervalNamedTerminalDerivative

/-!
# The increment and its dyadic bound on a negative Gamma interval

Subtracting the base offset from its original named sum recovers the
increment. The terminal derivative modulus bounds the increment by the
dyadic radius needed for the finite inverse factor.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedIncrementSetup

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialSmallPerturbation (smallSamples small_samples_at)
open GaussianGammaNegativeIntervalNamedTerminalDerivative (source modulus derivativeModulus)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast zeroF zero_at zero_fast
  add_associative add_commutative add_negative)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "sumF" => GaussianNamedGammaSmallIncrementInput.sumF
local notation "sumData" => GaussianNamedGammaSmallIncrementInput.sumData
local notation "diffF" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem zero_cross (x z : PTm n) : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF x z := by
  refine GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast _) (zero_fast _) (.allI ?_)
  exact (zero_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x)).eqTrans (zero_at (var 0) (Syn.shift z)).eqSymm

theorem increment_cross (f K : PR 2) (x z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hk : Γ ⊢[PRAAx] pointCN K z) :
    Γ ⊢[PRAAx] crossEquivalent (diffF (sumF f K) f) K (diffData (sumData x z) x) z := by
  let H := negativeF f
  let w := negativeData x
  let F := addF f H
  let u := addData x w
  have hh := negative_fast f x hf
  have turn := add_cross (addF f K) (addF K f) H H (addData x z) (addData z x) w w
    (add_fast _ _ _ _ hf hk) (add_fast _ _ _ _ hk hf) hh hh
    (add_commutative f K x z hf hk) (cross_refl H w hh)
  have assoc := add_associative K f H z x w hk hf hh
  have cancel := cross_trans F zeroF zeroF u x z (add_negative f x hf) (zero_cross x z)
  have move := add_cross K K F zeroF z z u z hk hk (add_fast _ _ _ _ hf hh)
    (zero_fast z) (cross_refl K z hk) cancel
  exact cross_trans _ _ _ _ _ _ turn
    (cross_trans _ _ _ _ _ _ assoc (cross_trans _ _ _ _ _ _ move (GaussianNameRingLaws.add_zero K z hk)))

private theorem unit_le_euler_modulus (p j R A : PTm n) :
    Γ ⊢[PRAAx] le (unit p) (GaussianEulerLogarithmicContinuity.modulus p j R A) := by
  let E := GaussianEulerLogarithmicContinuity.intervalDen p j R A
  let T := GaussianEulerLogarithmicContinuity.intervalTop p j R A
  let L := GaussianEulerLogarithmicMultiplier.logRadius E T
  let G := GaussianEulerLogarithmicContinuity.compactGain j R E T
  have hT : Γ ⊢[PRAAx] le one T := GaussianGammaIntegralCutoffs.top_positive _ _ _
  have hL : Γ ⊢[PRAAx] le one L := by
    dsimp only [L,GaussianEulerLogarithmicMultiplier.logRadius,GaussianCompactLogarithmBounds.radius]
    ipra_le 𝔞 E*(𝔞 T+1)+24
  have h3 : Γ ⊢[PRAAx] le one (num 3) := by ipra_le 2
  have majorant : Γ ⊢[PRAAx] le one (GaussianEulerLogarithmicMultiplier.majorant (succ j) R E T) :=
    positive_product _ _ (GaussianFactorBudget.power_positive _ _ h3) (GaussianFactorBudget.power_positive _ _ hL)
  have gain : Γ ⊢[PRAAx] le one G :=
    positive_product _ _ hT (le_trans majorant (le_add_left _ _))
  have lower : Γ ⊢[PRAAx] le (unit p) (G*unit p) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (unit p) gain)
  exact le_trans lower (le_add_left (G*unit p) _)

theorem unit_le_modulus (f : PR 2) (p x E : PTm n) : Γ ⊢[PRAAx] le (unit p) (modulus f p x E) := by
  let r := succ (succ p)+num 6
  have hrs : Γ ⊢[PRAAx] le p r :=
    le_trans (le_succ_self p) (le_trans (le_succ_self (succ p)) (le_add_right _ _))
  have h := unit_le_euler_modulus (Γ := Γ) r (succ (LeanProofs.ConciseIPRA.PTm.zero : PTm n))
    (GaussianNamedRightHalfPlane.radius (GaussianGammaNegativeIntervalNamedTerminalDerivative.terminalF f)
      (GaussianGammaNegativeIntervalNamedTerminalDerivative.terminalData x)) (two*one)
  have hd : Γ ⊢[PRAAx] le (unit r) (derivativeModulus f p x) := h
  exact le_trans (GaussianExponentialReference.unit_monotone hrs) (le_trans hd (le_add_left _ _))

theorem small_from_source (f K : PR 2) (p x z E a : PTm n) (h : Γ ⊢[PRAAx] source f K p x z E a) :
    Γ ⊢[PRAAx] smallSamples K z one (unit p) := by
  let M := modulus f p x E
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have hM := unit_le_modulus (Γ := Γ) f p x E
  have small : Γ ⊢[PRAAx] smallSamples K z one M := h.andE₂.andE₂.andE₂
  have s : Δ ⊢[PRAAx] smallSamples K (sh z) one (sh M) := by
    simpa only [Δ,Fm.shift,Syn.shift,sh,GaussianExponentialSmallPerturbation.subst_smallSamples,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using small.shift
  have m : Δ ⊢[PRAAx] le (unit (sh p)) (sh M) := by
    simpa only [Δ,Fm.shift,Syn.shift,sh,subst_le,GaussianCoefficientNameBounds.subst_unit] using hM.shift
  have hd : Δ ⊢[PRAAx] le one (unit (sh p)) := unit_positive (sh p)
  refine .allI ?_
  have out := bounded_radius_mono (ap2 K (var 0) (sh z)) one (sh M) one (unit (sh p))
    (le_trans hd m) hd (le_congr (by ipra_ring) (by ipra_ring) m)
    (small_samples_at K (sh z) one (sh M) (var 0) s)
  simpa only [smallSamples,GaussianCoefficientNameBounds.subst_unit,Syn.shift,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,sh] using out

theorem from_source (f K : PR 2) (p x z E a : PTm n) (h : Γ ⊢[PRAAx] source f K p x z E a) :
    Γ ⊢[PRAAx] crossEquivalent (diffF (sumF f K) f) K (diffData (sumData x z) x) z ⋏
      smallSamples K z one (unit p) :=
  .andI (increment_cross f K x z h.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁)
    (small_from_source f K p x z E a h)

theorem actual_negative_Gamma_increment_setup_closed (f K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f K (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        crossEquivalent (diffF (sumF f K) f) K (diffData (sumData (var 1) (var 2)) (var 1)) (var 2) ⋏
        smallSamples K (var 2) one (unit (var 0))) :=
  closeUniv 5 (.impI (from_source f K _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedIncrementSetup
