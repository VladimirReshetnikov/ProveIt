import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetFirstFormulaDecay
import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.GaussianBinetWeightedResolvent
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifferenceAlgebra
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifferenceZero

/-!
# The first Binet identity reduces to the actual Laplace unit difference

Use the independently checked remainder unit difference and the
weighted resolvent. If the actual improper Binet sampler has that same
unit difference on the translated chart family, its discrepancy from
the remainder is constant at every internal index and tends to zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetFirstFormulaPinning

open_ipra
open GaussianBinetFirstFormulaDecay
  (laplaceData subst_laplaceData laplace_regular family family_at parameters family_regular decay_envelope)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianLogGammaEulerHead (shifted_source)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNameRingLaws (zeroF)
open GaussianNamedDifference (name_regular)
open GaussianNamedDifferenceZero (cross_of_zero difference_zero)
open GaussianNamedFiniteEqualityChain (allSteps)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianBinetStirlingRemainder.nameF
local notation "sd" => GaussianBinetStirlingRemainder.data
local notation "J" => GaussianBinetLaplaceImproperName.nameF
local notation "W" => GaussianBinetWeightedResolvent.nameF
local notation "wd" => GaussianBinetWeightedResolvent.data
local notation "R" => GaussianBinetFirstFormulaDecay.nameF
local notation "rd" => GaussianBinetFirstFormulaDecay.data
local notation "F" => GaussianNamedDifference.nameF
local notation "fd" => GaussianNamedDifference.data

def laplaceStepData (A B D sign : PTm n) : PTm n := fd (laplaceData A B D sign) (laplaceData (A+D) B D sign)

def stepLaw (A B D sign : PTm n) : Fm PTm n :=
  .all (crossEquivalent (F J J) W
    (laplaceStepData (Syn.shift A+var 0*Syn.shift D) (Syn.shift B) (Syn.shift D) (Syn.shift sign))
    (wd (Syn.shift A+var 0*Syn.shift D) (Syn.shift B) (Syn.shift D) (Syn.shift sign)))

ipra_subst laplaceStepData

ipra_subst stepLaw [Syn.subst_shift, Syn.shift_subst]

theorem step_at (A B D sign j : PTm n) (h : Γ ⊢[PRAAx] stepLaw A B D sign) :
    Γ ⊢[PRAAx] crossEquivalent (F J J) W
      (laplaceStepData (A+j*D) B D sign) (wd (A+j*D) B D sign) := by
  simpa [stepLaw] using h.allE j

private theorem adjacent (A B D sign x j : PTm n)
    (h : Γ ⊢[PRAAx] source A D sign) (he : Γ ⊢[PRAAx] stepLaw A B D sign) :
    Γ ⊢[PRAAx] crossEquivalent R R (inst2 family (succ j) (parameters A B D sign x))
      (inst2 family j (parameters A B D sign x)) := by
  let a := A+j*D
  let b := a+D
  let u := sd a B D sign x
  let v := sd b B D sign x
  let r := laplaceData a B D sign
  let s := laplaceData b B D sign
  have hs : Γ ⊢[PRAAx] source a D sign := shifted_source j A D sign h
  have hb : Γ ⊢[PRAAx] source b D sign :=
    .andI (.andI (le_trans hs.andE₁.andE₁ (le_add_right _ _)) hs.andE₁.andE₂) hs.andE₂
  have hu := GaussianBinetStirlingRemainder.regular a B D sign x hs
  have hv := GaussianBinetStirlingRemainder.regular b B D sign x hb
  have hr := laplace_regular a B D sign hs
  have ht := laplace_regular b B D sign hb
  have stepEq : Γ ⊢[PRAAx] crossEquivalent (F S S) (F J J) (fd u v) (fd r s) :=
    cross_trans _ W _ _ (wd a B D sign) _
      (GaussianBinetWeightedResolvent.remainder_difference a B D sign x hs)
      (cross_symm _ _ _ _ (step_at A B D sign j he))
  have z := difference_zero (F S S) (F J J) (fd u v) (fd r s) zero
    (name_regular _ _ _ _ hu hv) (name_regular _ _ _ _ hr ht) stepEq
  have swap := GaussianNamedDifferenceAlgebra.shuffle S S J J u v r s hu hv hr ht
  have zeroStep : Γ ⊢[PRAAx] crossEquivalent (F R R) zeroF (fd (fd u r) (fd v s)) zero :=
    cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ swap) z
  have raw := cross_symm R R _ _
    (cross_of_zero R R (rd a B D sign x) (rd b B D sign x) zero
      (name_regular _ _ _ _ hu hr) (name_regular _ _ _ _ hv ht) zeroStep)
  have edge : Γ ⊢[PRAAx] b ≐ A+succ j*D := by dsimp only [b,a]; ipra_ring
  have ed : Γ ⊢[PRAAx] rd b B D sign x ≐ rd (A+succ j*D) B D sign x := by
    simpa only [GaussianBinetFirstFormulaDecay.subst_data,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (rd (var 0) (Syn.shift B) (Syn.shift D) (Syn.shift sign) (Syn.shift x)) edge
  exact cross_data_congr R R _ _ _ _
    (ed.eqTrans (family_at A B D sign x (succ j)).eqSymm) (family_at A B D sign x j).eqSymm raw

theorem adjacent_law (A B D sign x : PTm n) (h : Γ ⊢[PRAAx] source A D sign) (he : Γ ⊢[PRAAx] stepLaw A B D sign) :
    Γ ⊢[PRAAx] allSteps R family (parameters A B D sign x) := by
  refine .allI ?_
  let s (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s A) (s D) (s sign) := by simpa [s,Δ,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift
  have es : Δ ⊢[PRAAx] stepLaw (s A) (s B) (s D) (s sign) := by simpa [s,Δ,Fm.shift,Syn.shift] using he.shift
  simpa only [allSteps,parameters,GaussianCompactRiemannName.subst_sampleData,ConciseIPRA.PTm.subst_zero,Syn.shift,s,Δ] using
    adjacent (s A) (s B) (s D) (s sign) (s x) (var 0) hs es

theorem first_formula_of_unit_difference (A B D sign x : PTm n)
    (h : Γ ⊢[PRAAx] source A D sign) (he : Γ ⊢[PRAAx] stepLaw A B D sign) :
    Γ ⊢[PRAAx] crossEquivalent S J (sd A B D sign x) (laplaceData A B D sign) := by
  have z := GaussianNamedRecurrencePinning.zero_cross R family (parameters A B D sign x) zero
    (two*D+num 18*B) (num 9) (family_regular A B D sign x h) (adjacent_law A B D sign x h he)
    (decay_envelope A B D sign x h)
  have edge : Γ ⊢[PRAAx] A+zero*D ≐ A := by ipra_ring
  have ex : Γ ⊢[PRAAx] rd (A+zero*D) B D sign x ≐ rd A B D sign x := by
    simpa only [GaussianBinetFirstFormulaDecay.subst_data,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (rd (var 0) (Syn.shift B) (Syn.shift D) (Syn.shift sign) (Syn.shift x)) edge
  exact cross_of_zero S J (sd A B D sign x) (laplaceData A B D sign) zero
    (GaussianBinetStirlingRemainder.regular A B D sign x h) (laplace_regular A B D sign h)
    (cross_data_congr R zeroF _ _ _ _ ((family_at A B D sign x zero).eqTrans ex) (.eqRefl _) z)

theorem actual_first_Binet_identity_from_unit_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 2) (var 3) ⟶ stepLaw (var 0) (var 1) (var 2) (var 3) ⟶
      crossEquivalent S J (sd (var 0) (var 1) (var 2) (var 3) (var 4)) (laplaceData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (.impI (first_formula_of_unit_difference _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetFirstFormulaPinning
