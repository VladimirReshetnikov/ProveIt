import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaShiftedDeflatedName
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaShiftedDeflatedZero

/-!
# Source-only deflated polynomial identification for every native input

The actual sampler is unchanged. Its nonzero native input proof and its
exact zero-input proof combine by a finite natural norm case split.
The resulting cross-equivalence and regularity require only the original
native C7 disk certificate, with no apartness premise on the value.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaShiftedDeflatedIdentification

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (source constantF constant_at)
open GaussianGammaShiftedDeflatedName (nameF nameData)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit)
open ComplexLogarithmRemainder (normSq)
open GaussianRationalSyntheticDivision (qone)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem zero_name_at (p z R B d : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] normSq z ≐ zero) : Γ ⊢[PRAAx] ap2 nameF p (nameData z R B d) ≐ qone :=
  (GaussianGammaShiftedDeflatedName.name_at p z R B d).eqTrans
    (GaussianGammaShiftedDeflatedZero.raw_value_zero _ z R B d hB hz)

theorem original_zero_cross (z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hz : Γ ⊢[PRAAx] normSq z ≐ zero) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF nameF (GaussianGammaRepeatedShift.stageData z R B one) (nameData z R B d) := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) :=
    by simpa [Fm.shift,Syn.shift] using h.shift.shift
  have zs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] normSq (Syn.shift (Syn.shift z)) ≐ zero :=
    by simpa [Fm.shift,Syn.shift] using hz.shift.shift
  refine .allI (.allI ?_)
  have actual := cross_at _ _ _ _ (var 1) (var 0)
    (GaussianGammaShiftedDeflatedZero.original_shifted_one _ _ _ hs zs)
  have same := (constant_at (var 0) (qone : PTm (n+2))).eqTrans
    (zero_name_at (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift d)) hs.andE₂.andE₁ zs).eqSymm
  simpa only [crossEquivalent,GaussianEuclideanPointDistance.unit,unit,GaussianGammaRepeatedShift.subst_stageData,
    GaussianGammaShiftedDeflatedName.subst_nameData,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      distance_congr (.eqRefl _) same (.eqRefl _) (.eqRefl _) actual

/-- Original disk source only; the actual program contains no zero branch. -/
theorem original_cross (z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF nameF (GaussianGammaRepeatedShift.stageData z R B one) (nameData z R B d) := by
  refine .orE (zero_or_succ (normSq z)) ?_ ?_
  · exact original_zero_cross z R B d h.wk Prf.hyp0
  · exact GaussianGammaShiftedDeflatedName.original_cross z R B d
      (.andI h.wk (le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ (PTm.pred (normSq z)))))

theorem name_regular (z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN nameF (nameData z R B d) := by
  have actual := original_cross z R B d h
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ actual) actual

theorem original_observations (p q z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaShiftedDeflatedPolynomial.shiftedSample p z R B) (ap2 nameF q (nameData z R B d))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_cross z R B d h)

theorem actual_original_all_native_shifted_deflated_identification_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶
      (crossEquivalent GaussianGammaC7Name.nameF nameF (GaussianGammaRepeatedShift.stageData (var 0) (var 1) (var 2) one)
        (nameData (var 0) (var 1) (var 2) (var 3)) ⋏ pointCN nameF (nameData (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.andI (original_cross _ _ _ _ Prf.hyp0) (name_regular _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaShiftedDeflatedIdentification
