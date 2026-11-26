import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.Taylor.GaussianGammaShiftedDeflatedName
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.Taylor.GaussianGammaShiftedDeflatedZero

/-!
# Source-only deflated polynomial identification for every native input

The actual sampler is unchanged. Its nonzero native input proof and its
exact zero-input proof combine by a finite natural norm case split.
The resulting cross-equivalence and regularity require only the original
native C7 disk certificate, with no apartness premise on the value.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaShiftedDeflatedIdentification

open_ipra
open GaussianGammaCanonicalExponent (source constantF constant_at)
open GaussianGammaShiftedDeflatedName (nameF nameData)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open ComplexLogarithmRemainder (normSq)
open GaussianRationalSyntheticDivision (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem zero_name_at (p z R B d : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] normSq z ≐ zero) : Γ ⊢[PRAAx] ap2 nameF p (nameData z R B d) ≐ qone :=
  (GaussianGammaShiftedDeflatedName.name_at p z R B d).eqTrans
    (GaussianGammaShiftedDeflatedZero.raw_value_zero _ z R B d hB hz)

theorem original_zero_cross (z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hz : Γ ⊢[PRAAx] normSq z ≐ zero) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF nameF (GaussianGammaRepeatedShift.stageData z R B one) (nameData z R B d) := by
  let s (w : PTm n) := Syn.shift (Syn.shift w)
  have hb := Order.shift_one_le (Order.shift_one_le h.andE₂.andE₁)
  have zs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] normSq (s z) ≐ zero :=
    by simpa [Fm.shift, Syn.shift, s] using hz.shift.shift
  apply GaussianNameEquivalence.transport_by_sample_eq (GaussianGammaShiftedDeflatedZero.original_shifted_one z R B h hz)
  · exact .eqRefl _
  · simpa [s, Syn.shift] using
      (zero_name_at (var 0) (s z) (s R) (s B) (s d) hb zs).eqTrans (constant_at (var 0) _).eqSymm

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
