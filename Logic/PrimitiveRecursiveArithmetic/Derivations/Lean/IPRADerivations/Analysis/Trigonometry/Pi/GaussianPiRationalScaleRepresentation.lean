import IPRADerivations.Analysis.Trigonometry.Pi.GaussianPiRationalScale

/-!
# Rescaling the rational representation of the original π multiple

An internal positive common scale changes neither the signed rational
coefficient nor any sample of its π multiple at a fixed name radius.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPiRationalScaleRepresentation

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianNameConjugation (equal_samples_cross)
open GaussianNameEquivalence (crossEquivalent)
open GaussianPiRationalScale (nameF data point point_negate regular)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (qnegative)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem point_rescale (s : Bool) (A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] point s (k*A) (k*B) ≐ point s A B := by
  have e : Γ ⊢[PRAAx] point false (k*A) (k*B) ≐ point false A B :=
    GaussianSineProductImaginaryScaling.rational_real_rescale A B k hB hk
  cases s
  · exact e
  · have ne : Γ ⊢[PRAAx] qnegative (point false (k*A) (k*B)) ≐ qnegative (point false A B) := by
      simpa only [GaussianRationalMetric.subst_qnegative,Syn.subst_var,Matrix.cons_val_zero] using
        (Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (qnegative (var 0) : PTm 1)
          (σ := ![point false (k*A) (k*B)]) (σ' := ![point false A B]) (fun i => by fin_cases i; exact e))
    exact (point_negate false (k*A) (k*B) (positive_product _ _ hk hB)).eqSymm.eqTrans
      (ne.eqTrans (point_negate false A B hB))

theorem sample_rescale (s : Bool) (A B k R x p : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] ap2 nameF p (data s (k*A) (k*B) R x) ≐ ap2 nameF p (data s A B R x) := by
  let piF := GaussianGammaHalfPiName.nameF
  have hl := GaussianBoundedConstantProductName.sample_at (Γ := Γ) piF p R (point s (k*A) (k*B)) x
  have hr := GaussianBoundedConstantProductName.sample_at (Γ := Γ) piF p R (point s A B) x
  exact hl.eqTrans ((qmul_congr (point_rescale s A B k hB hk) (.eqRefl _)).eqTrans hr.eqSymm)

theorem rescale (s : Bool) (A B k R x : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hk : Γ ⊢[PRAAx] le one k) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data s (k*A) (k*B) R x) (data s A B R x) := by
  have hs : Γ ⊢[PRAAx] le (k*A) (R*(k*B)) :=
    le_congr (.eqRefl (k*A)) (by ipra_ring) (le_mul_mono (le_refl k) hA)
  apply equal_samples_cross _ _ _ _ (regular s _ _ R x (positive_product k B hk hB) hs) (regular s A B R x hB hA)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have bs : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hB.shift
  have ks : Δ ⊢[PRAAx] le one (sh k) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hk.shift
  simpa only [GaussianNameConjugation.pointwiseEqual,GaussianPiRationalScale.subst_data,PTm.subst_mul,
    Δ,sh,Syn.shift] using sample_rescale s (sh A) (sh B) (sh k) (sh R) (sh x) (var 0) bs ks

theorem original_pi_name_common_rational_rescaling_closed (s : Bool) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 1) ⋏ (le one (var 2) ⋏ le (var 0) (var 3*var 1))) ⟶
      crossEquivalent nameF nameF (data s (var 2*var 0) (var 2*var 1) (var 3) (var 4))
        (data s (var 0) (var 1) (var 3) (var 4))) :=
  closeUniv 5 (.impI (rescale s _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianPiRationalScaleRepresentation
