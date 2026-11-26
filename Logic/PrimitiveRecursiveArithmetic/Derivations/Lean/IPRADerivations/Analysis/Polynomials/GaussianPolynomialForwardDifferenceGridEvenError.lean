import IPRADerivations.Analysis.Polynomials.GaussianPolynomialForwardDifferenceGridEven

/-!
# Preserve the value error under opposite-step grid normalization

Combine the original forward and backward observations using their
actual parity weights. The leading value errors add before the adjacent
differences and the fractional inverse-step bound are applied.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGridEvenError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Analysis.Products (fact)
open GaussianPolynomialForwardDifferenceGrid (samples value)
open GaussianPolynomialForwardDifferenceGridEven (doubled coefficient)
open GaussianPolynomialForwardDifferenceGridError (rowBound row_at terminal_bound)
open GaussianPolynomialForwardDifferenceGridLinearity (combined combined_at)
open GaussianPolynomialForwardDifferenceNormalization (inversePower normalized)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalEulerCoefficients (parityPoint)
open GaussianRationalHorner (qzero)
open GaussianRationalLowerBounds (lower)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalNaturalScale (natScale)
open GaussianRationalSyntheticDivision (qone)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem parity_bounded (e : PTm n) : Γ ⊢[PRAAx] bounded (parityPoint e) one one := by
  let m : PTm n := GaussianRationalMatrixFiniteSums.minusOne
  have hm : Γ ⊢[PRAAx] bounded m one one :=
    GaussianRationalReciprocal.bounded_negative _ _ _ (le_refl one) GaussianRationalReciprocal.qone_bounded
  exact GaussianRationalReciprocal.bound_congr (GaussianRationalParityPower.minus_one_power e)
    (GaussianPolynomialPerturbation.one_power e) (GaussianPolynomialPerturbation.one_power e)
    (GaussianRationalReciprocal.bounded_power m one one e (le_refl one) hm)

theorem combined_rows (V W X Y a b K J N A C B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (ha : Γ ⊢[PRAAx] bounded a K one) (hb : Γ ⊢[PRAAx] bounded b J one)
    (hV : Γ ⊢[PRAAx] rowBound V X N A B) (hW : Γ ⊢[PRAAx] rowBound W Y N C B) :
    Γ ⊢[PRAAx] rowBound (combined V W a b N) (combined X Y a b N) N (K*A+J*C) B := by
  refine .allI (.impI ?_)
  let sh (t : PTm n) := Syn.shift t
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh N) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt i (sh N) := Prf.hyp0
  have bound : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,i,sh,Fm.shift,Syn.shift,one] using hB.shift.wk
  have a' : Δ ⊢[PRAAx] bounded (sh a) (sh K) one := by simpa [Δ,i,sh,Fm.shift,Syn.shift,one] using ha.shift.wk
  have b' : Δ ⊢[PRAAx] bounded (sh b) (sh J) one := by simpa [Δ,i,sh,Fm.shift,Syn.shift,one] using hb.shift.wk
  have v' : Δ ⊢[PRAAx] rowBound (sh V) (sh X) (sh N) (sh A) (sh B) := by
    simpa [Δ,i,sh,Fm.shift,Syn.shift] using hV.shift.wk
  have w' : Δ ⊢[PRAAx] rowBound (sh W) (sh Y) (sh N) (sh C) (sh B) := by
    simpa [Δ,i,sh,Fm.shift,Syn.shift] using hW.shift.wk
  have left := GaussianNamedDifferenceQuotient.scale_distance _ _ _ _ _ _ bound a'
    (row_at (sh V) (sh X) (sh N) (sh A) (sh B) i v' hi)
  have right := GaussianNamedDifferenceQuotient.scale_distance _ _ _ _ _ _ bound b'
    (row_at (sh W) (sh Y) (sh N) (sh C) (sh B) i w' hi)
  have d := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ bound left right
  simpa [Δ,i,sh,Syn.shift] using distance_congr
    (combined_at (sh V) (sh W) (sh a) (sh b) (sh N) i hi).eqSymm
    (combined_at (sh X) (sh Y) (sh a) (sh b) (sh N) i hi).eqSymm (.eqRefl _) (.eqRefl _) d

theorem fractional_normalized_error (V W e h L D A B : PTm n) (hL : Γ ⊢[PRAAx] le one L)
    (hD : Γ ⊢[PRAAx] le one D) (hh : Γ ⊢[PRAAx] lower h L D) (hB : Γ ⊢[PRAAx] le one B)
    (hrow : Γ ⊢[PRAAx] rowBound V W (succ e) A B) :
    Γ ⊢[PRAAx] distanceBounded (normalized V e h) (normalized W e h) (pw D e*(pw two e*A)) (pw L e*B) := by
  let s := inversePower h e
  have hs : Γ ⊢[PRAAx] bounded s (pw D e) (pw L e) :=
    GaussianRationalReciprocal.bounded_power _ _ _ _ hL (GaussianRationalLowerBounds.inverse_bound _ _ _ hL hD hh)
  exact GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference s (value V e) (value W e)).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (GaussianPolynomialPerturbation.power_positive L e hL)
      hB hs (terminal_bound V W e A B hB hrow))

def observedDouble (V W e h : PTm n) : PTm n :=
  normalized (combined V W qone (parityPoint e) (succ e)) e h

@[simp] theorem subst_observedDouble {m : ℕ} (σ : Fin n → PTm m) (V W e h : PTm n) :
    Syn.subst σ (observedDouble V W e h) =
      observedDouble (Syn.subst σ V) (Syn.subst σ W) (Syn.subst σ e) (Syn.subst σ h) := by
  simp [observedDouble]

theorem even_error (V W P Q e h L D A C B : PTm n) (hL : Γ ⊢[PRAAx] le one L)
    (hD : Γ ⊢[PRAAx] le one D) (hh : Γ ⊢[PRAAx] lower h L D) (hB : Γ ⊢[PRAAx] le one B)
    (hV : Γ ⊢[PRAAx] rowBound V P (succ e) A B) (hW : Γ ⊢[PRAAx] rowBound W Q (succ e) C B) :
    Γ ⊢[PRAAx] distanceBounded (observedDouble V W e h) (observedDouble P Q e h)
      (pw D e*(pw two e*(A+C))) (pw L e*B) := by
  have rows := combined_rows V W P Q qone (parityPoint e) one one (succ e) A C B
    hB GaussianRationalReciprocal.qone_bounded (parity_bounded e) hV hW
  have bound := fractional_normalized_error _ _ e h L D _ B hL hD hh hB rows
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) bound

theorem even_coefficient_error (V W P e h L D A C B : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ (succ e))
    (hL : Γ ⊢[PRAAx] le one L) (hD : Γ ⊢[PRAAx] le one D) (hh : Γ ⊢[PRAAx] lower h L D)
    (hB : Γ ⊢[PRAAx] le one B)
    (hV : Γ ⊢[PRAAx] rowBound V (samples P (succ e) qzero h) (succ e) A B)
    (hW : Γ ⊢[PRAAx] rowBound W (samples P (succ e) qzero (GaussianRationalMetric.qnegative h)) (succ e) C B) :
    Γ ⊢[PRAAx] distanceBounded (observedDouble V W e h) (natScale two (natScale (fact e) (entry P one)))
      (pw D e*(pw two e*(A+C))) (pw L e*B) := by
  have hd := GaussianRationalLowerBounds.name_lower h L D hL hD hh
  exact distance_congr (.eqRefl _) (coefficient P e h D hP hD hd) (.eqRefl _) (.eqRefl _)
    (even_error V W _ _ e h L D A C B hL hD hh hB hV hW)

theorem actual_Gaussian_even_grid_coefficient_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let V := var 0
     let W := var 1
     let P := var 2
     let e := var 3
     let h := var 4
     let L := var 5
     let D := var 6
     let A := var 7
     let C := var 8
     let B := var 9
     length P ≐ succ (succ e) ⟶ le one L ⟶ le one D ⟶ lower h L D ⟶ le one B ⟶
       rowBound V (samples P (succ e) qzero h) (succ e) A B ⟶
       rowBound W (samples P (succ e) qzero (GaussianRationalMetric.qnegative h)) (succ e) C B ⟶
       distanceBounded (observedDouble V W e h) (natScale two (natScale (fact e) (entry P one)))
         (pw D e*(pw two e*(A+C))) (pw L e*B)) :=
  closeUniv 10 (.impI (.impI (.impI (.impI (.impI (.impI (.impI (even_coefficient_error _ _ _ _ _ _ _ _ _ _
    Prf.hyp1.wk.wk.wk.wk.wk Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGridEvenError
