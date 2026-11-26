import IPRADerivations.Analysis.Integration.Partitions.GaussianRationalPanelTailDistance

/-!
# One-sided observed companion bounds for actual complex panel tails

The projected outer/middle hypothesis is a signed scalar comparison.
Actual split error and positive corrected tail domination suffice; no
two-sided estimate of the projected outer/middle gap is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalSignedPanelTailDistance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianPositiveRadiusFiniteSum (boundBy add_bound enlarge_radius)
open GaussianRationalPanelTailDistance (threeSum original_tail_distance)
open RationalGaussianRealPart (real_zero_represents)
open RationalValueBounds (upper upper_congr upper_triangle upper_of_radius)
open RationalRepresentedUpper (left right to_signed from_signed)
open RationalArithmetic (add add_value addNumerator productDenominator)
open RationalSupMetric (numeratorOf denominatorOf)
open PolynomialBisection (slack)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Cancelling a shared actual real summand preserves a one-sided radius,
including arbitrary raw encodings of the middle and tail values. -/
theorem real_add_cancel (middle tails A B : PTm n)
    (h : Γ ⊢[PRAAx] upper (fstT (qadd middle tails)) (fstT middle) A B) : Γ ⊢[PRAAx]
    upper (fstT tails) (fstT qzero) A B := by
  let a := fstT middle
  let b := fstT tails
  let E := denominatorOf a
  let F := denominatorOf b
  let u := numeratorOf a
  let v := numeratorOf b
  have hs : Γ ⊢[PRAAx] upper (add a b) a A B :=
    upper_congr (RationalGaussianRealPart.real_add middle tails) (.eqRefl _) (.eqRefl _) (.eqRefl _) h
  have signed := to_signed (add a b) a (addNumerator a b) u (productDenominator a b) E A B
    (add_value a b) (RationalRepresentations.represents_self a) hs
  apply from_signed b (fstT qzero) v (ZT.ofNat zero) F one A B
    (RationalArgmin.denominator_positive b) (le_refl one) (RationalRepresentations.represents_self b)
    (real_zero_represents one)
  apply PolynomialBisection.zle_scale_cancel (c := E*E)
    (positive_product _ _ (RationalArgmin.denominator_positive a) (RationalArgmin.denominator_positive a))
  apply zle_of_toZ (slack (left (addNumerator a b) E B) (right u (productDenominator a b) E A B))
  have order := zle_toZ signed
  dsimp only [E,F,u,v] at order ⊢
  simp only [left,right,slack,addNumerator,productDenominator,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat] at order ⊢
  ipra_simps
  linear_combination order

theorem three_rearrangement (left middle right : PTm n) : Γ ⊢[PRAAx]
    threeSum left middle right ≐ qadd middle (qadd left right) :=
  GaussianRationalPanelTailDistance.three_rearrangement left middle right

def tailNumerator (A B C D J K : PTm n) : PTm n := (A*D+C*B)*K+J*(B*D)
def tailDenominator (B D K : PTm n) : PTm n := B*D*K
@[simp] theorem subst_tailNumerator {m : ℕ} (σ : Fin n → PTm m) (A B C D J K : PTm n) :
    Syn.subst σ (tailNumerator A B C D J K) = tailNumerator (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ J) (Syn.subst σ K) := by simp [tailNumerator]
@[simp] theorem subst_tailDenominator {m : ℕ} (σ : Fin n → PTm m) (B D K : PTm n) :
    Syn.subst σ (tailDenominator B D K) = tailDenominator (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ K) := by simp [tailDenominator]

theorem original_signed_companion_split_distance (fO fM fL fR gO gM gL gR rL rR P Q A B C D J K : PTm n)
    (hQ : Γ ⊢[PRAAx] le one Q) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hK : Γ ⊢[PRAAx] le one K)
    (hf : Γ ⊢[PRAAx] distanceBounded fO (threeSum fL fM fR) P Q)
    (hl : Γ ⊢[PRAAx] boundBy fL rL) (hr : Γ ⊢[PRAAx] boundBy fR rR)
    (hg : Γ ⊢[PRAAx] distanceBounded gO (threeSum gL gM gR) A B)
    (gap : Γ ⊢[PRAAx] upper (fstT gO) (fstT gM) C D)
    (correction : Γ ⊢[PRAAx] upper (fstT (qadd rL rR)) (fstT (qadd gL gR)) J K) : Γ ⊢[PRAAx]
    distanceBounded fO fM
      (P*(B*D*K)+tailNumerator A B C D J K*Q) (Q*(B*D*K)) := by
  have splitUpper := upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hB
      (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hB hg))
  have sumUpper := upper_triangle _ _ _ A B C D splitUpper gap
  have moved := upper_congr (congrFst (three_rearrangement gL gM gR)) (.eqRefl _) (.eqRefl _) (.eqRefl _) sumUpper
  have rawTails := real_add_cancel gM (qadd gL gR) (A*D+C*B) (B*D) moved
  have corrected := upper_triangle _ _ _ J K (A*D+C*B) (B*D) correction rawTails
  have finalUpper : Γ ⊢[PRAAx] upper (fstT (qadd rL rR)) (fstT qzero)
      (tailNumerator A B C D J K) (tailDenominator B D K) :=
    upper_congr (.eqRefl _) (.eqRefl _) (by unfold tailNumerator; ipra_ring) (by unfold tailDenominator; ipra_ring) corrected
  have positive := positive_product _ _ (positive_product _ _ hB hD) hK
  have tails : Γ ⊢[PRAAx] bounded (qadd fL fR) (tailNumerator A B C D J K) (tailDenominator B D K) :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by unfold tailDenominator; ipra_ring)
      (enlarge_radius _ _ (fstT qzero) zero one _ _ (add_bound _ _ _ _ hl hr) (le_refl one) positive
        (real_zero_represents one) finalUpper)
  exact original_tail_distance _ _ _ _ _ _ _ _ hQ positive hf tails

theorem actual_original_real_add_upper_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (upper (fstT (qadd (var 0) (var 1))) (fstT (var 0)) (var 2) (var 3) ⟶
      upper (fstT (var 1)) (fstT qzero) (var 2) (var 3)) :=
  closeUniv 4 (.impI (real_add_cancel _ _ _ _ Prf.hyp0))

theorem actual_original_signed_companion_panel_tail_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18
    (((le one (var 11) ⋏ (le one (var 13) ⋏ (le one (var 15) ⋏ le one (var 17)))) ⋏
      (distanceBounded (var 0) (threeSum (var 2) (var 1) (var 3)) (var 10) (var 11) ⋏
        (boundBy (var 2) (var 8) ⋏ (boundBy (var 3) (var 9) ⋏
          (distanceBounded (var 4) (threeSum (var 6) (var 5) (var 7)) (var 12) (var 13) ⋏
            (upper (fstT (var 4)) (fstT (var 5)) (var 14) (var 15) ⋏
              upper (fstT (qadd (var 8) (var 9))) (fstT (qadd (var 6) (var 7))) (var 16) (var 17))))))) ⟶
      distanceBounded (var 0) (var 1)
        (var 10*(var 13*var 15*var 17)+tailNumerator (var 12) (var 13) (var 14) (var 15) (var 16) (var 17)*var 11)
        (var 11*(var 13*var 15*var 17))) :=
  closeUniv 18 (.impI (original_signed_companion_split_distance _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂.andE₁ Prf.hyp0.andE₁.andE₂.andE₂.andE₁ Prf.hyp0.andE₁.andE₂.andE₂.andE₂
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalSignedPanelTailDistance
