import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentNamedSlope
import IPRADerivations.Analysis.Optimization.RationalCubeInfimumIntervals

/-!
# Inverse distance bound for the original arctangent observations

The lower slope bounds the separation of the rational endpoints by the
observed ordinate distance plus the two original query tolerances.
An internal comparison of the cleared endpoint numerators handles
their order.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentInverseGap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentNamedSlope (ordinate gapNumerator named_slope_at)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (comparison_of_cleared)
open RationalArithmetic (add)
open RationalCubeMidpoint (fraction fraction_represents)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (radius radius_congr radius_of_upper radius_symmetric upper upper_of_order
  upper_of_radius upper_triangle positive_cancel)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

private theorem cancel_ordinate (a G E P Q : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (h : Γ ⊢[PRAAx] upper (add a (fraction G E)) a P Q) :
    Γ ⊢[PRAAx] le (Q*G) (P*E) := by
  let U := denominatorOf a
  let x := numeratorOf a
  let y := x*ZT.ofNat E+ZT.ofNat G*ZT.ofNat U
  let s := RationalRepresentedUpper.left y U Q
  let t := RationalRepresentedUpper.right x (U*E) U P Q
  have value := RationalRepresentations.represents_self (Γ := Γ) a
  have offset := RationalRepresentations.represents_add _ _ _ _ _ _ value (fraction_represents G E hE)
  have order : Γ ⊢[PRAAx] zle s t :=
    RationalRepresentedUpper.to_signed _ _ _ _ _ _ P Q offset value h
  have e := zle_toZ order
  have hU := RationalArgmin.denominator_positive (Γ := Γ) a
  apply positive_cancel (positive_product U U hU hU)
  apply le_of_eq_add (d := PolynomialBisection.slack s t)
  apply deriveNat
  change ZT.toZ Γ s + 𝔟(PolynomialBisection.slack s t) = ZT.toZ Γ t at e
  simp only [s,t,y,RationalRepresentedUpper.left,RationalRepresentedUpper.right,
    ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat] at e ⊢
  ipra_simps
  linear_combination -e

private theorem ordered_radius_of_gap (A B C D P Q : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hord : Γ ⊢[PRAAx] le (A*D) (C*B))
    (hgap : Γ ⊢[PRAAx] le (Q*gapNumerator A B C D) (P*(B*D))) :
    Γ ⊢[PRAAx] radius (fraction A B) (fraction C D) P Q := by
  have smaller := comparison_of_cleared _ _ A C B D hB hD (fraction_represents _ _ hB)
    (fraction_represents _ _ hD) (le_congr (mul_comm _ _) (.eqRefl _) hord)
  refine radius_of_upper _ _ _ _ (upper_of_order _ _ _ _ smaller) ?_
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ (ZT.ofNat C) (ZT.ofNat A) D B P Q
    hD hB (fraction_represents _ _ hD) (fraction_represents _ _ hB)
  have e := natEq (eq_add_of_le hord)
  have budget := natEq (eq_add_of_le hgap)
  apply zle_of_toZ (monus (P*(B*D)) (Q*gapNumerator A B C D))
  unfold gapNumerator at *
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
  ipra_simps
  linear_combination 𝔟 Q*e-budget

private theorem inverse_radius_ordered (p q A B C D H K : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hA : Γ ⊢[PRAAx] le A B) (hC : Γ ⊢[PRAAx] le C D)
    (hord : Γ ⊢[PRAAx] le (A*D) (C*B))
    (h : Γ ⊢[PRAAx] radius (ordinate p A B) (ordinate q C D) H K) :
    Γ ⊢[PRAAx] radius (fraction A B) (fraction C D)
      ((unit p+unit q)*K+H*(unit p*unit q)) ((unit p*unit q)*K) := by
  have lo := (named_slope_at p q A B C D hB hD hA hC hord).andE₁
  have back := upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ h)
  have sum := upper_triangle _ _ _ _ _ _ _ lo back
  exact ordered_radius_of_gap _ _ _ _ _ _ hB hD hord
    (cancel_ordinate (ordinate p A B) (gapNumerator A B C D) (B*D) _ _
      (positive_product B D hB hD) sum)

theorem inverse_radius (p q A B C D H K : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hA : Γ ⊢[PRAAx] le A B) (hC : Γ ⊢[PRAAx] le C D)
    (h : Γ ⊢[PRAAx] radius (ordinate p A B) (ordinate q C D) H K) :
    Γ ⊢[PRAAx] radius (fraction A B) (fraction C D)
      ((unit p+unit q)*K+H*(unit p*unit q)) ((unit p*unit q)*K) := by
  refine .orE (le_total (A*D) (C*B)) ?_ ?_
  · exact inverse_radius_ordered p q A B C D H K hB.wk hD.wk hA.wk hC.wk Prf.hyp0 h.wk
  · have swap := inverse_radius_ordered q p C D A B H K hD.wk hB.wk hC.wk hA.wk Prf.hyp0
      (radius_symmetric _ _ _ _ h.wk)
    exact radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (radius_symmetric _ _ _ _ swap)

theorem actual_partial_arctangent_inverse_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (((le one (var 3) ⋏ le one (var 5)) ⋏ (le (var 2) (var 3) ⋏ le (var 4) (var 5))) ⟶
      radius (ordinate (var 0) (var 2) (var 3)) (ordinate (var 1) (var 4) (var 5)) (var 6) (var 7) ⟶
      radius (fraction (var 2) (var 3)) (fraction (var 4) (var 5))
        ((unit (var 0)+unit (var 1))*var 7+var 6*(unit (var 0)*unit (var 1)))
        ((unit (var 0)*unit (var 1))*var 7)) :=
  closeUniv 8 (.impI (.impI (inverse_radius _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentInverseGap
