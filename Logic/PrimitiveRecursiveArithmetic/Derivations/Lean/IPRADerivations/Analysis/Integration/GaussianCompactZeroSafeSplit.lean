import IPRADerivations.Analysis.Integration.GaussianCompactZeroWidth
import IPRADerivations.Analysis.Beta.GaussianBetaIntegralThreeSplit

/-!
# Shared-step compact quadrature splitting with zero widths

A zero width uses its genuine empty sum even though the width-scaled
count is zero. Both degenerate cases are literal canonical identities.
The positive case is exactly the existing metric split on the original
shared step, so differing evaluator encodings retain their two ordinary
observation errors. No output equality is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactZeroSafeSplit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (quadrature sampledModulus)
open GaussianBetaIntegralThreeSplit (quadrature_congr)
open GaussianRationalHorner (qadd qmul qzero canonical)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalRiemannRefinement (weight)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem quadrature_empty (F : PR 3) (s a C E x : PTm n) : Γ ⊢[PRAAx]
    quadrature F s zero a C E x ≐ qzero :=
  (qmul_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_zero _ _)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _)

theorem quadrature_canonical (F : PR 3) (s M a C E x : PTm n) : Γ ⊢[PRAAx]
    canonical (quadrature F s M a C E x) := GaussianRationalHorner.qmul_canonical _ _

theorem zero_left_identity (F : PR 3) (s a C E K x : PTm n) : Γ ⊢[PRAAx]
    quadrature F s ((zero+C)*K) a (zero+C) E x ≐
      qadd (quadrature F s (zero*K) a zero E x) (quadrature F s (C*K) (a+zero) C E x) := by
  have left : Γ ⊢[PRAAx] quadrature F s (zero*K) a zero E x ≐ qzero :=
    (quadrature_congr (Γ := Γ) F (.eqRefl s) (zero_mul K) (.eqRefl a) (.eqRefl zero) (.eqRefl E) (.eqRefl x)).eqTrans
      (quadrature_empty F s a zero E x)
  have right := quadrature_congr (Γ := Γ) F (.eqRefl s) (.eqRefl (C*K)) (add_zero a) (.eqRefl C) (.eqRefl E) (.eqRefl x)
  have full := quadrature_congr (Γ := Γ) F (.eqRefl s) (congrMul (zero_add C) (.eqRefl K)) (.eqRefl a) (zero_add C) (.eqRefl E) (.eqRefl x)
  exact full.eqTrans ((qadd_congr left right).eqTrans
    (GaussianRationalSyntheticDivision.qzero_add _ (quadrature_canonical F s (C*K) a C E x))).eqSymm

theorem zero_right_identity (F : PR 3) (s a C E K x : PTm n) : Γ ⊢[PRAAx]
    quadrature F s ((C+zero)*K) a (C+zero) E x ≐
      qadd (quadrature F s (C*K) a C E x) (quadrature F s (zero*K) (a+C) zero E x) := by
  have right : Γ ⊢[PRAAx] quadrature F s (zero*K) (a+C) zero E x ≐ qzero :=
    (quadrature_congr (Γ := Γ) F (.eqRefl s) (zero_mul K) (.eqRefl (a+C)) (.eqRefl zero) (.eqRefl E) (.eqRefl x)).eqTrans
      (quadrature_empty F s (a+C) zero E x)
  have full := quadrature_congr (Γ := Γ) F (.eqRefl s) (congrMul (add_zero C) (.eqRefl K)) (.eqRefl a) (add_zero C) (.eqRefl E) (.eqRefl x)
  exact full.eqTrans ((qadd_congr (.eqRefl _) right).eqTrans
    (GaussianRationalLinearProduct.qadd_zero_right _ (quadrature_canonical F s (C*K) a C E x))).eqSymm

def splitLaw (F : PR 3) (s a C1 C2 E K x : PTm n) : Fm PTm n :=
  distanceBounded (quadrature F s ((C1+C2)*K) a (C1+C2) E x)
    (qadd (quadrature F s (C1*K) a C1 E x) (quadrature F s (C2*K) (a+C1) C2 E x))
    (two*(C1+C2)) (E*unit s)
@[simp] theorem subst_splitLaw {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (s a C1 C2 E K x : PTm n) :
    (splitLaw F s a C1 C2 E K x).subst σ = splitLaw F (Syn.subst σ s) (Syn.subst σ a)
      (Syn.subst σ C1) (Syn.subst σ C2) (Syn.subst σ E) (Syn.subst σ K) (Syn.subst σ x) := by simp [splitLaw]

theorem split_transport (F : PR 3) (s a E K x C1 C2 D1 D2 : PTm n)
    (h1 : Γ ⊢[PRAAx] C1 ≐ D1) (h2 : Γ ⊢[PRAAx] C2 ≐ D2)
    (h : Γ ⊢[PRAAx] splitLaw F s a D1 D2 E K x) : Γ ⊢[PRAAx] splitLaw F s a C1 C2 E K x := by
  have sum := congrAdd h1 h2
  have full := quadrature_congr (Γ := Γ) F (.eqRefl s) (congrMul sum (.eqRefl K)) (.eqRefl a) sum (.eqRefl E) (.eqRefl x)
  have left := quadrature_congr (Γ := Γ) F (.eqRefl s) (congrMul h1 (.eqRefl K)) (.eqRefl a) h1 (.eqRefl E) (.eqRefl x)
  have right := quadrature_congr (Γ := Γ) F (.eqRefl s) (congrMul h2 (.eqRefl K)) (congrAdd (.eqRefl a) h1) h2 (.eqRefl E) (.eqRefl x)
  exact distance_congr full.eqSymm (qadd_congr left right).eqSymm
    (congrMul (.eqRefl two) sum).eqSymm (.eqRefl _) h

theorem distance_of_identity (x y A D : PTm n) (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx]
    distanceBounded x y A D := by
  have old := distance_congr h.eqSymm (.eqRefl y) (.eqRefl zero) (.eqRefl D)
    (GaussianRationalPowerDifference.distance_refl_zero y D hD)
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ zero D A D hD hD
    (le_congr (by ipra_ring) (.eqRefl _) (zero_le _)) old

def input (F : PR 3) (a C1 C2 E K L x : PTm n) : Fm PTm n :=
  le one a ⋏ (le one E ⋏ (le one K ⋏ sampledModulus F a (C1+C2) E L x))
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (a C1 C2 E K L x : PTm n) :
    (input F a C1 C2 E K L x).subst σ = input F (Syn.subst σ a) (Syn.subst σ C1) (Syn.subst σ C2)
      (Syn.subst σ E) (Syn.subst σ K) (Syn.subst σ L) (Syn.subst σ x) := by simp [input]

/-- The existing genuine metric split, now allowing either width zero. -/
theorem shared_step_additivity (F : PR 3) (s a C1 C2 E K L x : PTm n)
    (h : Γ ⊢[PRAAx] input F a C1 C2 E K L x) : Γ ⊢[PRAAx] splitLaw F s a C1 C2 E K x := by
  have hd := GaussianRationalHorner.positive_product (Γ := Γ) _ _ h.andE₂.andE₁ (unit_positive s)
  refine .orE (zero_or_succ C1) ?_ ?_
  · exact split_transport F s a E K x C1 C2 zero C2 Prf.hyp0 (.eqRefl C2)
      (distance_of_identity _ _ _ _ hd.wk (zero_left_identity F s a C2 E K x))
  · refine .orE (zero_or_succ C2) ?_ ?_
    · exact split_transport F s a E K x C1 C2 C1 zero (.eqRefl C1) Prf.hyp0
        (distance_of_identity _ _ _ _ hd.wk.wk (zero_right_identity F s a C1 E K x))
    · have h1 : (C2 ≐ succ (pred C2)) :: (C1 ≐ succ (pred C1)) :: Γ ⊢[PRAAx] le one C1 :=
        le_congr (.eqRefl one) Prf.hyp1.eqSymm (zero_lt_succ (pred C1))
      have h2 : (C2 ≐ succ (pred C2)) :: (C1 ≐ succ (pred C1)) :: Γ ⊢[PRAAx] le one C2 :=
        le_congr (.eqRefl one) Prf.hyp0.eqSymm (zero_lt_succ (pred C2))
      exact GaussianCompactRiemannAdditivity.shared_step_additivity F s a C1 C2 E K L x
        (.andI h.andE₁.wk.wk (.andI h.andE₂.andE₁.wk.wk (.andI h.andE₂.andE₂.andE₁.wk.wk
          (.andI h1 (.andI h2 h.andE₂.andE₂.andE₂.wk.wk)))))

theorem original_zero_count_quadrature_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (quadrature F (var 0) zero (var 1) (var 2) (var 3) (var 4) ≐ qzero) :=
  closeUniv 5 (quadrature_empty F _ _ _ _ _)

theorem original_zero_safe_shared_step_split_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      splitLaw F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7)) :=
  closeUniv 8 (.impI (shared_step_additivity F _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactZeroSafeSplit
