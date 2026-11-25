import IPRADerivations.Analysis.GaussianSineMultipleAngleRecurrence
import IPRADerivations.Analysis.GaussianNamedDifference

/-!
# Uniform bounds for the zero-safe multiple-angle recurrence

On a trace disk of radius M, both state components and their sensitivity
to the trace have the same majorant (M+2)^k. The recurrence can therefore
be evaluated on regular trace names, including traces whose sine is zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 220000

namespace LeanProofs.IPRA.Analysis.GaussianSineMultipleAngleContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianSineMultipleAngleRecurrence (previous value previous_zero value_zero previous_succ value_succ)
open GaussianRationalHorner (qzero qmul)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (qone qone_bounded bound_congr bounded_product bounded_difference)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianNameArithmetic (product_distance)
open GaussianNamedDifference (difference_distance)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def growth (M k : PTm n) : PTm n := pw (M+two) k

def invariant (S T M A B k : PTm n) : Fm PTm n :=
  ((bounded (previous S k) (growth M k) one ⋏ bounded (value S k) (growth M k) one) ⋏
    (bounded (previous T k) (growth M k) one ⋏ bounded (value T k) (growth M k) one)) ⋏
  (distanceBounded (previous S k) (previous T k) (A*growth M k) B ⋏
    distanceBounded (value S k) (value T k) (A*growth M k) B)

@[simp] theorem subst_growth {l : ℕ} (σ : Fin n → PTm l) (M k : PTm n) :
    Syn.subst σ (growth M k) = growth (Syn.subst σ M) (Syn.subst σ k) := by simp [growth,two,one]
@[simp] theorem subst_invariant {l : ℕ} (σ : Fin n → PTm l) (S T M A B k : PTm n) :
    (invariant S T M A B k).subst σ = invariant (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ M)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by simp [invariant,one]

private theorem base (S T M A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] invariant S T M A B zero := by
  have scale : Γ ⊢[PRAAx] growth M zero ≐ one := pw_zero _
  have z := GaussianMonicResidualRadius.zero_bounded (Γ := Γ) one one (le_refl one)
  have o := qone_bounded (Γ := Γ) (n := n)
  have compare : Γ ⊢[PRAAx] le (zero*B) ((A*growth M zero)*B) :=
    le_congr (zero_mul B).eqSymm (.eqRefl _) (zero_le _)
  have ez : Γ ⊢[PRAAx] distanceBounded qzero qzero (A*growth M zero) B :=
    distance_radius_mono _ _ _ _ _ _ hB hB compare (distance_refl_zero _ _ hB)
  have eo : Γ ⊢[PRAAx] distanceBounded qone qone (A*growth M zero) B :=
    distance_radius_mono _ _ _ _ _ _ hB hB compare (distance_refl_zero _ _ hB)
  exact .andI (.andI
    (.andI (bound_congr (previous_zero S).eqSymm scale.eqSymm (.eqRefl _) z)
      (bound_congr (value_zero S).eqSymm scale.eqSymm (.eqRefl _) o))
    (.andI (bound_congr (previous_zero T).eqSymm scale.eqSymm (.eqRefl _) z)
      (bound_congr (value_zero T).eqSymm scale.eqSymm (.eqRefl _) o)))
    (.andI (distance_congr (previous_zero S).eqSymm (previous_zero T).eqSymm (.eqRefl _) (.eqRefl _) ez)
      (distance_congr (value_zero S).eqSymm (value_zero T).eqSymm (.eqRefl _) (.eqRefl _) eo))

private theorem step (S T M A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hS : Γ ⊢[PRAAx] bounded S M one) (hT : Γ ⊢[PRAAx] bounded T M one)
    (hST : Γ ⊢[PRAAx] distanceBounded S T A B) (h : Γ ⊢[PRAAx] invariant S T M A B k) :
    Γ ⊢[PRAAx] invariant S T M A B (succ k) := by
  let W := growth M k
  let X := growth M (succ k)
  have advance : Γ ⊢[PRAAx] X ≐ W*(M+two) := pw_succ _ _
  have grow : Γ ⊢[PRAAx] le W X :=
    le_of_eq_add (d := W*(M+one)) (advance.eqTrans (by ipra_ring))
  have build (U : PTm n) (hu : Γ ⊢[PRAAx] bounded U M one)
      (hprev : Γ ⊢[PRAAx] bounded (previous U k) W one)
      (hval : Γ ⊢[PRAAx] bounded (value U k) W one) :
      Γ ⊢[PRAAx] bounded (previous U (succ k)) X one ⋏ bounded (value U (succ k)) X one := by
    have first := bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
      (le_mul_mono grow (le_refl one)) hval
    have product := bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
      (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) hu hval)
    have next : Γ ⊢[PRAAx] bounded (value U (succ k)) (M*W+W) one :=
      bound_congr (value_succ U k).eqSymm (by ipra_ring) (one_mul one)
      (bounded_difference _ _ _ _ _ _ (le_refl one) (le_refl one) product hprev)
    have cmp : Γ ⊢[PRAAx] le ((M*W+W)*one) (X*one) :=
      le_of_eq_add (d := W) ((congrMul advance (.eqRefl _)).eqTrans (by ipra_ring))
    exact .andI (bound_congr (previous_succ U k).eqSymm (.eqRefl _) (.eqRefl _) first)
      (bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one) cmp next)
  have oldS := h.andE₁.andE₁
  have oldT := h.andE₁.andE₂
  have dif := h.andE₂
  have next1 : Γ ⊢[PRAAx] distanceBounded (previous S (succ k)) (previous T (succ k)) (A*X) B :=
    distance_congr (previous_succ S k).eqSymm (previous_succ T k).eqSymm (.eqRefl _) (.eqRefl _)
      (distance_radius_mono _ _ _ _ _ _ hB hB (le_mul_mono (le_mul_mono (le_refl A) grow) (le_refl B)) dif.andE₂)
  have product := product_distance S T (value S k) (value T k) A (A*W) B W M hB hST dif.andE₂ oldS.andE₂ hT
  have next2 := difference_distance _ _ _ _ _ _ _ hB product dif.andE₁
  exact .andI (.andI (build S hS oldS.andE₁ oldS.andE₂) (build T hT oldT.andE₁ oldT.andE₂))
    (.andI next1 (distance_congr (value_succ S k).eqSymm (value_succ T k).eqSymm
      ((by ipra_ring : Γ ⊢[PRAAx] A*W+M*(A*W)+A*W ≐ A*(W*(M+two))).eqTrans
        (congrMul (.eqRefl A) advance.eqSymm)) (.eqRefl _) next2))

theorem invariant_all (S T M A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hS : Γ ⊢[PRAAx] bounded S M one) (hT : Γ ⊢[PRAAx] bounded T M one)
    (hST : Γ ⊢[PRAAx] distanceBounded S T A B) : Γ ⊢[PRAAx] invariant S T M A B k := by
  let C := Γ.map Fm.shift
  let sh (q : PTm n) := Syn.shift q
  have hs : C ⊢[PRAAx] bounded (sh S) (sh M) one := by simpa [Fm.shift,Syn.shift,C,sh,one] using hS.shift
  have ht : C ⊢[PRAAx] bounded (sh T) (sh M) one := by simpa [Fm.shift,Syn.shift,C,sh,one] using hT.shift
  have hb : C ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,C,sh,one] using hB.shift
  have hst : C ⊢[PRAAx] distanceBounded (sh S) (sh T) (sh A) (sh B) :=
    by simpa [Fm.shift,Syn.shift,C,sh] using hST.shift
  have all : Γ ⊢[PRAAx] .all (invariant (sh S) (sh T) (sh M) (sh A) (sh B) (var 0)) := by
    refine PRA.qfInd _ ⟨⟨⟨trivial,trivial⟩,⟨trivial,trivial⟩⟩,⟨trivial,trivial⟩⟩ ?_ ?_
    · simp only [sh,subst_invariant,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact base S T M A B hB
    · simp only [sh,subst_invariant,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact step _ _ _ _ _ _ hb.wk hs.wk ht.wk hst.wk Prf.hyp0
  simpa only [sh,subst_invariant,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem value_distance (S T M A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hS : Γ ⊢[PRAAx] bounded S M one) (hT : Γ ⊢[PRAAx] bounded T M one)
    (hST : Γ ⊢[PRAAx] distanceBounded S T A B) :
    Γ ⊢[PRAAx] distanceBounded (value S k) (value T k) (A*growth M k) B :=
  (invariant_all S T M A B k hB hS hT hST).andE₂.andE₂

theorem value_bound (S M k : PTm n) (hS : Γ ⊢[PRAAx] bounded S M one) :
    Γ ⊢[PRAAx] bounded (value S k) (growth M k) one :=
  (invariant_all S S M zero one k (le_refl one) hS hS (distance_refl_zero _ _ (le_refl one))).andE₁.andE₁.andE₂

end LeanProofs.IPRA.Analysis.GaussianSineMultipleAngleContinuity
