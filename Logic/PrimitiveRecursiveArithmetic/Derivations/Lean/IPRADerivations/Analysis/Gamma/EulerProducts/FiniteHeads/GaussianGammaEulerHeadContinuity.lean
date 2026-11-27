import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerHeadLower
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameArithmetic

/-!
# Quantitative continuity of the same original finite Euler head

For two encoded points in the original radius-R disk, genuine input
Euclidean distance A/D gives head distance (N+1)(1+R)^N*A/D.
All parameters and the actual original head recursion remain numerical.
The only induction hypothesis is the actual finite-head distance.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadContinuity

open_ipra
open GaussianGammaEulerHead (head factor head_zero head_succ)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (z w R B A D : PTm n) : Fm PTm n := le one B ⋏ (le one D ⋏
  (ComplexLogarithmRemainder.bounded z (R*B) ⋏ (ComplexLogarithmRemainder.bounded w (R*B) ⋏
    distanceBounded (ofGaussian z B) (ofGaussian w B) A D)))
def gain (R N : PTm n) : PTm n := succ N*pw (one+R) N
def law (z w R B A D N : PTm n) : Fm PTm n := distanceBounded (head z B N) (head w B N) (gain R N*A) D
ipra_subst input [ComplexLogarithmRemainder.bounded]
ipra_subst gain
ipra_subst law

theorem translated_difference (z w B i : PTm n) : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
    (GaussianRootAlgebra.sub (GaussianGammaEulerHeadLower.translated z B (succ i))
      (GaussianGammaEulerHeadLower.translated w B (succ i))) (GaussianRootAlgebra.sub z w) := by
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianGammaEulerHeadLower.translated,
      GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add]
  all_goals ring

/-- Cancellation of the common real shift is proved on the original
represented factors before any distance estimate is used. -/
theorem factor_distance (z w R B A D i : PTm n) (h : Γ ⊢[PRAAx] input z w R B A D) : Γ ⊢[PRAAx]
    distanceBounded (factor i z B) (factor i w B) A D := by
  let E := B*succ i
  have hE := positive_product (Γ := Γ) _ _ h.andE₁ (zero_lt_succ i)
  have old := (GaussianRationalMetric.bounded_difference_iff (ofGaussian z B) (ofGaussian w B) z w B A D
    h.andE₁ h.andE₂.andE₁ (GaussianRationalHorner.ofGaussian_represents _ _ h.andE₁)
    (GaussianRationalHorner.ofGaussian_represents _ _ h.andE₁)).iffMp h.andE₂.andE₂.andE₂.andE₂
  have grow : Γ ⊢[PRAAx] le B E := le_congr (one_mul B) (mul_comm _ _)
    (mul_le_mul_right B (zero_lt_succ i))
  apply (GaussianRationalMetric.bounded_difference_iff _ _ _ _ E A D hE h.andE₂.andE₁
    (GaussianGammaEulerHeadLower.factor_represents i z B h.andE₁)
    (GaussianGammaEulerHeadLower.factor_represents i w B h.andE₁)).iffMpr
  have aligned := le_congr (congrMul (.eqRefl _) (GaussianRootAlgebra.normSq_equal (translated_difference z w B i))).eqSymm
    (.eqRefl _) old
  exact le_trans aligned (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (A*A)) (sq_le_sq grow))

theorem gain_zero (R : PTm n) : Γ ⊢[PRAAx] gain R zero ≐ one := by
  unfold gain
  exact (congrMul (.eqRefl _) (pw_zero _)).eqTrans (by ipra_ring)

theorem gain_growth (R N : PTm n) : Γ ⊢[PRAAx]
    le (gain R N*(one+R)+R*pw (one+R) N) (gain R (succ N)) := by
  refine le_of_eq_add (d := pw (one+R) N) ?_
  have e := natEq (pw_succ (Γ := Γ) (one+R) N)
  apply deriveNat
  unfold gain
  ipra_simps
  rw [e]
  ring

theorem head_distance_zero (z w R B A D : PTm n) (h : Γ ⊢[PRAAx] input z w R B A D) : Γ ⊢[PRAAx] law z w R B A D zero :=
  distance_congr (head_zero z B h.andE₁).eqSymm (head_zero w B h.andE₁).eqSymm
    ((congrMul (gain_zero R) (.eqRefl A)).eqTrans (one_mul A)).eqSymm (.eqRefl _)
    h.andE₂.andE₂.andE₂.andE₂

theorem head_distance_step (z w R B A D N : PTm n) (h : Γ ⊢[PRAAx] input z w R B A D)
    (ih : Γ ⊢[PRAAx] law z w R B A D N) : Γ ⊢[PRAAx] law z w R B A D (succ N) := by
  have raw := GaussianNameArithmetic.product_distance (head z B N) (head w B N) (factor N z B) (factor N w B)
    (gain R N*A) A D (one+R) (R*pw (one+R) N) h.andE₂.andE₁ ih (factor_distance z w R B A D N h)
    (GaussianGammaEulerHead.factor_bound N z R B h.andE₁ h.andE₂.andE₂.andE₁)
    (GaussianGammaEulerHead.prefix_bound w R B N h.andE₁ h.andE₂.andE₂.andE₂.andE₁)
  have aligned := distance_congr (head_succ z B N).eqSymm (head_succ w B N).eqSymm (.eqRefl _) (.eqRefl _) raw
  apply distance_radius_mono _ _ _ _ (gain R (succ N)*A) D h.andE₂.andE₁ h.andE₂.andE₁ _ aligned
  have widened := AnalyticNumberTheory.PhiLower.le_mul_mono (Γ := Γ) (mul_le_mul_right A (gain_growth R N)) (le_refl D)
  have e : Γ ⊢[PRAAx] ((gain R N*(one+R)+R*pw (one+R) N)*A*D) ≐
      ((gain R N*A*(one+R)+R*pw (one+R) N*A)*D) := by ipra_ring
  exact le_congr e (.eqRefl _) widened

/-- All N are internal. The inducted formula is one original numerical
Euclidean distance; no evaluator or output-continuity law is an input. -/
theorem head_distance (z w R B A D N : PTm n) (h : Γ ⊢[PRAAx] input z w R B A D) : Γ ⊢[PRAAx] law z w R B A D N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift z) (Syn.shift w) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift D) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (law (Syn.shift z) (Syn.shift w) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift D) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using head_distance_zero z w R B A D h
    · simpa only [subst_law,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        head_distance_step (Syn.shift z) (Syn.shift w) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift D) (var 0) hs.wk Prf.hyp0
  simpa only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem returned_head_distance (z w R B A D N : PTm n) (h : Γ ⊢[PRAAx] input z w R B A D) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaEulerHead.run z B N) (GaussianGammaEulerHead.run w B N) (gain R N*A) D :=
  distance_congr (GaussianGammaEulerHead.program_at z B N).eqSymm (GaussianGammaEulerHead.program_at w B N).eqSymm
    (.eqRefl _) (.eqRefl _) (head_distance z w R B A D N h)

/-- Actual original heads and their computed rational continuity budget. -/
def output (z w R B A D N : PTm n) : PTm n := pairT (head z B N)
  (pairT (head w B N) (pairT (gain R N*A) D))
def outputF : PR 7 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (z w R B A D N : PTm n) : PTm n := PTm.app outputF ![z,w,R,B,A,D,N]
ipra_subst output
ipra_subst run

theorem program_at (z w R B A D N : PTm n) : Γ ⊢[PRAAx] run z w R B A D N ≐ output z w R B A D N := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![z,w,R,B,A,D,N]
theorem returned_left (z w R B A D N : PTm n) : Γ ⊢[PRAAx] fstT (run z w R B A D N) ≐ head z B N :=
  (program_at z w R B A D N).fstE
theorem returned_right (z w R B A D N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run z w R B A D N)) ≐ head w B N :=
  ((congrFst (congrSnd (program_at z w R B A D N))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_radius (z w R B A D N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run z w R B A D N))) ≐ gain R N*A :=
  (((congrFst (congrSnd (congrSnd (program_at z w R B A D N)))).eqTrans (congrFst (congrSnd (snd_pair _ _)))).eqTrans
    (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_denominator (z w R B A D N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run z w R B A D N))) ≐ D :=
  (((congrSnd (congrSnd (congrSnd (program_at z w R B A D N)))).eqTrans (congrSnd (congrSnd (snd_pair _ _)))).eqTrans
    (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_distance (z w R B A D N : PTm n) (h : Γ ⊢[PRAAx] input z w R B A D) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run z w R B A D N)) (fstT (sndT (run z w R B A D N)))
      (fstT (sndT (sndT (run z w R B A D N)))) (sndT (sndT (sndT (run z w R B A D N)))) :=
  distance_congr (returned_left z w R B A D N).eqSymm (returned_right z w R B A D N).eqSymm
    (returned_radius z w R B A D N).eqSymm (returned_denominator z w R B A D N).eqSymm
      (head_distance z w R B A D N h)

theorem actual_factor_input_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      distanceBounded (factor (var 6) (var 0) (var 3)) (factor (var 6) (var 1) (var 3)) (var 4) (var 5)) :=
  closeUniv 7 (.impI (factor_distance _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_head_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      law (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (head_distance _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_returned_old_head_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      distanceBounded (GaussianGammaEulerHead.run (var 0) (var 3) (var 6))
        (GaussianGammaEulerHead.run (var 1) (var 3) (var 6)) (gain (var 2) (var 6)*(var 4)) (var 5)) :=
  closeUniv 7 (.impI (returned_head_distance _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_head_continuity_gain_base_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (gain (var 0) zero ≐ one) := closeUniv 1 (gain_zero _)
theorem actual_head_continuity_gain_growth_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (gain (var 0) (var 1)*(one+var 0)+var 0*pw (one+var 0) (var 1)) (gain (var 0) (succ (var 1)))) :=
  closeUniv 2 (gain_growth _ _)
theorem actual_head_continuity_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) := closeUniv 7 (program_at _ _ _ _ _ _ _)
theorem actual_returned_head_continuity_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      distanceBounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))))
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))))
        (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))))) :=
  closeUniv 7 (.impI (returned_distance _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadContinuity
