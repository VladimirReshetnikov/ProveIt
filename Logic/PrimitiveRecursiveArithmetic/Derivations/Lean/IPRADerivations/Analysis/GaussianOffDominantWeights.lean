import IPRADerivations.Algebra.DescentDomination
import IPRADerivations.Analysis.GaussianDominantScoreWeights
import IPRADerivations.Analysis.GaussianRelativeNormTriangle

/-!
# Computed finite geometric weights for the off-dominant terms

The lower and upper lists use the genuine degree distances from the
selected degree. Their natural weights are 4^(N-distance), and the
actual finite sums satisfy 3(sumLower+sumUpper) <= 2*4^N. The geometric
budget is derived from the original finite index guards, rather than
accepted as a condition on the output of a weight program.

A separate exact squared reweighting lemma converts the already checked
16^distance score comparison to the relative Gaussian-norm hypothesis
needed for the finite triangle theorem. No square root or L1 estimate is
used. All lengths, indices, Gaussian codes and persistent data are internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianOffDominantWeights

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.DescentDomination (four)
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (unit)
open LeanProofs.IPRA.Analysis.GaussianRelativeNormTriangle (weightBody weightSum)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq scale normSq_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def C (N : PTm n) : PTm n := pw four N
def lowerCount (k : PTm n) : PTm n := pred k
def upperCount (N k : PTm n) : PTm n := monus N k
def lowerDistance (k s : PTm n) : PTm n := monus k (succ s)
def upperDistance (s : PTm n) : PTm n := succ s
def lowerWeight (N k s : PTm n) : PTm n := pw four (monus N (lowerDistance k s))
def upperWeight (N s : PTm n) : PTm n := pw four (monus N (upperDistance s))
def data (N k payload : PTm n) : PTm n := pairT N (pairT k payload)
def lowerBody : PTm 2 := lowerWeight (fstT (var 1)) (fstT (sndT (var 1))) (var 0)
def upperBody : PTm 2 := upperWeight (fstT (var 1)) (var 0)
def gLower : PR 2 := PTm.toPR lowerBody
def gUpper : PR 2 := PTm.toPR upperBody
def sumLower (N k payload : PTm n) : PTm n := weightSum gLower (lowerCount k) (data N k payload)
def sumUpper (N k payload : PTm n) : PTm n := weightSum gUpper (upperCount N k) (data N k payload)

@[simp] theorem subst_C {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (C N) = C (Syn.subst σ N) := by simp [C]
@[simp] theorem subst_lowerCount {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (lowerCount k) = lowerCount (Syn.subst σ k) := by simp [lowerCount]
@[simp] theorem subst_upperCount {m : ℕ} (σ : Fin n → PTm m) (N k : PTm n) :
    Syn.subst σ (upperCount N k) = upperCount (Syn.subst σ N) (Syn.subst σ k) := by simp [upperCount]
@[simp] theorem subst_lowerDistance {m : ℕ} (σ : Fin n → PTm m) (k s : PTm n) :
    Syn.subst σ (lowerDistance k s) = lowerDistance (Syn.subst σ k) (Syn.subst σ s) := by simp [lowerDistance]
@[simp] theorem subst_upperDistance {m : ℕ} (σ : Fin n → PTm m) (s : PTm n) :
    Syn.subst σ (upperDistance s) = upperDistance (Syn.subst σ s) := by simp [upperDistance]
@[simp] theorem subst_lowerWeight {m : ℕ} (σ : Fin n → PTm m) (N k s : PTm n) :
    Syn.subst σ (lowerWeight N k s) = lowerWeight (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ s) := by simp [lowerWeight]
@[simp] theorem subst_upperWeight {m : ℕ} (σ : Fin n → PTm m) (N s : PTm n) :
    Syn.subst σ (upperWeight N s) = upperWeight (Syn.subst σ N) (Syn.subst σ s) := by simp [upperWeight]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (N k payload : PTm n) :
    Syn.subst σ (data N k payload) = data (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ payload) := by simp [data]
@[simp] theorem subst_sumLower {m : ℕ} (σ : Fin n → PTm m) (N k payload : PTm n) :
    Syn.subst σ (sumLower N k payload) = sumLower (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ payload) := by simp [sumLower]
@[simp] theorem subst_sumUpper {m : ℕ} (σ : Fin n → PTm m) (N k payload : PTm n) :
    Syn.subst σ (sumUpper N k payload) = sumUpper (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ payload) := by simp [sumUpper]

theorem lower_program (N k payload s : PTm n) : Γ ⊢[PRAAx]
    ap2 gLower s (data N k payload) ≐ lowerWeight N k s := by
  have decoded : Γ ⊢[PRAAx]
      monus (fstT (data N k payload)) (monus (fstT (sndT (data N k payload))) (succ s)) ≐
        monus N (lowerDistance k s) := congrMonus (fst_pair N (pairT k payload))
    (congrMonus ((congrFst (snd_pair N (pairT k payload))).eqTrans (fst_pair k payload)) (.eqRefl (succ s)))
  have reified := toPR_eq (Γ := Γ) lowerBody ![s,data N k payload]
  simp only [lowerBody,subst_lowerWeight,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one] at reified
  exact reified.eqTrans (congrAp2 powF decoded (.eqRefl four))

theorem upper_program (N k payload s : PTm n) : Γ ⊢[PRAAx]
    ap2 gUpper s (data N k payload) ≐ upperWeight N s := by
  have reified := toPR_eq (Γ := Γ) upperBody ![s,data N k payload]
  simp only [upperBody,subst_upperWeight,subst_fstT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] at reified
  exact reified.eqTrans (congrAp2 powF (congrMonus (fst_pair N (pairT k payload)) (.eqRefl (succ s))) (.eqRefl four))

theorem lower_sum_program (N k payload : PTm n) : Γ ⊢[PRAAx]
    sumLower N k payload ≐ ap2 (sumF (weightBody gLower)) (lowerCount k) (data N k payload) := .eqRefl _

theorem upper_sum_program (N k payload : PTm n) : Γ ⊢[PRAAx]
    sumUpper N k payload ≐ ap2 (sumF (weightBody gUpper)) (upperCount N k) (data N k payload) := .eqRefl _

theorem difference_le (a b : PTm n) : Γ ⊢[PRAAx] le (monus a b) a := by
  refine .orE (le_total a b) ?_ ?_
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le a)
  · exact le_of_eq_add ((eq_add_of_le Prf.hyp0).eqTrans (add_comm _ _))

theorem positive_succ_pred (k : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] k ≐ succ (pred k) :=
  pos_of_eq_succ ((eq_add_of_le hk).eqTrans (by ipra_ring))

theorem lower_distance_identity (k s : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    lowerDistance k s ≐ monus (lowerCount k) s :=
  (congrMonus (positive_succ_pred k hk) (.eqRefl _)).eqTrans (succ_monus_succ _ _)

theorem lower_distance_bound (N k s : PTm n) (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    le (lowerDistance k s) N := le_trans (difference_le k (succ s)) hkN

theorem upper_distance_bound (N k s : PTm n) (hs : Γ ⊢[PRAAx] lt s (upperCount N k)) : Γ ⊢[PRAAx]
    le (upperDistance s) N := le_trans hs (difference_le N k)

theorem power_split (N d : PTm n) (hd : Γ ⊢[PRAAx] le d N) : Γ ⊢[PRAAx]
    pw four d*pw four (monus N d) ≐ C N :=
  ((congrAp2 powF (eq_add_of_le hd) (.eqRefl four)).eqTrans (pw_add four d (monus N d))).eqSymm

theorem lower_identity (N k s : PTm n) (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    pw four (lowerDistance k s)*lowerWeight N k s ≐ C N :=
  power_split N _ (lower_distance_bound N k s hkN)

theorem upper_identity (N k s : PTm n) (hs : Γ ⊢[PRAAx] lt s (upperCount N k)) : Γ ⊢[PRAAx]
    pw four (upperDistance s)*upperWeight N s ≐ C N :=
  power_split N _ (upper_distance_bound N k s hs)

theorem lower_geometric_contract (N k payload : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx] .all
    (lt (var 0) (Syn.shift (lowerCount k)) ⟶
      le (pw four (monus (Syn.shift (lowerCount k)) (var 0))*
        inst2 (weightBody gLower) (var 0) (Syn.shift (data N k payload))) (Syn.shift (C N))) := by
  refine .allI (.impI ?_)
  have hk' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift k) := by
    simpa only [Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hk.shift
  have hkN' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift k) (Syn.shift N) := by simpa only [Fm.shift,subst_le,Syn.shift] using hkN.shift
  simp only [Syn.shift,subst_lowerCount,subst_data,subst_C,GaussianRelativeNormTriangle.weight_body_at]
  exact le_congr ((congrMul (congrAp2 powF (lower_distance_identity (Syn.shift k) (var 0) hk'.wk).eqSymm (.eqRefl four))
    (lower_program (Syn.shift N) (Syn.shift k) (Syn.shift payload) (var 0))).eqTrans
      (lower_identity (Syn.shift N) (Syn.shift k) (var 0) hkN'.wk)).eqSymm (.eqRefl _) (le_refl _)

theorem upper_geometric_contract (N k payload : PTm n) : Γ ⊢[PRAAx] .all
    (lt (var 0) (Syn.shift (upperCount N k)) ⟶
      le (pw four (succ (var 0))*inst2 (weightBody gUpper) (var 0) (Syn.shift (data N k payload))) (Syn.shift (C N))) := by
  refine .allI (.impI ?_)
  simp only [Syn.shift,subst_upperCount,subst_data,subst_C,GaussianRelativeNormTriangle.weight_body_at]
  exact le_congr ((congrMul (.eqRefl _) (upper_program (Syn.shift N) (Syn.shift k) (Syn.shift payload) (var 0))).eqTrans
    (upper_identity (Syn.shift N) (Syn.shift k) (var 0) Prf.hyp0)).eqSymm (.eqRefl _) (le_refl _)

theorem lower_budget (N k payload : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx] le ((two+one)*sumLower N k payload) (C N) :=
  Algebra.DescentDomination.geo_dom (weightBody gLower) (lowerCount k) (C N) (data N k payload)
    (lower_geometric_contract N k payload hk hkN)

theorem upper_budget (N k payload : PTm n) : Γ ⊢[PRAAx] le ((two+one)*sumUpper N k payload) (C N) :=
  Algebra.DescentDomination.geo_dom_up (weightBody gUpper) (upperCount N k) (C N) (data N k payload)
    (upper_geometric_contract N k payload)

theorem weight_budget (N k payload : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx] le ((two+one)*(sumLower N k payload+sumUpper N k payload)) (two*C N) :=
  le_congr (.eqRefl _) (by ipra_ring)
    (Algebra.DescentDomination.other_terms (weightBody gLower) (weightBody gUpper)
      (lowerCount k) (upperCount N k) (C N) (data N k payload)
      (lower_geometric_contract N k payload hk hkN) (upper_geometric_contract N k payload))

theorem C_as_unit (N : PTm n) : Γ ⊢[PRAAx] C N ≐ unit (two*N) := by
  have p4 : Γ ⊢[PRAAx] pw two two ≐ four :=
    (pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl two))
  exact (congrAp2 powF (.eqRefl N) p4.eqSymm).eqTrans (GaussianDescentClockArithmetic.power_composition two two N)

theorem C_positive (N : PTm n) : Γ ⊢[PRAAx] le one (C N) :=
  le_congr (.eqRefl _) (C_as_unit N).eqSymm (GaussianBalancedRadiusSyntax.unit_positive (two*N))

/-- This identifies the exact squared score factor with the square of
the natural fourth-power geometric weight. -/
theorem unit_four_square (d : PTm n) : Γ ⊢[PRAAx] unit (four*d) ≐ pw four d*pw four d := by
  have p := C_as_unit (Γ := Γ) d
  exact (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] four*d ≐ two*d+two*d) (.eqRefl two)).eqTrans
    ((pw_add two (two*d) (two*d)).eqTrans (congrMul p.eqSymm p.eqSymm))

/-- Exact integer reweighting for the genuine relative norm triangle.
No positivity of the reference norm or target coefficient is required. -/
theorem squared_reweight (N d t v : PTm n) (hd : Γ ⊢[PRAAx] le d N)
    (h : Γ ⊢[PRAAx] le (unit (four*d)*normSq t) (normSq v)) : Γ ⊢[PRAAx]
    le (normSq (scale (C N) t)) (pw four (monus N d)*pw four (monus N d)*normSq v) := by
  have split := power_split N d hd
  have lhs : Γ ⊢[PRAAx] (unit (four*d)*normSq t)*(pw four (monus N d)*pw four (monus N d)) ≐ normSq (scale (C N) t) :=
    (congrMul (congrMul (unit_four_square d) (.eqRefl _)) (.eqRefl _)).eqTrans
      ((by ipra_ring : Γ ⊢[PRAAx]
        (pw four d*pw four d*normSq t)*(pw four (monus N d)*pw four (monus N d)) ≐
          (pw four d*pw four (monus N d))*(pw four d*pw four (monus N d))*normSq t).eqTrans
        ((congrMul (congrMul split split) (.eqRefl _)).eqTrans (normSq_scale (C N) t).eqSymm))
  exact le_congr lhs (by ipra_ring) (mul_le_mul_right (pw four (monus N d)*pw four (monus N d)) h)

theorem singleton_sums (payload : PTm n) : Γ ⊢[PRAAx]
    sumLower one one payload ≐ zero ⋏ sumUpper one one payload ≐ zero :=
  .andI ((congrAp2 (sumF (weightBody gLower)) (pred_succ zero) (.eqRefl _)).eqTrans
    (GaussianRelativeNormTriangle.weight_sum_zero gLower _))
    ((congrAp2 (sumF (weightBody gUpper)) (monus_self one) (.eqRefl _)).eqTrans
      (GaussianRelativeNormTriangle.weight_sum_zero gUpper _))

theorem geometric_weight_programs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((ap2 gLower (var 3) (data (var 0) (var 1) (var 2)) ≐ lowerWeight (var 0) (var 1) (var 3)) ⋏
      (ap2 gUpper (var 3) (data (var 0) (var 1) (var 2)) ≐ upperWeight (var 0) (var 3))) :=
  closeUniv 4 (.andI (lower_program _ _ _ _) (upper_program _ _ _ _))

theorem geometric_weight_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le (var 1) (var 0) ⟶
      le ((two+one)*(sumLower (var 0) (var 1) (var 2)+sumUpper (var 0) (var 1) (var 2))) (two*C (var 0))) :=
  closeUniv 3 (.impI (.impI (weight_budget _ _ _ Prf.hyp1 Prf.hyp0)))

theorem separate_geometric_budgets_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le (var 1) (var 0) ⟶
      (le ((two+one)*sumLower (var 0) (var 1) (var 2)) (C (var 0)) ⋏
        le ((two+one)*sumUpper (var 0) (var 1) (var 2)) (C (var 0)))) :=
  closeUniv 3 (.impI (.impI (.andI (lower_budget _ _ _ Prf.hyp1 Prf.hyp0) (upper_budget _ _ _))))

theorem positive_scale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (le one (C (var 0))) :=
  closeUniv 1 (C_positive _)

theorem geometric_singleton_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (sumLower one one (var 0) ≐ zero ⋏ sumUpper one one (var 0) ≐ zero) :=
  closeUniv 1 (singleton_sums _)

theorem squared_geometric_reweight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 1) (var 0) ⟶ le (unit (four*var 1)*normSq (var 2)) (normSq (var 3)) ⟶
      le (normSq (scale (C (var 0)) (var 2)))
        (pw four (monus (var 0) (var 1))*pw four (monus (var 0) (var 1))*normSq (var 3))) :=
  closeUniv 4 (.impI (.impI (squared_reweight _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianOffDominantWeights
