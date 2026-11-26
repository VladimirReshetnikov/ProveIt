import IPRADerivations.Analysis.Exponential.GaussianRationalRadiusExponentialLipschitz
import IPRADerivations.Analysis.Exponential.GaussianPositiveExponentialMajorant

/-!
# Uniform actual finite exponential Lipschitz on every numerical disk

The actual factorial sum at every cutoff K is 3^R-Lipschitz on the
original Euclidean radius-R disk. The genuine QF prefix bound retains
the original positive exponential numerator and factorial denominator.
No derivative, output law, completed exponential or K-dependent factor
is supplied as a hypothesis. The paper's sharper real-part majorant is
a distinct downstream obligation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalUniformExponentialLipschitz

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalPolynomialExponential (scalarSum inverseFactorial factorial_positive)
open GaussianRationalExponentialLipschitz (termDifference difference difference_zero difference_one difference_succ difference_congr)
open GaussianExponentialDiskMajorant (numerator numerator_zero numerator_succ)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The actual positive factorial sum supplies its cleared uniform bound. -/
theorem numerator_upper (R k : PTm n) : Γ ⊢[PRAAx] le (numerator R k) (pw (num 3) R*fact (succ k)) := by
  have old := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (GaussianExponentialDiskMajorant.real_majorant_represents (Γ := Γ) R k)
    (GaussianRationalSyntheticBounds.natCode_represents (pw (num 3) R))
    (GaussianPositiveExponentialMajorant.positive_real_majorant R k)
  exact le_congr (one_mul _) (.eqRefl _) old

/-- Actual factorial cancellation is performed by a positive-denominator
metric comparison; no raw output normalization identity is assumed. -/
theorem term_bound (u v R A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u R one) (hv : Γ ⊢[PRAAx] bounded v R one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx]
    bounded (termDifference u v (succ k)) (pw R k*A) (fact k*B) := by
  have inv : Γ ⊢[PRAAx] bounded (inverseFactorial (succ k)) one (fact (succ k)) :=
    GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (factorial_positive _)
      (RationalArgmin.rationalLE_congr (GaussianFiniteExponentialWeightedNorm.inverse_factorial_norm _).eqSymm
        (.eqRefl _) (RationalArgmin.reflexive _))
  have pwr := GaussianRationalPowerDifference.power_distance_bound u v R A B (succ k) hB hu hv hd
  have old := bound_congr (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference _ _ _).eqSymm
    ((one_mul _).eqTrans (GaussianRationalPowerDifference.budget_succ R A k)) (.eqRefl _)
    (bounded_product _ _ _ _ _ _ (factorial_positive _) hB inv pwr)
  have oldD := positive_product _ _ (factorial_positive (succ k)) hB
  have newD := positive_product _ _ (factorial_positive k) hB
  apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ oldD newD _ old
  refine le_of_eq_add (d := zero) ?_
  have f := natEq (fact_succ (Γ := Γ) k zero)
  apply deriveNat
  ipra_simps
  rw [f]
  ring

def prefixLaw (u v R A B k : PTm n) : Fm PTm n := bounded (difference u v (succ k))
  (A*numerator R k) (B*fact (succ k))
@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (u v R A B k : PTm n) :
    (prefixLaw u v R A B k).subst σ = prefixLaw (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ R)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by simp [prefixLaw,fact]

theorem prefix_zero (u v R A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u R one) (hv : Γ ⊢[PRAAx] bounded v R one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx] prefixLaw u v R A B zero := by
  have n0 := natEq (numerator_zero (Γ := Γ) R)
  have p0 := natEq (pw_zero (Γ := Γ) R)
  have f0 := natEq (fact_zero (Γ := Γ) zero)
  have f1 := natEq (fact_succ (Γ := Γ) zero zero)
  have nom : Γ ⊢[PRAAx] pw R zero*A ≐ A*numerator R zero := by apply deriveNat; ipra_simps; rw [p0,n0]; ring
  have den : Γ ⊢[PRAAx] fact zero*B ≐ B*fact (succ zero) := by apply deriveNat; ipra_simps; rw [f1,f0]; ring
  exact bound_congr (difference_one u v).eqSymm nom den (term_bound u v R A B zero hB hu hv hd)

theorem prefix_step (u v R A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u R one) (hv : Γ ⊢[PRAAx] bounded v R one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) (ih : Γ ⊢[PRAAx] prefixLaw u v R A B k) : Γ ⊢[PRAAx]
    prefixLaw u v R A B (succ k) := by
  have oldD := positive_product _ _ hB (factorial_positive (succ k))
  have newD := positive_product _ _ hB (factorial_positive (succ (succ k)))
  have term := bound_congr (.eqRefl _) (.eqRefl _) (mul_comm _ _) (term_bound u v R A B (succ k) hB hu hv hd)
  have combined := GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ oldD ih term
  have budget : Γ ⊢[PRAAx] le
      ((A*numerator R k+pw R (succ k)*A)*(B*fact (succ (succ k))))
      ((A*numerator R (succ k))*(B*fact (succ k))) := by
    refine le_of_eq_add (d := zero) ?_
    have ns := natEq (numerator_succ (Γ := Γ) R k)
    have fs := natEq (fact_succ (Γ := Γ) (succ k) zero)
    apply deriveNat
    ipra_simps
    rw [ns,fs]
    ring
  exact bound_congr (difference_succ u v (succ k)).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ oldD newD budget combined)

/-- A genuine QF induction on the SAME actual scalarSum difference. -/
theorem prefix_bound (u v R A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u R one) (hv : Γ ⊢[PRAAx] bounded v R one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx] prefixLaw u v R A B k := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have us : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift u) (Syn.shift R) one := by simpa [Fm.shift,Syn.shift] using hu.shift
  have vs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift v) (Syn.shift R) one := by simpa [Fm.shift,Syn.shift] using hv.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] distanceBounded (Syn.shift u) (Syn.shift v) (Syn.shift A) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift u) (Syn.shift v) (Syn.shift R) (Syn.shift A) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero u v R A B hB hu hv hd
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact prefix_step _ _ _ _ _ _ bs.wk us.wk vs.wk ds.wk Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

/-- Uniform in every numerical cutoff, including K=0 and radius R=0. -/
theorem scalar_sum_lipschitz (u v R A B K : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u R one) (hv : Γ ⊢[PRAAx] bounded v R one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx]
    distanceBounded (scalarSum u K) (scalarSum v K) (pw (num 3) R*A) B := by
  refine .orE (zero_or_succ K) ?_ ?_
  · exact bound_congr ((difference_congr Prf.hyp0).eqTrans (difference_zero u v)).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianMonicResidualRadius.zero_bounded _ _ hB.wk)
  · have old : (K ≐ succ (pred K)) :: Γ ⊢[PRAAx] prefixLaw u v R A B (pred K) :=
      prefix_bound u v R A B (pred K) hB.wk hu.wk hv.wk hd.wk
    have clear : (K ≐ succ (pred K)) :: Γ ⊢[PRAAx]
        le ((A*numerator R (pred K))*B) ((pw (num 3) R*A)*(B*fact (succ (pred K)))) :=
      le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (A*B) (numerator_upper R (pred K)))
    exact bound_congr (difference_congr Prf.hyp0).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
        (positive_product _ _ hB.wk (factorial_positive _)) hB.wk clear old)


def input (u v R A B : PTm n) : Fm PTm n := le one B ⋏
  (bounded u R one ⋏ (bounded v R one ⋏ distanceBounded u v A B))
def output (u v R A B K : PTm n) : PTm n := pairT (scalarSum u K)
  (pairT (scalarSum v K) (pairT (pw (num 3) R*A) B))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (u v R A B K : PTm n) : PTm n := PTm.app outputF ![u,v,R,A,B,K]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (u v R A B K : PTm n) :
    Syn.subst σ (output u v R A B K) = output (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ R)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ K) := by simp [output]
theorem program_at (u v R A B K : PTm n) : Γ ⊢[PRAAx] run u v R A B K ≐ output u v R A B K := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![u,v,R,A,B,K]
theorem returned_first (u v R A B K : PTm n) : Γ ⊢[PRAAx] fstT (run u v R A B K) ≐ scalarSum u K :=
  (congrFst (program_at u v R A B K)).eqTrans (fst_pair _ _)
theorem returned_tail (u v R A B K : PTm n) : Γ ⊢[PRAAx]
    sndT (run u v R A B K) ≐ pairT (scalarSum v K) (pairT (pw (num 3) R*A) B) :=
  (congrSnd (program_at u v R A B K)).eqTrans (snd_pair _ _)
theorem returned_second (u v R A B K : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run u v R A B K)) ≐ scalarSum v K :=
  (congrFst (returned_tail u v R A B K)).eqTrans (fst_pair _ _)
theorem returned_budget (u v R A B K : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run u v R A B K)) ≐ pairT (pw (num 3) R*A) B :=
  (congrSnd (returned_tail u v R A B K)).eqTrans (snd_pair _ _)
theorem returned_numerator (u v R A B K : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run u v R A B K))) ≐ pw (num 3) R*A :=
  (congrFst (returned_budget u v R A B K)).eqTrans (fst_pair _ _)
theorem returned_denominator (u v R A B K : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run u v R A B K))) ≐ B :=
  (congrSnd (returned_budget u v R A B K)).eqTrans (snd_pair _ _)
theorem returned_distance (u v R A B K : PTm n) (h : Γ ⊢[PRAAx] input u v R A B) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run u v R A B K)) (fstT (sndT (run u v R A B K)))
      (fstT (sndT (sndT (run u v R A B K)))) (sndT (sndT (sndT (run u v R A B K)))) :=
  GaussianRationalDistanceOrder.distance_congr (returned_first u v R A B K).eqSymm (returned_second u v R A B K).eqSymm
    (returned_numerator u v R A B K).eqSymm (returned_denominator u v R A B K).eqSymm
    (scalar_sum_lipschitz u v R A B K h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂)

theorem actual_positive_exponential_cleared_upper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (numerator (var 0) (var 1)) (pw (num 3) (var 0)*fact (succ (var 1)))) := closeUniv 2 (numerator_upper _ _)
theorem actual_uniform_exponential_difference_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ prefixLaw (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (prefix_bound _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem original_all_cutoff_uniform_disk_exponential_lipschitz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ distanceBounded (scalarSum (var 0) (var 5)) (scalarSum (var 1) (var 5))
      (pw (num 3) (var 2)*var 3) (var 4)) :=
  closeUniv 6 (.impI (scalar_sum_lipschitz _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_uniform_exponential_lipschitz_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_returned_uniform_exponential_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      distanceBounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))))
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))))
        (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))))) :=
  closeUniv 6 (.impI (returned_distance _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalUniformExponentialLipschitz
