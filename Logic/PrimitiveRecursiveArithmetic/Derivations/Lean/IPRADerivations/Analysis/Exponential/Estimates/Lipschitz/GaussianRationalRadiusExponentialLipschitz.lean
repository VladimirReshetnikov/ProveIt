import IPRADerivations.Analysis.Exponential.Estimates.Lipschitz.GaussianRationalExponentialLipschitz

/-!
# Actual finite exponential on an arbitrary integer disk

The SAME factorial-weighted scalarSum is Lipschitz with the explicit
finite constant(R+2)^K on the Euclidean radius-R disk. A genuine native
power derivative estimate and equality-free finite prefix induction
prove the bound; no derivative or completed exponential law is assumed.
The binary bound(R+2)^K<=2^((R+2)K) supplies a real input precision clock
for the subsequent regular-name constructor. Radius0/raw inputs included.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRadiusExponentialLipschitz

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalExponentialLipschitz (termDifference difference difference_zero difference_succ)
open GaussianRationalPolynomialExponential (scalarSum inverseFactorial factorial_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def derivativeLaw (R j : PTm n) : Fm PTm n := le (succ j*pw R j) (pw (succ R) (succ j))
ipra_subst derivativeLaw
theorem derivative_zero (R : PTm n) : Γ ⊢[PRAAx] derivativeLaw R zero := by
  have p := natEq (pw_zero (Γ := Γ) R)
  have q := natEq (pw_one (Γ := Γ) (succ R))
  refine le_of_eq_add (d := R) ?_
  apply deriveNat; ipra_simps; rw [p,q]; ring

theorem derivative_step (R j : PTm n) (ih : Γ ⊢[PRAAx] derivativeLaw R j) : Γ ⊢[PRAAx] derivativeLaw R (succ j) := by
  have combined := add_le_add₂ (le_mul_mono ih (le_refl R)) (pw_le_pw (succ j) (le_succ_self R))
  have p := natEq (pw_succ (Γ := Γ) R j)
  have q := natEq (pw_succ (Γ := Γ) (succ R) (succ j))
  exact le_congr (by apply deriveNat; ipra_simps; rw [p]; ring)
    (by apply deriveNat; ipra_simps; rw [q]; ring) combined

theorem derivative_power_bound (R j : PTm n) : Γ ⊢[PRAAx] derivativeLaw R j := by
  have all : Γ ⊢[PRAAx] .all (derivativeLaw (Syn.shift R) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_derivativeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using derivative_zero (Γ := Γ) R
    · simp only [subst_derivativeLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact derivative_step _ _ Prf.hyp0
  simpa only [subst_derivativeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

def factor (R K : PTm n) : PTm n := pw (R+two) K
ipra_subst factor
theorem factor_zero (R : PTm n) : Γ ⊢[PRAAx] factor R zero ≐ one := pw_zero _
theorem factor_succ (R K : PTm n) : Γ ⊢[PRAAx] factor R (succ K) ≐ factor R K*(R+two) := pw_succ _ _
theorem factor_positive (R K : PTm n) : Γ ⊢[PRAAx] le one (factor R K) :=
  GaussianFactorBudget.power_positive _ _ (le_of_eq_add (d := succ R) (by ipra_ring))

/-- Only the actual inverse factorial's proven denominator is discarded. -/
theorem term_bound (u v R A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u R one) (hv : Γ ⊢[PRAAx] bounded v R one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx]
    bounded (termDifference u v (succ k)) ((succ R)*factor R k*A) B := by
  have inv : Γ ⊢[PRAAx] bounded (inverseFactorial (succ k)) one (Products.fact (succ k)) :=
    GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (factorial_positive _)
      (RationalArgmin.rationalLE_congr (GaussianFiniteExponentialWeightedNorm.inverse_factorial_norm _).eqSymm
        (.eqRefl _) (RationalArgmin.reflexive _))
  have invUnit : Γ ⊢[PRAAx] bounded (inverseFactorial (succ k)) one one :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (factorial_positive _) (le_refl _)
      (le_congr (by ipra_ring) (by ipra_ring) (factorial_positive _)) inv
  have pwr := GaussianRationalPowerDifference.power_distance_bound u v R A B (succ k) hB hu hv hd
  have old := bound_congr (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference _ _ _).eqSymm
    (one_mul _) (by ipra_ring) (bounded_product _ _ _ _ _ _ (le_refl one) hB invUnit pwr)
  have budget : Γ ⊢[PRAAx] le (GaussianRationalPowerDifference.budget R A (succ k)) ((succ R)*factor R k*A) := by
    have native := le_trans (derivative_power_bound (Γ := Γ) R k)
      (le_congr (pw_succ (succ R) k).eqSymm (.eqRefl _)
        (le_mul_mono (pw_le_pw k (le_of_eq_add (d := one) (by ipra_ring) : Γ ⊢[PRAAx] le (succ R) (R+two))) (le_refl (succ R))))
    exact le_congr (GaussianRationalPowerDifference.budget_succ R A k).eqSymm
      (by unfold factor; ipra_ring) (le_mul_mono native (le_refl A))
  exact GaussianCoefficientNameBounds.bounded_radius_mono_same hB budget old

def boundLaw (u v R A B K : PTm n) : Fm PTm n := bounded (difference u v K) (factor R K*A) B
ipra_subst boundLaw
theorem bound_zero (u v R A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] boundLaw u v R A B zero :=
  bound_congr (difference_zero u v).eqSymm (.eqRefl _) (.eqRefl _) (GaussianMonicResidualRadius.zero_bounded _ _ hB)
theorem bound_step (u v R A B K : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u R one) (hv : Γ ⊢[PRAAx] bounded v R one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) (ih : Γ ⊢[PRAAx] boundLaw u v R A B K) : Γ ⊢[PRAAx]
    boundLaw u v R A B (succ K) :=
  bound_congr (difference_succ u v K).eqSymm
    ((by ipra_ring : Γ ⊢[PRAAx] factor R K*A+(succ R)*factor R K*A ≐ (factor R K*(R+two))*A).eqTrans
      (congrMul (factor_succ R K).eqSymm (.eqRefl _))) (.eqRefl _)
    (GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ hB ih (term_bound u v R A B K hB hu hv hd))

/-- All radii/cutoffs are numerical, no externally supplied factor law. -/
theorem scalar_sum_lipschitz (u v R A B K : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] bounded u R one) (hv : Γ ⊢[PRAAx] bounded v R one)
    (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx]
    distanceBounded (scalarSum u K) (scalarSum v K) (factor R K*A) B := by
  change Γ ⊢[PRAAx] boundLaw u v R A B K
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have us : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift u) (Syn.shift R) one := by simpa [Fm.shift,Syn.shift] using hu.shift
  have vs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift v) (Syn.shift R) one := by simpa [Fm.shift,Syn.shift] using hv.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] distanceBounded (Syn.shift u) (Syn.shift v) (Syn.shift A) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have all : Γ ⊢[PRAAx] .all (boundLaw (Syn.shift u) (Syn.shift v) (Syn.shift R) (Syn.shift A) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_boundLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using bound_zero u v R A B hB
    · simp only [subst_boundLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact bound_step _ _ _ _ _ _ bs.wk us.wk vs.wk ds.wk Prf.hyp0
  simpa only [subst_boundLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE K

def clockLaw (R K : PTm n) : Fm PTm n := le (factor R K) (pw two ((R+two)*K))
ipra_subst clockLaw
theorem clock_zero (R : PTm n) : Γ ⊢[PRAAx] clockLaw R zero :=
  le_congr (factor_zero R).eqSymm ((congrAp2 powF (mul_zero _) (.eqRefl two)).eqTrans (pw_zero two)).eqSymm (le_refl _)
theorem clock_step (R K : PTm n) (ih : Γ ⊢[PRAAx] clockLaw R K) : Γ ⊢[PRAAx] clockLaw R (succ K) := by
  have base : Γ ⊢[PRAAx] le (R+two) (pw two (R+two)) := le_trans (le_succ_self _) (RationalClosure.succ_le_two_pow _)
  exact le_congr (factor_succ R K).eqSymm
    ((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] (R+two)*succ K ≐ (R+two)*K+(R+two)) (.eqRefl two)).eqTrans
      (pw_add two ((R+two)*K) (R+two))).eqSymm (le_mul_mono ih base)
theorem factor_binary_bound (R K : PTm n) : Γ ⊢[PRAAx] clockLaw R K := by
  have all : Γ ⊢[PRAAx] .all (clockLaw (Syn.shift R) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_clockLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using clock_zero (Γ := Γ) R
    · simp only [subst_clockLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact clock_step _ _ Prf.hyp0
  simpa only [subst_clockLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE K

def factorF : PR 2 := PTm.toPR (factor (var 0) (var 1))
def run (R K : PTm n) : PTm n := ap2 factorF R K
ipra_subst run
theorem factor_program_at (R K : PTm n) : Γ ⊢[PRAAx] run R K ≐ factor R K := by
  simpa [run,factorF,ap2] using toPR_eq (Γ := Γ) (factor (var 0) (var 1) : PTm 2) ![R,K]
theorem returned_factor_bounds (R K : PTm n) : Γ ⊢[PRAAx] le one (run R K) ⋏ le (run R K) (pw two ((R+two)*K)) :=
  .andI (le_congr (.eqRefl _) (factor_program_at R K).eqSymm (factor_positive R K))
    (le_congr (factor_program_at R K).eqSymm (.eqRefl _) (factor_binary_bound R K))

theorem actual_native_power_derivative_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (derivativeLaw (var 0) (var 1)) := closeUniv 2 (derivative_power_bound _ _)
theorem actual_radius_lipschitz_factor_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (factor (var 0) (var 1))) := closeUniv 2 (factor_positive _ _)
theorem actual_radius_lipschitz_binary_clock_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (clockLaw (var 0) (var 1)) := closeUniv 2 (factor_binary_bound _ _)
theorem original_disk_finite_exponential_lipschitz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 4) ⟶ bounded (var 0) (var 2) one ⟶ bounded (var 1) (var 2) one ⟶
      distanceBounded (var 0) (var 1) (var 3) (var 4) ⟶
        distanceBounded (scalarSum (var 0) (var 5)) (scalarSum (var 1) (var 5))
          (factor (var 2) (var 5)*var 3) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (scalar_sum_lipschitz _ _ _ _ _ _
    (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))
theorem actual_radius_lipschitz_factor_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ factor (var 0) (var 1)) := closeUniv 2 (factor_program_at _ _)
theorem actual_returned_radius_lipschitz_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (run (var 0) (var 1)) ⋏ le (run (var 0) (var 1)) (pw two ((var 0+two)*var 1))) :=
  closeUniv 2 (returned_factor_bounds _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalRadiusExponentialLipschitz
