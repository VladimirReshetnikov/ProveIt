import IPRADerivations.Analysis.GaussianBalancedRadiusSyntax
import IPRADerivations.Analysis.GaussianDescentClockArithmetic

/-!
# Exact natural arithmetic for the executable balanced-radius scan

Actual squared Gaussian comparisons are cleared in the shared syntax.
Uniform coefficient numerator/denominator bounds derive both finite scan
endpoints. Monotonicity and the exact doubled-radius power identity then
convert a genuine failed comparison into the source squared balanced
witness, with the factor 4^N. Every degree, height and index is numerical.
No scan success or Euclidean linear-magnitude comparison is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBalancedRadiusArithmetic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (unit three unit_positive subst_unit subst_three)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def exponent (b : PTm n) : PTm n := two*b+three
@[simp] theorem subst_exponent {m : ℕ} (σ : Fin n → PTm m) (b : PTm n) :
    Syn.subst σ (exponent b) = exponent (Syn.subst σ b) := by simp [exponent]

theorem unit_monotone (j k : PTm n) (hjk : Γ ⊢[PRAAx] le j k) : Γ ⊢[PRAAx] le (unit j) (unit k) :=
  GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) hjk

theorem unit_strict (j k : PTm n) (hjk : Γ ⊢[PRAAx] lt j k) : Γ ⊢[PRAAx] lt (unit j) (unit k) := by
  have oneStep : Γ ⊢[PRAAx] lt (unit j) (unit (succ j)) :=
    le_congr (succ_eq_add_one _).eqSymm (pw_succ two j).eqSymm
      (le_congr (.eqRefl _) (by unfold unit; ipra_ring) (add_le_add₂ (le_refl (unit j)) (unit_positive j)))
  exact lt_of_lt_of_le oneStep (unit_monotone (succ j) k hjk)

theorem unit_square (b : PTm n) : Γ ⊢[PRAAx] unit b*unit b ≐ unit (two*b) :=
  (pw_add two b b).eqSymm.eqTrans (congrAp2 powF (by ipra_ring) (.eqRefl _))

theorem low_index (b i : PTm n) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx]
    le (two*b) (two*exponent b*i) := by
  have height : Γ ⊢[PRAAx] le b (exponent b) := le_of_eq_add (d := b+three) (by unfold exponent; ipra_ring)
  have times : Γ ⊢[PRAAx] le (exponent b) (exponent b*i) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (exponent b)) hi)
  exact le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono (le_refl two) (le_trans height times))

/-- Genuine lower endpoint, valid also when this coefficient is zero.
Only the bounds and positive factors actually needed here are premises. -/
theorem low_endpoint (b ni di n0 d0 i : PTm n)
    (hni : Γ ⊢[PRAAx] le ni (unit b)) (hd0 : Γ ⊢[PRAAx] le d0 (unit b))
    (hn0 : Γ ⊢[PRAAx] le one n0) (hdi : Γ ⊢[PRAAx] le one di) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx]
    le (ni*d0) (n0*di*unit (two*exponent b*i)) := by
  have coefficient := le_mul_mono hni hd0
  have power := unit_monotone (two*b) (two*exponent b*i) (low_index b i hi)
  have target := le_mul_mono (positive_product _ _ hn0 hdi) (le_refl (unit (two*exponent b*i)))
  exact le_trans (le_trans (le_congr (.eqRefl _) (unit_square b) coefficient) power)
    (le_congr (one_mul _) (.eqRefl _) target)

/-- The doubled upper endpoint has a strict power advantage. -/
theorem high_index (b i : PTm n) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx]
    lt (two*b+two*exponent b*i) (two*(two*exponent b)*i) := by
  have e := natEq (eq_add_of_le hi)
  refine le_of_eq_add (d := two*exponent b*PTm.monus i one+two*b+(two+three)) ?_
  apply deriveNat
  unfold exponent three
  ipra_simps
  rw [e]
  ring

/-- A genuine positive coefficient forces the upper endpoint to fail.
No assumption about a returned search index is used. -/
theorem high_endpoint (b ni di n0 d0 i : PTm n)
    (hn0 : Γ ⊢[PRAAx] le n0 (unit b)) (hdi : Γ ⊢[PRAAx] le di (unit b))
    (hni : Γ ⊢[PRAAx] le one ni) (hd0 : Γ ⊢[PRAAx] le one d0) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx]
    lt (n0*di*unit (two*exponent b*i)) (ni*d0*unit (two*(two*exponent b)*i)) := by
  have coefficient := le_mul_mono hn0 hdi
  have first := le_mul_mono coefficient (le_refl (unit (two*exponent b*i)))
  have right : Γ ⊢[PRAAx] (unit b*unit b)*unit (two*exponent b*i) ≐ unit (two*b+two*exponent b*i) :=
    (congrMul (unit_square b) (.eqRefl _)).eqTrans (pw_add two _ _).eqSymm
  have power := unit_strict _ _ (high_index b i hi)
  have last := le_mul_mono (positive_product _ _ hni hd0) (le_refl (unit (two*(two*exponent b)*i)))
  exact lt_of_le_of_lt (le_congr (.eqRefl _) right first)
    (lt_of_lt_of_le power (le_congr (one_mul _) (.eqRefl _) last))

/-- Actual dyadic scores increase with the scanned natural exponent. -/
theorem score_monotone (ni d0 j k i : PTm n) (hjk : Γ ⊢[PRAAx] le j k) : Γ ⊢[PRAAx]
    le (ni*d0*unit (two*j*i)) (ni*d0*unit (two*k*i)) := by
  have index := le_mul_mono (le_mul_mono (le_refl two) hjk) (le_refl i)
  exact le_mul_mono (le_refl (ni*d0)) (unit_monotone _ _ index)

/-- Fitting at a later exponent entails fitting at every earlier one. -/
theorem fit_monotone (ni di n0 d0 E j k i : PTm n)
    (hjk : Γ ⊢[PRAAx] le j k)
    (hfit : Γ ⊢[PRAAx] le (ni*d0*unit (two*k*i)) (n0*di*unit (two*E*i))) : Γ ⊢[PRAAx]
    le (ni*d0*unit (two*j*i)) (n0*di*unit (two*E*i)) :=
  le_trans (score_monotone ni d0 j k i hjk) hfit

theorem score_succ (ni d0 j i : PTm n) : Γ ⊢[PRAAx]
    ni*d0*unit (two*succ j*i) ≐ unit (two*i)*(ni*d0*unit (two*j*i)) := by
  have index : Γ ⊢[PRAAx] two*succ j*i ≐ two*j*i+two*i := by ipra_ring
  exact (congrMul (.eqRefl (ni*d0)) ((congrAp2 powF index (.eqRefl two)).eqTrans (pw_add two _ _))).eqTrans
    (by unfold unit; ipra_ring)

/-- A doubled-radius failed comparison yields a true squared-norm
balanced witness with factor 2^(2N), for the same actual coefficient. -/
theorem doubled_failure_witness (ni di n0 d0 N E j i : PTm n)
    (hiN : Γ ⊢[PRAAx] le i N)
    (hFail : Γ ⊢[PRAAx] lt (n0*di*unit (two*E*i)) (ni*d0*unit (two*succ j*i))) : Γ ⊢[PRAAx]
    lt (n0*di*unit (two*E*i)) (unit (two*N)*(ni*d0*unit (two*j*i))) := by
  have power := unit_monotone (two*i) (two*N) (le_mul_mono (le_refl two) hiN)
  exact lt_of_lt_of_le (lt_congr (.eqRefl _) (score_succ ni d0 j i) hFail)
    (le_mul_mono power (le_refl (ni*d0*unit (two*j*i))))

theorem unit_four_power (N : PTm n) : Γ ⊢[PRAAx] unit (two*N) ≐ pw (two*two) N := by
  have twoPower : Γ ⊢[PRAAx] pw two two ≐ two*two :=
    (pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _))
  exact (GaussianDescentClockArithmetic.power_composition two two N).eqSymm.eqTrans
    (congrAp2 powF (.eqRefl _) twoPower)

/-- The same witness in the literal source factor 4^N. All inequalities
remain squared-norm comparisons; no sum of linear magnitudes is inferred. -/
theorem balanced_four_witness (ni di n0 d0 N E j i : PTm n)
    (hiN : Γ ⊢[PRAAx] le i N)
    (hFail : Γ ⊢[PRAAx] lt (n0*di*unit (two*E*i)) (ni*d0*unit (two*succ j*i))) : Γ ⊢[PRAAx]
    lt (n0*di*unit (two*E*i)) (pw (two*two) N*(ni*d0*unit (two*j*i))) :=
  lt_congr (.eqRefl _) (congrMul (unit_four_power N) (.eqRefl _))
    (doubled_failure_witness ni di n0 d0 N E j i hiN hFail)

/-! Bind the generic arithmetic to the actual descending coefficient
lookup and independent-denominator squared norms used by the scan. -/
theorem score_zero (C N E i : PTm n) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.score C N E zero i ≐
      GaussianBalancedRadiusSyntax.numerator C N i*GaussianBalancedRadiusSyntax.denominator C N zero := by
  have power : Γ ⊢[PRAAx] unit (two*zero*i) ≐ one :=
    (congrAp2 powF (by ipra_ring) (.eqRefl two)).eqTrans (pw_zero two)
  exact (congrMul (.eqRefl _) power).eqTrans (by ipra_ring)

theorem low_fit (C N b i : PTm n)
    (hni : Γ ⊢[PRAAx] le (GaussianBalancedRadiusSyntax.numerator C N i) (unit b))
    (hd0 : Γ ⊢[PRAAx] le (GaussianBalancedRadiusSyntax.denominator C N zero) (unit b))
    (hn0 : Γ ⊢[PRAAx] le one (GaussianBalancedRadiusSyntax.numerator C N zero))
    (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.fitAt C N (exponent b) zero i :=
  le_congr (score_zero C N (exponent b) i).eqSymm (.eqRefl _)
    (low_endpoint b _ _ _ _ i hni hd0 hn0 (GaussianBalancedRadiusSyntax.denominator_positive C N i) hi)

theorem high_fail (C N b i : PTm n)
    (hn0 : Γ ⊢[PRAAx] le (GaussianBalancedRadiusSyntax.numerator C N zero) (unit b))
    (hdi : Γ ⊢[PRAAx] le (GaussianBalancedRadiusSyntax.denominator C N i) (unit b))
    (hni : Γ ⊢[PRAAx] le one (GaussianBalancedRadiusSyntax.numerator C N i))
    (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx]
    lt (GaussianBalancedRadiusSyntax.cap C N (exponent b) i)
      (GaussianBalancedRadiusSyntax.score C N (exponent b) (two*exponent b) i) :=
  high_endpoint b _ _ _ _ i hn0 hdi hni (GaussianBalancedRadiusSyntax.denominator_positive C N zero) hi

theorem fitAt_monotone (C N E j k i : PTm n)
    (hjk : Γ ⊢[PRAAx] le j k) (hfit : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.fitAt C N E k i) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.fitAt C N E j i :=
  fit_monotone _ _ _ _ E j k i hjk hfit

theorem actual_balanced_witness (C N E j i : PTm n) (hiN : Γ ⊢[PRAAx] le i N)
    (hFail : Γ ⊢[PRAAx] lt (GaussianBalancedRadiusSyntax.cap C N E i) (GaussianBalancedRadiusSyntax.score C N E (succ j) i)) :
    Γ ⊢[PRAAx] lt (GaussianBalancedRadiusSyntax.cap C N E i)
      (pw (two*two) N*GaussianBalancedRadiusSyntax.score C N E j i) :=
  balanced_four_witness _ _ _ _ N E j i hiN hFail

/-! The numerical output exposes the computed height exponent and literal
endpoint/factor powers used by the genuine scan producer. -/
def output (b i N j : PTm n) : PTm n := pairT (exponent b)
  (pairT (unit (two*exponent b*i)) (pairT (unit (two*(two*exponent b)*i))
    (pairT (pw (two*two) N) (unit (two*j*i)))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (b i N j : PTm n) :
    Syn.subst σ (output b i N j) = output (Syn.subst σ b) (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ j) := by simp [output]

theorem program_at (b i N j : PTm n) : Γ ⊢[PRAAx] PTm.app outputF ![b,i,N,j] ≐ output b i N j := by
  simpa [outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![b,i,N,j]

theorem balanced_radius_low_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 1) (unit (var 0)) ⟶ le (var 4) (unit (var 0)) ⟶ le one (var 3) ⟶ le one (var 2) ⟶ le one (var 5) ⟶
      le (var 1*var 4) (var 3*var 2*unit (two*exponent (var 0)*var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI
    (low_endpoint _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

theorem balanced_radius_high_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 3) (unit (var 0)) ⟶ le (var 2) (unit (var 0)) ⟶ le one (var 1) ⟶ le one (var 4) ⟶ le one (var 5) ⟶
      lt (var 3*var 2*unit (two*exponent (var 0)*var 5)) (var 1*var 4*unit (two*(two*exponent (var 0))*var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI
    (high_endpoint _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

theorem balanced_radius_fit_monotone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 3) (var 4) ⟶ GaussianBalancedRadiusSyntax.fitAt (var 0) (var 1) (var 2) (var 4) (var 5) ⟶
      GaussianBalancedRadiusSyntax.fitAt (var 0) (var 1) (var 2) (var 3) (var 5)) :=
  closeUniv 6 (.impI (.impI (fitAt_monotone _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem balanced_radius_squared_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1) ⟶
      lt (GaussianBalancedRadiusSyntax.cap (var 0) (var 1) (var 2) (var 4))
        (GaussianBalancedRadiusSyntax.score (var 0) (var 1) (var 2) (succ (var 3)) (var 4)) ⟶
      lt (GaussianBalancedRadiusSyntax.cap (var 0) (var 1) (var 2) (var 4))
        (pw (two*two) (var 1)*GaussianBalancedRadiusSyntax.score (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (actual_balanced_witness _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem balanced_radius_endpoint_fit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (GaussianBalancedRadiusSyntax.numerator (var 0) (var 1) (var 3)) (unit (var 2)) ⟶
      le (GaussianBalancedRadiusSyntax.denominator (var 0) (var 1) zero) (unit (var 2)) ⟶
      le one (GaussianBalancedRadiusSyntax.numerator (var 0) (var 1) zero) ⟶ le one (var 3) ⟶
        GaussianBalancedRadiusSyntax.fitAt (var 0) (var 1) (exponent (var 2)) zero (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (low_fit _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem balanced_radius_endpoint_failure_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (GaussianBalancedRadiusSyntax.numerator (var 0) (var 1) zero) (unit (var 2)) ⟶
      le (GaussianBalancedRadiusSyntax.denominator (var 0) (var 1) (var 3)) (unit (var 2)) ⟶
      le one (GaussianBalancedRadiusSyntax.numerator (var 0) (var 1) (var 3)) ⟶ le one (var 3) ⟶
        lt (GaussianBalancedRadiusSyntax.cap (var 0) (var 1) (exponent (var 2)) (var 3))
          (GaussianBalancedRadiusSyntax.score (var 0) (var 1) (exponent (var 2)) (two*exponent (var 2)) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (high_fail _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem balanced_radius_arithmetic_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app outputF ![var 0,var 1,var 2,var 3] ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianBalancedRadiusArithmetic
