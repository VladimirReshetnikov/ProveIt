import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianCoefficientNameBounds
import IPRADerivations.Analysis.Polynomials.RootFinding.BalancedRadius.GaussianBalancedRadiusArithmetic
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalProductWitness
import IPRADerivations.Core.LinearCombination

/-!
# General Gaussian coefficient names and their actual apart tail

All coefficients through the internal upper degree N have the original
fast-name coherence. Apartness is tested at the actual precision h+2,
not at precision zero. Exact native squared-norm arithmetic transports
that single test to the lower bound 1/2^(h+1) at every later precision.
No square root, canonical input code or tail-apartness law is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralCoefficientNames

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product represents)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq squaredTolerance distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra (sub re_sub im_sub re_scale im_scale)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq normSq_eval scale)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def generalCN (a : PR 3) (N x : PTm n) : Fm PTm n := GaussianCoefficientNameBounds.CN a (succ N) x
def referencePrecision (h : PTm n) : PTm n := h+two
def lambdaDenominator (h : PTm n) : PTm n := unit (succ h)
def apart (a : PR 3) (k h x : PTm n) : Fm PTm n := rationalLE (squaredTolerance one (unit h))
  (qnormSq (ap3 a k (referencePrecision h) x))
def tailApart (a : PR 3) (k h s x : PTm n) : Fm PTm n := rationalLE
  (squaredTolerance one (lambdaDenominator h)) (qnormSq (ap3 a k s x))

@[simp] theorem subst_generalCN {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N x : PTm n) :
    (generalCN a N x).subst σ = generalCN a (Syn.subst σ N) (Syn.subst σ x) := by simp [generalCN]
@[simp] theorem subst_referencePrecision {m : ℕ} (σ : Fin n → PTm m) (h : PTm n) :
    Syn.subst σ (referencePrecision h) = referencePrecision (Syn.subst σ h) := by simp [referencePrecision]
@[simp] theorem subst_lambdaDenominator {m : ℕ} (σ : Fin n → PTm m) (h : PTm n) :
    Syn.subst σ (lambdaDenominator h) = lambdaDenominator (Syn.subst σ h) := by simp [lambdaDenominator]
@[simp] theorem subst_apart {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (k h x : PTm n) :
    (apart a k h x).subst σ = apart a (Syn.subst σ k) (Syn.subst σ h) (Syn.subst σ x) := by simp [apart]
@[simp] theorem subst_tailApart {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (k h s x : PTm n) :
    (tailApart a k h s x).subst σ = tailApart a (Syn.subst σ k) (Syn.subst σ h) (Syn.subst σ s) (Syn.subst σ x) := by simp [tailApart]

theorem lambda_denominator_positive (h : PTm n) : Γ ⊢[PRAAx] le one (lambdaDenominator h) := unit_positive _
theorem lambda_unit (h : PTm n) : Γ ⊢[PRAAx] lambdaDenominator h ≐ two*unit h :=
  (pw_succ two h).eqTrans (mul_comm _ _)
theorem reference_unit (h : PTm n) : Γ ⊢[PRAAx] unit (referencePrecision h) ≐ two*lambdaDenominator h :=
  ((congrAp2 powF (by unfold referencePrecision; ipra_ring) (.eqRefl two)).eqTrans
    (pw_succ two (succ h))).eqTrans (mul_comm _ _)

theorem coherence (a : PR 3) (N k s t x : PTm n) (h : Γ ⊢[PRAAx] generalCN a N x)
    (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    distanceBounded (ap3 a k s x) (ap3 a k t x) (unit s+unit t) (unit s*unit t) :=
  GaussianCoefficientNameBounds.CN_at a (succ N) x k s t h ((succ_monus_succ _ _).eqTrans hk)

theorem reference_distance (a : PR 3) (N k h s x : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hk : Γ ⊢[PRAAx] le k N)
    (hs : Γ ⊢[PRAAx] le (referencePrecision h) s) : Γ ⊢[PRAAx]
    distanceBounded (ap3 a k (referencePrecision h) x) (ap3 a k s x) one (lambdaDenominator h) := by
  have monotone : Γ ⊢[PRAAx] le (unit (referencePrecision h)) (unit s) :=
    GaussianBalancedRadiusArithmetic.unit_monotone _ _ hs
  have order := add_le_add₂ (mul_le_mul_right (lambdaDenominator h) monotone)
    (le_refl (unit s*lambdaDenominator h))
  have radius : Γ ⊢[PRAAx] le ((unit (referencePrecision h)+unit s)*lambdaDenominator h)
      (one*(unit (referencePrecision h)*unit s)) := le_congr (by ipra_ring) (by
        apply deriveNat
        have e := natEq (reference_unit (Γ := Γ) h)
        ipra_simps
        rw [e]
        ring) order
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _)) (lambda_denominator_positive h) radius
    (coherence a N k (referencePrecision h) s x hCN hk)

/-- Exact parallelogram rearrangement supplies the squared reverse
triangle estimate without a square-root operation or order oracle. -/
theorem native_reference_triangle (r t : PTm n) : Γ ⊢[PRAAx]
    le (normSq r) (two*normSq t+two*normSq (sub r t)) := by
  apply le_of_eq_add (d := normSq (sub r (scale two t)))
  apply deriveNat
  simp only [Q.mk_add,Q.mk_mul,map_add,map_mul]
  rw [normSq_eval,normSq_eval,normSq_eval,normSq_eval]
  simp only [re_sub,im_sub,re_scale,im_scale]
  ipra_simps
  ring

theorem native_apart_tail (r t D K : PTm n)
    (hRef : Γ ⊢[PRAAx] le (two*two*(D*D)) (K*K*normSq r))
    (hDiff : Γ ⊢[PRAAx] le (K*K*normSq (sub r t)) (D*D)) : Γ ⊢[PRAAx]
    le (D*D) (K*K*normSq t) := by
  have triangle := mul_le_mul_right (K*K) (native_reference_triangle (Γ := Γ) r t)
  have lower : Γ ⊢[PRAAx] le (two*(D*D)) (two*(K*K*normSq t)) := by
    apply le_of_eq_add (d := PTm.monus (K*K*normSq r) (two*two*(D*D)) +
      PTm.monus ((two*normSq t+two*normSq (sub r t))*(K*K)) (normSq r*(K*K)) +
        two*PTm.monus (D*D) (K*K*normSq (sub r t)))
    ipra_lc natEq (eq_add_of_le hRef)+natEq (eq_add_of_le triangle)+2*natEq (eq_add_of_le hDiff)
  exact RationalValueBounds.positive_cancel (le_succ_self one) lower

/-- The actual h+2 observation and genuine coherence give the complete
tail lower bound for every internal s>=h+2. -/
theorem apart_tail (a : PR 3) (N k h s x : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hk : Γ ⊢[PRAAx] le k N)
    (hApart : Γ ⊢[PRAAx] apart a k h x) (hs : Γ ⊢[PRAAx] le (referencePrecision h) s) : Γ ⊢[PRAAx]
    tailApart a k h s x := by
  let r := ap3 a k (referencePrecision h) x
  let t := ap3 a k s x
  let D := rawDen r*rawDen t
  let R := scale (rawDen t) (rawGaussian r)
  let T := scale (rawDen r) (rawGaussian t)
  let K := lambdaDenominator h
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (raw_den_positive r) (raw_den_positive t)
  have hK : Γ ⊢[PRAAx] le one K := lambda_denominator_positive h
  have hr : Γ ⊢[PRAAx] represents r R D :=
    GaussianRationalHorner.represents_rescale r (rawGaussian r) (rawDen r) (rawDen t) (raw_represents r)
  have ht : Γ ⊢[PRAAx] represents t T D :=
    GaussianRationalSyntheticDivision.rescale_to t (rawGaussian t) (rawDen t) (rawDen r) D (raw_represents t) (mul_comm _ _)
  have reference : Γ ⊢[PRAAx] le (D*D) (unit h*unit h*normSq R) :=
    le_congr (by ipra_ring) (by ipra_ring) (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
      (GaussianRationalMetric.squared_tolerance_represents one (unit h) (unit_positive h))
      (GaussianRationalMetric.qnormSq_represents r R D hD hr) hApart)
  have referenceScaled : Γ ⊢[PRAAx] le (two*two*(D*D)) (K*K*normSq R) :=
    le_congr (by ipra_ring) (by
      apply deriveNat
      have e := natEq (lambda_unit (Γ := Γ) h)
      ipra_simps
      rw [e]
      ring) (mul_le_mul_right (two*two) reference)
  have difference : Γ ⊢[PRAAx] le (K*K*normSq (sub R T)) (D*D) :=
    le_congr (.eqRefl _) (by ipra_ring)
      ((GaussianRationalMetric.bounded_difference_iff r t R T D one K hD hK hr ht).iffMp
        (reference_distance a N k h s x hCN hk hs))
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (positive_product K K hK hK) (positive_product D D hD hD)
    (GaussianRationalMetric.squared_tolerance_represents one K hK)
    (GaussianRationalMetric.qnormSq_represents t T D hD ht)
  exact le_congr (by ipra_ring) (mul_comm _ _) (native_apart_tail R T D K referenceScaled difference)

def output (a : PR 3) (k h s x : PTm n) : PTm n := pairT (ap3 a k (referencePrecision h) x)
  (pairT (ap3 a k s x) (lambdaDenominator h))
def outputF (a : PR 3) : PR 4 := PTm.toPR (output a (var 0) (var 1) (var 2) (var 3))
def run (a : PR 3) (k h s x : PTm n) : PTm n := PTm.app (outputF a) ![k,h,s,x]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (k h s x : PTm n) :
    Syn.subst σ (output a k h s x) = output a (Syn.subst σ k) (Syn.subst σ h) (Syn.subst σ s) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (k h s x : PTm n) :
    Syn.subst σ (run a k h s x) = run a (Syn.subst σ k) (Syn.subst σ h) (Syn.subst σ s) (Syn.subst σ x) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (a : PR 3) (k h s x : PTm n) : Γ ⊢[PRAAx] run a k h s x ≐ output a k h s x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output a (var 0) (var 1) (var 2) (var 3) : PTm 4) ![k,h,s,x]
theorem returned_reference (a : PR 3) (k h s x : PTm n) : Γ ⊢[PRAAx]
    fstT (run a k h s x) ≐ ap3 a k (referencePrecision h) x :=
  (congrFst (program_at a k h s x)).eqTrans (fst_pair _ _)
theorem returned_tail (a : PR 3) (k h s x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run a k h s x)) ≐ ap3 a k s x :=
  ((congrFst (congrSnd (program_at a k h s x))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_denominator (a : PR 3) (k h s x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run a k h s x)) ≐ lambdaDenominator h :=
  ((congrSnd (congrSnd (program_at a k h s x))).eqTrans (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_tail_lower (a : PR 3) (N k h s x : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hk : Γ ⊢[PRAAx] le k N)
    (hApart : Γ ⊢[PRAAx] apart a k h x) (hs : Γ ⊢[PRAAx] le (referencePrecision h) s) : Γ ⊢[PRAAx]
    rationalLE (squaredTolerance one (lambdaDenominator h)) (qnormSq (fstT (sndT (run a k h s x)))) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (GaussianRationalProductWitness.qnormSq_congr (returned_tail a k h s x)).eqSymm
    (apart_tail a N k h s x hCN hk hApart hs)

theorem coefficient_apart_tail_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (generalCN a (var 0) (var 4) ⟶ le (var 1) (var 0) ⟶ apart a (var 1) (var 2) (var 4) ⟶
      le (referencePrecision (var 2)) (var 3) ⟶ tailApart a (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (apart_tail _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem general_coefficient_coherence_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (generalCN a (var 0) (var 4) ⟶ le (var 1) (var 0) ⟶
      distanceBounded (ap3 a (var 1) (var 2) (var 4)) (ap3 a (var 1) (var 3) (var 4))
        (unit (var 2)+unit (var 3)) (unit (var 2)*unit (var 3))) :=
  closeUniv 5 (.impI (.impI (coherence _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_general_name_query_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run a (var 0) (var 1) (var 2) (var 3) ≐ output a (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _ _)
theorem returned_general_tail_lower_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (generalCN a (var 0) (var 4) ⟶ le (var 1) (var 0) ⟶ apart a (var 1) (var 2) (var 4) ⟶
      le (referencePrecision (var 2)) (var 3) ⟶
      rationalLE (squaredTolerance one (lambdaDenominator (var 2)))
        (qnormSq (fstT (sndT (run a (var 1) (var 2) (var 3) (var 4)))))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (returned_tail_lower _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianGeneralCoefficientNames
