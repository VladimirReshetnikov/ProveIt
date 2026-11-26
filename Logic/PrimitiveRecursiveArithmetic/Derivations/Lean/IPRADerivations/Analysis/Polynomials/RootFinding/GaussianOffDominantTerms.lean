import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianDominantScoreWeights
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalProductWitness
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalReciprocal
import IPRADerivations.Core.CommonLemmas

/-!
# Actual off-dominant Gaussian terms at every point in the selected disk

The actual rational power and product programs form each coefficient
times Delta^i. The genuine local disk condition bounds its squared norm
by the checked radial score. A directly computed radial reference has
exactly the dominant squared score, with the original coefficient's two
decoded denominators preserved. The actual lower and upper term lists
inherit the checked geometric squared weights. No sum bound, direction,
power-value law, or successful scan is supplied as an input condition.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianOffDominantTerms

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax
  (coefficient subst_coefficient unit unit_positive input)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul ofGaussian positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq bounded)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_den_positive)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.Analysis.GaussianDominantPlateau (center winner)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def term (C N delta i : PTm n) : PTm n :=
  qmul (coefficient C N i) (GaussianRationalReciprocal.power delta i)
def reference (C N A B k : PTm n) : PTm n := ofGaussian
  (ComplexLogarithmRemainder.scale (pw A k) (rawGaussian (coefficient C N k)))
  (rawDen (coefficient C N k)*pw B k)
def radiusNumerator (C N : PTm n) : PTm n := unit (GaussianBalancedRadiusSearch.radiusIndex C N)
def radiusDenominator (C N : PTm n) : PTm n :=
  unit (GaussianDominantRadiusValues.scaleExponent C N (center C N))
def withinRadius (C N delta : PTm n) : Fm PTm n :=
  bounded delta (radiusNumerator C N) (radiusDenominator C N)
def selectedReference (C N : PTm n) : PTm n :=
  reference C N (radiusNumerator C N) (radiusDenominator C N) (winner C N)
def weightedNorm (q d : PTm n) : PTm n :=
  RationalArithmetic.multiply (fraction (GaussianDominantScoreWeights.weight d) one) (qnormSq q)

@[simp] theorem subst_term {m : ℕ} (σ : Fin n → PTm m) (C N delta i : PTm n) :
    Syn.subst σ (term C N delta i) = term (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ delta) (Syn.subst σ i) := by simp [term]
@[simp] theorem subst_reference {m : ℕ} (σ : Fin n → PTm m) (C N A B k : PTm n) :
    Syn.subst σ (reference C N A B k) = reference (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by simp [reference]
@[simp] theorem subst_radiusNumerator {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (radiusNumerator C N) = radiusNumerator (Syn.subst σ C) (Syn.subst σ N) := by simp [radiusNumerator]
@[simp] theorem subst_radiusDenominator {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (radiusDenominator C N) = radiusDenominator (Syn.subst σ C) (Syn.subst σ N) := by simp [radiusDenominator]
@[simp] theorem subst_withinRadius {m : ℕ} (σ : Fin n → PTm m) (C N delta : PTm n) :
    (withinRadius C N delta).subst σ = withinRadius (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ delta) := by simp [withinRadius]
@[simp] theorem subst_selectedReference {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (selectedReference C N) = selectedReference (Syn.subst σ C) (Syn.subst σ N) := by simp [selectedReference]
@[simp] theorem subst_weightedNorm {m : ℕ} (σ : Fin n → PTm m) (q d : PTm n) :
    Syn.subst σ (weightedNorm q d) = weightedNorm (Syn.subst σ q) (Syn.subst σ d) := by simp [weightedNorm]

alias power_double := Common.pw_double

theorem squared_power_tolerance (A B i : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.squaredTolerance (pw A i) (pw B i) ≐ RationalNonnegativePowers.power A B (two*i) :=
  RationalNonnegativePowers.fraction_congr (power_double A i).eqSymm (power_double B i).eqSymm

/-- The existing actual power evaluator supplies this exact rational
squared-power bound, including zero radius and exponent zero. -/
theorem power_norm_le (delta A B i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hDelta : Γ ⊢[PRAAx] bounded delta A B) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq (GaussianRationalReciprocal.power delta i))
      (RationalNonnegativePowers.power A B (two*i)) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (squared_power_tolerance A B i)
    (GaussianRationalReciprocal.bounded_power delta A B i hB hDelta)

theorem term_norm_le (C N delta A B i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hDelta : Γ ⊢[PRAAx] bounded delta A B) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq (term C N delta i))
      (RationalArithmetic.multiply (qnormSq (coefficient C N i)) (RationalNonnegativePowers.power A B (two*i))) := by
  have nonnegative := GaussianRationalL1.nonnegative_of_representation _ _ _
    (GaussianBalancedRadiusSyntax.denominator_positive (Γ := Γ) C N i)
    (GaussianBalancedRadiusSyntax.coefficient_norm_represents C N i)
  exact RationalArgmin.rationalLE_congr (GaussianRationalProductWitness.norm_multiply _ _).eqSymm (.eqRefl _)
    (RationalArithmetic.multiply_monotone _ _ _ nonnegative (power_norm_le delta A B i hB hDelta))

theorem term_norm_le_score (C N E j delta i : PTm n)
    (hDelta : Γ ⊢[PRAAx] bounded delta (unit j) (unit E)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq (term C N delta i)) (GaussianBalancedRadiusValues.scaledNorm C N E j i) :=
  term_norm_le C N delta (unit j) (unit E) i (unit_positive E) hDelta

/-- The computed radial reference has the exact norm of coefficient k
times (A/B)^k. No incoming radial product or norm identity is used. -/
theorem reference_norm_general (C N A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qnormSq (reference C N A B k) ≐
      RationalArithmetic.multiply (qnormSq (coefficient C N k)) (RationalNonnegativePowers.power A B (two*k)) := by
  have pb := RationalNonnegativePowers.denominator_positive B k hB
  have d := positive_product _ _ (raw_den_positive (coefficient C N k)) pb
  have left := GaussianRationalMetric.qnormSq_represents _ _ _ d
    (GaussianRationalHorner.ofGaussian_represents
      (ComplexLogarithmRemainder.scale (pw A k) (rawGaussian (coefficient C N k)))
      (rawDen (coefficient C N k)*pw B k) d)
  have right := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (GaussianBalancedRadiusSyntax.coefficient_norm_represents C N k)
    (RationalNonnegativePowers.power_represents A B (two*k) hB)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (GaussianRationalMetric.qnormSq_canonical _)
    (RationalArithmetic.multiply_guard _ _) left right (positive_product _ _ d d)
    (positive_product _ _ (GaussianBalancedRadiusSyntax.denominator_positive C N k)
      (RationalNonnegativePowers.denominator_positive B (two*k) hB))
  apply ZT.derive
  have scale := natEq (ComplexLogarithmRemainder.normSq_scale (Γ := Γ) (pw A k) (rawGaussian (coefficient C N k)))
  have aa := natEq (power_double (Γ := Γ) A k)
  have bb := natEq (power_double (Γ := Γ) B k)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  unfold GaussianBalancedRadiusSyntax.numerator GaussianBalancedRadiusSyntax.denominator
  ipra_simps
  rw [scale,aa,bb]
  ring

theorem reference_norm (C N E j k : PTm n) : Γ ⊢[PRAAx]
    qnormSq (reference C N (unit j) (unit E) k) ≐ GaussianBalancedRadiusValues.scaledNorm C N E j k :=
  reference_norm_general C N (unit j) (unit E) k (unit_positive E)

theorem selected_reference_norm (C N : PTm n) : Γ ⊢[PRAAx]
    qnormSq (selectedReference C N) ≐ GaussianDominantRadiusValues.score C N (center C N) (winner C N) :=
  reference_norm C N _ _ _

theorem weightedNorm_congr {q r d e : PTm n} (hqr : Γ ⊢[PRAAx] q ≐ r) (hde : Γ ⊢[PRAAx] d ≐ e) : Γ ⊢[PRAAx]
    weightedNorm q d ≐ weightedNorm r e :=
  RationalAlgebra.multiply_congr
    (RationalNonnegativePowers.fraction_congr
      (congrAp2 powF (congrMul (.eqRefl _) hde) (.eqRefl _)) (.eqRefl _))
    (GaussianRationalProductWitness.qnormSq_congr hqr)

theorem term_congr {C D N M delta epsilon i j : PTm n}
    (hC : Γ ⊢[PRAAx] C ≐ D) (hN : Γ ⊢[PRAAx] N ≐ M)
    (hd : Γ ⊢[PRAAx] delta ≐ epsilon) (hi : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx]
    term C N delta i ≐ term D M epsilon j :=
  GaussianRationalSyntheticDivision.qmul_congr (entry_congr hC (congrMonus hN hi))
    (congrAp2 GaussianRationalReciprocal.powerF hi hd)

theorem radius_denominator_positive (C N : PTm n) : Γ ⊢[PRAAx] le one (radiusDenominator C N) := unit_positive _

theorem term_canonical (C N delta i : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (term C N delta i) :=
  GaussianRationalHorner.qmul_canonical _ _

theorem reference_canonical (C N A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (reference C N A B k) :=
  GaussianRationalHorner.ofGaussian_canonical _ _
    (positive_product _ _ (raw_den_positive _) (RationalNonnegativePowers.denominator_positive B k hB))

theorem selected_reference_canonical (C N : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (selectedReference C N) :=
  reference_canonical C N _ _ _ (radius_denominator_positive C N)

theorem weighted_term_le (C N delta i d : PTm n) (hDelta : Γ ⊢[PRAAx] withinRadius C N delta) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (weightedNorm (term C N delta i) d) (GaussianDominantScoreWeights.atCenter C N i d) := by
  have nonnegative := GaussianRationalL1.nonnegative_of_representation (Γ := Γ) _ _ _ (le_refl one)
    (fraction_represents (GaussianDominantScoreWeights.weight d) one (le_refl one))
  exact RationalArithmetic.multiply_monotone _ _ _ nonnegative
    (term_norm_le_score C N _ _ delta i hDelta)

theorem below_bound (C N delta i : PTm n) (hInput : Γ ⊢[PRAAx] input C N)
    (hDelta : Γ ⊢[PRAAx] withinRadius C N delta) (hi : Γ ⊢[PRAAx] le one i)
    (hiN : Γ ⊢[PRAAx] le i N) (hik : Γ ⊢[PRAAx] le i (winner C N)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (weightedNorm (term C N delta i) (monus (winner C N) i)) (qnormSq (selectedReference C N)) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (selected_reference_norm C N).eqSymm
    (RationalArgmin.transitive (weighted_term_le C N delta i _ hDelta)
      (GaussianDominantScoreWeights.below_weight C N i hInput hi hiN hik))

theorem above_bound (C N delta i : PTm n) (hInput : Γ ⊢[PRAAx] input C N)
    (hDelta : Γ ⊢[PRAAx] withinRadius C N delta) (hi : Γ ⊢[PRAAx] le one i)
    (hiN : Γ ⊢[PRAAx] le i N) (hki : Γ ⊢[PRAAx] le (winner C N) i) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (weightedNorm (term C N delta i) (monus i (winner C N))) (qnormSq (selectedReference C N)) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (selected_reference_norm C N).eqSymm
    (RationalArgmin.transitive (weighted_term_le C N delta i _ hDelta)
      (GaussianDominantScoreWeights.above_weight C N i hInput hi hiN hki))

def data (C N delta k : PTm n) : PTm n := pairT C (pairT N (pairT delta k))
def lowerBody : PTm 2 := term (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (succ (var 0))
def upperBody : PTm 2 := term (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))+succ (var 0))
def lowerList (C N delta k : PTm n) : PTm n := sequence lowerBody (pred k) (data C N delta k)
def upperList (C N delta k : PTm n) : PTm n := sequence upperBody (monus N k) (data C N delta k)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (C N delta k : PTm n) :
    Syn.subst σ (data C N delta k) = data (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ delta) (Syn.subst σ k) := by simp [data]
@[simp] theorem subst_lowerList {m : ℕ} (σ : Fin n → PTm m) (C N delta k : PTm n) :
    Syn.subst σ (lowerList C N delta k) = lowerList (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ delta) (Syn.subst σ k) := by simp [lowerList]
@[simp] theorem subst_upperList {m : ℕ} (σ : Fin n → PTm m) (C N delta k : PTm n) :
    Syn.subst σ (upperList C N delta k) = upperList (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ delta) (Syn.subst σ k) := by simp [upperList]

theorem lower_body_at (C N delta k s : PTm n) : Γ ⊢[PRAAx]
    inst2 lowerBody s (data C N delta k) ≐ term C N delta (succ s) := by
  simp only [lowerBody,inst2,subst_term,subst_fstT,subst_sndT,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have t := snd_pair (Γ := Γ) C (pairT N (pairT delta k))
  have u := (congrSnd t).eqTrans (snd_pair N (pairT delta k))
  exact term_congr (fst_pair _ _) ((congrFst t).eqTrans (fst_pair _ _))
    ((congrFst u).eqTrans (fst_pair _ _)) (.eqRefl _)

theorem upper_body_at (C N delta k s : PTm n) : Γ ⊢[PRAAx]
    inst2 upperBody s (data C N delta k) ≐ term C N delta (k+succ s) := by
  simp only [upperBody,inst2,subst_term,subst_fstT,subst_sndT,PTm.subst_add,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have t := snd_pair (Γ := Γ) C (pairT N (pairT delta k))
  have u := (congrSnd t).eqTrans (snd_pair N (pairT delta k))
  exact term_congr (fst_pair _ _) ((congrFst t).eqTrans (fst_pair _ _))
    ((congrFst u).eqTrans (fst_pair _ _)) (congrAdd ((congrSnd u).eqTrans (snd_pair _ _)) (.eqRefl _))

theorem lower_length (C N delta k : PTm n) : Γ ⊢[PRAAx] length (lowerList C N delta k) ≐ pred k := sequence_length _ _ _
theorem upper_length (C N delta k : PTm n) : Γ ⊢[PRAAx] length (upperList C N delta k) ≐ monus N k := sequence_length _ _ _

theorem lower_lookup (C N delta k s : PTm n) (hs : Γ ⊢[PRAAx] lt s (pred k)) : Γ ⊢[PRAAx]
    entry (lowerList C N delta k) s ≐ term C N delta (succ s) :=
  (sequence_decode lowerBody hs).eqTrans (lower_body_at C N delta k s)

theorem upper_lookup (C N delta k s : PTm n) (hs : Γ ⊢[PRAAx] lt s (monus N k)) : Γ ⊢[PRAAx]
    entry (upperList C N delta k) s ≐ term C N delta (k+succ s) :=
  (sequence_decode upperBody hs).eqTrans (upper_body_at C N delta k s)

theorem upper_degree_bound (N k s : PTm n) (hkN : Γ ⊢[PRAAx] le k N)
    (hs : Γ ⊢[PRAAx] lt s (monus N k)) : Γ ⊢[PRAAx] le (k+succ s) N :=
  le_congr (.eqRefl _) (eq_add_of_le hkN).eqSymm (add_le_add₂ (le_refl k) hs)

/-- Actual original list lookups inherit the squared geometric bound.
The only point hypothesis is the genuine local disk condition. -/
theorem lower_norm_bound (C N delta s : PTm n) (hInput : Γ ⊢[PRAAx] input C N)
    (hDelta : Γ ⊢[PRAAx] withinRadius C N delta)
    (hs : Γ ⊢[PRAAx] lt s (pred (winner C N))) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (weightedNorm (entry (lowerList C N delta (winner C N)) s) (monus (winner C N) (succ s)))
      (qnormSq (selectedReference C N)) := by
  have kBounds := GaussianDominantPlateau.winner_bounds C N hInput
  have ik : Γ ⊢[PRAAx] le (succ s) (winner C N) := le_trans hs
    (le_congr (.eqRefl _) (RationalIntegerNormalization.positive_form (Prf.andE₁ kBounds)).eqSymm (le_succ_self _))
  exact RationalArgmin.rationalLE_congr
    (weightedNorm_congr (lower_lookup C N delta (winner C N) s hs) (.eqRefl _)).eqSymm (.eqRefl _)
    (below_bound C N delta (succ s) hInput hDelta (zero_lt_succ _) (le_trans ik (Prf.andE₂ kBounds)) ik)

theorem upper_norm_bound (C N delta s : PTm n) (hInput : Γ ⊢[PRAAx] input C N)
    (hDelta : Γ ⊢[PRAAx] withinRadius C N delta)
    (hs : Γ ⊢[PRAAx] lt s (monus N (winner C N))) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (weightedNorm (entry (upperList C N delta (winner C N)) s) (succ s))
      (qnormSq (selectedReference C N)) := by
  have kBounds := GaussianDominantPlateau.winner_bounds C N hInput
  have degree := upper_degree_bound N (winner C N) s (Prf.andE₂ kBounds) hs
  have h := above_bound C N delta (winner C N+succ s) hInput hDelta
    (le_trans (zero_lt_succ s) (le_add_left _ _)) degree (le_add_right _ _)
  exact RationalArgmin.rationalLE_congr
    (weightedNorm_congr (upper_lookup C N delta (winner C N) s hs) (add_monus' _ _).eqSymm).eqSymm
    (.eqRefl _) h

/-! Literal PR3 output of the actual two lists and reference. -/
def output (C N delta : PTm n) : PTm n := pairT (lowerList C N delta (winner C N))
  (pairT (upperList C N delta (winner C N)) (selectedReference C N))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C N delta : PTm n) : PTm n := ap3 outputF C N delta

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C N delta : PTm n) :
    Syn.subst σ (output C N delta) = output (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ delta) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C N delta : PTm n) :
    Syn.subst σ (run C N delta) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ delta) := by simp [run]

theorem program_at (C N delta : PTm n) : Γ ⊢[PRAAx] run C N delta ≐ output C N delta := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,N,delta]

theorem returned_lower (C N delta : PTm n) : Γ ⊢[PRAAx]
    fstT (run C N delta) ≐ lowerList C N delta (winner C N) :=
  (congrFst (program_at C N delta)).eqTrans (fst_pair _ _)
theorem returned_upper (C N delta : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run C N delta)) ≐ upperList C N delta (winner C N) :=
  (congrFst ((congrSnd (program_at C N delta)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_reference (C N delta : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run C N delta)) ≐ selectedReference C N :=
  (congrSnd ((congrSnd (program_at C N delta)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem actual_power_norm_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ bounded (var 0) (var 1) (var 2) ⟶
      RationalArgmin.rationalLE (qnormSq (GaussianRationalReciprocal.power (var 0) (var 3)))
        (RationalNonnegativePowers.power (var 1) (var 2) (two*var 3))) :=
  closeUniv 4 (.impI (.impI (power_norm_le _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_term_norm_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 4) ⟶ bounded (var 2) (var 3) (var 4) ⟶
      RationalArgmin.rationalLE (qnormSq (term (var 0) (var 1) (var 2) (var 5)))
        (RationalArithmetic.multiply (qnormSq (coefficient (var 0) (var 1) (var 5)))
          (RationalNonnegativePowers.power (var 3) (var 4) (two*var 5)))) :=
  closeUniv 6 (.impI (.impI (term_norm_le _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem radial_reference_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ qnormSq (reference (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
      RationalArithmetic.multiply (qnormSq (coefficient (var 0) (var 1) (var 4)))
        (RationalNonnegativePowers.power (var 2) (var 3) (two*var 4))) :=
  closeUniv 5 (.impI (reference_norm_general _ _ _ _ _ Prf.hyp0))

theorem actual_selected_reference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (qnormSq (selectedReference (var 0) (var 1)) ≐
      GaussianDominantRadiusValues.score (var 0) (var 1) (center (var 0) (var 1)) (winner (var 0) (var 1))) :=
  closeUniv 2 (selected_reference_norm _ _)

theorem actual_lower_term_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) ⟶ withinRadius (var 0) (var 1) (var 2) ⟶ lt (var 3) (pred (winner (var 0) (var 1))) ⟶
      RationalArgmin.rationalLE
        (weightedNorm (entry (lowerList (var 0) (var 1) (var 2) (winner (var 0) (var 1))) (var 3))
          (monus (winner (var 0) (var 1)) (succ (var 3)))) (qnormSq (selectedReference (var 0) (var 1)))) :=
  closeUniv 4 (.impI (.impI (.impI (lower_norm_bound _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem actual_upper_term_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) ⟶ withinRadius (var 0) (var 1) (var 2) ⟶ lt (var 3) (monus (var 1) (winner (var 0) (var 1))) ⟶
      RationalArgmin.rationalLE
        (weightedNorm (entry (upperList (var 0) (var 1) (var 2) (winner (var 0) (var 1))) (var 3)) (succ (var 3)))
        (qnormSq (selectedReference (var 0) (var 1)))) :=
  closeUniv 4 (.impI (.impI (.impI (upper_norm_bound _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem actual_term_lists_metadata_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (lowerList (var 0) (var 1) (var 2) (var 3)) ≐ pred (var 3) ⋏
      length (upperList (var 0) (var 1) (var 2) (var 3)) ≐ monus (var 1) (var 3)) :=
  closeUniv 4 (.andI (lower_length _ _ _ _) (upper_length _ _ _ _))

theorem actual_term_lists_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2) ⋏
      (fstT (run (var 0) (var 1) (var 2)) ≐ lowerList (var 0) (var 1) (var 2) (winner (var 0) (var 1)) ⋏
        (fstT (sndT (run (var 0) (var 1) (var 2))) ≐ upperList (var 0) (var 1) (var 2) (winner (var 0) (var 1)) ⋏
          sndT (sndT (run (var 0) (var 1) (var 2))) ≐ selectedReference (var 0) (var 1)))) :=
  closeUniv 3 (.andI (program_at _ _ _) (.andI (returned_lower _ _ _)
    (.andI (returned_upper _ _ _) (returned_reference _ _ _))))

end LeanProofs.IPRA.Analysis.GaussianOffDominantTerms
