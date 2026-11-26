import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalReconstruction
import IPRADerivations.Analysis.FiniteOperations.GaussianProductStability
import IPRADerivations.Analysis.RationalArithmetic.RationalProductWitness
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalCover
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual original-point witnesses from the rational product program

The searched factors are the actual reverse-index factors of Reconstruction.
Their numerators and positive denominators are computed independently from
those actual points. QF induction identifies the norm of the actual rational
factor fold with the actual products of this numerator/denominator data.
Thus the finite factor search returns an original target-list entry. No
forward/reverse product reordering or coefficient-producer identity is used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalProductWitness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qmul qmul_represents ofGaussian positive_product scalar_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub qnormSq bounded distanceBounded qnormSq_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalReconstruction (factors product factors_zero factors_succ)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq)
open LeanProofs.IPRA.Analysis.RationalArithmetic (multiply)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Exact norm multiplicativity for the actual independently normalizing
Gaussian-rational product. -/
theorem norm_multiply (q r : PTm n) : Γ ⊢[PRAAx]
    qnormSq (qmul q r) ≐ multiply (qnormSq q) (qnormSq r) := by
  have dq := raw_den_positive (Γ := Γ) q
  have dr := raw_den_positive (Γ := Γ) r
  have both := positive_product _ _ dq dr
  have left := qnormSq_represents _ _ _ both
    (qmul_represents q r (rawGaussian q) (rawGaussian r) (rawDen q) (rawDen r) dq dr (raw_represents q) (raw_represents r))
  have right := RationalRepresentations.represents_multiply (Γ := Γ) (qnormSq q) (qnormSq r) _ _ _ _
    (qnormSq_represents _ _ _ dq (raw_represents q)) (qnormSq_represents _ _ _ dr (raw_represents r))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (GaussianRationalMetric.qnormSq_canonical _)
    (RationalArithmetic.multiply_guard _ _) left right (positive_product _ _ both both)
    (positive_product _ _ (positive_product _ _ dq dq) (positive_product _ _ dr dr))
  apply ZT.derive
  have e := natEq (ComplexLogarithmRemainder.normSq_mul (Γ := Γ) (rawGaussian q) (rawGaussian r))
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  rw [e]
  ring

def data (T N z : PTm n) : PTm n := pairT T (pairT N z)
def factor (T N z i : PTm n) : PTm n := qsub z (entry T (monus N (succ i)))
def normNumerator (q : PTm n) : PTm n := normSq (rawGaussian q)
def normDenominator (q : PTm n) : PTm n := rawDen q*rawDen q

def factorBody : PTm 2 := qsub (sndT (sndT (var 1)))
  (entry (fstT (var 1)) (monus (fstT (sndT (var 1))) (succ (var 0))))
def numeratorBody : PTm 2 := normNumerator factorBody
def denominatorBody : PTm 2 := normDenominator factorBody
def numeratorProduct (T N z k : PTm n) : PTm n := ap2 (prodF numeratorBody) k (data T N z)
def denominatorProduct (T N z k : PTm n) : PTm n := ap2 (prodF denominatorBody) k (data T N z)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (T N z : PTm n) :
    Syn.subst σ (data T N z) = data (Syn.subst σ T) (Syn.subst σ N) (Syn.subst σ z) := by simp only [data,subst_pairT]
@[simp] theorem subst_factor {m : ℕ} (σ : Fin n → PTm m) (T N z i : PTm n) :
    Syn.subst σ (factor T N z i) = factor (Syn.subst σ T) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ i) := by simp [factor]
@[simp] theorem subst_normNumerator {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (normNumerator q) = normNumerator (Syn.subst σ q) := by simp [normNumerator]
@[simp] theorem subst_normDenominator {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (normDenominator q) = normDenominator (Syn.subst σ q) := by simp [normDenominator]
@[simp] theorem subst_numeratorProduct {m : ℕ} (σ : Fin n → PTm m) (T N z k : PTm n) :
    Syn.subst σ (numeratorProduct T N z k) = numeratorProduct (Syn.subst σ T) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ k) := by simp only [numeratorProduct,subst_ap2,subst_data]
@[simp] theorem subst_denominatorProduct {m : ℕ} (σ : Fin n → PTm m) (T N z k : PTm n) :
    Syn.subst σ (denominatorProduct T N z k) = denominatorProduct (Syn.subst σ T) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ k) := by simp only [denominatorProduct,subst_ap2,subst_data]

theorem normNumerator_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx] normNumerator q ≐ normNumerator r := by
  ipra_congr (normNumerator (var 0) : PTm 1) with [h]
theorem normDenominator_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx] normDenominator q ≐ normDenominator r := by
  ipra_congr (normDenominator (var 0) : PTm 1) with [h]
theorem qnormSq_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx] qnormSq q ≐ qnormSq r := by
  ipra_congr (qnormSq (var 0) : PTm 1) with [h]

theorem factor_at (T N z i : PTm n) : Γ ⊢[PRAAx] inst2 factorBody i (data T N z) ≐ factor T N z i := by
  simp only [factorBody,inst2,GaussianRationalMetric.subst_qsub,subst_sndT,subst_fstT,
    subst_entry,PTm.subst_monus,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have zfield : Γ ⊢[PRAAx] sndT (sndT (data T N z)) ≐ z := (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  have Nfield : Γ ⊢[PRAAx] fstT (sndT (data T N z)) ≐ N := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  exact GaussianRationalSyntheticDivision.qsub_congr zfield (entry_congr (fst_pair _ _) (congrMonus Nfield (.eqRefl _)))

theorem numerator_at (T N z i : PTm n) : Γ ⊢[PRAAx] inst2 numeratorBody i (data T N z) ≐ normNumerator (factor T N z i) := by
  simpa only [numeratorBody,inst2,subst_normNumerator] using normNumerator_congr (factor_at (Γ := Γ) T N z i)
theorem denominator_at (T N z i : PTm n) : Γ ⊢[PRAAx] inst2 denominatorBody i (data T N z) ≐ normDenominator (factor T N z i) := by
  simpa only [denominatorBody,inst2,subst_normDenominator] using normDenominator_congr (factor_at (Γ := Γ) T N z i)

theorem norm_represents (q : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (qnormSq q) (ZT.ofNat (normNumerator q)) (normDenominator q) :=
  qnormSq_represents q (rawGaussian q) (rawDen q) (raw_den_positive q) (raw_represents q)

theorem numerator_zero (T N z : PTm n) : Γ ⊢[PRAAx] numeratorProduct T N z zero ≐ one := prod_zero _ _
theorem denominator_zero (T N z : PTm n) : Γ ⊢[PRAAx] denominatorProduct T N z zero ≐ one := prod_zero _ _
theorem numerator_succ (T N z k : PTm n) : Γ ⊢[PRAAx]
    numeratorProduct T N z (succ k) ≐ numeratorProduct T N z k*normNumerator (factor T N z k) :=
  (prod_succ numeratorBody k (data T N z)).eqTrans (congrMul (.eqRefl _) (numerator_at T N z k))
theorem denominator_succ (T N z k : PTm n) : Γ ⊢[PRAAx]
    denominatorProduct T N z (succ k) ≐ denominatorProduct T N z k*normDenominator (factor T N z k) :=
  (prod_succ denominatorBody k (data T N z)).eqTrans (congrMul (.eqRefl _) (denominator_at T N z k))


def normLaw (T N z k : PTm n) : Fm PTm n := RationalArithmetic.represents
  (qnormSq (factors T N z k)) (ZT.ofNat (numeratorProduct T N z k)) (denominatorProduct T N z k)
@[simp] theorem subst_normLaw {m : ℕ} (σ : Fin n → PTm m) (T N z k : PTm n) :
    (normLaw T N z k).subst σ = normLaw (Syn.subst σ T) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ k) := by
  simp only [normLaw,RationalArithmetic.subst_represents,GaussianRationalMetric.subst_qnormSq,
    GaussianRationalReconstruction.subst_factors,ZT.subst_ofNat,subst_numeratorProduct,subst_denominatorProduct]

theorem norm_law_zero (T N z : PTm n) : Γ ⊢[PRAAx] normLaw T N z zero := by
  have rep := qnormSq_represents (Γ := Γ) qone ComplexLogarithmRemainder.oneCode one (le_refl _)
    (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))
  apply scalar_congr (qnormSq_congr (factors_zero T N z)).eqSymm (h := rep)
  · apply ZT.derive
    have e := natEq (ComplexLogarithmRemainder.normSq_one (Γ := Γ) (n := n))
    have p := natEq (numerator_zero (Γ := Γ) T N z)
    simp only [ZT.toZ_ofNat]
    rw [e,p]
  · exact (one_mul one).eqTrans (denominator_zero T N z).eqSymm

theorem norm_law_step (T N z k : PTm n) (ih : Γ ⊢[PRAAx] normLaw T N z k) :
    Γ ⊢[PRAAx] normLaw T N z (succ k) := by
  have rep := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (norm_represents (factor T N z k)) ih
  have actual : Γ ⊢[PRAAx] qnormSq (factors T N z (succ k)) ≐
      multiply (qnormSq (factor T N z k)) (qnormSq (factors T N z k)) :=
    (qnormSq_congr (factors_succ T N z k)).eqTrans (norm_multiply _ _)
  apply scalar_congr actual.eqSymm (h := rep)
  · apply ZT.derive
    have e := natEq (numerator_succ (Γ := Γ) T N z k)
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    rw [e]
    ipra_simps
    ring
  · exact (mul_comm _ _).eqTrans (denominator_succ T N z k).eqSymm

/-- The actual rational reverse factor fold has exactly the numerator and
denominator products searched below. Induction follows its literal order. -/
theorem norm_product_represents (T N z k : PTm n) : Γ ⊢[PRAAx] normLaw T N z k := by
  have all : Γ ⊢[PRAAx] .all (normLaw (Syn.shift T) (Syn.shift N) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_normLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact norm_law_zero T N z
    · simp only [subst_normLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact norm_law_step _ _ _ _ Prf.hyp0
  simpa only [subst_normLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem denominator_positive (T N z k : PTm n) : Γ ⊢[PRAAx] le one (denominatorProduct T N z k) := by
  have all : Γ ⊢[PRAAx] .all (le one (denominatorProduct (Syn.shift T) (Syn.shift N) (Syn.shift z) (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le,subst_denominatorProduct,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact le_congr (.eqRefl one) (denominator_zero T N z).eqSymm (le_refl _)
    · simp only [subst_le,subst_denominatorProduct,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact le_congr (.eqRefl one) (denominator_succ _ _ _ _).eqSymm
        (positive_product _ _ Prf.hyp0 (positive_product _ _ (raw_den_positive _) (raw_den_positive _)))
  simpa only [subst_le,subst_denominatorProduct,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

/-- A bound on the actual qproduct yields the genuine finite numerical
product comparison used by RationalProductWitness. -/
theorem product_comparison (T N z p q : PTm n) (hq : Γ ⊢[PRAAx] le one q)
    (h : Γ ⊢[PRAAx] bounded (product T N z) (pw p N) (pw q N)) : Γ ⊢[PRAAx]
    le (RationalProductWitness.scaledProduct numeratorBody N (q*q) (data T N z))
      (RationalProductWitness.scaledProduct denominatorBody N (p*p) (data T N z)) := by
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (norm_product_represents (Γ := Γ) T N z N)
    (GaussianRationalMetric.squared_tolerance_represents (pw p N) (pw q N)
      (GaussianPolynomialPerturbation.power_positive _ _ hq)) h
  exact le_congr (congrMul (GaussianProductStability.power_product q q N).eqSymm (.eqRefl _))
    (congrMul (GaussianProductStability.power_product p p N).eqSymm (.eqRefl _)) raw

def selectedReverse (T N z p q : PTm n) : PTm n := RationalProductWitness.selected
  numeratorBody denominatorBody N (p*p) (q*q) (data T N z)
def selected (T N z p q : PTm n) : PTm n := monus N (succ (selectedReverse T N z p q))

@[simp] theorem subst_selectedReverse {m : ℕ} (σ : Fin n → PTm m) (T N z p q : PTm n) :
    Syn.subst σ (selectedReverse T N z p q) = selectedReverse (Syn.subst σ T) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ p) (Syn.subst σ q) := by simp [selectedReverse]
@[simp] theorem subst_selected {m : ℕ} (σ : Fin n → PTm m) (T N z p q : PTm n) :
    Syn.subst σ (selected T N z p q) = selected (Syn.subst σ T) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ p) (Syn.subst σ q) := by simp [selected]

theorem selected_reverse_range (T N z p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le one q) (h : Γ ⊢[PRAAx] bounded (product T N z) (pw p N) (pw q N)) : Γ ⊢[PRAAx]
    lt (selectedReverse T N z p q) N :=
  RationalProductWitness.selected_found _ _ _ _ _ _ hN (product_comparison T N z p q hq h)

theorem selected_range (T N z p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le one q) (h : Γ ⊢[PRAAx] bounded (product T N z) (pw p N) (pw q N)) : Γ ⊢[PRAAx]
    lt (selected T N z p q) N := by
  have e := AnalyticNumberTheory.Totatives.split_lt (selected_reverse_range T N z p q hN hq h)
  exact le_congr (.eqRefl _) e.eqSymm (le_add_right _ _)

theorem selected_distance (T N z p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le one q) (h : Γ ⊢[PRAAx] bounded (product T N z) (pw p N) (pw q N)) : Γ ⊢[PRAAx]
    distanceBounded z (entry T (selected T N z p q)) p q := by
  have search := RationalProductWitness.selected_comparison numeratorBody denominatorBody N (p*p) (q*q)
    (data T N z) hN (product_comparison T N z p q hq h)
  have raw : Γ ⊢[PRAAx] le ((q*q)*normNumerator (factor T N z (selectedReverse T N z p q)))
      ((p*p)*normDenominator (factor T N z (selectedReverse T N z p q))) :=
    le_congr (congrMul (.eqRefl _) (numerator_at T N z _)) (congrMul (.eqRefl _) (denominator_at T N z _)) search
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ (raw_den_positive _) hq (raw_represents _) raw


/-- The returned index refers to a genuine original stored target entry.
Only the numerical prefix guard N <= length(T) is required. -/
theorem product_witness (T N z p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le one q) (hLen : Γ ⊢[PRAAx] le N (length T))
    (h : Γ ⊢[PRAAx] bounded (product T N z) (pw p N) (pw q N)) : Γ ⊢[PRAAx]
    lt (selected T N z p q) (length T) ⋏ distanceBounded z (entry T (selected T N z p q)) p q :=
  .andI (lt_of_lt_of_le (selected_range T N z p q hN hq h) hLen) (selected_distance T N z p q hN hq h)

theorem product_hit (T N z p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le one q) (hLen : Γ ⊢[PRAAx] le N (length T))
    (h : Γ ⊢[PRAAx] bounded (product T N z) (pw p N) (pw q N)) : Γ ⊢[PRAAx]
    GaussianRationalCover.hit z T p q :=
  GaussianRationalCover.hit_intro z T p q (selected T N z p q)
    (Prf.andE₁ (product_witness T N z p q hN hq hLen h)) (selected_distance T N z p q hN hq h)

def output (T N z p q : PTm n) : PTm n := pairT (selected T N z p q)
  (pairT (entry T (selected T N z p q)) (qnormSq (qsub z (entry T (selected T N z p q)))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (T N z p q : PTm n) : PTm n := PTm.app outputF ![T,N,z,p,q]

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (T N z p q : PTm n) :
    Syn.subst σ (output T N z p q) = output (Syn.subst σ T) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ p) (Syn.subst σ q) := by
  simp only [output,subst_pairT,subst_selected,subst_entry,GaussianRationalMetric.subst_qnormSq,GaussianRationalMetric.subst_qsub]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (T N z p q : PTm n) :
    Syn.subst σ (run T N z p q) = run (Syn.subst σ T) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ p) (Syn.subst σ q) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem output_program_at (T N z p q : PTm n) : Γ ⊢[PRAAx] run T N z p q ≐ output T N z p q := by
  simpa only [run,outputF,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![T,N,z,p,q]

theorem output_index (T N z p q : PTm n) : Γ ⊢[PRAAx] fstT (run T N z p q) ≐ selected T N z p q :=
  (congrFst (output_program_at T N z p q)).eqTrans (fst_pair _ _)
theorem output_point (T N z p q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run T N z p q)) ≐ entry T (selected T N z p q) :=
  (congrFst ((congrSnd (output_program_at T N z p q)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem output_point_index (T N z p q : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run T N z p q)) ≐ entry T (fstT (run T N z p q)) :=
  (output_point T N z p q).eqTrans (entry_congr (.eqRefl _) (output_index T N z p q).eqSymm)

theorem output_norm (T N z p q : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run T N z p q)) ≐ qnormSq (qsub z (fstT (sndT (run T N z p q)))) :=
  ((congrSnd ((congrSnd (output_program_at T N z p q)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)).eqTrans
    (qnormSq_congr (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl _) (output_point T N z p q).eqSymm))

/-- The actual PR5 code returns an original index and its actual original
point, with the original Euclidean distance bound. This includes p=0. -/
theorem output_certificate (T N z p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le one q) (hLen : Γ ⊢[PRAAx] le N (length T))
    (h : Γ ⊢[PRAAx] bounded (product T N z) (pw p N) (pw q N)) : Γ ⊢[PRAAx]
    lt (fstT (run T N z p q)) (length T) ⋏
      ((fstT (sndT (run T N z p q)) ≐ entry T (fstT (run T N z p q))) ⋏
        distanceBounded z (fstT (sndT (run T N z p q))) p q) := by
  have actual := product_witness T N z p q hN hq hLen h
  exact .andI (lt_congr (output_index T N z p q).eqSymm (.eqRefl _) (Prf.andE₁ actual))
    (.andI (output_point_index T N z p q)
      (GaussianRationalCover.distance_congr (.eqRefl _) (output_point T N z p q).eqSymm
        (.eqRefl _) (.eqRefl _) (Prf.andE₂ actual)))

theorem rational_norm_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (RationalArithmetic.represents (qnormSq (factors (var 0) (var 1) (var 2) (var 3)))
      (ZT.ofNat (numeratorProduct (var 0) (var 1) (var 2) (var 3)))
      (denominatorProduct (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (norm_product_represents _ _ _ _)

theorem rational_product_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 4) ⟶ le (var 1) (length (var 0)) ⟶
      bounded (product (var 0) (var 1) (var 2)) (pw (var 3) (var 1)) (pw (var 4) (var 1)) ⟶
      (lt (selected (var 0) (var 1) (var 2) (var 3) (var 4)) (length (var 0)) ⋏
        distanceBounded (var 2) (entry (var 0) (selected (var 0) (var 1) (var 2) (var 3) (var 4))) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (product_witness _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem original_product_hit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 4) ⟶ le (var 1) (length (var 0)) ⟶
      bounded (product (var 0) (var 1) (var 2)) (pw (var 3) (var 1)) (pw (var 4) (var 1)) ⟶
      GaussianRationalCover.hit (var 2) (var 0) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (product_hit _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem original_product_output_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 4) ⟶ le (var 1) (length (var 0)) ⟶
      bounded (product (var 0) (var 1) (var 2)) (pw (var 3) (var 1)) (pw (var 4) (var 1)) ⟶
      (lt (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (length (var 0)) ⋏
        ((fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐
          entry (var 0) (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ⋏
            distanceBounded (var 2) (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (output_certificate _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem product_witness_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐
        qnormSq (qsub (var 2) (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))))) :=
  closeUniv 5 (.andI (output_program_at _ _ _ _ _) (output_norm _ _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianRationalProductWitness
