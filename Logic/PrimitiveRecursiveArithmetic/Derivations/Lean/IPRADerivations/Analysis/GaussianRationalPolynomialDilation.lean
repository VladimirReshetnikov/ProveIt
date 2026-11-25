import IPRADerivations.Analysis.GaussianRationalLowCoefficientConvolution
import IPRADerivations.Analysis.GaussianRationalPowerExpansion
import IPRADerivations.Analysis.GaussianRationalGridCoefficientEquality
import IPRADerivations.Analysis.GaussianRationalConvolutionNorm
import IPRADerivations.Core.LinearCombination

/-!
# Actual variable dilation and its finite coefficient norm

The numerical N+1 buffer stores original coefficient i times t^(N-i).
Its actual evaluator is the original polynomial at t*z, proved through
actual finite power expansions. Genuine bounded-grid coefficient reflection
then binds dilation of the actual convolution to convolution of the actual
dilations. This supplies a stored weighted coefficient norm for finite C4
majorants; no dilation, product or evaluator law is an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDilation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd qmul qzero hornerF evaluate canonical)
open GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr canonicalCoefficients)
open GaussianRationalReciprocal (power powerF)
open GaussianRationalPolynomialProduct (product product_length product_canonical product_evaluation)
open GaussianCoefficientL1 (coefficientNorm)
open GaussianRationalSumSegments (entriesEqual)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open GaussianRationalPowerAlgebra (qmul_commutative)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (C N t : PTm n) : PTm n := pairT C (pairT N t)
def body : PTm 2 := qmul (entry (fstT (var 1)) (var 0))
  (power (sndT (sndT (var 1))) (monus (fstT (sndT (var 1))) (var 0)))
def dilated (C N t : PTm n) : PTm n := sequence body (succ N) (data C N t)
def weightedNorm (C N t : PTm n) : PTm n := coefficientNorm (dilated C N t)
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (C N t : PTm n) :
    Syn.subst σ (data C N t) = data (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ t) := by simp [data]
@[simp] theorem subst_dilated {l : ℕ} (σ : Fin n → PTm l) (C N t : PTm n) :
    Syn.subst σ (dilated C N t) = dilated (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ t) := by simp [dilated]
@[simp] theorem subst_weightedNorm {l : ℕ} (σ : Fin n → PTm l) (C N t : PTm n) :
    Syn.subst σ (weightedNorm C N t) = weightedNorm (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ t) := by simp [weightedNorm]

theorem body_at (C N t i : PTm n) : Γ ⊢[PRAAx]
    inst2 body i (data C N t) ≐ qmul (entry C i) (power t (monus N i)) := by
  have p := snd_pair (Γ := Γ) C (pairT N t)
  have e := Prf.eqCongr (Γ := Γ)
    (qmul (entry (var 0) (var 3)) (power (var 2) (monus (var 1) (var 3))) : PTm 4)
    (σ := ![fstT (data C N t),fstT (sndT (data C N t)),sndT (sndT (data C N t)),i])
    (σ' := ![C,N,t,i])
    (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (congrFst p).eqTrans (fst_pair _ _)
      · exact (congrSnd p).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  simpa [body,inst2,data] using e

theorem dilated_length (C N t : PTm n) : Γ ⊢[PRAAx] length (dilated C N t) ≐ succ N := sequence_length _ _ _
theorem dilated_lookup (C N t i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (dilated C N t) i ≐ qmul (entry C i) (power t (monus N i)) :=
  (sequence_decode body ((succ_monus_succ _ _).eqTrans hi)).eqTrans (body_at C N t i)
theorem dilated_canonical (C N t : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (dilated C N t) := by
  refine .allI (.impI ?_)
  have hi : (lt (var 0) (length (Syn.shift (dilated C N t))) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (var 0) (Syn.shift N) := by
    have h : (lt (var 0) (length (Syn.shift (dilated C N t))) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (var 0) (succ (Syn.shift N)) :=
      lt_congr (.eqRefl _) (dilated_length (Syn.shift C) (Syn.shift N) (Syn.shift t))
        (by simpa only [Syn.shift,subst_dilated] using
          (Prf.hyp0 : (lt (var 0) (length (Syn.shift (dilated C N t))) :: Γ.map Fm.shift) ⊢[PRAAx]
            lt (var 0) (length (Syn.shift (dilated C N t)))))
    exact (succ_monus_succ _ _).eqSymm.eqTrans h
  simpa only [Syn.shift,subst_dilated] using
    GaussianRationalHorner.canonical_congr (dilated_lookup _ _ _ _ hi) (GaussianRationalHorner.qmul_canonical _ _)

theorem exponent_dilated (C N t e : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    exponentCoefficient (dilated C N t) N e ≐ qmul (exponentCoefficient C N e) (power t e) :=
  (GaussianRationalLowCoefficientConvolution.exponent_inside _ _ _ he).eqTrans
    ((dilated_lookup C N t (monus N e) (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
      (qmul_congr (GaussianRationalLowCoefficientConvolution.exponent_inside C N e he).eqSymm
        (congrAp2 powerF (GaussianRationalMonicReconstruction.complement N e he) (.eqRefl _))))

/-- Each original numerical power-expansion term has the exact dilated
coefficient/power product, with all exponents checked in range. -/
theorem term_dilated (C N t z e : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    GaussianOffDominantTerms.term (dilated C N t) N z e ≐ GaussianOffDominantTerms.term C N (qmul t z) e :=
  (qmul_congr
    ((dilated_lookup C N t (monus N e) (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
      (qmul_congr (.eqRefl _) (congrAp2 powerF (GaussianRationalMonicReconstruction.complement N e he) (.eqRefl _))))
    (.eqRefl _)).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
      (qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.power_product t z e).eqSymm))

theorem expansion_entries (C N t z : PTm n) : Γ ⊢[PRAAx] entriesEqual
    (GaussianRationalPowerExpansion.terms (dilated C N t) N z)
    (GaussianRationalPowerExpansion.terms C N (qmul t z)) (succ N) := by
  refine .allI (.impI ?_)
  have he : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
    (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Syn.shift,subst_dilated,GaussianRationalPowerExpansion.subst_terms,GaussianRationalHorner.subst_qmul] using
    (GaussianRationalPowerExpansion.terms_lookup _ _ _ _ he).eqTrans
      ((term_dilated (Syn.shift C) (Syn.shift N) (Syn.shift t) (Syn.shift z) (var 0) he).eqTrans
        (GaussianRationalPowerExpansion.terms_lookup _ _ _ _ he).eqSymm)

/-- The actual original evaluator conjugacy follows from existing genuine
finite power-expansion induction and bounded actual stored entries. -/
theorem dilation_evaluation (C N t z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (dilated C N t) z ≐ evaluate C (qmul t z) := by
  have same := GaussianRationalSumSegments.prefix_entries_congr (Γ := Γ) _ _ (succ N) (succ N)
    (expansion_entries C N t z) (le_refl _)
  have evalSame : Γ ⊢[PRAAx]
      evaluate (GaussianRationalPowerExpansion.terms (dilated C N t) N z) qone ≐
      evaluate (GaussianRationalPowerExpansion.terms C N (qmul t z)) qone := (congrAp3 hornerF (GaussianRationalPowerExpansion.terms_length (dilated C N t) N z)
    (.eqRefl _) (.eqRefl _)).eqTrans
      (same.eqTrans (congrAp3 hornerF (GaussianRationalPowerExpansion.terms_length C N (qmul t z)).eqSymm
        (.eqRefl _) (.eqRefl _)))
  exact (GaussianRationalPowerExpansion.power_expansion _ _ _ (dilated_length C N t)).eqTrans
    (evalSame.eqTrans (GaussianRationalPowerExpansion.power_expansion C N (qmul t z) hC).eqSymm)

theorem dilated_product_value (P Q N M t z : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx]
    evaluate (dilated (product P Q N M) (N+M) t) z ≐
      evaluate (product (dilated P N t) (dilated Q M t) N M) z :=
  (dilation_evaluation _ _ t z (product_length _ _ _ _)).eqTrans
    ((product_evaluation P Q N M (qmul t z) hP hQ).eqTrans
      ((qmul_congr (dilation_evaluation P N t z hP).eqSymm (dilation_evaluation Q M t z hQ).eqSymm).eqTrans
        (product_evaluation _ _ _ _ z (dilated_length P N t) (dilated_length Q M t)).eqSymm))

theorem product_grid (P Q N M t : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx] GaussianRationalGridCoefficientEquality.gridEqual
    (dilated (product P Q N M) (N+M) t) (product (dilated P N t) (dilated Q M t) N M) (N+M) := by
  have ps : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift P) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hP.shift
  have qs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift Q) ≐ succ (Syn.shift M) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hQ.shift
  refine .allI (.impI ?_)
  let Δ := le (var 0) (Syn.shift (N+M)) :: Γ.map Fm.shift
  simpa only [Δ,Syn.shift,subst_dilated,GaussianRationalPolynomialProduct.subst_product,PTm.subst_add] using
    dilated_product_value (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift t)
      (GaussianRationalFiniteGridIdentity.gridPoint (var 0)) ps.wk qs.wk

theorem product_coefficient (P Q N M t i : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) (hi : Γ ⊢[PRAAx] le i (N+M)) : Γ ⊢[PRAAx]
    entry (dilated (product P Q N M) (N+M) t) i ≐ entry (product (dilated P N t) (dilated Q M t) N M) i :=
  GaussianRationalGridCoefficientEquality.coefficient_equal _ _ _ i
    (dilated_length _ _ _) (product_length _ _ _ _) (dilated_canonical _ _ _) (product_canonical _ _ _ _)
    (product_grid P Q N M t hP hQ) hi

theorem product_entries (P Q N M t : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx] entriesEqual
    (dilated (product P Q N M) (N+M) t) (product (dilated P N t) (dilated Q M t) N M) (succ (N+M)) := by
  have grid := GaussianRationalGridCoefficientEquality.coefficients_equal _ _ _
    (dilated_length _ _ _) (product_length _ _ _ _) (dilated_canonical _ _ _) (product_canonical _ _ _ _)
    (product_grid (Γ := Γ) P Q N M t hP hQ)
  refine .allI (.impI ?_)
  have hi : (lt (var 0) (Syn.shift (succ (N+M))) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (var 0) (Syn.shift (N+M)) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have hAt := Prf.impE grid.allOpen.wk hi
  simpa only [Syn.shift] using hAt

/-- The actual original convolution is submultiplicative for the computed
weighted norm. Its coefficient identity was derived from the SAME program. -/
theorem weighted_product_bound (P Q N M t : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx] RationalArgmin.rationalLE
    (weightedNorm (product P Q N M) (N+M) t)
    (RationalArithmetic.multiply (weightedNorm P N t) (weightedNorm Q M t)) :=
  RationalArgmin.rationalLE_congr
    (GaussianPolynomialNormBuffers.norm_entries _ _ _ (dilated_length _ _ _) (product_length _ _ _ _)
      (product_entries P Q N M t hP hQ)).eqSymm (.eqRefl _)
    (GaussianRationalConvolutionNorm.product_norm _ _ N M (dilated_length _ _ _) (dilated_length _ _ _))

theorem multiply_sum_right (a b c : PTm n) : Γ ⊢[PRAAx]
    qmul (qadd a b) c ≐ qadd (qmul a c) (qmul b c) :=
  (qmul_commutative _ _).eqTrans ((GaussianRationalCoefficientScaling.qmul_add c a b).eqTrans
    (qadd_congr (qmul_commutative _ _) (qmul_commutative _ _)))

theorem added_coefficient (P Q N t i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (dilated (GaussianRationalPolynomialBuffers.added P Q (succ N)) N t) i ≐
      entry (GaussianRationalPolynomialBuffers.added (dilated P N t) (dilated Q N t) (succ N)) i :=
  (dilated_lookup _ _ _ i hi).eqTrans
    ((qmul_congr (GaussianRationalPolynomialBuffers.added_lookup P Q (succ N) i ((succ_monus_succ _ _).eqTrans hi))
      (.eqRefl _)).eqTrans
      ((multiply_sum_right _ _ _).eqTrans
        ((qadd_congr (dilated_lookup P N t i hi).eqSymm (dilated_lookup Q N t i hi).eqSymm).eqTrans
          (GaussianRationalPolynomialBuffers.added_lookup _ _ (succ N) i ((succ_monus_succ _ _).eqTrans hi)).eqSymm)))

theorem added_entries (P Q N t : PTm n) : Γ ⊢[PRAAx] entriesEqual
    (dilated (GaussianRationalPolynomialBuffers.added P Q (succ N)) N t)
    (GaussianRationalPolynomialBuffers.added (dilated P N t) (dilated Q N t) (succ N)) (succ N) := by
  refine .allI (.impI ?_)
  have hi : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (var 0) (Syn.shift N) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Syn.shift,subst_dilated,GaussianRationalPolynomialBuffers.subst_added,ConciseIPRA.PTm.subst_succ] using
    added_coefficient (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift t) (var 0) hi

/-- Actual finite addition is subadditive for the weighted coefficient norm;
its truncation semantics are the original N+1 constructor's semantics. -/
theorem weighted_added_bound (P Q N t : PTm n) : Γ ⊢[PRAAx] RationalArgmin.rationalLE
    (weightedNorm (GaussianRationalPolynomialBuffers.added P Q (succ N)) N t)
    (RationalArithmetic.add (weightedNorm P N t) (weightedNorm Q N t)) :=
  RationalArgmin.rationalLE_congr
    (GaussianPolynomialNormBuffers.norm_entries _ _ _ (dilated_length _ _ _)
      (GaussianRationalPolynomialBuffers.added_length _ _ _) (added_entries P Q N t)).eqSymm (.eqRefl _)
    (GaussianPolynomialNormBuffers.norm_added _ _ _ (dilated_length _ _ _) (dilated_length _ _ _))

theorem scaled_coefficient (C N t a i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (dilated (GaussianRationalCoefficientScaling.scaled C a) N t) i ≐
      entry (GaussianRationalCoefficientScaling.scaled (dilated C N t) a) i := by
  have range : Γ ⊢[PRAAx] lt i (length C) :=
    lt_congr (.eqRefl _) hC.eqSymm ((succ_monus_succ _ _).eqTrans hi)
  exact (dilated_lookup _ _ _ i hi).eqTrans
    ((qmul_congr (GaussianRationalCoefficientScaling.scaled_lookup C a i range) (.eqRefl _)).eqTrans
      ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
        ((qmul_congr (.eqRefl _) (dilated_lookup C N t i hi).eqSymm).eqTrans
          (GaussianRationalCoefficientScaling.scaled_lookup _ a i
            (lt_congr (.eqRefl _) (dilated_length C N t).eqSymm ((succ_monus_succ _ _).eqTrans hi))).eqSymm)))

theorem scaled_entries (C N t a : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx] entriesEqual
    (dilated (GaussianRationalCoefficientScaling.scaled C a) N t)
    (GaussianRationalCoefficientScaling.scaled (dilated C N t) a) (succ N) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  refine .allI (.impI ?_)
  have hi : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (var 0) (Syn.shift N) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Syn.shift,subst_dilated,GaussianRationalCoefficientScaling.subst_scaled] using
    scaled_coefficient (Syn.shift C) (Syn.shift N) (Syn.shift t) (Syn.shift a) (var 0) cs.wk hi

theorem weighted_scaled_bound (C N t a : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE (weightedNorm (GaussianRationalCoefficientScaling.scaled C a) N t)
      (RationalArithmetic.multiply (GaussianRationalL1.qL1 a) (weightedNorm C N t)) :=
  RationalArgmin.rationalLE_congr
    (GaussianPolynomialNormBuffers.norm_entries _ _ _ (dilated_length _ _ _)
      ((GaussianRationalCoefficientScaling.scaled_length _ _).eqTrans (dilated_length _ _ _))
      (scaled_entries C N t a hC)).eqSymm (.eqRefl _)
    (GaussianPolynomialNormBuffers.norm_scaled _ _)

theorem pad_length (C N k : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    length (GaussianRationalPolynomialBuffers.leftPad C k) ≐ succ (k+N) :=
  (GaussianRationalPolynomialBuffers.pad_length C k).eqTrans ((congrAdd (.eqRefl _) hC).eqTrans (by ipra_ring))

theorem padded_coefficient (C N t k i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hi : Γ ⊢[PRAAx] le i (k+N)) : Γ ⊢[PRAAx]
    entry (dilated (GaussianRationalPolynomialBuffers.leftPad C k) (k+N) t) i ≐
      entry (GaussianRationalPolynomialBuffers.leftPad (dilated C N t) k) i := by
  refine .orE (lt_or_le i k) ?_ ?_
  · exact (dilated_lookup _ _ _ i hi.wk).eqTrans
      ((qmul_congr (GaussianRationalPolynomialBuffers.pad_leading C k i Prf.hyp0) (.eqRefl _)).eqTrans
        ((GaussianRationalSyntheticDivision.qmul_zero_left _).eqTrans
          (GaussianRationalPolynomialBuffers.pad_leading _ k i Prf.hyp0).eqSymm))
  · let Δ := le k i :: Γ
    have idx : Δ ⊢[PRAAx] i ≐ k+monus i k := eq_add_of_le Prf.hyp0
    have range : Δ ⊢[PRAAx] le (monus i k) N := by
      apply le_of_eq_add (d := monus (k+N) i)
      ipra_lc natEq (eq_add_of_le (Γ := Δ) hi.wk)+natEq idx
    have expIdx : Δ ⊢[PRAAx] monus (k+N) i ≐ monus N (monus i k) :=
      (congrMonus (add_comm k N) (idx.eqTrans (add_comm _ _))).eqTrans (monus_add_add N (monus i k) k)
    have rawRange : Δ ⊢[PRAAx] lt i (k+length C) :=
      le_congr (succ_eq_add_one i).eqSymm (by
        exact ((congrAdd (.eqRefl _) hC.wk).eqTrans (by ipra_ring)).eqSymm)
        (add_le_add_right one hi.wk)
    have newRange : Δ ⊢[PRAAx] lt i (k+length (dilated C N t)) :=
      le_congr (succ_eq_add_one i).eqSymm (by
        exact ((congrAdd (.eqRefl _) (dilated_length C N t)).eqTrans (by ipra_ring)).eqSymm)
        (add_le_add_right one hi.wk)
    have rawEntry := (GaussianRationalPolynomialBuffers.pad_lookup C k i rawRange).eqTrans
      (GaussianRationalPolynomialBuffers.pad_coefficient_after C k i Prf.hyp0)
    have newEntry := (GaussianRationalPolynomialBuffers.pad_lookup (dilated C N t) k i newRange).eqTrans
      (GaussianRationalPolynomialBuffers.pad_coefficient_after _ k i Prf.hyp0)
    exact (dilated_lookup _ _ _ i hi.wk).eqTrans
      ((qmul_congr rawEntry (congrAp2 powerF expIdx (.eqRefl _))).eqTrans
        ((dilated_lookup C N t (monus i k) range).eqSymm.eqTrans newEntry.eqSymm))

theorem padded_entries (C N t k : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx] entriesEqual
    (dilated (GaussianRationalPolynomialBuffers.leftPad C k) (k+N) t)
    (GaussianRationalPolynomialBuffers.leftPad (dilated C N t) k) (succ (k+N)) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  refine .allI (.impI ?_)
  have hi : (lt (var 0) (Syn.shift (succ (k+N))) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (var 0) (Syn.shift k+Syn.shift N) := by
    have hlt : (lt (var 0) (Syn.shift (succ (k+N))) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (var 0) (succ (Syn.shift k+Syn.shift N)) := by
      simpa only [Syn.shift,PTm.subst_add,ConciseIPRA.PTm.subst_succ] using
        (Prf.hyp0 : (lt (var 0) (Syn.shift (succ (k+N))) :: Γ.map Fm.shift) ⊢[PRAAx]
          lt (var 0) (Syn.shift (succ (k+N))))
    exact (succ_monus_succ _ _).eqSymm.eqTrans hlt
  simpa only [Syn.shift,subst_dilated,GaussianRationalPolynomialBuffers.subst_leftPad,PTm.subst_add] using
    padded_coefficient (Syn.shift C) (Syn.shift N) (Syn.shift t) (Syn.shift k) (var 0) cs.wk hi

theorem weighted_padding (C N t k : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    weightedNorm (GaussianRationalPolynomialBuffers.leftPad C k) (k+N) t ≐ weightedNorm C N t :=
  (GaussianPolynomialNormBuffers.norm_entries _ _ _ (dilated_length _ _ _)
    (pad_length _ N k (dilated_length C N t)) (padded_entries C N t k hC)).eqTrans
      (GaussianPolynomialNormBuffers.norm_padding _ k)

theorem weighted_norm_nonnegative (C N t : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianRationalSyntheticBounds.natCode zero) (weightedNorm C N t) :=
  GaussianCoefficientNormOrder.coefficient_nonnegative _

/-! The actual fixed PR4 returns the stored dilation, its finite coefficient
norm and both evaluator outputs. All numerical degrees and queries are data. -/
def output (C N t z : PTm n) : PTm n := pairT (dilated C N t)
  (pairT (weightedNorm C N t) (pairT (evaluate (dilated C N t) z) (evaluate C (qmul t z))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (C N t z : PTm n) : PTm n := PTm.app outputF ![C,N,t,z]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (C N t z : PTm n) :
    Syn.subst σ (output C N t z) = output (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ z) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (C N t z : PTm n) :
    Syn.subst σ (run C N t z) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ z) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (C N t z : PTm n) : Γ ⊢[PRAAx] run C N t z ≐ output C N t z := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,t,z]
theorem returned_dilation (C N t z : PTm n) : Γ ⊢[PRAAx] fstT (run C N t z) ≐ dilated C N t :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_tail (C N t z : PTm n) : Γ ⊢[PRAAx] sndT (run C N t z) ≐
    pairT (weightedNorm C N t) (pairT (evaluate (dilated C N t) z) (evaluate C (qmul t z))) :=
  (congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_norm (C N t z : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N t z)) ≐ weightedNorm C N t :=
  (congrFst (returned_tail _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_values (C N t z : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run C N t z)) ≐
    pairT (evaluate (dilated C N t) z) (evaluate C (qmul t z)) :=
  (congrSnd (returned_tail _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_dilated_value (C N t z : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run C N t z))) ≐ evaluate (dilated C N t) z :=
  (congrFst (returned_values _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_original_value (C N t z : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run C N t z))) ≐ evaluate C (qmul t z) :=
  (congrSnd (returned_values _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_equal (C N t z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run C N t z))) ≐ sndT (sndT (sndT (run C N t z))) :=
  (returned_dilated_value _ _ _ _).eqTrans
    ((dilation_evaluation C N t z hC).eqTrans (returned_original_value _ _ _ _).eqSymm)

theorem actual_dilation_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (dilated (var 0) (var 1) (var 2)) ≐ succ (var 1) ⋏
      canonicalCoefficients (dilated (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (dilated_length _ _ _) (dilated_canonical _ _ _))
theorem actual_dilation_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1) ⟶ entry (dilated (var 0) (var 1) (var 2)) (var 3) ≐
      qmul (entry (var 0) (var 3)) (power (var 2) (monus (var 1) (var 3)))) :=
  closeUniv 4 (.impI (dilated_lookup _ _ _ _ Prf.hyp0))
theorem actual_dilation_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ evaluate (dilated (var 0) (var 1) (var 2)) (var 3) ≐
      evaluate (var 0) (qmul (var 2) (var 3))) :=
  closeUniv 4 (.impI (dilation_evaluation _ _ _ _ Prf.hyp0))
theorem actual_dilation_product_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (length (var 0) ≐ succ (var 2) ⟶ length (var 1) ≐ succ (var 3) ⟶ le (var 5) (var 2+var 3) ⟶
      entry (dilated (product (var 0) (var 1) (var 2) (var 3)) (var 2+var 3) (var 4)) (var 5) ≐
        entry (product (dilated (var 0) (var 2) (var 4)) (dilated (var 1) (var 3) (var 4)) (var 2) (var 3)) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (product_coefficient _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_weighted_product_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 2) ⟶ length (var 1) ≐ succ (var 3) ⟶
      RationalArgmin.rationalLE (weightedNorm (product (var 0) (var 1) (var 2) (var 3)) (var 2+var 3) (var 4))
        (RationalArithmetic.multiply (weightedNorm (var 0) (var 2) (var 4)) (weightedNorm (var 1) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (.impI (weighted_product_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_weighted_added_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (RationalArgmin.rationalLE
      (weightedNorm (GaussianRationalPolynomialBuffers.added (var 0) (var 1) (succ (var 2))) (var 2) (var 3))
      (RationalArithmetic.add (weightedNorm (var 0) (var 2) (var 3)) (weightedNorm (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (weighted_added_bound _ _ _ _)
theorem actual_weighted_scaled_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶
      RationalArgmin.rationalLE (weightedNorm (GaussianRationalCoefficientScaling.scaled (var 0) (var 3)) (var 1) (var 2))
        (RationalArithmetic.multiply (GaussianRationalL1.qL1 (var 3)) (weightedNorm (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (.impI (weighted_scaled_bound _ _ _ _ Prf.hyp0))
theorem actual_weighted_padding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶
      weightedNorm (GaussianRationalPolynomialBuffers.leftPad (var 0) (var 3)) (var 3+var 1) (var 2) ≐
        weightedNorm (var 0) (var 1) (var 2)) :=
  closeUniv 4 (.impI (weighted_padding _ _ _ _ Prf.hyp0))
theorem actual_dilation_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem returned_dilation_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐
      sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) :=
  closeUniv 4 (.impI (returned_equal _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDilation
