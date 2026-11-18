import IPRADerivations.Analysis.GaussianRootProduct

/-!
# Canonically normalized common-denominator root-product coefficients

Finite-demand Section 4, rational frontend of the runtime product constructor.
If roots have Gaussian integer numerators `r_j` over one positive common `D`,
the generated integer coefficient list `a_i` is the descending list for
`∏(Y-r_j)`. The actual rational coefficient producer returns the canonical
components of `a_i D^(N-i)/D^N`, namely the coefficients of
`D^(-N) ∏(DX-r_j) = ∏(X-r_j/D)`.

All degree, denominator, list and coefficient indices are numerical inputs.
The normalization cross identities, actual list lookup and literal leading
coefficient one are proved. Converting arbitrary independently denominated
root inputs to this common-D format, and evaluating the normalized rational
coefficient list, remain separate adapters. The integer Horner/factor identity
is proved in GaussianRootProduct; no full stability theorem is claimed here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRootProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im scale)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra (equal_re equal_im re_scale im_scale re_one im_one)
open LeanProofs.IPRA.Analysis.GaussianRootProduct (coefficients coefficients_monic)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization
  (normalize integerCode normalize_integer normalize_preserves_value positive_form)
open LeanProofs.IPRA.Analysis.RationalNormalForm (wellFormed normalize_well_formed)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def commonDenominator (D N : PTm n) : PTm n := pw D N
def numeratorScale (D N i : PTm n) : PTm n := pw D (monus N i)
def scaledCoefficient (R N D i : PTm n) : PTm n :=
  scale (numeratorScale D N i) (entry (coefficients R N) i)
def realCoefficient (R N D i : PTm n) : PTm n := normalize (re (scaledCoefficient R N D i)) (commonDenominator D N)
def imagCoefficient (R N D i : PTm n) : PTm n := normalize (im (scaledCoefficient R N D i)) (commonDenominator D N)
def rationalCoefficient (R N D i : PTm n) : PTm n := pairT (realCoefficient R N D i) (imagCoefficient R N D i)

@[simp] theorem subst_commonDenominator {m : ℕ} (σ : Fin n → PTm m) (D N : PTm n) :
    Syn.subst σ (commonDenominator D N) = commonDenominator (Syn.subst σ D) (Syn.subst σ N) := by simp [commonDenominator]
@[simp] theorem subst_numeratorScale {m : ℕ} (σ : Fin n → PTm m) (D N i : PTm n) :
    Syn.subst σ (numeratorScale D N i) = numeratorScale (Syn.subst σ D) (Syn.subst σ N) (Syn.subst σ i) := by simp [numeratorScale]
@[simp] theorem subst_scaledCoefficient {m : ℕ} (σ : Fin n → PTm m) (R N D i : PTm n) :
    Syn.subst σ (scaledCoefficient R N D i) = scaledCoefficient (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ D) (Syn.subst σ i) := by simp [scaledCoefficient]
@[simp] theorem subst_realCoefficient {m : ℕ} (σ : Fin n → PTm m) (R N D i : PTm n) :
    Syn.subst σ (realCoefficient R N D i) = realCoefficient (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ D) (Syn.subst σ i) := by simp [realCoefficient]
@[simp] theorem subst_imagCoefficient {m : ℕ} (σ : Fin n → PTm m) (R N D i : PTm n) :
    Syn.subst σ (imagCoefficient R N D i) = imagCoefficient (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ D) (Syn.subst σ i) := by simp [imagCoefficient]
@[simp] theorem subst_rationalCoefficient {m : ℕ} (σ : Fin n → PTm m) (R N D i : PTm n) :
    Syn.subst σ (rationalCoefficient R N D i) = rationalCoefficient (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ D) (Syn.subst σ i) := by simp [rationalCoefficient]

theorem common_denominator_positive (D N : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le one (commonDenominator D N) := by
  have h := AnalyticNumberTheory.Valuation.pw_pos' (positive_form hD) N
  exact le_congr (.eqRefl _) h.eqSymm (zero_lt_succ _)

def coefficientClearing (R N D i : PTm n) : Fm PTm n :=
  ZT.eq (numeratorOf (realCoefficient R N D i)*ZT.ofNat (commonDenominator D N))
    ((re (entry (coefficients R N) i)*ZT.ofNat (numeratorScale D N i))*ZT.ofNat (denominatorOf (realCoefficient R N D i))) ⋏
  ZT.eq (numeratorOf (imagCoefficient R N D i)*ZT.ofNat (commonDenominator D N))
    ((im (entry (coefficients R N) i)*ZT.ofNat (numeratorScale D N i))*ZT.ofNat (denominatorOf (imagCoefficient R N D i)))

@[simp] theorem subst_coefficientClearing {m : ℕ} (σ : Fin n → PTm m) (R N D i : PTm n) :
    (coefficientClearing R N D i).subst σ = coefficientClearing (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ D) (Syn.subst σ i) := by
  simp [coefficientClearing]

/-- Exact coefficient normalization, including arbitrary signed numerator
pairs. No coefficient value or desired clearing law is supplied. -/
theorem coefficient_clearing (R N D i : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] coefficientClearing R N D i := by
  have hr := ZT.toZ_eq (normalize_preserves_value (Γ := Γ) (re (scaledCoefficient R N D i))
    (commonDenominator D N) (common_denominator_positive D N hD))
  have hi := ZT.toZ_eq (normalize_preserves_value (Γ := Γ) (im (scaledCoefficient R N D i))
    (commonDenominator D N) (common_denominator_positive D N hD))
  refine .andI (ZT.derive ?_) (ZT.derive ?_)
  · simp only [ZT.toZ_mul,ZT.toZ_ofNat] at hr ⊢
    simp only [scaledCoefficient,re_scale] at hr
    simp only [realCoefficient,scaledCoefficient]
    linear_combination -hr
  · simp only [ZT.toZ_mul,ZT.toZ_ofNat] at hi ⊢
    simp only [scaledCoefficient,im_scale] at hi
    simp only [imagCoefficient,scaledCoefficient]
    linear_combination -hi

theorem coefficient_guards (R N D i : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] wellFormed (realCoefficient R N D i) ⋏ wellFormed (imagCoefficient R N D i) :=
  .andI (normalize_well_formed _ _ (common_denominator_positive D N hD))
    (normalize_well_formed _ _ (common_denominator_positive D N hD))

def coefficientData (R N D : PTm n) : PTm n := pairT R (pairT N D)
def rationalBody : PTm 2 := rationalCoefficient (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def rationalCoefficients (R N D : PTm n) : PTm n := sequence rationalBody (succ N) (coefficientData R N D)
def rationalCoefficientsF : PR 3 := PTm.toPR (rationalCoefficients (var 0) (var 1) (var 2))

@[simp] theorem subst_coefficientData {m : ℕ} (σ : Fin n → PTm m) (R N D : PTm n) :
    Syn.subst σ (coefficientData R N D) = coefficientData (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ D) := by simp [coefficientData]
@[simp] theorem subst_rationalCoefficients {m : ℕ} (σ : Fin n → PTm m) (R N D : PTm n) :
    Syn.subst σ (rationalCoefficients R N D) = rationalCoefficients (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ D) := by simp [rationalCoefficients]

theorem rational_body_at (R N D i : PTm n) :
    Γ ⊢[PRAAx] inst2 rationalBody i (coefficientData R N D) ≐ rationalCoefficient R N D i := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (rationalCoefficient (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (coefficientData R N D),fstT (sndT (coefficientData R N D)),sndT (sndT (coefficientData R N D)),i])
    (σ' := ![R,N,D,i]) (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  simpa only [rationalBody,inst2,subst_rationalCoefficient,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons] using e

theorem rational_coefficients_length (R N D : PTm n) :
    Γ ⊢[PRAAx] length (rationalCoefficients R N D) ≐ succ N := sequence_length _ _ _

theorem rational_coefficients_lookup (R N D i : PTm n) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] entry (rationalCoefficients R N D) i ≐ rationalCoefficient R N D i :=
  (sequence_decode rationalBody ((succ_monus_succ _ _).eqTrans hi)).eqTrans (rational_body_at R N D i)

/-- Literal canonical rational one, as the pair of its real and imaginary
canonical integer scalar codes. -/
def rationalOne : PTm n := pairT (integerCode (ZT.natLit 1)) (integerCode (ZT.natLit 0))

@[simp] theorem subst_rationalOne {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (rationalOne : PTm n) = (rationalOne : PTm m) := by simp [rationalOne]

/-- The normalized leading coefficient is literally one, rather than merely
having that decoded value. The actual generated integer polynomial is monic. -/
theorem rational_monic (R N D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] rationalCoefficient R N D zero ≐ rationalOne := by
  have hm := coefficients_monic (Γ := Γ) R N
  have hp : Groth.ι (Q.mk Γ (numeratorScale D N zero)) = Groth.ι (Q.mk Γ (commonDenominator D N)) :=
    natEq (congrAp2 powF (monus_zero N) (.eqRefl D) : Γ ⊢[PRAAx] numeratorScale D N zero ≐ commonDenominator D N)
  have hr : Γ ⊢[PRAAx] ZT.eq (re (scaledCoefficient R N D zero)) (ZT.ofNat (commonDenominator D N)*ZT.natLit 1) := by
    apply ZT.derive
    simp only [scaledCoefficient,re_scale,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_natLit]
    rw [hp,equal_re hm,re_one]
    ring
  have hi : Γ ⊢[PRAAx] ZT.eq (im (scaledCoefficient R N D zero)) (ZT.ofNat (commonDenominator D N)*ZT.natLit 0) := by
    apply ZT.derive
    simp only [scaledCoefficient,im_scale,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_natLit]
    rw [hp,equal_im hm,im_one]
    ring
  exact congrPairT (normalize_integer _ _ _ (common_denominator_positive D N hD) hr)
    (normalize_integer _ _ _ (common_denominator_positive D N hD) hi)

theorem rational_list_monic (R N D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] entry (rationalCoefficients R N D) zero ≐ rationalOne :=
  (rational_coefficients_lookup R N D zero (zero_le N)).eqTrans (rational_monic R N D hD)

theorem rational_program_at (R N D : PTm n) :
    Γ ⊢[PRAAx] ap3 rationalCoefficientsF R N D ≐ rationalCoefficients R N D := by
  simpa [rationalCoefficientsF,ap3] using toPR_eq (Γ := Γ) (rationalCoefficients (var 0) (var 1) (var 2) : PTm 3) ![R,N,D]

theorem normalized_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶
      (coefficientClearing (var 0) (var 1) (var 2) (var 3) ⋏
        (wellFormed (realCoefficient (var 0) (var 1) (var 2) (var 3)) ⋏
          wellFormed (imagCoefficient (var 0) (var 1) (var 2) (var 3))))) :=
  closeUniv 4 (.impI (.andI (coefficient_clearing _ _ _ _ Prf.hyp0) (coefficient_guards _ _ _ _ Prf.hyp0)))

theorem normalized_list_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1) ⟶
      (entry (rationalCoefficients (var 0) (var 1) (var 2)) (var 3) ≐
        pairT (realCoefficient (var 0) (var 1) (var 2) (var 3)) (imagCoefficient (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (rational_coefficients_lookup _ _ _ _ Prf.hyp0))

theorem normalized_monic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶
      ((length (rationalCoefficients (var 0) (var 1) (var 2)) ≐ succ (var 1)) ⋏
        (entry (rationalCoefficients (var 0) (var 1) (var 2)) zero ≐ rationalOne))) :=
  closeUniv 3 (.impI (.andI (rational_coefficients_length _ _ _) (rational_list_monic _ _ _ Prf.hyp0)))

theorem normalized_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 rationalCoefficientsF (var 0) (var 1) (var 2) ≐ rationalCoefficients (var 0) (var 1) (var 2)) ⋏
      (le one (var 2) ⟶ le one (commonDenominator (var 2) (var 1)))) :=
  closeUniv 3 (.andI (rational_program_at _ _ _) (.impI (common_denominator_positive _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalRootProduct
