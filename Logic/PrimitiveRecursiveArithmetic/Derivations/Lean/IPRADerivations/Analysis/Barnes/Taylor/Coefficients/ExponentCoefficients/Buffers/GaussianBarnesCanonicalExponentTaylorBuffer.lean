import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.CorrectedMercator.GaussianBarnesCanonicalCorrectedMercatorPrefix
import IPRADerivations.Analysis.Barnes.CanonicalProducts.Values.GaussianBarnesCanonicalSingleExponential
import IPRADerivations.Analysis.Polynomials.Representation.GaussianRationalPolynomialBuffers

/-!
# Stored rational Taylor coefficients of the original Barnes exponent

The common prefactor clock and the finite tail cutoff are fixed before
the increment is supplied. The buffer has its constant term exactly
zero and uses the descending storage expected by the original Horner
and polynomial exponential programs.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorBuffer

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_le sg_lt)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalHigherRows (degree previous)
open GaussianBarnesCanonicalPrefactor (negativeHalf quadraticCoefficientF quadraticCoefficientData)
open GaussianBarnesCanonicalHeadCorrectionDerivative (slope)
open GaussianGammaCanonicalExponent (harmonicPoint)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianRationalHorner (ofGaussian qadd qmul qzero canonical qadd_canonical qmul_canonical canonical_congr)
open GaussianRationalSyntheticDivision (qzero_canonical canonicalCoefficients)
open RationalArithmetic (select select_zero select_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "S" => GaussianStirlingConstant.nameF
local notation "sd" => GaussianStirlingConstant.nameData
local notation "Q" => quadraticCoefficientF
local notation "qd" => quadraticCoefficientData
local notation "FV" => GaussianBarnesCanonicalDerivativeTail.value
local notation "SV" => GaussianBarnesCanonicalSecondDerivativeTail.value
local notation "HV" => GaussianBarnesCanonicalHigherTail.value
local notation "sg" => LeanProofs.IPRA.Signum.sg

def prefactorLinear (q z B : PTm n) : PTm n :=
  qadd (ap2 S q (sd zero))
    (qmul negativeHalf (qadd GaussianRationalSyntheticDivision.qone
      (qmul (GaussianBarnesCanonicalPrefactorExponentDerivative.twicePoint z B) (ap2 Q q qd))))

def prefactorQuadratic (q : PTm n) : PTm n := qmul negativeHalf (ap2 Q q qd)

def linearCoefficient (q z R B r : PTm n) : PTm n :=
  qadd (qadd (prefactorLinear q z B) (slope z B (initial R))) (FV z B (initial R) r)

def quadraticCoefficient (q z R B r : PTm n) : PTm n :=
  qadd (qadd (prefactorQuadratic q) (qmul (radiusPoint one two) (harmonicPoint (initial R))))
    (qmul (radiusPoint one two) (SV z B (initial R) r))

def highCoefficient (z R B r j : PTm n) : PTm n := HV z B (initial R) j r

def coefficient (q z R B r e : PTm n) : PTm n :=
  select (sg e) qzero (select (sg (monus e one)) (linearCoefficient q z R B r)
    (select (sg (monus e two)) (quadraticCoefficient q z R B r) (highCoefficient z R B r (monus e (num 3)))))

def bufferData (q z R B r M : PTm n) : PTm n := pairT (pairT q z) (pairT R (pairT B (pairT r M)))

def bufferBody : PTm 2 :=
  let x := var 1
  let p := fstT x
  let y := sndT x
  let u := sndT y
  let v := sndT u
  coefficient (fstT p) (sndT p) (fstT y) (fstT u) (fstT v) (monus (previous (sndT v)) (var 0))

def buffer (q z R B r M : PTm n) : PTm n := sequence bufferBody (succ (previous M)) (bufferData q z R B r M)

@[simp] theorem subst_prefactorLinear {l : ℕ} (σ : Fin n → PTm l) (q z B : PTm n) :
    Syn.subst σ (prefactorLinear q z B) = prefactorLinear (Syn.subst σ q) (Syn.subst σ z) (Syn.subst σ B) := by
  simp [prefactorLinear,quadraticCoefficientData,negativeHalf,one,two]

@[simp] theorem subst_prefactorQuadratic {l : ℕ} (σ : Fin n → PTm l) (q : PTm n) :
    Syn.subst σ (prefactorQuadratic q) = prefactorQuadratic (Syn.subst σ q) := by
  simp [prefactorQuadratic,quadraticCoefficientData,negativeHalf,one,two]

@[simp] theorem subst_linearCoefficient {l : ℕ} (σ : Fin n → PTm l) (q z R B r : PTm n) :
    Syn.subst σ (linearCoefficient q z R B r) = linearCoefficient (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) := by simp [linearCoefficient]

@[simp] theorem subst_quadraticCoefficient {l : ℕ} (σ : Fin n → PTm l) (q z R B r : PTm n) :
    Syn.subst σ (quadraticCoefficient q z R B r) = quadraticCoefficient (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) := by simp [quadraticCoefficient,one,two]

@[simp] theorem subst_highCoefficient {l : ℕ} (σ : Fin n → PTm l) (z R B r j : PTm n) :
    Syn.subst σ (highCoefficient z R B r j) = highCoefficient (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ j) := by simp [highCoefficient]

@[simp] theorem subst_coefficient {l : ℕ} (σ : Fin n → PTm l) (q z R B r e : PTm n) :
    Syn.subst σ (coefficient q z R B r e) = coefficient (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ e) := by simp [coefficient,one,two]

@[simp] theorem subst_bufferData {l : ℕ} (σ : Fin n → PTm l) (q z R B r M : PTm n) :
    Syn.subst σ (bufferData q z R B r M) = bufferData (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ M) := by simp [bufferData]

@[simp] theorem subst_buffer {l : ℕ} (σ : Fin n → PTm l) (q z R B r M : PTm n) :
    Syn.subst σ (buffer q z R B r M) = buffer (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ M) := by simp [buffer]

theorem coefficient_index_congr (q z R B r : PTm n) {e f : PTm n}
    (h : Γ ⊢[PRAAx] e ≐ f) : Γ ⊢[PRAAx]
    coefficient q z R B r e ≐ coefficient q z R B r f := by
  ipra_congr (coefficient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [.eqRefl q,.eqRefl z,.eqRefl R,.eqRefl B,.eqRefl r,h]

/-- Split a positive encoded degree into the linear, quadratic, and higher cases. -/
theorem positive_degree_cases (e : PTm n) {P : Fm PTm n} (he : Γ ⊢[PRAAx] le one e)
    (linear : (e ≐ one) :: Γ ⊢[PRAAx] P)
    (quadratic : (e ≐ two) :: Γ ⊢[PRAAx] P)
    (higher : (e ≐ degree (monus e (num 3))) :: Γ ⊢[PRAAx] P) : Γ ⊢[PRAAx] P := by
  refine .orE (lt_or_le e two) ?_ ?_
  · have h : lt e two :: Γ ⊢[PRAAx] e ≐ one :=
      le_antisymm ((succ_monus_succ e one).eqSymm.eqTrans Prf.hyp0) he.wk
    exact (Prf.impI linear).wk.impE h
  · refine .orE (lt_or_le e (num 3)) ?_ ?_
    · have h : lt e (num 3) :: le two e :: Γ ⊢[PRAAx] e ≐ two :=
        le_antisymm ((succ_monus_succ e two).eqSymm.eqTrans Prf.hyp0) Prf.hyp1
      exact (Prf.impI quadratic).wk.wk.impE h
    · have h : le (num 3) e :: le two e :: Γ ⊢[PRAAx] e ≐ degree (monus e (num 3)) :=
        (eq_add_of_le Prf.hyp0).eqTrans (by unfold degree previous; ipra_ring)
      exact (Prf.impI higher).wk.wk.impE h

/-- The degree split used by the stored exponent coefficient reader. -/
theorem degree_cases (e : PTm n) {P : Fm PTm n}
    (constant : (e ≐ zero) :: Γ ⊢[PRAAx] P)
    (linear : (e ≐ one) :: Γ ⊢[PRAAx] P)
    (quadratic : (e ≐ two) :: Γ ⊢[PRAAx] P)
    (higher : (e ≐ degree (monus e (num 3))) :: Γ ⊢[PRAAx] P) : Γ ⊢[PRAAx] P := by
  refine .orE (lt_or_le e one) ?_ ?_
  · have h : lt e one :: Γ ⊢[PRAAx] e ≐ zero :=
      le_antisymm ((succ_monus_succ e zero).eqSymm.eqTrans Prf.hyp0) (zero_le e)
    exact (Prf.impI constant).wk.impE h
  · exact positive_degree_cases e Prf.hyp0
      ((Prf.impI linear).wk.wk.impE Prf.hyp0)
      ((Prf.impI quadratic).wk.wk.impE Prf.hyp0)
      ((Prf.impI higher).wk.wk.impE Prf.hyp0)

theorem coefficient_zero (q z R B r : PTm n) : Γ ⊢[PRAAx] coefficient q z R B r zero ≐ qzero :=
  select_zero _ _ _ LeanProofs.IPRA.Signum.sg_zero

theorem coefficient_one (q z R B r : PTm n) : Γ ⊢[PRAAx] coefficient q z R B r one ≐ linearCoefficient q z R B r :=
  (select_one _ _ _ (LeanProofs.IPRA.Signum.sg_succ zero)).eqTrans (select_zero _ _ _ (sg_le (le_refl one)))

theorem coefficient_two (q z R B r : PTm n) : Γ ⊢[PRAAx] coefficient q z R B r two ≐ quadraticCoefficient q z R B r :=
  (select_one _ _ _ (LeanProofs.IPRA.Signum.sg_succ one)).eqTrans
    ((select_one _ _ _ (sg_lt (le_refl two))).eqTrans (select_zero _ _ _ (sg_le (le_refl two))))

theorem coefficient_high (q z R B r j : PTm n) :
    Γ ⊢[PRAAx] coefficient q z R B r (degree j) ≐ highCoefficient z R B r j := by
  let e := degree j
  have hl : Γ ⊢[PRAAx] le two (previous j) :=
    LeanProofs.IPRA.Common.succ_le_succ (zero_lt_succ j)
  have h₂ : Γ ⊢[PRAAx] lt two e := LeanProofs.IPRA.Common.succ_le_succ hl
  have h₁ : Γ ⊢[PRAAx] lt one e := le_trans (le_succ_self two) h₂
  have fm : Γ ⊢[PRAAx] monus e (num 3) ≐ j :=
    (succ_monus_succ (previous j) two).eqTrans ((succ_monus_succ (succ j) one).eqTrans
      ((succ_monus_succ j zero).eqTrans (monus_zero j)))
  have read : Γ ⊢[PRAAx] highCoefficient z R B r (monus e (num 3)) ≐ highCoefficient z R B r j := by
    simpa only [subst_highCoefficient,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using
      Prf.eqCongr1 (highCoefficient (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift r) (var 0)) fm
  exact (select_one _ _ _ (LeanProofs.IPRA.Signum.sg_succ (previous j))).eqTrans
    ((select_one _ _ _ (sg_lt h₁)).eqTrans ((select_one _ _ _ (sg_lt h₂)).eqTrans read))

private theorem coefficient_canonical (q z R B r e : PTm n) : Γ ⊢[PRAAx] canonical (coefficient q z R B r e) := by
  refine degree_cases e ?_ ?_ ?_ ?_
  · exact canonical_congr ((coefficient_index_congr q z R B r Prf.hyp0).eqTrans
      (coefficient_zero q z R B r)) qzero_canonical
  · exact canonical_congr ((coefficient_index_congr q z R B r Prf.hyp0).eqTrans
      (coefficient_one q z R B r)) (qadd_canonical _ _)
  · exact canonical_congr ((coefficient_index_congr q z R B r Prf.hyp0).eqTrans
      (coefficient_two q z R B r)) (qadd_canonical _ _)
  · exact canonical_congr ((coefficient_index_congr q z R B r Prf.hyp0).eqTrans
      (coefficient_high q z R B r (monus e (num 3)))) (GaussianRationalFiniteSum.sum_canonical _ _ _)

theorem buffer_length (q z R B r M : PTm n) : Γ ⊢[PRAAx] length (buffer q z R B r M) ≐ succ (previous M) :=
  sequence_length _ _ _

private theorem body_at (q z R B r M i : PTm n) :
    Γ ⊢[PRAAx] inst2 bufferBody i (bufferData q z R B r M) ≐ coefficient q z R B r (monus (previous M) i) := by
  let d := bufferData q z R B r M
  let p := fstT d
  let y := sndT d
  let u := sndT y
  let v := sndT u
  have left := fst_pair (Γ := Γ) (pairT q z) (pairT R (pairT B (pairT r M)))
  have hY := snd_pair (Γ := Γ) (pairT q z) (pairT R (pairT B (pairT r M)))
  have hU := (congrSnd hY).eqTrans (snd_pair R (pairT B (pairT r M)))
  have hV := (congrSnd hU).eqTrans (snd_pair B (pairT r M))
  let t : PTm 7 := coefficient (var 1) (var 2) (var 3) (var 4) (var 5) (monus (previous (var 6)) (var 0))
  have read := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) t
    (σ := ![i,fstT p,sndT p,fstT y,fstT u,fstT v,sndT v]) (σ' := ![i,q,z,R,B,r,M]) (fun j => by
      fin_cases j
      · exact .eqRefl i
      · exact (congrFst left).eqTrans (fst_pair _ _)
      · exact (congrSnd left).eqTrans (snd_pair _ _)
      · exact (congrFst hY).eqTrans (fst_pair _ _)
      · exact (congrFst hU).eqTrans (fst_pair _ _)
      · exact (congrFst hV).eqTrans (fst_pair _ _)
      · exact (congrSnd hV).eqTrans (snd_pair _ _))
  simpa only [t,inst2,bufferBody,subst_coefficient,GaussianBarnesCanonicalHigherRows.subst_previous,PTm.subst_monus,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val,d,p,y,u,v] using read

theorem descending_at (q z R B r M i : PTm n) (hi : Γ ⊢[PRAAx] le i (previous M)) :
    Γ ⊢[PRAAx] entry (buffer q z R B r M) i ≐ coefficient q z R B r (monus (previous M) i) :=
  (sequence_decode bufferBody (x := bufferData q z R B r M) ((succ_monus_succ _ _).eqTrans hi)).eqTrans
    (body_at q z R B r M i)

theorem entry_at (q z R B r M e : PTm n) (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] entry (buffer q z R B r M) (monus (previous M) e) ≐ coefficient q z R B r e := by
  have read := descending_at (Γ := Γ) q z R B r M (monus (previous M) e)
    (GaussianRationalMonicReconstruction.monus_le_left _ _)
  have e' := GaussianRationalMonicReconstruction.complement (previous M) e he
  exact read.eqTrans (by
    simpa only [subst_coefficient,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using
      Prf.eqCongr1 (coefficient (Syn.shift q) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift r) (var 0)) e')

theorem buffer_zero (q z R B r M : PTm n) :
    Γ ⊢[PRAAx] entry (buffer q z R B r M) (previous M) ≐ qzero :=
  (entry_congr (.eqRefl _) (monus_zero (previous M)).eqSymm).eqTrans
    ((entry_at q z R B r M zero (zero_le _)).eqTrans (coefficient_zero q z R B r))

theorem buffer_canonical (q z R B r M : PTm n) :
    Γ ⊢[PRAAx] canonicalCoefficients (buffer q z R B r M) := by
  refine .allI (.impI ?_)
  let s (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (length (buffer (s q) (s z) (s R) (s B) (s r) (s M))) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (previous (s M)) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (lt_congr (.eqRefl _) (buffer_length (s q) (s z) (s R) (s B) (s r) (s M)) Prf.hyp0)
  simpa only [Δ,s,Syn.shift,subst_buffer] using
    canonical_congr (descending_at (s q) (s z) (s R) (s B) (s r) (s M) (var 0) hi)
      (coefficient_canonical _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorBuffer
