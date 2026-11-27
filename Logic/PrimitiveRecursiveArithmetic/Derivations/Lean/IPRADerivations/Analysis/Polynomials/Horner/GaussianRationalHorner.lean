import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.RootProducts.GaussianRationalRootProduct
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentations
import IPRADerivations.Analysis.Polynomials.Taylor.GaussianPolynomialPerturbation
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalNormalization

/-!
# Canonical Gaussian-rational Horner evaluation

Actual arithmetic uses a pair of independently normalized scalar rational
codes. All list lengths, coefficient data, point numerators and denominators
are numerical inputs. Cross-value representations retain the independently
reduced denominators of both components. The generated common-D coefficient
list evaluates to the actual integer root-product kernel divided by D^N,
including degree zero and repeated roots. Canonical uniqueness also gives
literal output-code equality. The final input bridge uses the independently
computed denominator pool and the original canonical query code; coefficient
perturbation bounds and the final product-stability witness are separate.
-/

set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalHorner

open_ipra
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im scale zeroCode)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal equal_re equal_im re_add im_add re_mul im_mul re_scale im_scale re_zero im_zero)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize normalize_preserves_value)
open LeanProofs.IPRA.Analysis.RationalNormalForm (wellFormed normalize_well_formed)
open LeanProofs.IPRA.Analysis.RationalRepresentations
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry sequence sequence_length sequence_decode subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

/-- A value representation with an alternative raw fraction. -/
def represents (q a D : PTm n) : Fm PTm n :=
  RationalArithmetic.represents (fstT q) (re a) D ⋏
  RationalArithmetic.represents (sndT q) (im a) D

def canonical (q : PTm n) : Fm PTm n :=
  q ≐ pairT (fstT q) (sndT q) ⋏ (wellFormed (fstT q) ⋏ wellFormed (sndT q))

def ofGaussian (a D : PTm n) : PTm n := pairT (normalize (re a) D) (normalize (im a) D)
def qzero : PTm n := ofGaussian zeroCode one

def qadd (q r : PTm n) : PTm n :=
  pairT (RationalArithmetic.add (fstT q) (fstT r))
    (RationalArithmetic.add (sndT q) (sndT r))
def qmul (q r : PTm n) : PTm n :=
  pairT
    (RationalArithmetic.add (RationalArithmetic.multiply (fstT q) (fstT r))
      (RationalArithmetic.negative (RationalArithmetic.multiply (sndT q) (sndT r))))
    (RationalArithmetic.add (RationalArithmetic.multiply (fstT q) (sndT r))
      (RationalArithmetic.multiply (sndT q) (fstT r)))

ipra_subst represents
ipra_subst canonical
ipra_subst ofGaussian
ipra_subst qzero
ipra_subst qadd
ipra_subst qmul

theorem scalar_congr {c d : PTm n} {a b : ZT n} {A B : PTm n}
    (hcd : Γ ⊢[PRAAx] c ≐ d) (hab : Γ ⊢[PRAAx] ZT.eq a b) (hAB : Γ ⊢[PRAAx] A ≐ B)
    (h : Γ ⊢[PRAAx] RationalArithmetic.represents c a A) :
    Γ ⊢[PRAAx] RationalArithmetic.represents d b B := by
  apply ZT.derive
  have e := ZT.toZ_eq h
  have num : ZT.toZ Γ (numeratorOf c) = ZT.toZ Γ (numeratorOf d) := by
    simp only [numeratorOf,ZT.toZ]
    rw [natEq (congrFst (congrFst hcd)),natEq (congrSnd (congrFst hcd))]
  have den : 𝔞(denominatorOf c) = 𝔞(denominatorOf d) := natEq (congrSucc (congrSnd hcd))
  simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat] at e ⊢
  rw [ZT.toZ_eq hab,num,den,natEq hAB] at e
  exact e

theorem scalar_rescale (c : PTm n) (a : ZT n) (A t : PTm n)
    (h : Γ ⊢[PRAAx] RationalArithmetic.represents c a A) :
    Γ ⊢[PRAAx] RationalArithmetic.represents c (a*ZT.ofNat t) (A*t) := by
  ipra_lc [RationalArithmetic.represents] 𝔞(t)*ZT.toZ_eq h

theorem scalar_cancel (c : PTm n) (a : ZT n) (A t : PTm n)
    (ht : Γ ⊢[PRAAx] le one t)
    (h : Γ ⊢[PRAAx] RationalArithmetic.represents c (a*ZT.ofNat t) (A*t)) :
    Γ ⊢[PRAAx] RationalArithmetic.represents c a A := by
  apply RationalNormalForm.positive_integer_cancel t _ _ ht
  ipra_lc [RationalArithmetic.represents] ZT.toZ_eq h

theorem scalar_add_same (c d : PTm n) (a b : ZT n) (A : PTm n)
    (hA : Γ ⊢[PRAAx] le one A)
    (hc : Γ ⊢[PRAAx] RationalArithmetic.represents c a A)
    (hd : Γ ⊢[PRAAx] RationalArithmetic.represents d b A) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (RationalArithmetic.add c d) (a+b) A := by
  apply scalar_cancel _ _ _ A hA
  have h := represents_add c d a b A A hc hd
  refine scalar_congr (.eqRefl _) ?_ (.eqRefl _) h
  ipra_lc

theorem represents_congr {q r a b A B : PTm n}
    (hqr : Γ ⊢[PRAAx] q ≐ r) (hab : Γ ⊢[PRAAx] equal a b) (hAB : Γ ⊢[PRAAx] A ≐ B)
    (h : Γ ⊢[PRAAx] represents q a A) : Γ ⊢[PRAAx] represents r b B :=
  .andI (scalar_congr (congrFst hqr) (Prf.andE₁ hab) hAB (Prf.andE₁ h))
    (scalar_congr (congrSnd hqr) (Prf.andE₂ hab) hAB (Prf.andE₂ h))

/-- Transport the Gaussian numerator and denominator through construction. -/
theorem ofGaussian_congr {a b D E : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ b) (hD : Γ ⊢[PRAAx] D ≐ E) :
    Γ ⊢[PRAAx] ofGaussian a D ≐ ofGaussian b E := by
  ipra_congr (ofGaussian (var 0) (var 1) : PTm 2) with [ha, hD]

/-- Transport a real fraction written as a Gaussian rational. -/
theorem real_fraction_congr {a b D E : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ b) (hD : Γ ⊢[PRAAx] D ≐ E) :
    Γ ⊢[PRAAx] ofGaussian (scale a ComplexLogarithmRemainder.oneCode) D ≐
      ofGaussian (scale b ComplexLogarithmRemainder.oneCode) E := by
  ipra_congr
    (ofGaussian (scale (var 0) ComplexLogarithmRemainder.oneCode) (var 1) : PTm 2) with [ha, hD]

theorem ofGaussian_represents (a D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] represents (ofGaussian a D) a D :=
  .andI (scalar_congr (fst_pair _ _).eqSymm (.eqRefl _) (.eqRefl _) (normalize_preserves_value _ _ hD))
    (scalar_congr (snd_pair _ _).eqSymm (.eqRefl _) (.eqRefl _) (normalize_preserves_value _ _ hD))

theorem canonical_pair (c d : PTm n) (hc : Γ ⊢[PRAAx] wellFormed c) (hd : Γ ⊢[PRAAx] wellFormed d) :
    Γ ⊢[PRAAx] canonical (pairT c d) := by
  refine .andI (congrPairT (fst_pair _ _) (snd_pair _ _)).eqSymm ?_
  exact .andI (RationalArithmetic.guard_congr (fst_pair _ _) hc)
    (RationalArithmetic.guard_congr (snd_pair _ _) hd)

theorem ofGaussian_canonical (a D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] canonical (ofGaussian a D) :=
  canonical_pair _ _ (normalize_well_formed _ _ hD) (normalize_well_formed _ _ hD)

theorem qadd_canonical (q r : PTm n) : Γ ⊢[PRAAx] canonical (qadd q r) :=
  canonical_pair _ _ (RationalArithmetic.add_guard _ _) (RationalArithmetic.add_guard _ _)
theorem qmul_canonical (q r : PTm n) : Γ ⊢[PRAAx] canonical (qmul q r) :=
  canonical_pair _ _ (RationalArithmetic.add_guard _ _) (RationalArithmetic.add_guard _ _)

theorem represents_rescale (q a A t : PTm n) (h : Γ ⊢[PRAAx] represents q a A) :
    Γ ⊢[PRAAx] represents q (scale t a) (A*t) := by
  refine .andI (scalar_congr (.eqRefl _) ?_ (.eqRefl _) (scalar_rescale _ _ _ _ (Prf.andE₁ h)))
    (scalar_congr (.eqRefl _) ?_ (.eqRefl _) (scalar_rescale _ _ _ _ (Prf.andE₂ h)))
  all_goals apply ZT.derive; simp only [ZT.toZ_mul,ZT.toZ_ofNat,re_scale,im_scale]; ring

theorem represents_cancel (q a A t : PTm n) (ht : Γ ⊢[PRAAx] le one t)
    (h : Γ ⊢[PRAAx] represents q (scale t a) (A*t)) : Γ ⊢[PRAAx] represents q a A := by
  refine .andI (scalar_cancel _ _ _ t ht (scalar_congr (.eqRefl _) ?_ (.eqRefl _) (Prf.andE₁ h)))
    (scalar_cancel _ _ _ t ht (scalar_congr (.eqRefl _) ?_ (.eqRefl _) (Prf.andE₂ h)))
  all_goals apply ZT.derive; simp only [ZT.toZ_mul,ZT.toZ_ofNat,re_scale,im_scale]; ring

alias positive_product := Common.one_le_mul

theorem qadd_represents (q r a b A : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hq : Γ ⊢[PRAAx] represents q a A) (hr : Γ ⊢[PRAAx] represents r b A) :
    Γ ⊢[PRAAx] represents (qadd q r) (ComplexLogarithmRemainder.add a b) A := by
  refine .andI (scalar_congr (fst_pair _ _).eqSymm ?_ (.eqRefl _)
      (scalar_add_same _ _ _ _ _ hA (Prf.andE₁ hq) (Prf.andE₁ hr)))
    (scalar_congr (snd_pair _ _).eqSymm ?_ (.eqRefl _)
      (scalar_add_same _ _ _ _ _ hA (Prf.andE₂ hq) (Prf.andE₂ hr)))
  all_goals apply ZT.derive; simp only [ZT.toZ_add,re_add,im_add]

theorem qmul_represents (q r a b A B : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] represents q a A) (hr : Γ ⊢[PRAAx] represents r b B) :
    Γ ⊢[PRAAx] represents (qmul q r) (ComplexLogarithmRemainder.mul a b) (A*B) := by
  have rr := represents_multiply _ _ _ _ _ _ (Prf.andE₁ hq) (Prf.andE₁ hr)
  have ii := represents_negative _ _ _ (represents_multiply _ _ _ _ _ _ (Prf.andE₂ hq) (Prf.andE₂ hr))
  have ri := represents_multiply _ _ _ _ _ _ (Prf.andE₁ hq) (Prf.andE₂ hr)
  have ir := represents_multiply _ _ _ _ _ _ (Prf.andE₂ hq) (Prf.andE₁ hr)
  refine .andI (scalar_congr (fst_pair _ _).eqSymm ?_ (.eqRefl _)
      (scalar_add_same _ _ _ _ _ (positive_product A B hA hB) rr ii))
    (scalar_congr (snd_pair _ _).eqSymm ?_ (.eqRefl _)
      (scalar_add_same _ _ _ _ _ (positive_product A B hA hB) ri ir))
  · ipra_lc [re_mul]
  · apply ZT.derive; simp only [ZT.toZ_add,ZT.toZ_mul,im_mul]

def hornerStep : PTm 4 := qadd (qmul (var 1) (var 3)) (entry (var 2) (var 0))
def hornerF : PR 3 := recDef qzero hornerStep
def horner (C z k : PTm n) : PTm n := ap3 hornerF k C z
def evaluate (C z : PTm n) : PTm n := horner C z (length C)

ipra_subst horner
ipra_subst evaluate

theorem horner_zero (C z : PTm n) : Γ ⊢[PRAAx] horner C z zero ≐ qzero := by
  have h := rec_zero_vecCons (Γ := Γ) (qzero : PTm 2) hornerStep ![C,z]
  simpa only [horner,hornerF,ap3,subst_qzero] using h

theorem horner_succ (C z k : PTm n) : Γ ⊢[PRAAx]
    horner C z (succ k) ≐ qadd (qmul (horner C z k) z) (entry C k) := by
  have h := rec_succ_vecCons (Γ := Γ) (qzero : PTm 2) hornerStep k ![C,z]
  simpa [horner,hornerF,ap3,hornerStep] using h

/-- Literal entries determine an actual Horner prefix up to the certified bound. -/
theorem horner_congr_entries (C D y N k : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift N) ⟶ entry (Syn.shift C) (var 0) ≐ entry (Syn.shift D) (var 0)))
    (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx] horner C y k ≐ horner D y k := by
  let invariant := horner (Syn.shift C) (Syn.shift y) (var 0) ≐ horner (Syn.shift D) (Syn.shift y) (var 0)
  suffices result : Γ ⊢[PRAAx] invariant.subst (Syn.inst k) by simpa [invariant] using result
  refine qfIndAtMost hk trivial ?_ ?_
  · simpa [invariant] using (horner_zero (Γ := Γ) C y).eqTrans (horner_zero D y).eqSymm
  · simp [invariant]
    refine .impI ?_
    refine (horner_succ _ _ _).eqTrans (Prf.eqTrans ?_ (horner_succ _ _ _).eqSymm)
    ipra_congr (qadd (qmul (var 0) (var 1)) (var 2) : PTm 3) with
      [Prf.hyp1, .eqRefl _, .impE h.allOpen.wk.wk Prf.hyp0]

theorem canonical_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r)
    (hr : Γ ⊢[PRAAx] canonical r) : Γ ⊢[PRAAx] canonical q := by
  have e := Prf.eqSubst (canonical (var 0) : Fm PTm 1) ![r] ![q]
    (fun i => by fin_cases i; exact h.eqSymm) (by simpa using hr)
  simpa using e

theorem scalar_same_value (c d : PTm n) (a : ZT n) (A : PTm n)
    (hA : Γ ⊢[PRAAx] le one A)
    (hc : Γ ⊢[PRAAx] RationalArithmetic.represents c a A)
    (hd : Γ ⊢[PRAAx] RationalArithmetic.represents d a A) :
    Γ ⊢[PRAAx] ZT.eq (numeratorOf c*ZT.ofNat (denominatorOf d))
      (numeratorOf d*ZT.ofNat (denominatorOf c)) := by
  apply RationalNormalForm.positive_integer_cancel A _ _ hA
  ipra_lc [RationalArithmetic.represents] -𝔞(denominatorOf d)*ZT.toZ_eq hc+𝔞(denominatorOf c)*ZT.toZ_eq hd

theorem canonical_unique (q r a A : PTm n)
    (hq : Γ ⊢[PRAAx] canonical q) (hr : Γ ⊢[PRAAx] canonical r)
    (hA : Γ ⊢[PRAAx] le one A)
    (hqv : Γ ⊢[PRAAx] represents q a A) (hrv : Γ ⊢[PRAAx] represents r a A) :
    Γ ⊢[PRAAx] q ≐ r :=
  (Prf.andE₁ hq).eqTrans ((congrPairT
    (RationalNormalForm.well_formed_unique _ _ (Prf.andE₁ (Prf.andE₂ hq)) (Prf.andE₁ (Prf.andE₂ hr))
      (scalar_same_value _ _ _ _ hA (Prf.andE₁ hqv) (Prf.andE₁ hrv)))
    (RationalNormalForm.well_formed_unique _ _ (Prf.andE₂ (Prf.andE₂ hq)) (Prf.andE₂ (Prf.andE₂ hr))
      (scalar_same_value _ _ _ _ hA (Prf.andE₂ hqv) (Prf.andE₂ hrv)))).eqTrans (Prf.andE₁ hr).eqSymm)

theorem horner_canonical (C w k : PTm n) : Γ ⊢[PRAAx] canonical (horner C w k) := by
  refine .orE (zero_or_succ k) ?_ ?_
  · exact canonical_congr
      ((congrAp3 hornerF Prf.hyp0 (.eqRefl _) (.eqRefl _)).eqTrans (horner_zero C w))
      (ofGaussian_canonical zeroCode one (le_refl _))
  · exact canonical_congr
      ((congrAp3 hornerF Prf.hyp0 (.eqRefl _) (.eqRefl _)).eqTrans (horner_succ C w _))
      (qadd_canonical _ _)

/-! Generic prefix correctness for a real coefficient list and its independently
normalized rational codes. The representation premise is pointwise coefficient
input data, rather than an assumed evaluation identity. -/

def coefficientRepresentations (Q C E : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift C)) ⟶
    represents (entry (Syn.shift Q) (var 0)) (entry (Syn.shift C) (var 0)) (Syn.shift E))

ipra_subst coefficientRepresentations [Syn.subst_shift, Syn.shift_subst]

theorem coefficient_representation_at (Q C E i : PTm n)
    (h : Γ ⊢[PRAAx] coefficientRepresentations Q C E) (hi : Γ ⊢[PRAAx] lt i (length C)) :
    Γ ⊢[PRAAx] represents (entry Q i) (entry C i) E := by
  have rule : Γ ⊢[PRAAx] lt i (length C) ⟶ represents (entry Q i) (entry C i) E := by
    simpa only [coefficientRepresentations,Fm.subst_imp,subst_lt,subst_length,subst_represents,
      subst_entry,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE i h
  exact .impE rule hi

theorem zero_represents (A : PTm n) : Γ ⊢[PRAAx] represents qzero zeroCode A := by
  have h := ofGaussian_represents (Γ := Γ) zeroCode one (le_refl _)
  refine .andI (ZT.derive ?_) (ZT.derive ?_)
  · have e := ZT.toZ_eq (Prf.andE₁ h)
    simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat,re_zero] at e ⊢
    simp only [qzero] at e ⊢
    ipra_simps
    linear_combination 𝔞(A)*e
  · have e := ZT.toZ_eq (Prf.andE₂ h)
    simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat,im_zero] at e ⊢
    simp only [qzero] at e ⊢
    ipra_simps
    linear_combination 𝔞(A)*e

def prefixLaw (Q C w z E D k : PTm n) : Fm PTm n := le k (length C) ⟶
  represents (horner Q w k) (scale D (GaussianPolynomialPerturbation.H C z D k)) (E*pw D k)

ipra_subst prefixLaw

theorem prefix_zero (Q C w z E D : PTm n) : Γ ⊢[PRAAx]
    represents (horner Q w zero) (scale D (GaussianPolynomialPerturbation.H C z D zero)) (E*pw D zero) := by
  have hz := GaussianRootAlgebra.values_of_code (GaussianPolynomialPerturbation.H_zero (Γ := Γ) C z D)
  apply represents_congr (horner_zero Q w).eqSymm (hAB := .eqRefl _) (h := zero_represents _)
  apply GaussianRootAlgebra.equal_of_values
  · simp only [re_scale,re_zero]; rw [hz.1,re_zero]; ring
  · simp only [im_scale,im_zero]; rw [hz.2,im_zero]; ring

theorem prefix_step (Q C w z E D k : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E)
    (hCoefficients : Γ ⊢[PRAAx] coefficientRepresentations Q C E)
    (hw : Γ ⊢[PRAAx] represents w z D) (hk : Γ ⊢[PRAAx] lt k (length C))
    (ih : Γ ⊢[PRAAx] represents (horner Q w k)
      (scale D (GaussianPolynomialPerturbation.H C z D k)) (E*pw D k)) :
    Γ ⊢[PRAAx] represents (horner Q w (succ k))
      (scale D (GaussianPolynomialPerturbation.H C z D (succ k))) (E*pw D (succ k)) := by
  have hp := GaussianPolynomialPerturbation.power_positive D k hD
  have hm := qmul_represents _ _ _ _ _ _ (positive_product E _ hE hp) hD ih hw
  have de : Γ ⊢[PRAAx] (E*pw D k)*D ≐ E*pw D (succ k) := by
    exact (mul_assoc _ _ _).eqTrans (congrMul (.eqRefl _) (pw_succ D k).eqSymm)
  have hm' := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) de hm
  have hc := represents_rescale _ _ _ (pw D (succ k)) (coefficient_representation_at Q C E k hCoefficients hk)
  have hs := qadd_represents _ _ _ _ _
    (positive_product _ _ hE (GaussianPolynomialPerturbation.power_positive D (succ k) hD)) hm' hc
  have he := GaussianPolynomialPerturbation.H_succ C z D k hk
  have heR := equal_re he
  have heI := equal_im he
  have p : 𝔞(pw D (succ k)) = 𝔞(pw D k)*𝔞(D) := by
    simpa only [IPRA.Q.mk_mul,map_mul] using natEq (pw_succ (Γ := Γ) D k)
  apply represents_congr (horner_succ Q w k).eqSymm (hAB := .eqRefl _) (h := hs)
  apply GaussianRootAlgebra.equal_of_values
  · simp only [re_add,re_mul,im_mul,re_scale,im_scale] at heR ⊢
    rw [p,heR]
    ring
  · simp only [im_add,re_mul,im_mul,re_scale,im_scale] at heI ⊢
    rw [p,heI]
    ring

/-- QF induction proves the actual prefix evaluator. D and E are positive
raw denominators; the scalar components retain their own reduced denominators. -/
theorem horner_represents (Q C w z E D k : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E)
    (hc : Γ ⊢[PRAAx] coefficientRepresentations Q C E)
    (hw : Γ ⊢[PRAAx] represents w z D) (hk : Γ ⊢[PRAAx] le k (length C)) :
    Γ ⊢[PRAAx] represents (horner Q w k)
      (scale D (GaussianPolynomialPerturbation.H C z D k)) (E*pw D k) := by
  have dShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hD.shift
  have eShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hE.shift
  have cShift : Γ.map Fm.shift ⊢[PRAAx] coefficientRepresentations (Syn.shift Q) (Syn.shift C) (Syn.shift E) := by
    simpa only [Fm.shift,subst_coefficientRepresentations,Syn.shift] using hc.shift
  have wShift : Γ.map Fm.shift ⊢[PRAAx] represents (Syn.shift w) (Syn.shift z) (Syn.shift D) := by
    simpa only [Fm.shift,subst_represents,Syn.shift] using hw.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift Q) (Syn.shift C) (Syn.shift w)
      (Syn.shift z) (Syn.shift E) (Syn.shift D) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,⟨trivial,trivial⟩⟩) [subst_prefixLaw, prefixLaw, subst_le, subst_length, subst_represents,
        subst_horner, ComplexLogarithmRemainder.subst_scale, GaussianPolynomialPerturbation.subst_H, subst_ap2]
    · exact .impI (prefix_zero Q C w z E D)
    · refine .impI ?_
      let I := prefixLaw (Syn.shift Q) (Syn.shift C) (Syn.shift w) (Syn.shift z) (Syn.shift E) (Syn.shift D) (var 0)
      let Δ := le (succ (var 0)) (length (Syn.shift C)) :: I :: Γ.map Fm.shift
      have d : Δ ⊢[PRAAx] le one (Syn.shift D) := dShift.wk.wk
      have e : Δ ⊢[PRAAx] le one (Syn.shift E) := eShift.wk.wk
      have coeff : Δ ⊢[PRAAx] coefficientRepresentations (Syn.shift Q) (Syn.shift C) (Syn.shift E) := cShift.wk.wk
      have point : Δ ⊢[PRAAx] represents (Syn.shift w) (Syn.shift z) (Syn.shift D) := wShift.wk.wk
      exact prefix_step _ _ _ _ _ _ _ d e coeff point Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw Q C w z E D k := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all
  exact .impE rule hk

/-! The generated common-D coefficient list, with its actual numerator list. -/

def scaledBody : PTm 2 := GaussianRationalRootProduct.scaledCoefficient
  (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def scaledCoefficients (R N D : PTm n) : PTm n := sequence scaledBody (succ N)
  (GaussianRationalRootProduct.coefficientData R N D)

ipra_subst scaledCoefficients

theorem scaled_body_at (R N D i : PTm n) : Γ ⊢[PRAAx]
    inst2 scaledBody i (GaussianRationalRootProduct.coefficientData R N D) ≐
      GaussianRationalRootProduct.scaledCoefficient R N D i := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (GaussianRationalRootProduct.scaledCoefficient (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (GaussianRationalRootProduct.coefficientData R N D),
      fstT (sndT (GaussianRationalRootProduct.coefficientData R N D)),
      sndT (sndT (GaussianRationalRootProduct.coefficientData R N D)),i])
    (σ' := ![R,N,D,i]) (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (snd_pair _ _).fstE
      · exact (snd_pair _ _).sndE
      · exact .eqRefl _)
  simpa only [scaledBody,inst2,GaussianRationalRootProduct.subst_scaledCoefficient,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using e

theorem scaled_coefficients_length (R N D : PTm n) : Γ ⊢[PRAAx]
    length (scaledCoefficients R N D) ≐ succ N := sequence_length _ _ _
theorem scaled_coefficients_lookup (R N D i : PTm n) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] entry (scaledCoefficients R N D) i ≐
      GaussianRationalRootProduct.scaledCoefficient R N D i :=
  (sequence_decode scaledBody ((succ_monus_succ _ _).eqTrans hi)).eqTrans (scaled_body_at R N D i)

theorem normalized_coefficients_represent (R N D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] coefficientRepresentations (GaussianRationalRootProduct.rationalCoefficients R N D)
      (scaledCoefficients R N D) (pw D N) := by
  simp only [coefficientRepresentations,Syn.shift,GaussianRationalRootProduct.subst_rationalCoefficients,
    subst_scaledCoefficients,subst_ap2]
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (scaledCoefficients (Syn.shift R) (Syn.shift N) (Syn.shift D))) :: Γ.map Fm.shift
  have d : Δ ⊢[PRAAx] le one (Syn.shift D) := by
    simpa only [Δ,Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hD.shift.wk
  have index : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) :=
    (succ_monus_succ _ _).eqSymm.eqTrans
      (lt_congr (.eqRefl _) (scaled_coefficients_length _ _ _) Prf.hyp0)
  have h := ofGaussian_represents
    (GaussianRationalRootProduct.scaledCoefficient (Syn.shift R) (Syn.shift N) (Syn.shift D) (var 0))
    (pw (Syn.shift D) (Syn.shift N)) (GaussianRationalRootProduct.common_denominator_positive _ _ d)
  have raw : Δ ⊢[PRAAx]
      ofGaussian (GaussianRationalRootProduct.scaledCoefficient (Syn.shift R) (Syn.shift N) (Syn.shift D) (var 0))
        (pw (Syn.shift D) (Syn.shift N)) ≐
      GaussianRationalRootProduct.rationalCoefficient (Syn.shift R) (Syn.shift N) (Syn.shift D) (var 0) := .eqRefl _
  exact represents_congr
    (raw.eqTrans (GaussianRationalRootProduct.rational_coefficients_lookup (Syn.shift R) (Syn.shift N) (Syn.shift D) (var 0) index).eqSymm)
    (GaussianRootAlgebra.equal_of_code (scaled_coefficients_lookup (Syn.shift R) (Syn.shift N) (Syn.shift D) (var 0) index).eqSymm)
    (.eqRefl _) h

def scaledPrefixLaw (R N z D k : PTm n) : Fm PTm n := le k (succ N) ⟶
  equal (GaussianPolynomialPerturbation.H (scaledCoefficients R N D) z D k)
    (scale (pw D N) (GaussianRootProduct.horner (GaussianRootProduct.coefficients R N) z k))

ipra_subst scaledPrefixLaw

theorem complementary_power (D N k : PTm n) (hk : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] pw D k*pw D (monus N k) ≐ pw D N :=
  (pw_add D k (monus N k)).eqSymm.eqTrans
    (congrAp2 powF (eq_add_of_le hk).eqSymm (.eqRefl _))

theorem scaled_homogeneous_zero (R N z D : PTm n) : Γ ⊢[PRAAx]
    equal (GaussianPolynomialPerturbation.H (scaledCoefficients R N D) z D zero)
      (scale (pw D N) (GaussianRootProduct.horner (GaussianRootProduct.coefficients R N) z zero)) := by
  have h := GaussianRootAlgebra.values_of_code
    (GaussianPolynomialPerturbation.H_zero (Γ := Γ) (scaledCoefficients R N D) z D)
  have g := GaussianRootAlgebra.values_of_code
    (GaussianRootProduct.horner_zero (Γ := Γ) (GaussianRootProduct.coefficients R N) z)
  apply GaussianRootAlgebra.equal_of_values
  · rw [h.1,re_scale,g.1,re_zero]; ring
  · rw [h.2,im_scale,g.2,im_zero]; ring

theorem scaled_homogeneous_step (R N z D k : PTm n) (hk : Γ ⊢[PRAAx] le k N)
    (ih : Γ ⊢[PRAAx] equal (GaussianPolynomialPerturbation.H (scaledCoefficients R N D) z D k)
      (scale (pw D N) (GaussianRootProduct.horner (GaussianRootProduct.coefficients R N) z k))) :
    Γ ⊢[PRAAx] equal (GaussianPolynomialPerturbation.H (scaledCoefficients R N D) z D (succ k))
      (scale (pw D N) (GaussianRootProduct.horner (GaussianRootProduct.coefficients R N) z (succ k))) := by
  have h := GaussianPolynomialPerturbation.H_succ (scaledCoefficients R N D) z D k
    (lt_congr (.eqRefl _) (scaled_coefficients_length R N D).eqSymm ((succ_monus_succ _ _).eqTrans hk))
  have g := GaussianRootAlgebra.values_of_code
    (GaussianRootProduct.horner_succ (Γ := Γ) (GaussianRootProduct.coefficients R N) z k)
  have c := GaussianRootAlgebra.values_of_code (scaled_coefficients_lookup R N D k hk)
  have p := GaussianRootProduct.padded_inside (GaussianRootProduct.coefficients R N) k
    (lt_congr (.eqRefl _) (GaussianRootProduct.coefficients_length R N).eqSymm ((succ_monus_succ _ _).eqTrans hk))
  have powe : 𝔞(pw D k)*𝔞(GaussianRationalRootProduct.numeratorScale D N k) = 𝔞(pw D N) := by
    have e : Γ ⊢[PRAAx] pw D k*GaussianRationalRootProduct.numeratorScale D N k ≐ pw D N := complementary_power D N k hk
    exact (by have v := natEq e; ipra_simps; exact v)
  have hr := equal_re h
  have hi := equal_im h
  have ir := equal_re ih
  have ii := equal_im ih
  apply GaussianRootAlgebra.equal_of_values
  · rw [hr,re_add,re_mul,re_scale,c.1,GaussianRationalRootProduct.scaledCoefficient,re_scale,ir,ii,
      re_scale,im_scale,re_scale,g.1,re_add,re_mul,equal_re p]
    linear_combination ZT.toZ Γ (re (entry (GaussianRootProduct.coefficients R N) k))*powe
  · rw [hi,im_add,im_mul,im_scale,c.2,GaussianRationalRootProduct.scaledCoefficient,im_scale,ir,ii,
      re_scale,im_scale,im_scale,g.2,im_add,im_mul,equal_im p]
    linear_combination ZT.toZ Γ (im (entry (GaussianRootProduct.coefficients R N) k))*powe

theorem scaled_homogeneous (R N z D k : PTm n) (hk : Γ ⊢[PRAAx] le k (succ N)) :
    Γ ⊢[PRAAx] equal (GaussianPolynomialPerturbation.H (scaledCoefficients R N D) z D k)
      (scale (pw D N) (GaussianRootProduct.horner (GaussianRootProduct.coefficients R N) z k)) := by
  have all : Γ ⊢[PRAAx] .all (scaledPrefixLaw (Syn.shift R) (Syn.shift N) (Syn.shift z) (Syn.shift D) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,⟨trivial,trivial⟩⟩) [subst_scaledPrefixLaw, scaledPrefixLaw, subst_le,
        GaussianRootAlgebra.subst_equal, GaussianPolynomialPerturbation.subst_H, subst_scaledCoefficients,
        ComplexLogarithmRemainder.subst_scale, GaussianRootProduct.subst_horner,
        GaussianRootProduct.subst_coefficients, subst_ap2]
    · exact .impI (scaled_homogeneous_zero R N z D)
    · refine .impI ?_
      let I := scaledPrefixLaw (Syn.shift R) (Syn.shift N) (Syn.shift z) (Syn.shift D) (var 0)
      let Δ := le (succ (var 0)) (succ (Syn.shift N)) :: I :: Γ.map Fm.shift
      have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
      exact scaled_homogeneous_step _ _ _ _ _ bound (.impE Prf.hyp1 (le_trans bound (le_succ_self _)))
  have rule : Γ ⊢[PRAAx] scaledPrefixLaw R N z D k := by
    simpa only [subst_scaledPrefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all
  exact .impE rule hk

/-- The actual normalized coefficient list evaluated by actual canonical
rational Horner has the integer root-product value divided by D^N. -/
theorem root_evaluation_represents (R N z D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] represents
      (evaluate (GaussianRationalRootProduct.rationalCoefficients R N D) (ofGaussian z D))
      (GaussianRootProduct.evaluate (GaussianRootProduct.coefficients R N) z) (pw D N) := by
  have hE := GaussianRationalRootProduct.common_denominator_positive D N hD
  have h := horner_represents
    (GaussianRationalRootProduct.rationalCoefficients R N D) (scaledCoefficients R N D)
    (ofGaussian z D) z (pw D N) D (succ N) hD hE
    (normalized_coefficients_represent R N D hD) (ofGaussian_represents z D hD)
    (le_congr (.eqRefl _) (scaled_coefficients_length R N D).eqSymm (le_refl _))
  have hs := scaled_homogeneous (Γ := Γ) R N z D (succ N) (le_refl _)
  have hp : Γ ⊢[PRAAx]
      GaussianRootProduct.horner (GaussianRootProduct.coefficients R N) z (succ N) ≐
        GaussianRootProduct.evaluate (GaussianRootProduct.coefficients R N) z :=
    congrAp3 GaussianRootProduct.hornerF (GaussianRootProduct.coefficients_length R N).eqSymm (.eqRefl _) (.eqRefl _)
  have he : Γ ⊢[PRAAx]
      horner (GaussianRationalRootProduct.rationalCoefficients R N D) (ofGaussian z D) (succ N) ≐
        evaluate (GaussianRationalRootProduct.rationalCoefficients R N D) (ofGaussian z D) :=
    congrAp3 hornerF (GaussianRationalRootProduct.rational_coefficients_length R N D).eqSymm (.eqRefl _) (.eqRefl _)
  apply represents_cancel _ _ _ (pw D N*D) (positive_product _ _ hE hD)
  apply represents_congr he (h := h)
  · have v := GaussianRootAlgebra.values_of_code hp
    apply GaussianRootAlgebra.equal_of_values
    · simp only [re_scale]
      rw [equal_re hs,re_scale,v.1]
      ipra_simps
      ring
    · simp only [im_scale]
      rw [equal_im hs,im_scale,v.2]
      ipra_simps
      ring
  · exact congrMul (.eqRefl _) (pw_succ D N)

/-- Canonical components turn the scaling value identity into literal output
code equality. Consequently arbitrary formulas can use the exact qEval code. -/
theorem root_evaluation_exact (R N z D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx]
      evaluate (GaussianRationalRootProduct.rationalCoefficients R N D) (ofGaussian z D) ≐
        ofGaussian (GaussianRootProduct.evaluate (GaussianRootProduct.coefficients R N) z) (pw D N) :=
  canonical_unique _ _ _ _ (horner_canonical _ _ _)
    (ofGaussian_canonical _ _ (GaussianRationalRootProduct.common_denominator_positive D N hD))
    (GaussianRationalRootProduct.common_denominator_positive D N hD)
    (root_evaluation_represents R N z D hD)
    (ofGaussian_represents _ _ (GaussianRationalRootProduct.common_denominator_positive D N hD))

theorem rational_product_represents (R N z D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] represents
      (evaluate (GaussianRationalRootProduct.rationalCoefficients R N D) (ofGaussian z D))
      (GaussianRootProduct.factors R z N) (pw D N) :=
  represents_congr (.eqRefl _) (GaussianRootProduct.evaluate_product R z N) (.eqRefl _)
    (root_evaluation_represents R N z D hD)

/-- Every original root is a zero of the actual normalized rational polynomial,
including roots repeated in the input list. -/
theorem listed_rational_root_zero (R N D j : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx]
      evaluate (GaussianRationalRootProduct.rationalCoefficients R N D) (ofGaussian (entry R j) D) ≐ qzero := by
  have h := represents_congr (.eqRefl _) (GaussianRootProduct.listed_root_zero R N j hj) (.eqRefl _)
    (root_evaluation_represents R N (entry R j) D hD)
  exact canonical_unique _ _ _ _ (horner_canonical _ _ _)
    (ofGaussian_canonical zeroCode one (le_refl _))
    (GaussianRationalRootProduct.common_denominator_positive D N hD) h (zero_represents _)

/-- Exact cross-value clearing identifies a canonical original input with
its freshly normalized common-D code. The raw input tuple guard is explicit. -/
theorem cleared_input_exact (q g D : PTm n)
    (hq : Γ ⊢[PRAAx] canonical q) (hD : Γ ⊢[PRAAx] le one D)
    (hclear : Γ ⊢[PRAAx] GaussianRationalNormalization.clearing D g q) :
    Γ ⊢[PRAAx] q ≐ ofGaussian g D :=
  canonical_unique _ _ _ _ hq (ofGaussian_canonical g D hD) hD hclear (ofGaussian_represents g D hD)

/-- Actual source-list coefficients, evaluated at the original canonical query.
The common denominator is computed from both input lists and the query. -/
theorem source_query_evaluation_exact (S T z : PTm n) (hz : Γ ⊢[PRAAx] canonical z) :
    Γ ⊢[PRAAx]
      evaluate (GaussianRationalRootProduct.rationalCoefficients
        (GaussianRationalNormalization.sourceNumerators S T z) (length S)
        (GaussianRationalNormalization.commonD S T z)) z ≐
      ofGaussian
        (GaussianRootProduct.evaluate
          (GaussianRootProduct.coefficients (GaussianRationalNormalization.sourceNumerators S T z) (length S))
          (GaussianRationalNormalization.queryNumerator S T z))
        (pw (GaussianRationalNormalization.commonD S T z) (length S)) := by
  have hd := GaussianRationalNormalization.commonD_positive (Γ := Γ) S T z
  have point := cleared_input_exact z (GaussianRationalNormalization.queryNumerator S T z)
    (GaussianRationalNormalization.commonD S T z) hz hd (GaussianRationalNormalization.query_clearing S T z)
  exact (congrAp3 hornerF (.eqRefl _) (.eqRefl _) point).eqTrans
    (root_evaluation_exact _ _ _ _ hd)

def evaluateF : PR 2 := PTm.toPR (evaluate (var 0) (var 1))
def rootEvaluation (R N z D : PTm n) : PTm n :=
  evaluate (GaussianRationalRootProduct.rationalCoefficients R N D) (ofGaussian z D)
def rootEvaluationF : PR 4 := PTm.toPR (rootEvaluation (var 0) (var 1) (var 2) (var 3))

ipra_subst rootEvaluation

theorem evaluate_program_at (C z : PTm n) : Γ ⊢[PRAAx] ap2 evaluateF C z ≐ evaluate C z := by
  simpa [evaluateF,ap2] using toPR_eq (Γ := Γ) (evaluate (var 0) (var 1) : PTm 2) ![C,z]
theorem root_program_at (R N z D : PTm n) : Γ ⊢[PRAAx] PTm.app rootEvaluationF ![R,N,z,D] ≐ rootEvaluation R N z D := by
  simpa [rootEvaluationF] using toPR_eq (Γ := Γ) (rootEvaluation (var 0) (var 1) (var 2) (var 3) : PTm 4) ![R,N,z,D]

theorem rational_horner_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 5) ⟶ le one (var 4) ⟶
      coefficientRepresentations (var 0) (var 1) (var 4) ⟶ represents (var 2) (var 3) (var 5) ⟶
      le (var 6) (length (var 1)) ⟶
        represents (horner (var 0) (var 2) (var 6))
          (scale (var 5) (GaussianPolynomialPerturbation.H (var 1) (var 3) (var 5) (var 6)))
          (var 4*pw (var 5) (var 6))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI
    (horner_represents _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

theorem normalized_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶
      (represents (rootEvaluation (var 0) (var 1) (var 2) (var 3))
          (GaussianRootProduct.evaluate (GaussianRootProduct.coefficients (var 0) (var 1)) (var 2))
          (pw (var 3) (var 1)) ⋏
        (rootEvaluation (var 0) (var 1) (var 2) (var 3) ≐
          ofGaussian (GaussianRootProduct.evaluate (GaussianRootProduct.coefficients (var 0) (var 1)) (var 2))
            (pw (var 3) (var 1))))) :=
  closeUniv 4 (.impI (.andI (root_evaluation_represents _ _ _ _ Prf.hyp0)
    (root_evaluation_exact _ _ _ _ Prf.hyp0)))

theorem rational_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ represents (rootEvaluation (var 0) (var 1) (var 2) (var 3))
      (GaussianRootProduct.factors (var 0) (var 2) (var 1)) (pw (var 3) (var 1))) :=
  closeUniv 4 (.impI (rational_product_represents _ _ _ _ Prf.hyp0))

theorem rational_root_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ lt (var 3) (var 1) ⟶
      (rootEvaluation (var 0) (var 1) (entry (var 0) (var 3)) (var 2) ≐ qzero)) :=
  closeUniv 4 (.impI (.impI (listed_rational_root_zero _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_query_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (canonical (var 2) ⟶
      (evaluate (GaussianRationalRootProduct.rationalCoefficients
        (GaussianRationalNormalization.sourceNumerators (var 0) (var 1) (var 2)) (length (var 0))
        (GaussianRationalNormalization.commonD (var 0) (var 1) (var 2))) (var 2) ≐
        ofGaussian
          (GaussianRootProduct.evaluate
            (GaussianRootProduct.coefficients (GaussianRationalNormalization.sourceNumerators (var 0) (var 1) (var 2))
              (length (var 0))) (GaussianRationalNormalization.queryNumerator (var 0) (var 1) (var 2)))
          (pw (GaussianRationalNormalization.commonD (var 0) (var 1) (var 2)) (length (var 0))))) :=
  closeUniv 3 (.impI (source_query_evaluation_exact _ _ _ Prf.hyp0))

theorem rational_evaluation_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((PTm.app rootEvaluationF ![var 0,var 1,var 2,var 3] ≐ rootEvaluation (var 0) (var 1) (var 2) (var 3)) ⋏
      (canonical (rootEvaluation (var 0) (var 1) (var 2) (var 3)) ⋏
        (le one (var 3) ⟶ le one (pw (var 3) (var 1))))) :=
  closeUniv 4 (.andI (root_program_at _ _ _ _) (.andI (horner_canonical _ _ _)
    (.impI (GaussianRationalRootProduct.common_denominator_positive _ _ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalHorner
