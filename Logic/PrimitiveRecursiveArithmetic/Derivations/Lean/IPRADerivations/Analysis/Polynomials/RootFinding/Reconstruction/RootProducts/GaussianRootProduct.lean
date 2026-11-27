import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootAlgebra
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalNormalForm
import IPRADerivations.Foundations.SequenceEquality

/-!
# Actual runtime-degree Gaussian root-product polynomials

Finite-demand Section 4, the literal product-polynomial dependency of
`lem:product-stability`. Coefficients are stored in descending degree order.
Multiplication by `X-r` constructs a new actual coefficient sequence using
zero-padded and one-position-delayed reads. The separate Horner evaluator
and root-factor product use actual primitive recursions. Degree, root-list
code, evaluation point and all indices remain internal numerical inputs.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootProduct

open_ipra
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder
  (re im code add mul scale zeroCode oneCode normSq normSq_mul normSq_one)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.Signum (sg)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "ℜ" c:max => ZT.toZ Γ (re c)
local notation "ℑ" c:max => ZT.toZ Γ (im c)
local notation "𝔞" c:max => Groth.ι (Q.mk Γ c)

/-- The raw sequence decoder is explicitly zero-padded by this program. -/
def padded (C i : PTm n) : PTm n := scale (sg (monus (length C) i)) (entry C i)
def delayed (C i : PTm n) : PTm n := scale (sg i) (padded C (pred i))

ipra_subst padded
ipra_subst delayed

theorem padded_inside (C i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) :
    Γ ⊢[PRAAx] equal (padded C i) (entry C i) := by
  have e := natEq (AnalyticNumberTheory.Totatives.sg_lt hi)
  apply equal_of_values <;> simp only [padded,re_scale,im_scale] <;> rw [e] <;> ipra_simps <;> ring

theorem padded_outside (C i : PTm n) (hi : Γ ⊢[PRAAx] le (length C) i) :
    Γ ⊢[PRAAx] equal (padded C i) zeroCode := by
  have e := natEq (AnalyticNumberTheory.Totatives.sg_le hi)
  apply equal_of_values <;> simp only [padded,re_scale,im_scale,re_zero,im_zero] <;> rw [e] <;> ipra_simps <;> ring

theorem delayed_zero (C : PTm n) : Γ ⊢[PRAAx] equal (delayed C zero) zeroCode := by
  have e := natEq (Signum.sg_zero (Γ := Γ) (n := n))
  apply equal_of_values <;> simp only [delayed,re_scale,im_scale,re_zero,im_zero] <;> rw [e] <;> ipra_simps <;> ring

theorem delayed_succ (C i : PTm n) : Γ ⊢[PRAAx] equal (delayed C (succ i)) (padded C i) := by
  have e := natEq (Signum.sg_succ (Γ := Γ) i)
  have p := natEq (pred_succ (Γ := Γ) i)
  have codeEq : Γ ⊢[PRAAx] padded C (pred (succ i)) ≐ padded C i := by
    ipra_congr (padded (var 0) (var 1) : PTm 2) with [.eqRefl C, pred_succ i]
  have v := values_of_code codeEq
  apply equal_of_values <;> simp only [delayed,re_scale,im_scale] <;> rw [e] <;> ipra_simps
  · linear_combination v.1
  · linear_combination v.2

/-- Literal descending coefficient of `(X-r)C(X)`. -/
def linearCoefficient (C r i : PTm n) : PTm n := sub (padded C i) (mul r (delayed C i))
def linearCoefficientF : PR 3 := PTm.toPR (linearCoefficient (var 0) (var 1) (var 2))
def linearBody : PTm 2 := ap3 linearCoefficientF (fstT (var 1)) (sndT (var 1)) (var 0)
def linear (C r : PTm n) : PTm n := sequence linearBody (succ (length C)) (pairT C r)

ipra_subst linearCoefficient
ipra_subst linear

theorem linearCoefficient_at (C r i : PTm n) : Γ ⊢[PRAAx] ap3 linearCoefficientF C r i ≐ linearCoefficient C r i := by
  simpa [linearCoefficientF,ap3] using toPR_eq (Γ := Γ) (linearCoefficient (var 0) (var 1) (var 2) : PTm 3) ![C,r,i]

theorem linear_length (C r : PTm n) : Γ ⊢[PRAAx] length (linear C r) ≐ succ (length C) := sequence_length _ _ _

theorem linear_lookup (C r i : PTm n) (hi : Γ ⊢[PRAAx] le i (length C)) :
    Γ ⊢[PRAAx] entry (linear C r) i ≐ linearCoefficient C r i := by
  have range : Γ ⊢[PRAAx] lt i (succ (length C)) := (succ_monus_succ _ _).eqTrans hi
  have e := sequence_decode (Γ := Γ) linearBody (x := pairT C r) range
  have body : Γ ⊢[PRAAx] inst2 linearBody i (pairT C r) ≐ ap3 linearCoefficientF C r i := by
    simp only [linearBody,inst2,subst_ap3,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
    exact congrAp3 linearCoefficientF (fst_pair _ _) (snd_pair _ _) (.eqRefl _)
  exact e.eqTrans (body.eqTrans (linearCoefficient_at C r i))

def hornerStep : PTm 4 := add (mul (var 1) (var 3)) (padded (var 2) (var 0))
def hornerF : PR 3 := recDef zeroCode hornerStep
def horner (C z k : PTm n) : PTm n := ap3 hornerF k C z
def evaluate (C z : PTm n) : PTm n := horner C z (length C)

ipra_subst horner
ipra_subst evaluate

theorem horner_zero (C z : PTm n) : Γ ⊢[PRAAx] horner C z zero ≐ zeroCode := by
  have h := rec_zero_vecCons (Γ := Γ) (zeroCode : PTm 2) hornerStep ![C,z]
  simpa only [horner,hornerF,ap3,ComplexLogarithmRemainder.subst_zeroCode] using h

theorem horner_succ (C z k : PTm n) : Γ ⊢[PRAAx] horner C z (succ k) ≐ add (mul (horner C z k) z) (padded C k) := by
  have h := rec_succ_vecCons (Γ := Γ) (zeroCode : PTm 2) hornerStep k ![C,z]
  simpa [horner,hornerF,ap3,hornerStep] using h

/-- The delayed read and the previous Horner prefix satisfy the exact
recurrence even at prefix zero. -/
theorem previous_horner (C z k : PTm n) :
    Γ ⊢[PRAAx] equal (add (mul (horner C z (pred k)) z) (delayed C k)) (horner C z k) := by
  refine .orE (zero_or_succ k) ?_ ?_
  · have eqK := Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := k ≐ zero)
    have codeEq : (k ≐ zero) :: Γ ⊢[PRAAx] horner C z k ≐ zeroCode :=
      (congrAp3 hornerF eqK (.eqRefl _) (.eqRefl _)).eqTrans (horner_zero C z)
    have predEq : (k ≐ zero) :: Γ ⊢[PRAAx] horner C z (pred k) ≐ zeroCode :=
      (congrAp3 hornerF ((congrPred eqK).eqTrans pred_zero) (.eqRefl _) (.eqRefl _)).eqTrans (horner_zero C z)
    have delayEq : (k ≐ zero) :: Γ ⊢[PRAAx] delayed C k ≐ delayed C zero := by
      ipra_congr (delayed (var 0) (var 1) : PTm 2) with [.eqRefl C, eqK]
    have dh := equal_trans (equal_of_code delayEq) (delayed_zero C)
    apply equal_of_values
    · simp only [re_add,re_mul]
      rw [(values_of_code predEq).1,(values_of_code predEq).2,equal_re dh,(values_of_code codeEq).1]
      simp only [re_zero,im_zero]; ring
    · simp only [im_add,im_mul]
      rw [(values_of_code predEq).1,(values_of_code predEq).2,equal_im dh,(values_of_code codeEq).2]
      simp only [re_zero,im_zero]; ring
  · have eqK := Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := k ≐ succ (pred k))
    have h := equal_of_code (horner_succ (Γ := (k ≐ succ (pred k)) :: Γ) C z (pred k))
    have delayEq : (k ≐ succ (pred k)) :: Γ ⊢[PRAAx] delayed C k ≐ delayed C (succ (pred k)) := by
      ipra_congr (delayed (var 0) (var 1) : PTm 2) with [.eqRefl C, eqK]
    have dh := equal_trans (equal_of_code delayEq) (delayed_succ C (pred k))
    have kh := values_of_code (a := horner C z k) (b := horner C z (succ (pred k))) (congrAp3 hornerF eqK (.eqRefl C) (.eqRefl z))
    apply equal_of_values
    · rw [re_add,re_mul,equal_re dh,kh.1,equal_re h,re_add,re_mul]
    · rw [im_add,im_mul,equal_im dh,kh.2,equal_im h,im_add,im_mul]

theorem linear_relation (C r k : PTm n) (hk : Γ ⊢[PRAAx] le k (length C)) :
    Γ ⊢[PRAAx] equal (add (padded (linear C r) k) (mul r (delayed C k))) (padded C k) := by
  have range := lt_congr (.eqRefl _) (linear_length C r).eqSymm ((succ_monus_succ _ _).eqTrans hk)
  have p := equal_trans (padded_inside (linear C r) k range) (equal_of_code (linear_lookup C r k hk))
  apply equal_of_values
  · simp only [re_add,re_mul]
    rw [equal_re p]
    simp only [linearCoefficient,re_sub,re_mul,im_mul]
    ring
  · simp only [im_add,im_mul]
    rw [equal_im p]
    simp only [linearCoefficient,im_sub,re_mul,im_mul]
    ring

def prefixLaw (C r z k : PTm n) : Fm PTm n := le k (succ (length C)) ⟶
  equal (add (horner (linear C r) z k) (mul r (horner C z (pred k)))) (horner C z k)

ipra_subst prefixLaw

theorem prefix_zero (C r z : PTm n) : Γ ⊢[PRAAx]
    equal (add (horner (linear C r) z zero) (mul r (horner C z (pred zero)))) (horner C z zero) := by
  have a := values_of_code (horner_zero (Γ := Γ) (linear C r) z)
  have b := values_of_code (horner_zero (Γ := Γ) C z)
  have c := values_of_code (Γ := Γ) (a := horner C z (pred zero)) (b := zeroCode)
    ((congrAp3 hornerF pred_zero (.eqRefl C) (.eqRefl z)).eqTrans (horner_zero C z))
  apply equal_of_values
  · simp only [re_add,re_mul]
    rw [a.1,b.1,c.1,c.2]
    simp only [re_zero,im_zero]; ring
  · simp only [im_add,im_mul]
    rw [a.2,b.2,c.1,c.2]
    simp only [re_zero,im_zero]; ring

/-- QF induction on actual Horner prefixes proves multiplication by the
literal constructed linear factor, with no evaluation identity as input. -/
theorem linear_prefix (C r z k : PTm n) : Γ ⊢[PRAAx] prefixLaw C r z k := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift r) (Syn.shift z) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,⟨trivial,trivial⟩⟩) [subst_prefixLaw, prefixLaw, subst_le, subst_length, subst_equal,
        ComplexLogarithmRemainder.subst_add, ComplexLogarithmRemainder.subst_mul, subst_horner, subst_linear]
    · exact .impI (prefix_zero C r z)
    · refine .impI ?_
      let I := prefixLaw (Syn.shift C) (Syn.shift r) (Syn.shift z) (var 0)
      let Δ := le (succ (var 0)) (succ (length (Syn.shift C))) :: I :: Γ.map Fm.shift
      have bound : Δ ⊢[PRAAx] le (var 0) (length (Syn.shift C)) :=
        (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
      have ih : Δ ⊢[PRAAx] equal
          (add (horner (linear (Syn.shift C) (Syn.shift r)) (Syn.shift z) (var 0))
            (mul (Syn.shift r) (horner (Syn.shift C) (Syn.shift z) (pred (var 0)))))
          (horner (Syn.shift C) (Syn.shift z) (var 0)) :=
        .impE Prf.hyp1 (le_trans bound (le_succ_self _))
      have previous := previous_horner (Γ := Δ) (Syn.shift C) (Syn.shift z) (var 0)
      have coeff := linear_relation (Γ := Δ) (Syn.shift C) (Syn.shift r) (var 0) bound
      have ir := equal_re ih; have ii := equal_im ih
      have pr := equal_re previous; have pi := equal_im previous
      have cr := equal_re coeff; have ci := equal_im coeff
      simp only [re_add,im_add,re_mul,im_mul] at ir ii pr pi cr ci
      have b := values_of_code (horner_succ (Γ := Δ) (linear (Syn.shift C) (Syn.shift r)) (Syn.shift z) (var 0))
      have a := values_of_code (horner_succ (Γ := Δ) (Syn.shift C) (Syn.shift z) (var 0))
      have predCode : Δ ⊢[PRAAx] horner (Syn.shift C) (Syn.shift z) (pred (succ (var 0))) ≐
          horner (Syn.shift C) (Syn.shift z) (var 0) :=
        congrAp3 hornerF (pred_succ _) (.eqRefl _) (.eqRefl _)
      have predValue := values_of_code predCode
      change Δ ⊢[PRAAx] equal
        (add (horner (linear (Syn.shift C) (Syn.shift r)) (Syn.shift z) (succ (var 0)))
          (mul (Syn.shift r) (horner (Syn.shift C) (Syn.shift z) (pred (succ (var 0))))))
        (horner (Syn.shift C) (Syn.shift z) (succ (var 0)))
      apply equal_of_values
      · simp only [re_add,re_mul]
        rw [b.1,a.1,predValue.1,predValue.2]
        simp only [re_add,im_add,re_mul,im_mul]
        linear_combination ZT.toZ Δ (re (Syn.shift z))*ir-ZT.toZ Δ (im (Syn.shift z))*ii-
          ZT.toZ Δ (re (Syn.shift r))*pr+ZT.toZ Δ (im (Syn.shift r))*pi+cr
      · simp only [im_add,im_mul]
        rw [b.2,a.2,predValue.1,predValue.2]
        simp only [re_add,im_add,re_mul,im_mul]
        linear_combination ZT.toZ Δ (im (Syn.shift z))*ir+ZT.toZ Δ (re (Syn.shift z))*ii-
          ZT.toZ Δ (re (Syn.shift r))*pi-ZT.toZ Δ (im (Syn.shift r))*pr+ci
  ipra_simpa_inst [subst_prefixLaw] using Prf.allE k all

/-- Horner evaluation of the actual constructed coefficient list is exactly
`(z-r)` times the old Horner value, at arbitrary runtime list length. -/
theorem evaluate_linear (C r z : PTm n) :
    Γ ⊢[PRAAx] equal (evaluate (linear C r) z) (mul (sub z r) (evaluate C z)) := by
  have h := Prf.impE (linear_prefix (Γ := Γ) C r z (succ (length C))) (le_refl _)
  have hr := equal_re h; have hi := equal_im h
  have b := values_of_code (Γ := Γ) (a := evaluate (linear C r) z) (b := horner (linear C r) z (succ (length C)))
    (congrAp3 hornerF (linear_length C r) (.eqRefl _) (.eqRefl _))
  have a := values_of_code (horner_succ (Γ := Γ) C z (length C))
  have p := values_of_code (Γ := Γ) (a := horner C z (pred (succ (length C)))) (b := horner C z (length C))
    (congrAp3 hornerF (pred_succ _) (.eqRefl _) (.eqRefl _))
  have zp := padded_outside (Γ := Γ) C (length C) (le_refl _)
  simp only [re_add,im_add,re_mul,im_mul] at hr hi
  rw [p.1,p.2,a.1] at hr
  rw [p.1,p.2,a.2] at hi
  simp only [re_add,im_add,re_mul,im_mul] at hr hi
  rw [equal_re zp] at hr
  rw [equal_im zp] at hi
  simp only [re_zero,im_zero] at hr hi
  apply equal_of_values
  · rw [b.1]
    simp only [evaluate,re_mul,re_sub,im_sub]
    linear_combination hr
  · rw [b.2]
    simp only [evaluate,im_mul,re_sub,im_sub]
    linear_combination hi

/-! ## Actual root-list coefficient construction and independent factor fold -/

def initial : PTm n := sequence (oneCode : PTm 2) one zero
ipra_subst initial

def coefficientStep : PTm 3 := linear (var 1) (entry (var 2) (var 0))
def coefficientsF : PR 2 := rec2 initial coefficientStep
def coefficients (R N : PTm n) : PTm n := ap2 coefficientsF N R

ipra_subst coefficients

theorem coefficients_zero (R : PTm n) : Γ ⊢[PRAAx] coefficients R zero ≐ initial := by
  simpa only [coefficients,coefficientsF,subst_initial] using rec2_zero (Γ := Γ) initial coefficientStep R

theorem coefficients_succ (R N : PTm n) : Γ ⊢[PRAAx]
    coefficients R (succ N) ≐ linear (coefficients R N) (entry R N) := by
  simpa [coefficients,coefficientsF,coefficientStep] using rec2_succ (Γ := Γ) initial coefficientStep N R

theorem coefficients_length (R N : PTm n) : Γ ⊢[PRAAx] length (coefficients R N) ≐ succ N := by
  have all : Γ ⊢[PRAAx] .all (length (coefficients (Syn.shift R) (var 0)) ≐ succ (var 0)) := by
    ipra_qfind [subst_length, subst_coefficients]
    · exact (congrFst (coefficients_zero R)).eqTrans (sequence_length _ _ _)
    · exact (congrFst (coefficients_succ _ _)).eqTrans ((linear_length _ _).eqTrans (congrSucc Prf.hyp0))
  ipra_simpa_inst [Fm.subst_eq,subst_length,subst_coefficients,ConciseIPRA.PTm.subst_succ] using Prf.allE N all

def factorStep : PTm 4 := mul (sub (var 3) (entry (var 2) (var 0))) (var 1)
def factorF : PR 3 := recDef oneCode factorStep
def factors (R z N : PTm n) : PTm n := ap3 factorF N R z

ipra_subst factors

theorem factors_zero (R z : PTm n) : Γ ⊢[PRAAx] factors R z zero ≐ oneCode := by
  have h := rec_zero_vecCons (Γ := Γ) (oneCode : PTm 2) factorStep ![R,z]
  simpa only [factors,factorF,ap3,ComplexLogarithmRemainder.subst_oneCode] using h

theorem factors_succ (R z N : PTm n) : Γ ⊢[PRAAx]
    factors R z (succ N) ≐ mul (sub z (entry R N)) (factors R z N) := by
  have h := rec_succ_vecCons (Γ := Γ) (oneCode : PTm 2) factorStep N ![R,z]
  simpa [factors,factorF,ap3,factorStep] using h

theorem evaluate_code_congr {C C' z z' : PTm n} (hC : Γ ⊢[PRAAx] C ≐ C') (hz : Γ ⊢[PRAAx] z ≐ z') :
    Γ ⊢[PRAAx] evaluate C z ≐ evaluate C' z' := by
  ipra_congr (evaluate (var 0) (var 1) : PTm 2) with [hC, hz]

theorem initial_entry : Γ ⊢[PRAAx] entry (initial : PTm n) zero ≐ oneCode := by
  simpa [initial,inst2] using sequence_decode (Γ := Γ) (oneCode : PTm 2) (x := (zero : PTm n)) (zero_lt_succ zero)

theorem initial_evaluate (z : PTm n) : Γ ⊢[PRAAx] equal (evaluate initial z) oneCode := by
  have len : Γ ⊢[PRAAx] length (initial : PTm n) ≐ one := sequence_length _ _ _
  have er : Γ ⊢[PRAAx] evaluate initial z ≐ add (mul (horner initial z zero) z) (padded initial zero) :=
    (congrAp3 hornerF len (.eqRefl _) (.eqRefl _)).eqTrans (horner_succ initial z zero)
  have eq := values_of_code er
  have hz := values_of_code (horner_zero (Γ := Γ) (initial : PTm n) z)
  have pad := equal_trans (padded_inside (initial : PTm n) zero
    (Order.zero_lt_of_eq_succ len)) (equal_of_code initial_entry)
  apply equal_of_values
  · rw [eq.1,re_add,re_mul,hz.1,hz.2,equal_re pad]
    simp only [re_zero,im_zero,re_one]; ring
  · rw [eq.2,im_add,im_mul,hz.1,hz.2,equal_im pad]
    simp only [re_zero,im_zero,im_one]; ring

def evaluationLaw (R z N : PTm n) : Fm PTm n := equal (evaluate (coefficients R N) z) (factors R z N)
ipra_subst evaluationLaw

theorem evaluation_step (R z N : PTm n) (ih : Γ ⊢[PRAAx] evaluationLaw R z N) :
    Γ ⊢[PRAAx] evaluationLaw R z (succ N) :=
  equal_trans (equal_of_code (evaluate_code_congr (coefficients_succ R N) (.eqRefl z)))
    (equal_trans (evaluate_linear (coefficients R N) (entry R N) z)
      (equal_trans (mul_equal (equal_refl _) ih) (equal_symm (equal_of_code (factors_succ R z N)))))

/-- The coefficient producer and the separately computed factor fold agree
at every internally quantified degree. No polynomial/factor identity is supplied. -/
theorem evaluate_product (R z N : PTm n) : Γ ⊢[PRAAx] evaluationLaw R z N := by
  have all : Γ ⊢[PRAAx] .all (evaluationLaw (Syn.shift R) (Syn.shift z) (var 0)) := by
    ipra_qfind (⟨trivial,trivial⟩) [subst_evaluationLaw]
    · exact equal_trans (equal_of_code (evaluate_code_congr (coefficients_zero R) (.eqRefl z)))
        (equal_trans (initial_evaluate z) (equal_symm (equal_of_code (factors_zero R z))))
    · exact evaluation_step _ _ _ Prf.hyp0
  ipra_simpa_inst [subst_evaluationLaw] using Prf.allE N all

theorem factor_tail_step (R z s k : PTm n) (h : Γ ⊢[PRAAx] equal (factors R z (s+k)) zeroCode) :
    Γ ⊢[PRAAx] equal (factors R z (s+succ k)) zeroCode := by
  have e : Γ ⊢[PRAAx] factors R z (s+succ k) ≐ factors R z (succ (s+k)) :=
    congrAp3 factorF (by ipra_ring) (.eqRefl _) (.eqRefl _)
  exact equal_trans (equal_of_code e) (equal_trans (equal_of_code (factors_succ R z (s+k)))
    (equal_trans (mul_equal (equal_refl _) h) (GaussianRootAlgebra.mul_zero _)))

theorem factor_tail_zero (R z s k : PTm n) (h : Γ ⊢[PRAAx] equal (factors R z s) zeroCode) :
    Γ ⊢[PRAAx] equal (factors R z (s+k)) zeroCode := by
  have all : Γ ⊢[PRAAx] .all (equal (factors (Syn.shift R) (Syn.shift z) (Syn.shift s+var 0)) zeroCode) := by
    ipra_qfind (⟨trivial,trivial⟩) [subst_equal, subst_factors, ComplexLogarithmRemainder.subst_zeroCode]
    · exact equal_trans (equal_of_code (congrAp3 factorF (add_zero s) (.eqRefl _) (.eqRefl _))) h
    · exact factor_tail_step _ _ _ _ Prf.hyp0
  ipra_simpa_inst [subst_equal,subst_factors,PTm.subst_add,ComplexLogarithmRemainder.subst_zeroCode] using Prf.allE k all

theorem root_factor_zero (R j : PTm n) : Γ ⊢[PRAAx] equal (factors R (entry R j) (succ j)) zeroCode :=
  equal_trans (equal_of_code (factors_succ R (entry R j) j))
    (equal_trans (mul_equal (sub_self _) (equal_refl _)) (GaussianRootAlgebra.zero_mul _))

/-- Every listed root is an exact root of the actually produced polynomial.
No distinctness assumption is imposed, so repeated roots are included. -/
theorem listed_root_zero (R N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] equal (evaluate (coefficients R N) (entry R j)) zeroCode := by
  have bound : Γ ⊢[PRAAx] N ≐ succ j+monus N (succ j) := eq_add_of_le hj
  have countEq : Γ ⊢[PRAAx] factors R (entry R j) N ≐ factors R (entry R j) (succ j+monus N (succ j)) :=
    congrAp3 factorF bound (.eqRefl _) (.eqRefl _)
  exact equal_trans (evaluate_product R (entry R j) N) (equal_trans (equal_of_code countEq)
    (factor_tail_zero R (entry R j) (succ j) (monus N (succ j)) (root_factor_zero R j)))

/-! ## Monicity and the actual product of squared factor norms -/

theorem linear_leading (C r : PTm n) (hC : Γ ⊢[PRAAx] le one (length C)) :
    Γ ⊢[PRAAx] equal (entry (linear C r) zero) (entry C zero) := by
  have raw := equal_of_code (linear_lookup (Γ := Γ) C r zero (zero_le _))
  have pad := padded_inside (Γ := Γ) C zero hC
  have delay := delayed_zero (Γ := Γ) C
  apply equal_of_values
  · rw [equal_re raw]
    simp only [linearCoefficient,re_sub,re_mul]
    rw [equal_re pad,equal_re delay,equal_im delay]
    simp only [re_zero,im_zero]; ring
  · rw [equal_im raw]
    simp only [linearCoefficient,im_sub,im_mul]
    rw [equal_im pad,equal_re delay,equal_im delay]
    simp only [re_zero,im_zero]; ring

theorem coefficients_monic_step (R N : PTm n)
    (h : Γ ⊢[PRAAx] equal (entry (coefficients R N) zero) oneCode) :
    Γ ⊢[PRAAx] equal (entry (coefficients R (succ N)) zero) oneCode :=
  equal_trans (equal_of_code (Foundations.SequenceComposition.entry_congr (coefficients_succ R N) (.eqRefl zero)))
    (equal_trans (linear_leading _ _ (Order.zero_lt_of_eq_succ (coefficients_length R N))) h)

/-- The generated list is genuinely monic, uniformly in its numerical degree. -/
theorem coefficients_monic (R N : PTm n) :
    Γ ⊢[PRAAx] equal (entry (coefficients R N) zero) oneCode := by
  have all : Γ ⊢[PRAAx] .all (equal (entry (coefficients (Syn.shift R) (var 0)) zero) oneCode) := by
    ipra_qfind (⟨trivial,trivial⟩) [subst_equal, subst_entry, subst_coefficients,
        ComplexLogarithmRemainder.subst_oneCode]
    · exact equal_of_code ((Foundations.SequenceComposition.entry_congr (coefficients_zero R) (.eqRefl zero)).eqTrans initial_entry)
    · exact coefficients_monic_step _ _ Prf.hyp0
  ipra_simpa_inst [subst_equal,subst_entry,subst_coefficients,ConciseIPRA.PTm.subst_zero,
    ComplexLogarithmRemainder.subst_oneCode] using Prf.allE N all

def normBody : PTm 2 := normSq (sub (sndT (var 1)) (entry (fstT (var 1)) (var 0)))
def normFactors (R z N : PTm n) : PTm n := ap2 (prodF normBody) N (pairT R z)

ipra_subst normFactors

theorem normBody_at (R z j : PTm n) :
    Γ ⊢[PRAAx] inst2 normBody j (pairT R z) ≐ normSq (sub z (entry R j)) := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (normSq (sub (var 0) (entry (var 1) (var 2))) : PTm 3)
    (σ := ![sndT (pairT R z),fstT (pairT R z),j]) (σ' := ![z,R,j])
    (fun i => by fin_cases i; exact snd_pair _ _; exact fst_pair _ _; exact .eqRefl _)
  simpa only [normBody,inst2,ComplexLogarithmRemainder.subst_normSq,subst_sub,subst_entry,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using e

theorem normFactors_zero (R z : PTm n) : Γ ⊢[PRAAx] normFactors R z zero ≐ one := prod_zero _ _
theorem normFactors_succ (R z N : PTm n) : Γ ⊢[PRAAx]
    normFactors R z (succ N) ≐ normFactors R z N*normSq (sub z (entry R N)) :=
  (prod_succ normBody N (pairT R z)).eqTrans (congrMul (.eqRefl _) (normBody_at R z N))

theorem factors_norm_step (R z N : PTm n)
    (h : Γ ⊢[PRAAx] normSq (factors R z N) ≐ normFactors R z N) :
    Γ ⊢[PRAAx] normSq (factors R z (succ N)) ≐ normFactors R z (succ N) :=
  (ComplexLogarithmRemainder.congr_normSq (factors_succ R z N)).eqTrans
    ((normSq_mul _ _).eqTrans ((congrMul (.eqRefl _) h).eqTrans
      ((mul_comm _ _).eqTrans (normFactors_succ R z N).eqSymm)))

/-- Exact multiplicativity for the actual finite squared-norm product.
This is suitable for the numerical bounded factor-witness search. -/
theorem factors_norm (R z N : PTm n) : Γ ⊢[PRAAx] normSq (factors R z N) ≐ normFactors R z N := by
  have all : Γ ⊢[PRAAx] .all (normSq (factors (Syn.shift R) (Syn.shift z) (var 0)) ≐
      normFactors (Syn.shift R) (Syn.shift z) (var 0)) := by
    ipra_qfind [ComplexLogarithmRemainder.subst_normSq, subst_factors, subst_normFactors]
    · exact (ComplexLogarithmRemainder.congr_normSq (factors_zero R z)).eqTrans
        ((normSq_one (Γ := Γ)).eqTrans (normFactors_zero R z).eqSymm)
    · exact factors_norm_step _ _ _ Prf.hyp0
  ipra_simpa_inst [Fm.subst_eq,ComplexLogarithmRemainder.subst_normSq,subst_factors,subst_normFactors] using Prf.allE N all

theorem evaluation_norm_product (R z N : PTm n) :
    Γ ⊢[PRAAx] normSq (evaluate (coefficients R N) z) ≐ normFactors R z N :=
  (normSq_equal (evaluate_product R z N)).eqTrans (factors_norm R z N)

/-! ## Fixed output metadata and closed source-linked endpoints -/

def program (R z N : PTm n) : PTm n :=
  pairT (coefficients R N) (pairT (evaluate (coefficients R N) z) (factors R z N))
def programF : PR 3 := PTm.toPR (program (var 0) (var 1) (var 2))
ipra_subst program

theorem program_at (R z N : PTm n) : Γ ⊢[PRAAx] ap3 programF R z N ≐ program R z N := by
  simpa [programF,ap3] using toPR_eq (Γ := Γ) (program (var 0) (var 1) (var 2) : PTm 3) ![R,z,N]

theorem linear_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (equal (evaluate (linear (var 0) (var 1)) (var 2)) (mul (sub (var 2) (var 1)) (evaluate (var 0) (var 2)))) :=
  closeUniv 3 (evaluate_linear _ _ _)

theorem root_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (equal (evaluate (coefficients (var 0) (var 2)) (var 1)) (factors (var 0) (var 1) (var 2))) :=
  closeUniv 3 (evaluate_product _ _ _)

theorem listed_root_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶ equal (evaluate (coefficients (var 0) (var 1)) (entry (var 0) (var 2))) zeroCode) :=
  closeUniv 3 (.impI (listed_root_zero _ _ _ Prf.hyp0))

theorem coefficient_monic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((length (coefficients (var 0) (var 1)) ≐ succ (var 1)) ⋏
      equal (entry (coefficients (var 0) (var 1)) zero) oneCode) :=
  closeUniv 2 (.andI (coefficients_length _ _) (coefficients_monic _ _))

theorem squared_norm_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (normSq (evaluate (coefficients (var 0) (var 2)) (var 1)) ≐ normFactors (var 0) (var 1) (var 2)) :=
  closeUniv 3 (evaluation_norm_product _ _ _)

theorem root_product_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 programF (var 0) (var 1) (var 2) ≐ program (var 0) (var 1) (var 2)) ⋏
      ((fstT (ap3 programF (var 0) (var 1) (var 2)) ≐ coefficients (var 0) (var 2)) ⋏
        equal (fstT (sndT (ap3 programF (var 0) (var 1) (var 2))))
          (sndT (sndT (ap3 programF (var 0) (var 1) (var 2)))))) := by
  apply closeUniv 3
  have p := program_at (Γ := ([] : List (Fm PTm 3))) (var 0) (var 1) (var 2)
  have f := p.fstE
  have l := (congrFst (congrSnd p)).eqTrans (snd_pair _ _).fstE
  have r := (congrSnd (congrSnd p)).eqTrans (snd_pair _ _).sndE
  exact .andI p (.andI f (equal_trans (equal_of_code l)
    (equal_trans (evaluate_product _ _ _) (equal_symm (equal_of_code r)))))

end LeanProofs.IPRA.Analysis.GaussianRootProduct
