import IPRADerivations.Analysis.GaussianRationalFiniteSum
import IPRADerivations.Analysis.GaussianTranslationCoefficientValues
import IPRADerivations.Analysis.GaussianRationalPowerAlgebra
import IPRADerivations.Combinatorics.Vandermonde
import IPRADerivations.Foundations.BoundedSyntaxBackwardInduction

/-!
# Literal finite binomial rows of actual translation stages

The finite term producer uses the actual synthetic-stage remainders and
the guarded binomial coefficient. Natural scaling, powers and sums are
actual rational programs. No inverse translation or row identity is an
input. Original coefficients are compared through their canonical recode.
All polynomial data, degrees, stage indices and coefficient positions are
numerical inputs, including the constant cell j=k=0.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianInverseBinomialRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (canonical qadd qmul represents positive_product canonical_unique represents_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnegative qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalNaturalScale (natScale natScale_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power powerF power_zero power_succ)
open LeanProofs.IPRA.Analysis.GaussianRationalTranslationStages (remaining remaining_step)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_self gb_pascal)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def b (C N z i : PTm n) : PTm n := GaussianTranslationCoefficientValues.translatedCoefficient C N z i
def term (C N z j k r : PTm n) : PTm n :=
  natScale (gb (k+r) k) (qmul (b C N z (j+k+r)) (power (qnegative z) r))
def data (C N z j k : PTm n) : PTm n := pairT C (pairT N (pairT z (pairT j k)))
def termBody : PTm 2 := term (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (fstT (sndT (sndT (sndT (var 1)))))
  (sndT (sndT (sndT (sndT (var 1))))) (var 0)
def R (C N z j k : PTm n) : PTm n :=
  GaussianRationalFiniteSum.sum termBody (succ (monus N (j+k))) (data C N z j k)

@[simp] theorem subst_b {m : ℕ} (σ : Fin n → PTm m) (C N z i : PTm n) :
    Syn.subst σ (b C N z i) = b (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ i) := by simp [b]
@[simp] theorem subst_term {m : ℕ} (σ : Fin n → PTm m) (C N z j k r : PTm n) :
    Syn.subst σ (term C N z j k r) = term (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ j) (Syn.subst σ k) (Syn.subst σ r) := by simp [term]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (C N z j k : PTm n) :
    Syn.subst σ (data C N z j k) = data (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ j) (Syn.subst σ k) := by simp [data]
@[simp] theorem subst_R {m : ℕ} (σ : Fin n → PTm m) (C N z j k : PTm n) :
    Syn.subst σ (R C N z j k) = R (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ j) (Syn.subst σ k) := by simp [R]

theorem b_canonical (C N z i : PTm n) : Γ ⊢[PRAAx] canonical (b C N z i) :=
  GaussianTranslationCoefficientValues.translated_coefficient_canonical _ _ _ _

theorem b_congr {C C' N N' z z' i i' : PTm n}
    (hC : Γ ⊢[PRAAx] C ≐ C') (hN : Γ ⊢[PRAAx] N ≐ N')
    (hz : Γ ⊢[PRAAx] z ≐ z') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx] b C N z i ≐ b C' N' z' i' := by
  simpa only [subst_b,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (b (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![C,N,z,i]) (σ' := ![C',N',z',i'])
      (fun j => by fin_cases j; exact hC; exact hN; exact hz; exact hi)

theorem b_index_congr (C N z : PTm n) {i l : PTm n} (h : Γ ⊢[PRAAx] i ≐ l) :
    Γ ⊢[PRAAx] b C N z i ≐ b C N z l := b_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) h

theorem negative_congr {z w : PTm n} (h : Γ ⊢[PRAAx] z ≐ w) : Γ ⊢[PRAAx] qnegative z ≐ qnegative w := by
  simpa only [GaussianRationalMetric.subst_qnegative,Syn.subst_var,Matrix.cons_val_zero] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (qnegative (var 0) : PTm 1)
      (σ := ![z]) (σ' := ![w]) (fun i => by fin_cases i; exact h)

theorem term_congr {C C' N N' z z' j j' k k' r r' : PTm n}
    (hC : Γ ⊢[PRAAx] C ≐ C') (hN : Γ ⊢[PRAAx] N ≐ N') (hz : Γ ⊢[PRAAx] z ≐ z')
    (hj : Γ ⊢[PRAAx] j ≐ j') (hk : Γ ⊢[PRAAx] k ≐ k') (hr : Γ ⊢[PRAAx] r ≐ r') :
    Γ ⊢[PRAAx] term C N z j k r ≐ term C' N' z' j' k' r' :=
  natScale_congr (congrGb (congrAdd hk hr) hk)
    (qmul_congr (b_congr hC hN hz (congrAdd (congrAdd hj hk) hr)) (congrAp2 powerF hr (negative_congr hz)))

theorem term_canonical (C N z j k r : PTm n) : Γ ⊢[PRAAx] canonical (term C N z j k r) :=
  GaussianRationalNaturalScale.natScale_canonical _ _
theorem R_canonical (C N z j k : PTm n) : Γ ⊢[PRAAx] canonical (R C N z j k) :=
  GaussianRationalFiniteSum.sum_canonical _ _ _

theorem term_at (C N z j k r : PTm n) : Γ ⊢[PRAAx]
    inst2 termBody r (data C N z j k) ≐ term C N z j k r := by
  have c := fst_pair (Γ := Γ) C (pairT N (pairT z (pairT j k)))
  have tail := snd_pair (Γ := Γ) C (pairT N (pairT z (pairT j k)))
  have nt := (congrSnd tail).eqTrans (snd_pair N (pairT z (pairT j k)))
  have zt := (congrSnd nt).eqTrans (snd_pair z (pairT j k))
  have eqs := term_congr c ((congrFst tail).eqTrans (fst_pair _ _))
    ((congrFst nt).eqTrans (fst_pair _ _)) ((congrFst zt).eqTrans (fst_pair _ _))
    ((congrSnd zt).eqTrans (snd_pair _ _)) (.eqRefl r)
  simpa only [termBody,inst2,subst_term,subst_fstT,subst_sndT,Syn.subst_var,data,
    Matrix.cons_val_zero,Matrix.cons_val_one] using eqs

theorem term_zero (C N z j k : PTm n) : Γ ⊢[PRAAx] term C N z j k zero ≐ b C N z (j+k) :=
  (natScale_congr ((congrGb (add_zero k) (.eqRefl _)).eqTrans (gb_self k))
    ((qmul_congr (b_index_congr C N z (add_zero _)) (power_zero _)).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ (b_canonical C N z (j+k))))).eqTrans
    (GaussianRationalNaturalScale.natScale_one_canonical _ (b_canonical C N z (j+k)))

theorem R_first (C N z j k : PTm n) : Γ ⊢[PRAAx]
    R C N z j k ≐ qadd (b C N z (j+k))
      (GaussianRationalFiniteSum.sum (shiftBody termBody) (monus N (j+k)) (data C N z j k)) :=
  (GaussianRationalFiniteSum.sum_shift_first _ _ _).eqTrans
    (qadd_congr ((term_at C N z j k zero).eqTrans (term_zero C N z j k)) (.eqRefl _))

theorem R_singleton (C N z j k : PTm n) (h : Γ ⊢[PRAAx] j+k ≐ N) : Γ ⊢[PRAAx]
    R C N z j k ≐ b C N z N := by
  have count := (congrMonus (.eqRefl N) h).eqTrans (monus_self N)
  exact (R_first C N z j k).eqTrans
    ((qadd_congr (b_index_congr C N z h)
      ((GaussianRationalFiniteSum.sum_index_congr (shiftBody termBody) count (.eqRefl _)).eqTrans
        (GaussianRationalFiniteSum.sum_zero _ _))).eqTrans
      (GaussianReciprocalHorner.qadd_zero_right _ (b_canonical C N z N)))

/-- Multiplication by -z raises the actual power index by one, with no
canonical or nonzero guard on the original numerical point. -/
theorem mul_power_step (z v r : PTm n) : Γ ⊢[PRAAx]
    qmul (qnegative z) (qmul v (power (qnegative z) r)) ≐ qmul v (power (qnegative z) (succ r)) :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
      (qmul_congr (.eqRefl _) (power_succ _ _).eqSymm))

theorem weighted_power_step (t z v r : PTm n) : Γ ⊢[PRAAx]
    qmul (qnegative z) (natScale t (qmul v (power (qnegative z) r))) ≐
      natScale t (qmul v (power (qnegative z) (succ r))) :=
  (GaussianRationalNaturalScale.natScale_product _ _ _).eqTrans
    (natScale_congr (.eqRefl _) (mul_power_step z v r))

/-- Guarded Pascal is used on actual numerical weights, rather than an
above-diagonal assumption about the unguarded factorial quotient. -/
theorem weighted_pascal (k r z v : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    natScale (gb (k+succ r) k) (qmul v (power (qnegative z) (succ r))) ≐
      qadd (natScale (gb (pred k+succ r) (pred k)) (qmul v (power (qnegative z) (succ r))))
        (qmul (qnegative z) (natScale (gb (k+r) k) (qmul v (power (qnegative z) r)))) := by
  have ek := RationalIntegerNormalization.positive_form (Γ := Γ) hk
  have upper : Γ ⊢[PRAAx] k+succ r ≐ succ (k+r) := by ipra_ring
  have left : Γ ⊢[PRAAx] k+r ≐ pred k+succ r := by
    have e := natEq ek
    apply deriveNat
    ipra_simps
    linear_combination e
  have pascal := ((congrGb upper ek).eqTrans (gb_pascal (k+r) (pred k))).eqTrans
    ((add_comm _ _).eqTrans (congrAdd (congrGb left (.eqRefl _)) (congrGb (.eqRefl _) ek.eqSymm)))
  exact (natScale_congr pascal (.eqRefl _)).eqTrans
    ((GaussianRationalNaturalScale.natScale_add _ _ _).eqTrans
      (qadd_congr (.eqRefl _) (weighted_power_step _ _ _ _).eqSymm))

theorem term_pascal (C N z j k r : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    term C N z j k (succ r) ≐ qadd (term C N z (succ j) (pred k) (succ r))
      (qmul (qnegative z) (term C N z (succ j) k r)) := by
  have ek := natEq (RationalIntegerNormalization.positive_form (Γ := Γ) hk)
  have left : Γ ⊢[PRAAx] succ j+pred k+succ r ≐ j+k+succ r := by
    apply deriveNat
    ipra_simps
    linear_combination -ek
  have right : Γ ⊢[PRAAx] succ j+k+r ≐ j+k+succ r := by ipra_ring
  exact (weighted_pascal k r z (b C N z (j+k+succ r)) hk).eqTrans
    (qadd_congr (natScale_congr (.eqRefl _) (qmul_congr (b_index_congr C N z left.eqSymm) (.eqRefl _)))
      (qmul_congr (.eqRefl _) (natScale_congr (.eqRefl _) (qmul_congr (b_index_congr C N z right.eqSymm) (.eqRefl _)))))

theorem zero_weight_term (C N z j r : PTm n) : Γ ⊢[PRAAx]
    term C N z j zero r ≐ qmul (b C N z (j+r)) (power (qnegative z) r) :=
  (natScale_congr ((congrGb (zero_add r) (.eqRefl _)).eqTrans (gb_zero r))
    (qmul_congr (b_index_congr C N z (by ipra_ring)) (.eqRefl _))).eqTrans
      (GaussianRationalNaturalScale.natScale_one_canonical _ (GaussianRationalHorner.qmul_canonical _ _))

theorem constant_term_step (C N z j r : PTm n) : Γ ⊢[PRAAx]
    term C N z j zero (succ r) ≐ qmul (qnegative z) (term C N z (succ j) zero r) :=
  ((qmul_congr (.eqRefl _) (zero_weight_term C N z (succ j) r)).eqTrans
    ((mul_power_step z (b C N z (succ j+r)) r).eqTrans
      ((qmul_congr (b_index_congr C N z (by ipra_ring)) (.eqRefl _)).eqTrans
        (zero_weight_term C N z j (succ r)).eqSymm))).eqSymm

def leftBody (t : PTm 2) : PTm 2 := inst2 t (var 0) (fstT (var 1))
def rightBody (t : PTm 2) : PTm 2 := inst2 t (var 0) (sndT (var 1))
def pairAddBody (t u : PTm 2) : PTm 2 := GaussianRationalFiniteSum.addBody (leftBody t) (rightBody u)

@[simp] theorem inst2_leftBody (t : PTm 2) (i x : PTm n) :
    inst2 (leftBody t) i x = inst2 t i (fstT x) := by
  simp only [leftBody,inst2,Syn.subst_subst]
  congr 1
  funext j
  fin_cases j <;> simp
@[simp] theorem inst2_rightBody (t : PTm 2) (i x : PTm n) :
    inst2 (rightBody t) i x = inst2 t i (sndT x) := by
  simp only [rightBody,inst2,Syn.subst_subst]
  congr 1
  funext j
  fin_cases j <;> simp

theorem left_sum (t : PTm 2) (m x : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum (leftBody t) m x ≐ GaussianRationalFiniteSum.sum t m (fstT x) := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  simp only [inst2_leftBody,Syn.shift,subst_fstT]
  exact .eqRefl _

theorem right_sum (t : PTm 2) (m x : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum (rightBody t) m x ≐ GaussianRationalFiniteSum.sum t m (sndT x) := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  simp only [inst2_rightBody,Syn.shift,subst_sndT]
  exact .eqRefl _

theorem pair_add_at (t u : PTm 2) (i x y : PTm n) : Γ ⊢[PRAAx]
    inst2 (pairAddBody t u) i (pairT x y) ≐ qadd (inst2 t i x) (inst2 u i y) := by
  simp only [pairAddBody,GaussianRationalFiniteSum.inst2_addBody,inst2_leftBody,inst2_rightBody]
  exact qadd_congr (congrInst2 t (.eqRefl _) (fst_pair _ _)) (congrInst2 u (.eqRefl _) (snd_pair _ _))

theorem pair_sum_add (t u : PTm 2) (m x y : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum (pairAddBody t u) m (pairT x y) ≐
      qadd (GaussianRationalFiniteSum.sum t m x) (GaussianRationalFiniteSum.sum u m y) :=
  (GaussianRationalFiniteSum.sum_add _ _ _ _).eqTrans (qadd_congr
    ((left_sum t m (pairT x y)).eqTrans (GaussianRationalFiniteSum.sum_index_congr _ (.eqRefl _) (fst_pair _ _)))
    ((right_sum u m (pairT x y)).eqTrans (GaussianRationalFiniteSum.sum_index_congr _ (.eqRefl _) (snd_pair _ _))))

def linearTerms (t u v : PTm 2) (m x y z a : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ inst2 t (var 0) (Syn.shift x) ≐
    qadd (inst2 u (var 0) (Syn.shift y)) (qmul (Syn.shift a) (inst2 v (var 0) (Syn.shift z))))
@[simp] theorem subst_linearTerms {l : ℕ} (σ : Fin n → PTm l) (t u v : PTm 2) (m x y z a : PTm n) :
    (linearTerms t u v m x y z a).subst σ = linearTerms t u v (Syn.subst σ m) (Syn.subst σ x)
      (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ a) := by simp [linearTerms,Syn.subst_shift,Syn.shift_subst]

theorem linear_at (t u v : PTm 2) (m x y z a i : PTm n)
    (h : Γ ⊢[PRAAx] linearTerms t u v m x y z a) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    inst2 t i x ≐ qadd (inst2 u i y) (qmul a (inst2 v i z)) := by
  have rule : Γ ⊢[PRAAx] lt i m ⟶ inst2 t i x ≐ qadd (inst2 u i y) (qmul a (inst2 v i z)) := by
    simpa [linearTerms] using h.allE i
  exact .impE rule hi

/-- Independent numerical data are packed into the already proved actual
sum-add/multiply programs. Only individual term equations are inputs. -/
theorem linear_sum (t u v : PTm 2) (m x y z a : PTm n)
    (h : Γ ⊢[PRAAx] linearTerms t u v m x y z a) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum t m x ≐ qadd (GaussianRationalFiniteSum.sum u m y)
      (qmul a (GaussianRationalFiniteSum.sum v m z)) := by
  have table : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual t
      (pairAddBody u (GaussianRationalFiniteSum.multiplyBody v)) m x (pairT y (pairT a z)) := by
    refine .allI (.impI ?_)
    have hs : Γ.map Fm.shift ⊢[PRAAx] linearTerms t u v (Syn.shift m) (Syn.shift x) (Syn.shift y)
        (Syn.shift z) (Syn.shift a) := by
      simpa only [Fm.shift,subst_linearTerms,Syn.shift] using h.shift
    have source := linear_at t u v _ _ _ _ _ (var 0) hs.wk Prf.hyp0
    have target := (pair_add_at (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) u
      (GaussianRationalFiniteSum.multiplyBody v) (var 0) (Syn.shift y) (pairT (Syn.shift a) (Syn.shift z))).eqTrans
      (qadd_congr (.eqRefl _) (GaussianRationalFiniteSum.multiply_body_at _ _ _ _))
    simpa only [Syn.shift,subst_pairT] using source.eqTrans target.eqSymm
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ table).eqTrans
    ((pair_sum_add _ _ _ _ _).eqTrans
      (qadd_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_multiply _ _ _ _)))

theorem negative_product (z v : PTm n) : Γ ⊢[PRAAx]
    qnegative (qmul z v) ≐ qmul (qnegative z) v := by
  let A := GaussianRationalL1.rawGaussian z
  let B := GaussianRationalL1.rawGaussian v
  let D := GaussianRationalL1.rawDen z*GaussianRationalL1.rawDen v
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _
    (GaussianRationalL1.raw_den_positive z) (GaussianRationalL1.raw_den_positive v)
  have product := GaussianRationalHorner.qmul_represents _ _ _ _ _ _
    (GaussianRationalL1.raw_den_positive z) (GaussianRationalL1.raw_den_positive v)
    (GaussianRationalL1.raw_represents (Γ := Γ) z) (GaussianRationalL1.raw_represents v)
  apply canonical_unique _ _ (ComplexLogarithmRemainder.neg (ComplexLogarithmRemainder.mul A B)) D
    (GaussianRationalMetric.qnegative_canonical _) (GaussianRationalHorner.qmul_canonical _ _) hd
    (GaussianRationalMetric.qnegative_represents _ _ _ product)
  exact represents_congr (.eqRefl _) (by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_neg,
        GaussianRootAlgebra.im_neg] <;> ring) (.eqRefl _)
    (GaussianRationalHorner.qmul_represents _ _ _ _ _ _
      (GaussianRationalL1.raw_den_positive z) (GaussianRationalL1.raw_den_positive v)
      (GaussianRationalMetric.qnegative_represents _ _ _ (GaussianRationalL1.raw_represents z))
      (GaussianRationalL1.raw_represents v))

theorem difference_negative_product (a z v : PTm n) : Γ ⊢[PRAAx]
    qsub a (qmul z v) ≐ qadd a (qmul (qnegative z) v) :=
  qadd_congr (.eqRefl _) (negative_product z v)

theorem shift_term_at (C N z j k r : PTm n) : Γ ⊢[PRAAx]
    inst2 (shiftBody termBody) r (data C N z j k) ≐ term C N z j k (succ r) := by
  simpa only [inst2_shiftBody] using term_at C N z j k (succ r)

theorem R_count (C N z j k m : PTm n) (hm : Γ ⊢[PRAAx] succ (monus N (j+k)) ≐ m) : Γ ⊢[PRAAx]
    R C N z j k ≐ GaussianRationalFiniteSum.sum termBody m (data C N z j k) :=
  GaussianRationalFiniteSum.sum_index_congr _ hm (.eqRefl _)

theorem R_index_congr (C N z j : PTm n) {k l : PTm n} (hk : Γ ⊢[PRAAx] k ≐ l) : Γ ⊢[PRAAx]
    R C N z j k ≐ R C N z j l :=
  GaussianRationalFiniteSum.sum_index_congr _ (congrSucc (congrMonus (.eqRefl _) (congrAdd (.eqRefl _) hk)))
    (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) hk))))

theorem constant_terms (C N z j m : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.termsEqual (shiftBody termBody) (GaussianRationalFiniteSum.multiplyBody termBody)
      m (data C N z j zero) (pairT (qnegative z) (data C N z (succ j) zero)) := by
  refine .allI (.impI ?_)
  have source : (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx]
      inst2 (shiftBody termBody) (var 0) (data (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift j) zero) ≐
        qmul (qnegative (Syn.shift z)) (term (Syn.shift C) (Syn.shift N) (Syn.shift z) (succ (Syn.shift j)) zero (var 0)) :=
    (shift_term_at _ _ _ _ _ _).eqTrans (constant_term_step _ _ _ _ _)
  have target := (GaussianRationalFiniteSum.multiply_body_at
    (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) termBody (qnegative (Syn.shift z)) (var 0)
      (data (Syn.shift C) (Syn.shift N) (Syn.shift z) (succ (Syn.shift j)) zero)).eqTrans
    (qmul_congr (.eqRefl _) (term_at _ _ _ _ _ _))
  simpa only [Syn.shift,subst_data,subst_pairT,GaussianRationalMetric.subst_qnegative,
    ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using source.eqTrans target.eqSymm

theorem R_constant (C N z j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    R C N z j zero ≐ qsub (b C N z j) (qmul z (R C N z (succ j) zero)) := by
  have count : Γ ⊢[PRAAx] monus N (j+zero) ≐ succ (monus N (succ j+zero)) :=
    ((congrMonus (.eqRefl _) (add_zero j)).eqTrans (remaining_step N j hj)).eqTrans
      (congrSucc (congrMonus (.eqRefl _) (add_zero (succ j))).eqSymm)
  have tail := (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _
    (constant_terms (Γ := Γ) C N z j (monus N (j+zero)))).eqTrans
      ((GaussianRationalFiniteSum.sum_multiply _ _ _ _).eqTrans
        (qmul_congr (.eqRefl _) (R_count C N z (succ j) zero _ count.eqSymm).eqSymm))
  exact (R_first C N z j zero).eqTrans ((qadd_congr (b_index_congr C N z (add_zero j)) tail).eqTrans
    (difference_negative_product _ _ _).eqSymm)

theorem pascal_terms (C N z j k m : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    linearTerms (shiftBody termBody) (shiftBody termBody) termBody m (data C N z j k)
      (data C N z (succ j) (pred k)) (data C N z (succ j) k) (qnegative z) := by
  refine .allI (.impI ?_)
  have ks : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift k) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hk.shift
  have source := (shift_term_at (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
    (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift j) (Syn.shift k) (var 0)).eqTrans
      ((term_pascal _ _ _ _ _ _ ks.wk).eqTrans (qadd_congr (shift_term_at _ _ _ _ _ _).eqSymm
        (qmul_congr (.eqRefl _) (term_at _ _ _ _ _ _).eqSymm)))
  simpa only [Syn.shift,subst_data,GaussianRationalMetric.subst_qnegative,PTm.subst_pred,
    ConciseIPRA.PTm.subst_succ] using source

theorem active_sum_index (N j k : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hk : Γ ⊢[PRAAx] lt k (remaining N j)) : Γ ⊢[PRAAx] lt (j+k) N := by
  change Γ ⊢[PRAAx] lt k (monus N j) at hk
  have en := natEq (eq_add_of_le (le_of_lt hj))
  have ek := natEq (eq_add_of_le hk)
  apply le_of_eq_add (d := monus (monus N j) (succ k))
  apply deriveNat
  ipra_simps
  linear_combination en+ek

theorem R_interior (C N z j k : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hk : Γ ⊢[PRAAx] le one k) (hkM : Γ ⊢[PRAAx] lt k (remaining N j)) : Γ ⊢[PRAAx]
    R C N z j k ≐ qsub (R C N z (succ j) (pred k)) (qmul z (R C N z (succ j) k)) := by
  have ek := natEq (RationalIntegerNormalization.positive_form (Γ := Γ) hk)
  have previous : Γ ⊢[PRAAx] succ j+pred k ≐ j+k := by
    apply deriveNat
    ipra_simps
    linear_combination -ek
  have next : Γ ⊢[PRAAx] succ j+k ≐ succ (j+k) := by ipra_ring
  have count : Γ ⊢[PRAAx] succ (monus N (succ j+k)) ≐ monus N (j+k) :=
    (congrSucc (congrMonus (.eqRefl _) next)).eqTrans
      (remaining_step N (j+k) (active_sum_index N j k hj hkM)).eqSymm
  have first : Γ ⊢[PRAAx] R C N z (succ j) (pred k) ≐ qadd (b C N z (j+k))
      (GaussianRationalFiniteSum.sum (shiftBody termBody) (monus N (j+k)) (data C N z (succ j) (pred k))) :=
    (R_first C N z (succ j) (pred k)).eqTrans (qadd_congr (b_index_congr C N z previous)
      (GaussianRationalFiniteSum.sum_index_congr _ (congrMonus (.eqRefl _) previous) (.eqRefl _)))
  have tail := (linear_sum _ _ _ _ _ _ _ _
    (pascal_terms C N z j k (monus N (j+k)) hk)).eqTrans
      (qadd_congr (.eqRefl _) (qmul_congr (.eqRefl _) (R_count C N z (succ j) k _ count).eqSymm))
  exact (R_first C N z j k).eqTrans ((qadd_congr (.eqRefl _) tail).eqTrans
    ((GaussianRationalSumAlgebra.qadd_associative _ _ _).eqSymm.eqTrans
      ((qadd_congr first.eqSymm (.eqRefl _)).eqTrans (difference_negative_product _ _ _).eqSymm)))

theorem R_leading (C N z j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    R C N z j (remaining N j) ≐ R C N z (succ j) (pred (remaining N j)) := by
  have en := eq_add_of_le (Γ := Γ) (le_of_lt hj)
  have em := RationalIntegerNormalization.positive_form (Γ := Γ)
    (GaussianRationalTranslationStages.remaining_positive N j hj)
  simp only [remaining] at em
  have next : Γ ⊢[PRAAx] succ j+pred (remaining N j) ≐ N := by
    change Γ ⊢[PRAAx] succ j+pred (monus N j) ≐ N
    have a := natEq en
    have b := natEq em
    apply deriveNat
    ipra_simps
    linear_combination -a-b
  exact (R_singleton C N z j (remaining N j) en.eqSymm).eqTrans
    (R_singleton C N z (succ j) _ next).eqSymm

theorem R_leading_at (C N z j k : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hk : Γ ⊢[PRAAx] k ≐ remaining N j) : Γ ⊢[PRAAx]
    R C N z j k ≐ R C N z (succ j) (pred k) :=
  (R_index_congr C N z j hk).eqTrans ((R_leading C N z j hj).eqTrans
    (R_index_congr C N z (succ j) (congrPred hk.eqSymm)))

def row (C N z j : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (remaining (Syn.shift N) (Syn.shift j))) ⟶
    GaussianTranslationCoefficientValues.coefficient (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift j) (var 0) ≐
      R (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift j) (var 0))

@[simp] theorem subst_row {m : ℕ} (σ : Fin n → PTm m) (C N z j : PTm n) :
    (row C N z j).subst σ = row (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ j) := by
  simp [row,Syn.subst_shift,Syn.shift_subst]

def rowSyntax (C N z j : PTm n) : Foundations.BoundedSyntax.BFm n := .all (succ (remaining N j))
  (.eq (GaussianTranslationCoefficientValues.coefficient (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift j) (var 0))
    (R (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift j) (var 0)))

theorem row_formula (C N z j : PTm n) : Foundations.BoundedSyntax.formula (rowSyntax C N z j) = row C N z j := by
  simp [rowSyntax,Foundations.BoundedSyntax.formula,row,Syn.shift]

theorem row_at (C N z j k : PTm n) (h : Γ ⊢[PRAAx] row C N z j)
    (hk : Γ ⊢[PRAAx] le k (remaining N j)) : Γ ⊢[PRAAx]
    GaussianTranslationCoefficientValues.coefficient C N z j k ≐ R C N z j k := by
  have rule : Γ ⊢[PRAAx] lt k (succ (remaining N j)) ⟶
      GaussianTranslationCoefficientValues.coefficient C N z j k ≐ R C N z j k := by
    simpa [row] using h.allE k
  exact .impE rule ((succ_monus_succ _ _).eqTrans hk)

theorem terminal_at (C N z k : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hk : Γ ⊢[PRAAx] le k (remaining N N)) : Γ ⊢[PRAAx]
    GaussianTranslationCoefficientValues.coefficient C N z N k ≐ R C N z N k := by
  have zeroBound := le_congr (.eqRefl _) (monus_self N) hk
  have ek : Γ ⊢[PRAAx] k ≐ zero := (monus_zero k).eqSymm.eqTrans zeroBound
  have left := (GaussianTranslationCoefficientValues.coefficient_index_congr C N z N ek).eqTrans
    (GaussianTranslationCoefficientValues.terminal_coefficient C N z hLen)
  have right := (R_index_congr C N z N ek).eqTrans (R_singleton C N z N zero (add_zero N))
  exact left.eqTrans right.eqSymm

theorem terminal_row (C N z : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx] row C N z N := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hLen.shift
  exact terminal_at _ _ _ (var 0) hs.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)

/-- The true smaller-stage row supplies only its individual actual
coefficient identities. Every branch, including j=k=0, is derived. -/
theorem backward_at (C N z j k : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] lt j N) (hk : Γ ⊢[PRAAx] le k (remaining N j))
    (hRow : Γ ⊢[PRAAx] row C N z (succ j)) : Γ ⊢[PRAAx]
    GaussianTranslationCoefficientValues.coefficient C N z j k ≐ R C N z j k := by
  refine .orE (zero_or_succ k) ?_ ?_
  · have next := row_at (Γ := (k ≐ zero)::Γ) C N z (succ j) zero hRow.wk (zero_le _)
    exact (GaussianTranslationCoefficientValues.coefficient_index_congr C N z j Prf.hyp0).eqTrans
      ((GaussianTranslationCoefficientValues.constant_coefficient C N z j hLen.wk hj.wk).eqTrans
        ((qsub_congr (.eqRefl _) (qmul_congr (.eqRefl _) next)).eqTrans
          ((R_constant C N z j hj.wk).eqSymm.eqTrans (R_index_congr C N z j Prf.hyp0.eqSymm))))
  · have kpos : (k ≐ succ (pred k))::Γ ⊢[PRAAx] le one k :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    have predRange : (k ≐ succ (pred k))::Γ ⊢[PRAAx] le (pred k) (remaining N (succ j)) :=
      (succ_monus_succ _ _).eqSymm.eqTrans
        (le_congr Prf.hyp0 (remaining_step N j hj.wk) hk.wk)
    have first := row_at C N z (succ j) (pred k) hRow.wk predRange
    refine .orE (lt_or_le k (remaining N j)) ?_ ?_
    · have nextRange : lt k (remaining N j)::(k ≐ succ (pred k))::Γ ⊢[PRAAx]
          le k (remaining N (succ j)) :=
        (succ_monus_succ _ _).eqSymm.eqTrans
          (le_congr (.eqRefl _) (remaining_step N j hj.wk.wk) Prf.hyp0)
      exact (GaussianTranslationCoefficientValues.interior_coefficient C N z j k hj.wk.wk kpos.wk Prf.hyp0).eqTrans
        ((qsub_congr first.wk (qmul_congr (.eqRefl _) (row_at _ _ _ _ _ hRow.wk.wk nextRange))).eqTrans
          (R_interior C N z j k hj.wk.wk kpos.wk Prf.hyp0).eqSymm)
    · have equalIndex : le (remaining N j) k::(k ≐ succ (pred k))::Γ ⊢[PRAAx] k ≐ remaining N j :=
        le_antisymm hk.wk.wk Prf.hyp0
      exact (GaussianTranslationCoefficientValues.leading_coefficient_at C N z j k hj.wk.wk equalIndex).eqTrans
        (first.wk.eqTrans (R_leading_at C N z j k hj.wk.wk equalIndex).eqSymm)

theorem backward_row (C N z j : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] lt j N) (hRow : Γ ⊢[PRAAx] row C N z (succ j)) : Γ ⊢[PRAAx] row C N z j := by
  refine .allI (.impI ?_)
  have ls : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hLen.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift N) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hj.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] row (Syn.shift C) (Syn.shift N) (Syn.shift z) (succ (Syn.shift j)) := by
    simpa only [Fm.shift,subst_row,ConciseIPRA.PTm.subst_succ,Syn.shift] using hRow.shift
  exact backward_at _ _ _ _ (var 0) ls.wk js.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) rs.wk

/-- Backward induction is performed by the existing actual Boolean
compiler and PRA.qfInd, with no added bounded induction principle. -/
theorem all_rows (C N z j : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] row C N z j := by
  let S := rowSyntax (Syn.shift C) (Syn.shift N) (Syn.shift z) (var 0)
  have terminal : Γ ⊢[PRAAx] (Foundations.BoundedSyntax.formula S).subst (Syn.inst N) := by
    simpa only [S,row_formula,subst_row,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using terminal_row C N z hLen
  have step : Γ ⊢[PRAAx] Foundations.BoundedSyntaxBackwardInduction.localStep S N := by
    simp only [Foundations.BoundedSyntaxBackwardInduction.localStep,S,row_formula,
      subst_row,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
    refine .allI (.impI (.impI ?_))
    have ls : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
      simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hLen.shift
    exact backward_row _ _ _ (var 0) ls.wk.wk Prf.hyp1 Prf.hyp0
  simpa only [S,row_formula,subst_row,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Foundations.BoundedSyntaxBackwardInduction.backward_induction_at S N j terminal step hj

theorem inverse_row (C N z j k : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] le j N) (hk : Γ ⊢[PRAAx] le k (remaining N j)) : Γ ⊢[PRAAx]
    GaussianTranslationCoefficientValues.coefficient C N z j k ≐ R C N z j k :=
  row_at C N z j k (all_rows C N z j hLen hj) hk

def rowSumF : PR 5 := PTm.toPR (R (var 0) (var 1) (var 2) (var 3) (var 4))
theorem program_at (C N z j k : PTm n) : Γ ⊢[PRAAx]
    PTm.app rowSumF ![C,N,z,j,k] ≐ R C N z j k := by
  simpa [rowSumF] using toPR_eq (Γ := Γ) (R (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,N,z,j,k]

theorem literal_inverse_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ le (var 3) (var 1) ⟶ le (var 4) (remaining (var 1) (var 3)) ⟶
      GaussianTranslationCoefficientValues.coefficient (var 0) (var 1) (var 2) (var 3) (var 4) ≐
        R (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (inverse_row _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem literal_binomial_row_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (PTm.app rowSumF ![(var 0),(var 1),(var 2),(var 3),(var 4)] ≐ R (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianInverseBinomialRows
