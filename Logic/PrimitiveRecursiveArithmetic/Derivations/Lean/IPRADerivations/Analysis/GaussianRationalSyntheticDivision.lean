import IPRADerivations.Analysis.GaussianSyntheticDivision
import IPRADerivations.Analysis.GaussianRationalMetric
import IPRADerivations.Analysis.GaussianRationalL1
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual canonical Gaussian-rational synthetic division

The quotient is the actual sequence of normalized rational Horner prefixes.
The runtime degree and all coefficient/point codes are internal inputs. The
local polynomial identities below are proved by positive-denominator value
composition and canonical uniqueness, retaining independently normalized
real and imaginary denominators. No polynomial evaluation identity is an
input contract.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul represents canonical qadd_canonical qmul_canonical qadd_represents qmul_represents
    represents_rescale represents_congr canonical_unique zero_represents positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub qsub_represents qsub_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal equal_of_values equal_re equal_im re_add im_add re_mul im_mul re_scale im_scale re_sub im_sub re_zero im_zero)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im scale zeroCode oneCode)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

/-- Small congruence adapters keep the fixed normalizing programs opaque. -/
theorem qadd_congr {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] qadd a b ≐ qadd a' b' := by
  ipra_congr (qadd (var 0) (var 1) : PTm 2) with [ha, hb]
theorem qmul_congr {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] qmul a b ≐ qmul a' b' := by
  ipra_congr (qmul (var 0) (var 1) : PTm 2) with [ha, hb]
theorem qsub_congr {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] qsub a b ≐ qsub a' b' := by
  ipra_congr (qsub (var 0) (var 1) : PTm 2) with [ha, hb]

theorem rescale_to (q a A t E : PTm n) (h : Γ ⊢[PRAAx] represents q a A)
    (he : Γ ⊢[PRAAx] A*t ≐ E) : Γ ⊢[PRAAx] represents q (scale t a) E :=
  represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) he (represents_rescale q a A t h)

/-- The one cubic identity needed by synthetic Horner induction. Its input
representations concern only the five arbitrary operands, never the output. -/
theorem step_from_representations (y z w r c a b d e f E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E)
    (hy : Γ ⊢[PRAAx] represents y a E) (hz : Γ ⊢[PRAAx] represents z b E)
    (hw : Γ ⊢[PRAAx] represents w d E) (hr : Γ ⊢[PRAAx] represents r e E)
    (hc : Γ ⊢[PRAAx] represents c f E) : Γ ⊢[PRAAx]
    qadd (qmul (qadd (qmul (qsub y z) w) r) y) c ≐
      qadd (qmul (qsub y z) (qadd (qmul w y) r)) (qadd (qmul r z) c) := by
  have E2 := positive_product E E hE hE
  have E3 := positive_product (E*E) E E2 hE
  have diff := qsub_represents y z a b E hE hy hz
  have fw := qmul_represents _ _ _ _ _ _ hE hE diff hw
  have r2 := represents_rescale r e E E hr
  have lhsInner := qadd_represents _ _ _ _ _ E2 fw r2
  have lhsMul := qmul_represents _ _ _ _ _ _ E2 hE lhsInner hy
  have c3 := rescale_to c f E (E*E) ((E*E)*E) hc (by ipra_ring)
  have lhs := qadd_represents _ _ _ _ _ E3 lhsMul c3
  have wy := qmul_represents _ _ _ _ _ _ hE hE hw hy
  have rhsInner := qadd_represents _ _ _ _ _ E2 wy r2
  have rhsMul0 := qmul_represents _ _ _ _ _ _ hE E2 diff rhsInner
  have rhsMul := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _)
    (mul_assoc E E E).eqSymm rhsMul0
  have rz := qmul_represents _ _ _ _ _ _ hE hE hr hz
  have c2 := represents_rescale c f E E hc
  have tail := qadd_represents _ _ _ _ _ E2 rz c2
  have tail3 := represents_rescale _ _ (E*E) E tail
  have rhs := qadd_represents _ _ _ _ _ E3 rhsMul tail3
  apply canonical_unique _ _ _ _ (qadd_canonical _ _) (qadd_canonical _ _) E3 (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values
  · simp only [re_add,im_add,re_mul,im_mul,re_sub,im_sub,re_scale,im_scale]
    ipra_simps
    ring
  · simp only [re_add,im_add,re_mul,im_mul,re_sub,im_sub,re_scale,im_scale]
    ipra_simps
    ring

/-- All five actual operand denominators are computed from their decoded
scalar codes. The input arity is fixed; the polynomial degree is unrestricted. -/
def remainingDen (a b c d : PTm n) : PTm n := rawDen a*rawDen b*rawDen c*rawDen d

theorem remaining_den_positive (a b c d : PTm n) : Γ ⊢[PRAAx] le one (remainingDen a b c d) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _ (raw_den_positive a) (raw_den_positive b))
    (raw_den_positive c)) (raw_den_positive d)

theorem synthetic_step_identity (y z w r c : PTm n) : Γ ⊢[PRAAx]
    qadd (qmul (qadd (qmul (qsub y z) w) r) y) c ≐
      qadd (qmul (qsub y z) (qadd (qmul w y) r)) (qadd (qmul r z) c) := by
  let E := rawDen y*remainingDen z w r c
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (raw_den_positive y) (remaining_den_positive z w r c)
  have hy := rescale_to y (rawGaussian y) (rawDen y) (remainingDen z w r c) E (raw_represents (Γ := Γ) y) (.eqRefl _)
  have hz := rescale_to z (rawGaussian z) (rawDen z) (remainingDen y w r c) E (raw_represents (Γ := Γ) z)
    (by unfold E remainingDen; ipra_ring)
  have hw := rescale_to w (rawGaussian w) (rawDen w) (remainingDen y z r c) E (raw_represents (Γ := Γ) w)
    (by unfold E remainingDen; ipra_ring)
  have hr := rescale_to r (rawGaussian r) (rawDen r) (remainingDen y z w c) E (raw_represents (Γ := Γ) r)
    (by unfold E remainingDen; ipra_ring)
  have hc := rescale_to c (rawGaussian c) (rawDen c) (remainingDen y z w r) E (raw_represents (Γ := Γ) c)
    (by unfold E remainingDen; ipra_ring)
  exact step_from_representations _ _ _ _ _ _ _ _ _ _ E hE hy hz hw hr hc

theorem qzero_canonical : Γ ⊢[PRAAx] canonical (qzero : PTm n) :=
  GaussianRationalHorner.ofGaussian_canonical zeroCode one (le_refl _)

theorem qmul_zero_left (q : PTm n) : Γ ⊢[PRAAx] qmul qzero q ≐ qzero := by
  have d := raw_den_positive (Γ := Γ) q
  have h := qmul_represents qzero q zeroCode (rawGaussian q) (rawDen q) (rawDen q)
    d d (zero_represents _) (raw_represents q)
  exact canonical_unique _ _ _ _ (qmul_canonical _ _) qzero_canonical (positive_product _ _ d d)
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.zero_mul _) (.eqRefl _) h) (zero_represents _)

theorem qmul_zero_right (q : PTm n) : Γ ⊢[PRAAx] qmul q qzero ≐ qzero := by
  have d := raw_den_positive (Γ := Γ) q
  have h := qmul_represents q qzero (rawGaussian q) zeroCode (rawDen q) (rawDen q)
    d d (raw_represents q) (zero_represents _)
  exact canonical_unique _ _ _ _ (qmul_canonical _ _) qzero_canonical (positive_product _ _ d d)
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.mul_zero _) (.eqRefl _) h) (zero_represents _)

theorem qzero_add (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] qadd qzero q ≐ q := by
  have d := raw_den_positive (Γ := Γ) q
  have h := qadd_represents qzero q zeroCode (rawGaussian q) (rawDen q) d (zero_represents _) (raw_represents q)
  apply canonical_unique _ _ _ _ (qadd_canonical _ _) hq d (hrv := raw_represents q)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := h)
  apply equal_of_values <;> simp only [re_add,im_add,re_zero,im_zero] <;> ring

theorem qadd_sub_cancel (q r : PTm n) (hr : Γ ⊢[PRAAx] canonical r) : Γ ⊢[PRAAx]
    qsub (qadd q r) q ≐ r := by
  have d := positive_product _ _ (raw_den_positive (Γ := Γ) q) (raw_den_positive r)
  have hq := represents_rescale q (rawGaussian q) (rawDen q) (rawDen r) (raw_represents (Γ := Γ) q)
  have hrv := rescale_to r (rawGaussian r) (rawDen r) (rawDen q) (rawDen q*rawDen r)
    (raw_represents (Γ := Γ) r) (mul_comm _ _)
  have h := qsub_represents _ _ _ _ _ d (qadd_represents _ _ _ _ _ d hq hrv) hq
  apply canonical_unique _ _ _ _ (qsub_canonical _ _) hr d (hrv := hrv)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := h)
  apply equal_of_values <;> simp only [re_sub,im_sub,re_add,im_add] <;> ring

/-! The actual rational quotient producer and its literal local recurrence. -/

def quotientBody : PTm 2 := GaussianRationalHorner.horner
  (fstT (var 1)) (sndT (var 1)) (succ (var 0))
def quotient (C z N : PTm n) : PTm n := sequence quotientBody N (pairT C z)
def remainder (C z : PTm n) : PTm n := GaussianRationalHorner.evaluate C z

@[simp] theorem subst_quotient {m : ℕ} (σ : Fin n → PTm m) (C z N : PTm n) :
    Syn.subst σ (quotient C z N) = quotient (Syn.subst σ C) (Syn.subst σ z) (Syn.subst σ N) := by simp [quotient]
@[simp] theorem subst_remainder {m : ℕ} (σ : Fin n → PTm m) (C z : PTm n) :
    Syn.subst σ (remainder C z) = remainder (Syn.subst σ C) (Syn.subst σ z) := by simp [remainder]

theorem quotient_body_at (C z i : PTm n) : Γ ⊢[PRAAx]
    inst2 quotientBody i (pairT C z) ≐ GaussianRationalHorner.horner C z (succ i) := by
  simp only [quotientBody,inst2,GaussianRationalHorner.subst_horner,subst_fstT,subst_sndT,
    ConciseIPRA.PTm.subst_succ,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrAp3 GaussianRationalHorner.hornerF (.eqRefl _) (fst_pair _ _) (snd_pair _ _)

theorem quotient_length (C z N : PTm n) : Γ ⊢[PRAAx] length (quotient C z N) ≐ N := sequence_length _ _ _
theorem quotient_lookup (C z N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    entry (quotient C z N) i ≐ GaussianRationalHorner.horner C z (succ i) :=
  (sequence_decode quotientBody hi).eqTrans (quotient_body_at C z i)

theorem quotient_coefficient_canonical (C z N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] canonical (entry (quotient C z N) i) :=
  GaussianRationalHorner.canonical_congr (quotient_lookup C z N i hi)
    (GaussianRationalHorner.horner_canonical C z (succ i))

theorem quotient_recurrence (C z N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    entry (quotient C z N) i ≐
      qadd (qmul (GaussianRationalHorner.horner C z i) z) (entry C i) :=
  (quotient_lookup C z N i hi).eqTrans (GaussianRationalHorner.horner_succ C z i)

theorem quotient_successor (C z N i : PTm n) (hi : Γ ⊢[PRAAx] lt (succ i) N) : Γ ⊢[PRAAx]
    entry (quotient C z N) (succ i) ≐ qadd (qmul (entry (quotient C z N) i) z) (entry C (succ i)) :=
  (quotient_recurrence C z N (succ i) hi).eqTrans
    (qadd_congr (qmul_congr (quotient_lookup C z N i (lt_of_le_of_lt (le_succ_self _) hi)).eqSymm (.eqRefl _)) (.eqRefl _))

theorem remainder_recurrence (C z N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    remainder C z ≐ qadd (qmul (entry (quotient C z N) (pred N)) z) (entry C N) := by
  have range : Γ ⊢[PRAAx] lt (pred N) N := lt_congr (.eqRefl _)
    (RationalIntegerNormalization.positive_form hN).eqSymm (le_refl _)
  have previous : Γ ⊢[PRAAx] entry (quotient C z N) (pred N) ≐ GaussianRationalHorner.horner C z N :=
    (quotient_lookup C z N (pred N) range).eqTrans
      (congrAp3 GaussianRationalHorner.hornerF (RationalIntegerNormalization.positive_form hN).eqSymm (.eqRefl _) (.eqRefl _))
  exact (congrAp3 GaussianRationalHorner.hornerF hC (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalHorner.horner_succ C z N).eqTrans
      (qadd_congr (qmul_congr previous.eqSymm (.eqRefl _)) (.eqRefl _)))

/-! Complete evaluation identity by QF induction on runtime prefixes. -/

theorem first_prefix (C z : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.horner C z (succ zero) ≐ qadd qzero (entry C zero) :=
  (GaussianRationalHorner.horner_succ C z zero).eqTrans
    ((qadd_congr (qmul_congr (GaussianRationalHorner.horner_zero C z) (.eqRefl _)) (.eqRefl _)).eqTrans
      (qadd_congr (qmul_zero_left z) (.eqRefl _)))

def prefixLaw (C z y N k : PTm n) : Fm PTm n := le k N ⟶
  GaussianRationalHorner.horner C y (succ k) ≐
    qadd (qmul (qsub y z) (GaussianRationalHorner.horner (quotient C z N) y k))
      (GaussianRationalHorner.horner C z (succ k))

@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (C z y N k : PTm n) :
    (prefixLaw C z y N k).subst σ = prefixLaw (Syn.subst σ C) (Syn.subst σ z)
      (Syn.subst σ y) (Syn.subst σ N) (Syn.subst σ k) := by simp [prefixLaw]

theorem prefix_zero (C z y N : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.horner C y (succ zero) ≐
      qadd (qmul (qsub y z) (GaussianRationalHorner.horner (quotient C z N) y zero))
        (GaussianRationalHorner.horner C z (succ zero)) := by
  have rhs : Γ ⊢[PRAAx]
      qadd (qmul (qsub y z) (GaussianRationalHorner.horner (quotient C z N) y zero))
        (GaussianRationalHorner.horner C z (succ zero)) ≐ qadd qzero (entry C zero) :=
    (qadd_congr (qmul_congr (.eqRefl _) (GaussianRationalHorner.horner_zero _ _)) (first_prefix C z)).eqTrans
      ((qadd_congr (qmul_zero_right _) (.eqRefl _)).eqTrans
        (qzero_add _ (qadd_canonical _ _)))
  exact (first_prefix C y).eqTrans rhs.eqSymm

theorem prefix_step (C z y N k : PTm n) (hk : Γ ⊢[PRAAx] lt k N)
    (ih : Γ ⊢[PRAAx] GaussianRationalHorner.horner C y (succ k) ≐
      qadd (qmul (qsub y z) (GaussianRationalHorner.horner (quotient C z N) y k))
        (GaussianRationalHorner.horner C z (succ k))) : Γ ⊢[PRAAx]
    GaussianRationalHorner.horner C y (succ (succ k)) ≐
      qadd (qmul (qsub y z) (GaussianRationalHorner.horner (quotient C z N) y (succ k)))
        (GaussianRationalHorner.horner C z (succ (succ k))) := by
  have hq : Γ ⊢[PRAAx] GaussianRationalHorner.horner (quotient C z N) y (succ k) ≐
      qadd (qmul (GaussianRationalHorner.horner (quotient C z N) y k) y)
        (GaussianRationalHorner.horner C z (succ k)) :=
    (GaussianRationalHorner.horner_succ _ _ _).eqTrans
      (qadd_congr (.eqRefl _) (quotient_lookup C z N k hk))
  exact (GaussianRationalHorner.horner_succ C y (succ k)).eqTrans
    ((qadd_congr (qmul_congr ih (.eqRefl _)) (.eqRefl _)).eqTrans
      ((synthetic_step_identity y z (GaussianRationalHorner.horner (quotient C z N) y k)
        (GaussianRationalHorner.horner C z (succ k)) (entry C (succ k))).eqTrans
          (qadd_congr (qmul_congr (.eqRefl _) hq.eqSymm) (GaussianRationalHorner.horner_succ C z (succ k)).eqSymm)))

theorem synthetic_prefix (C z y N k : PTm n) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.horner C y (succ k) ≐
      qadd (qmul (qsub y z) (GaussianRationalHorner.horner (quotient C z N) y k))
        (GaussianRationalHorner.horner C z (succ k)) := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift z) (Syn.shift y) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (prefix_zero C z y N)
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let I := prefixLaw (Syn.shift C) (Syn.shift z) (Syn.shift y) (Syn.shift N) (var 0)
      let Δ := le (succ (var 0)) (Syn.shift N) :: I :: Γ.map Fm.shift
      exact prefix_step _ _ _ _ _ (Prf.hyp0 (Ax := PRAAx) (Γ := I :: Γ.map Fm.shift))
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw C z y N k := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all
  exact .impE rule hk

/-- Literal canonical-code synthetic division at an arbitrary rational y.
All actual arithmetic operations and both actual Horner evaluations occur. -/
theorem division_evaluation (C z y N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate C y ≐
      qadd (qmul (qsub y z) (GaussianRationalHorner.evaluate (quotient C z N) y)) (remainder C z) := by
  have start : Γ ⊢[PRAAx] GaussianRationalHorner.evaluate C y ≐ GaussianRationalHorner.horner C y (succ N) :=
    congrAp3 GaussianRationalHorner.hornerF hC (.eqRefl _) (.eqRefl _)
  have q : Γ ⊢[PRAAx] GaussianRationalHorner.horner (quotient C z N) y N ≐ GaussianRationalHorner.evaluate (quotient C z N) y :=
    congrAp3 GaussianRationalHorner.hornerF (quotient_length C z N).eqSymm (.eqRefl _) (.eqRefl _)
  have r : Γ ⊢[PRAAx] GaussianRationalHorner.horner C z (succ N) ≐ remainder C z :=
    congrAp3 GaussianRationalHorner.hornerF hC.eqSymm (.eqRefl _) (.eqRefl _)
  exact start.eqTrans ((synthetic_prefix C z y N N (le_refl _)).eqTrans (qadd_congr (qmul_congr (.eqRefl _) q) r))

/-- Every interior coefficient satisfies the exact expanded coefficient
identity for (X−z)Q+r. Canonical storage is needed only to recover that input
coefficient's literal code, rather than its rational value. -/
theorem coefficient_inside (C z N i : PTm n) (hi : Γ ⊢[PRAAx] lt (succ i) N)
    (hCanonical : Γ ⊢[PRAAx] canonical (entry C (succ i))) : Γ ⊢[PRAAx]
    qsub (entry (quotient C z N) (succ i)) (qmul (entry (quotient C z N) i) z) ≐ entry C (succ i) :=
  (qsub_congr (quotient_successor C z N i hi) (.eqRefl _)).eqTrans (qadd_sub_cancel _ _ hCanonical)

theorem coefficient_tail (C z N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hN : Γ ⊢[PRAAx] le one N) (hCanonical : Γ ⊢[PRAAx] canonical (entry C N)) : Γ ⊢[PRAAx]
    qsub (remainder C z) (qmul (entry (quotient C z N) (pred N)) z) ≐ entry C N :=
  (qsub_congr (remainder_recurrence C z N hC hN) (.eqRefl _)).eqTrans (qadd_sub_cancel _ _ hCanonical)

def qone : PTm n := GaussianRationalHorner.ofGaussian oneCode one
@[simp] theorem subst_qone {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (qone : PTm n) = (qone : PTm m) := by simp [qone]

theorem qone_canonical : Γ ⊢[PRAAx] canonical (qone : PTm n) :=
  GaussianRationalHorner.ofGaussian_canonical oneCode one (le_refl _)

theorem quotient_leading (C z N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hCanonical : Γ ⊢[PRAAx] canonical (entry C zero)) : Γ ⊢[PRAAx]
    entry (quotient C z N) zero ≐ entry C zero :=
  (quotient_lookup C z N zero hN).eqTrans ((first_prefix C z).eqTrans (qzero_add _ hCanonical))

/-- The actual normalized quotient remains monic of degree N−1, with no
external degree cutoff. N=1 returns a monic constant polynomial. -/
theorem quotient_monic (C z N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hMonic : Γ ⊢[PRAAx] entry C zero ≐ qone) : Γ ⊢[PRAAx]
    length (quotient C z N) ≐ succ (pred N) ⋏ (entry (quotient C z N) zero ≐ qone) :=
  .andI ((quotient_length C z N).eqTrans (RationalIntegerNormalization.positive_form hN))
    ((quotient_lookup C z N zero hN).eqTrans ((first_prefix C z).eqTrans
      ((qadd_congr (.eqRefl _) hMonic).eqTrans (qzero_add qone qone_canonical))))

/-- Canonical normalized storage of every actual quotient coefficient is
proved, so the quotient can be passed directly to the next deflation stage. -/
def canonicalCoefficients (C : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift C)) ⟶ canonical (entry (Syn.shift C) (var 0)))

@[simp] theorem subst_canonicalCoefficients {m : ℕ} (σ : Fin n → PTm m) (C : PTm n) :
    (canonicalCoefficients C).subst σ = canonicalCoefficients (Syn.subst σ C) := by
  simp [canonicalCoefficients,Syn.subst_shift,Syn.shift_subst]

theorem canonical_coefficient_at (C i : PTm n) (h : Γ ⊢[PRAAx] canonicalCoefficients C)
    (hi : Γ ⊢[PRAAx] lt i (length C)) : Γ ⊢[PRAAx] canonical (entry C i) := by
  have rule : Γ ⊢[PRAAx] lt i (length C) ⟶ canonical (entry C i) := by
    simpa only [canonicalCoefficients,Fm.subst_imp,subst_lt,subst_length,GaussianRationalHorner.subst_canonical,
      subst_entry,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE i h
  exact .impE rule hi

theorem quotient_canonical (C z N : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (quotient C z N) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (quotient C z N))) :: Γ.map Fm.shift
  have inputRange : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift (quotient C z N))) := Prf.hyp0
  have range : Δ ⊢[PRAAx] lt (var 0) (Syn.shift N) :=
    lt_congr (.eqRefl _) (quotient_length (Syn.shift C) (Syn.shift z) (Syn.shift N))
      (by simpa only [Δ,Syn.shift,subst_quotient] using inputRange)
  simpa only [Δ,Syn.shift,subst_quotient] using
    quotient_coefficient_canonical (Syn.shift C) (Syn.shift z) (Syn.shift N) (var 0) range

/-- The canonical unit is the same literal real-one/imaginary-zero code
already used by the rational root-product coefficient producer. -/
theorem qone_standard : Γ ⊢[PRAAx] (qone : PTm n) ≐ GaussianRationalRootProduct.rationalOne := by
  have hr : Γ ⊢[PRAAx] ZT.eq (re (oneCode : PTm n)) (ZT.ofNat one*ZT.natLit 1) := by
    apply ZT.derive
    rw [GaussianRootAlgebra.re_one]
    ipra_simps
    ring
  have hi : Γ ⊢[PRAAx] ZT.eq (im (oneCode : PTm n)) (ZT.ofNat one*ZT.natLit 0) := by
    apply ZT.derive
    rw [GaussianRootAlgebra.im_one]
    ipra_simps
    ring
  exact congrPairT (RationalIntegerNormalization.normalize_integer _ _ _ (le_refl one) hr)
    (RationalIntegerNormalization.normalize_integer _ _ _ (le_refl one) hi)

/-! The actual fixed PR3 output contains the normalized quotient list and
actual input-polynomial evaluation remainder. -/

def output (C z N : PTm n) : PTm n := pairT (quotient C z N) (remainder C z)
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C z N : PTm n) : PTm n := ap3 outputF C z N

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C z N : PTm n) :
    Syn.subst σ (output C z N) = output (Syn.subst σ C) (Syn.subst σ z) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C z N : PTm n) :
    Syn.subst σ (run C z N) = run (Syn.subst σ C) (Syn.subst σ z) (Syn.subst σ N) := by simp [run]

theorem program_at (C z N : PTm n) : Γ ⊢[PRAAx] run C z N ≐ output C z N := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,z,N]
theorem output_quotient (C z N : PTm n) : Γ ⊢[PRAAx] fstT (run C z N) ≐ quotient C z N :=
  (congrFst (program_at C z N)).eqTrans (fst_pair _ _)
theorem output_remainder (C z N : PTm n) : Γ ⊢[PRAAx] sndT (run C z N) ≐ GaussianRationalHorner.evaluate C z :=
  (congrSnd (program_at C z N)).eqTrans (snd_pair _ _)

theorem rational_synthetic_division_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 3) ⟶
      (GaussianRationalHorner.evaluate (var 0) (var 2) ≐
        qadd (qmul (qsub (var 2) (var 1)) (GaussianRationalHorner.evaluate (quotient (var 0) (var 1) (var 3)) (var 2)))
          (remainder (var 0) (var 1)))) :=
  closeUniv 4 (.impI (division_evaluation _ _ _ _ Prf.hyp0))

theorem rational_synthetic_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 2) ⟶
      ((entry (quotient (var 0) (var 1) (var 2)) (var 3) ≐
        qadd (qmul (GaussianRationalHorner.horner (var 0) (var 1) (var 3)) (var 1)) (entry (var 0) (var 3))) ⋏
        canonical (entry (quotient (var 0) (var 1) (var 2)) (var 3)))) :=
  closeUniv 4 (.impI (.andI (quotient_recurrence _ _ _ _ Prf.hyp0) (quotient_coefficient_canonical _ _ _ _ Prf.hyp0)))

theorem rational_synthetic_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 2) ⟶ le one (var 2) ⟶ canonicalCoefficients (var 0) ⟶
      ((lt (succ (var 3)) (var 2) ⟶
        (qsub (entry (quotient (var 0) (var 1) (var 2)) (succ (var 3)))
          (qmul (entry (quotient (var 0) (var 1) (var 2)) (var 3)) (var 1)) ≐ entry (var 0) (succ (var 3)))) ⋏
        (qsub (remainder (var 0) (var 1))
          (qmul (entry (quotient (var 0) (var 1) (var 2)) (pred (var 2))) (var 1)) ≐ entry (var 0) (var 2)))) := by
  apply closeUniv 4
  refine .impI (.impI (.impI (.andI (.impI ?_) ?_)))
  · exact coefficient_inside _ _ _ _ Prf.hyp0 (canonical_coefficient_at _ _ Prf.hyp1
      (lt_congr (.eqRefl _) Prf.hyp0.wk.wk.wk.eqSymm (lt_of_lt_of_le Prf.hyp0 (le_succ_self _))))
  · exact coefficient_tail _ _ _ Prf.hyp0.wk.wk Prf.hyp1
      (canonical_coefficient_at _ _ Prf.hyp0 (lt_congr (.eqRefl _) Prf.hyp0.wk.wk.eqSymm (le_refl _)))

theorem rational_synthetic_monic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ (entry (var 0) zero ≐ qone) ⟶
      (length (quotient (var 0) (var 1) (var 2)) ≐ succ (pred (var 2)) ⋏
        (entry (quotient (var 0) (var 1) (var 2)) zero ≐ qone))) :=
  closeUniv 3 (.impI (.impI (quotient_monic _ _ _ Prf.hyp1 Prf.hyp0)))

theorem rational_synthetic_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((fstT (run (var 0) (var 1) (var 2)) ≐ quotient (var 0) (var 1) (var 2)) ⋏
      ((sndT (run (var 0) (var 1) (var 2)) ≐ GaussianRationalHorner.evaluate (var 0) (var 1)) ⋏
        ((length (quotient (var 0) (var 1) (var 2)) ≐ var 2) ⋏ canonicalCoefficients (quotient (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.andI (output_quotient _ _ _) (.andI (output_remainder _ _ _) (.andI (quotient_length _ _ _) (quotient_canonical _ _ _))))

end LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
