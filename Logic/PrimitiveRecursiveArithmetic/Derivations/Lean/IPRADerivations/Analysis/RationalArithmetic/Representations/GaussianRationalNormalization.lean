import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootAlgebra
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalIntegerNormalization
import IPRADerivations.Analysis.Optimization.RationalArgmin
import IPRADerivations.Foundations.SequenceComposition

/-!
# Actual common-denominator conversion of Gaussian rational input lists

A Gaussian rational point is the pair of its real and imaginary scalar
rational codes, with independently positive predecessor-stored denominators.
The actual product of every component denominator is positive. Exact integer
quotients by each original component denominator produce Gaussian integer
numerators preserving the original values. No denominator, divisibility or
output-preservation assertion is an input contract.

The general list slice has runtime start and count. The joint frontend
computes one pool from two supplied point lists and a query point, so both
root lists and the query share one computed positive scale. Arbitrary signed
and noncanonical input numerator pairs, and empty input lists, are allowed.
This is an input adapter for finite-demand Section 4, not product stability.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf subst_numeratorOf subst_denominatorOf)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im code eval_re_code eval_im_code)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr append append_length append_left append_right)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd' dvd_trans')
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

inductive Component | real | imag

def scalar (s : Component) (z : PTm n) : PTm n := match s with
  | .real => fstT z
  | .imag => sndT z
def part (s : Component) (z : PTm n) : ZT n := match s with
  | .real => re z
  | .imag => im z

@[simp] theorem subst_scalar {m : ℕ} (σ : Fin n → PTm m) (s : Component) (z : PTm n) :
    Syn.subst σ (scalar s z) = scalar s (Syn.subst σ z) := by cases s <;> simp [scalar]
@[simp] theorem subst_part {m : ℕ} (σ : Fin n → PTm m) (s : Component) (z : PTm n) :
    (part s z).subst σ = part s (Syn.subst σ z) := by cases s <;> simp [part]

theorem scalar_congr (s : Component) {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] scalar s a ≐ scalar s b := by cases s; exact congrFst h; exact congrSnd h

def pointDenominator (z : PTm n) : PTm n := denominatorOf (fstT z)*denominatorOf (sndT z)
def denominatorBody : PTm 2 := pointDenominator (entry (var 1) (var 0))
def denominator (P : PTm n) : PTm n := ap2 (prodF denominatorBody) (length P) P

@[simp] theorem subst_pointDenominator {m : ℕ} (σ : Fin n → PTm m) (z : PTm n) :
    Syn.subst σ (pointDenominator z) = pointDenominator (Syn.subst σ z) := by
  simp only [pointDenominator,PTm.subst_mul,subst_denominatorOf,subst_fstT,subst_sndT]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (P : PTm n) :
    Syn.subst σ (denominator P) = denominator (Syn.subst σ P) := by
  simp only [denominator,subst_ap2,subst_length]

@[simp] theorem denominatorBody_at (i P : PTm n) : inst2 denominatorBody i P = pointDenominator (entry P i) := by
  simp only [denominatorBody,inst2,subst_pointDenominator,subst_entry,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]

theorem point_denominator_positive (z : PTm n) : Γ ⊢[PRAAx] le one (pointDenominator z) :=
  le_congr (one_mul one) (.eqRefl _)
    (le_mul_mono (RationalArgmin.denominator_positive _) (RationalArgmin.denominator_positive _))

theorem denominatorBody_positive (i P : PTm n) : Γ ⊢[PRAAx]
    inst2 denominatorBody i P ≐ succ (PTm.pred (inst2 denominatorBody i P)) := by
  rw [denominatorBody_at]
  exact RationalIntegerNormalization.positive_form (point_denominator_positive _)

theorem denominator_positive (P : PTm n) : Γ ⊢[PRAAx] le one (denominator P) := by
  have pos : Γ ⊢[PRAAx] denominator P ≐ succ (PTm.pred (denominator P)) := by
    apply prod_pos_bounded denominatorBody P (length P)
    exact .allI (.impI (denominatorBody_positive _ _))
  exact le_congr (.eqRefl _) pos.eqSymm (zero_lt_succ _)

theorem denominator_empty (P : PTm n) (h : Γ ⊢[PRAAx] length P ≐ zero) : Γ ⊢[PRAAx] denominator P ≐ one :=
  (congrAp2 (prodF denominatorBody) h (.eqRefl _)).eqTrans (prod_zero _ _)

/-- This is the actual integer quotient D/d, not a supplied cofactor. -/
def cofactor (s : Component) (P j : PTm n) : PTm n := quo (denominator P) (denominatorOf (scalar s (entry P j)))
def clearNumerator (s : Component) (P j : PTm n) : ZT n :=
  numeratorOf (scalar s (entry P j))*ZT.ofNat (cofactor s P j)
def clearPoint (P j : PTm n) : PTm n := code (clearNumerator .real P j) (clearNumerator .imag P j)

@[simp] theorem subst_cofactor {m : ℕ} (σ : Fin n → PTm m) (s : Component) (P j : PTm n) :
    Syn.subst σ (cofactor s P j) = cofactor s (Syn.subst σ P) (Syn.subst σ j) := by
  simp only [cofactor,subst_ap2,subst_denominator,subst_denominatorOf,subst_scalar,subst_entry]
@[simp] theorem subst_clearNumerator {m : ℕ} (σ : Fin n → PTm m) (s : Component) (P j : PTm n) :
    (clearNumerator s P j).subst σ = clearNumerator s (Syn.subst σ P) (Syn.subst σ j) := by
  simp only [clearNumerator,ZT.subst_mul,subst_numeratorOf,subst_scalar,subst_entry,ZT.subst_ofNat,subst_cofactor]
@[simp] theorem subst_clearPoint {m : ℕ} (σ : Fin n → PTm m) (P j : PTm n) :
    Syn.subst σ (clearPoint P j) = clearPoint (Syn.subst σ P) (Syn.subst σ j) := by
  simp only [clearPoint,ComplexLogarithmRemainder.subst_code,subst_clearNumerator]

/-- Divisibility follows from the actual product, for either independently
decoded component denominator. -/
theorem cofactor_clears (s : Component) (P j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length P)) :
    Γ ⊢[PRAAx] denominatorOf (scalar s (entry P j))*cofactor s P j ≐ denominator P := by
  have pointDivides : Γ ⊢[PRAAx] dvd (pointDenominator (entry P j)) (denominator P) := by
    simpa only [denominator,denominatorBody_at] using Probability.TowerCommonDen.dvd_prod_term denominatorBody
      (x := P) (M := length P) (i := j) (denominatorBody_positive _ _) hj
  have componentDivides : Γ ⊢[PRAAx] dvd (denominatorOf (scalar s (entry P j))) (pointDenominator (entry P j)) := by
    cases s
    · exact dvd_of_eq' (RationalIntegerNormalization.positive_form (RationalArgmin.denominator_positive _)) (.eqRefl _)
    · exact dvd_of_eq' (RationalIntegerNormalization.positive_form (RationalArgmin.denominator_positive _)) (mul_comm _ _)
  exact (eq_of_dvd' (RationalIntegerNormalization.positive_form (RationalArgmin.denominator_positive _))
    (dvd_trans' (RationalIntegerNormalization.positive_form (RationalArgmin.denominator_positive _))
      (RationalIntegerNormalization.positive_form (point_denominator_positive _)) componentDivides pointDivides)).eqSymm

theorem clearPoint_value (s : Component) (P j : PTm n) :
    ZT.toZ Γ (part s (clearPoint P j)) = ZT.toZ Γ (clearNumerator s P j) := by
  cases s
  · exact eval_re_code _ _
  · exact eval_im_code _ _

theorem component_clearing (s : Component) (P j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length P)) : Γ ⊢[PRAAx]
    ZT.eq (part s (clearPoint P j)*ZT.ofNat (denominatorOf (scalar s (entry P j))))
      (numeratorOf (scalar s (entry P j))*ZT.ofNat (denominator P)) := by
  apply ZT.derive
  have factor := natEq (cofactor_clears (Γ := Γ) s P j hj)
  rw [ZT.toZ_mul,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_ofNat,clearPoint_value]
  simp only [clearNumerator,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [Q.mk_mul,map_mul] at factor
  linear_combination ZT.toZ Γ (numeratorOf (scalar s (entry P j)))*factor

/-- Value preservation transfers to an original input point identified by
an actual list lookup. The lookup equality is not a value/correctness premise. -/
theorem component_clearing_at (s : Component) (P j z : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length P)) (hz : Γ ⊢[PRAAx] entry P j ≐ z) : Γ ⊢[PRAAx]
    ZT.eq (part s (clearPoint P j)*ZT.ofNat (denominatorOf (scalar s z)))
      (numeratorOf (scalar s z)*ZT.ofNat (denominator P)) := by
  apply ZT.derive
  have value := ZT.toZ_eq (component_clearing (Γ := Γ) s P j hj)
  have component := scalar_congr s hz
  have d := natEq (congrSucc (congrSnd component))
  have p := natEq (congrFst (congrFst component))
  have q := natEq (congrSnd (congrFst component))
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at value ⊢
  simp only [numeratorOf,ZT.toZ] at value ⊢
  change 𝔞(denominatorOf (scalar s (entry P j))) = 𝔞(denominatorOf (scalar s z)) at d
  rw [d,p,q] at value
  exact value

/-- Arbitrary runtime slice of the actual normalized point pool. -/
def numeratorBody : PTm 2 := clearPoint (fstT (var 1)) (sndT (var 1)+var 0)
def numeratorList (P start N : PTm n) : PTm n := sequence numeratorBody N (pairT P start)

@[simp] theorem subst_numeratorList {m : ℕ} (σ : Fin n → PTm m) (P start N : PTm n) :
    Syn.subst σ (numeratorList P start N) = numeratorList (Syn.subst σ P) (Syn.subst σ start) (Syn.subst σ N) := by
  simp only [numeratorList,subst_sequence,subst_pairT]

theorem numeratorBody_at (P start i : PTm n) : Γ ⊢[PRAAx]
    inst2 numeratorBody i (pairT P start) ≐ clearPoint P (start+i) := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (clearPoint (var 0) (var 1) : PTm 2)
    (σ := ![fstT (pairT P start),sndT (pairT P start)+i]) (σ' := ![P,start+i])
    (fun j => by fin_cases j; exact fst_pair _ _; exact congrAdd (snd_pair _ _) (.eqRefl _))
  simpa only [numeratorBody,inst2,subst_clearPoint,subst_fstT,subst_sndT,PTm.subst_add,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using e

theorem numeratorList_length (P start N : PTm n) : Γ ⊢[PRAAx] length (numeratorList P start N) ≐ N := sequence_length _ _ _
theorem numeratorList_lookup (P start N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    entry (numeratorList P start N) i ≐ clearPoint P (start+i) :=
  (sequence_decode numeratorBody hi).eqTrans (numeratorBody_at P start i)

/-- Cross-value presentation of one Gaussian rational point at a positive
common denominator. Equality is of signed values, not raw input codes. -/
def clearing (D g z : PTm n) : Fm PTm n :=
  ZT.eq (re g*ZT.ofNat (denominatorOf (fstT z))) (numeratorOf (fstT z)*ZT.ofNat D) ⋏
  ZT.eq (im g*ZT.ofNat (denominatorOf (sndT z))) (numeratorOf (sndT z)*ZT.ofNat D)

@[simp] theorem subst_clearing {m : ℕ} (σ : Fin n → PTm m) (D g z : PTm n) :
    (clearing D g z).subst σ = clearing (Syn.subst σ D) (Syn.subst σ g) (Syn.subst σ z) := by
  simp only [clearing,Fm.subst_and,ZT.subst_eq,ZT.subst_mul,ZT.subst_ofNat,
    ComplexLogarithmRemainder.subst_re,ComplexLogarithmRemainder.subst_im,
    subst_denominatorOf,subst_numeratorOf,subst_fstT,subst_sndT]

theorem clearPoint_clearing (P j z : PTm n) (hj : Γ ⊢[PRAAx] lt j (length P))
    (hz : Γ ⊢[PRAAx] entry P j ≐ z) : Γ ⊢[PRAAx] clearing (denominator P) (clearPoint P j) z :=
  .andI (component_clearing_at .real P j z hj hz) (component_clearing_at .imag P j z hj hz)

theorem clearing_congr {D g g' z : PTm n} (h : Γ ⊢[PRAAx] g ≐ g')
    (hv : Γ ⊢[PRAAx] clearing D g' z) : Γ ⊢[PRAAx] clearing D g z := by
  have values := GaussianRootAlgebra.values_of_code h
  have r := ZT.toZ_eq (Prf.andE₁ hv)
  have i := ZT.toZ_eq (Prf.andE₂ hv)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at r i
  refine .andI (ZT.derive ?_) (ZT.derive ?_)
  · rw [ZT.toZ_mul,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_ofNat,values.1]
    exact r
  · rw [ZT.toZ_mul,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_ofNat,values.2]
    exact i

theorem numeratorList_clearing (P start N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N)
    (hp : Γ ⊢[PRAAx] lt (start+i) (length P)) : Γ ⊢[PRAAx]
    clearing (denominator P) (entry (numeratorList P start N) i) (entry P (start+i)) :=
  clearing_congr (numeratorList_lookup P start N i hi)
    (clearPoint_clearing P (start+i) (entry P (start+i)) hp (.eqRefl _))

/-! ## Two actual source lists and a query in one computed scale -/

def singleton (z : PTm n) : PTm n := sequence (var 1 : PTm 2) one z
def pool (S T z : PTm n) : PTm n := append S (append T (singleton z))
def commonD (S T z : PTm n) : PTm n := denominator (pool S T z)
def sourceNumerators (S T z : PTm n) : PTm n := numeratorList (pool S T z) zero (length S)
def targetNumerators (S T z : PTm n) : PTm n := numeratorList (pool S T z) (length S) (length T)
def queryNumerator (S T z : PTm n) : PTm n := clearPoint (pool S T z) (length S+length T)

@[simp] theorem subst_singleton {m : ℕ} (σ : Fin n → PTm m) (z : PTm n) :
    Syn.subst σ (singleton z) = singleton (Syn.subst σ z) := by
  simp only [singleton,subst_sequence,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ]
@[simp] theorem subst_pool {m : ℕ} (σ : Fin n → PTm m) (S T z : PTm n) :
    Syn.subst σ (pool S T z) = pool (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ z) := by
  simp only [pool,Foundations.SequenceComposition.subst_append,subst_singleton]
@[simp] theorem subst_commonD {m : ℕ} (σ : Fin n → PTm m) (S T z : PTm n) :
    Syn.subst σ (commonD S T z) = commonD (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ z) := by
  simp only [commonD,subst_denominator,subst_pool]
@[simp] theorem subst_sourceNumerators {m : ℕ} (σ : Fin n → PTm m) (S T z : PTm n) :
    Syn.subst σ (sourceNumerators S T z) = sourceNumerators (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ z) := by
  simp only [sourceNumerators,subst_numeratorList,subst_pool,subst_length,ConciseIPRA.PTm.subst_zero]
@[simp] theorem subst_targetNumerators {m : ℕ} (σ : Fin n → PTm m) (S T z : PTm n) :
    Syn.subst σ (targetNumerators S T z) = targetNumerators (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ z) := by
  simp only [targetNumerators,subst_numeratorList,subst_pool,subst_length]
@[simp] theorem subst_queryNumerator {m : ℕ} (σ : Fin n → PTm m) (S T z : PTm n) :
    Syn.subst σ (queryNumerator S T z) = queryNumerator (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ z) := by
  simp only [queryNumerator,subst_clearPoint,subst_pool,PTm.subst_add,subst_length]

theorem singleton_length (z : PTm n) : Γ ⊢[PRAAx] length (singleton z) ≐ one := sequence_length _ _ _
theorem singleton_lookup (z : PTm n) : Γ ⊢[PRAAx] entry (singleton z) zero ≐ z := by
  simpa [singleton,inst2] using
    sequence_decode (Γ := Γ) (var 1 : PTm 2) (x := z) (zero_lt_succ zero)

theorem pool_length (S T z : PTm n) : Γ ⊢[PRAAx] length (pool S T z) ≐ length S+(length T+one) :=
  (append_length _ _).eqTrans (congrAdd (.eqRefl _) ((append_length _ _).eqTrans (congrAdd (.eqRefl _) (singleton_length z))))

theorem source_bound (S T z j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length S)) : Γ ⊢[PRAAx] lt j (length (pool S T z)) :=
  lt_congr (.eqRefl _) (pool_length S T z).eqSymm (lt_of_lt_of_le hj (le_add_right _ _))
theorem target_bound (S T z j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length T)) : Γ ⊢[PRAAx]
    lt (length S+j) (length (pool S T z)) :=
  lt_congr (.eqRefl _) (pool_length S T z).eqSymm
    (Foundations.SequenceComposition.add_lt_left _ (lt_of_lt_of_le hj (le_add_right _ _)))
theorem query_bound (S T z : PTm n) : Γ ⊢[PRAAx] lt (length S+length T) (length (pool S T z)) := by
  have len : Γ ⊢[PRAAx] length (pool S T z) ≐ succ (length S+length T) :=
    (pool_length S T z).eqTrans (by ipra_ring)
  exact lt_congr (.eqRefl _) len.eqSymm (le_refl _)

theorem pool_source (S T z j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length S)) : Γ ⊢[PRAAx]
    entry (pool S T z) j ≐ entry S j := append_left hj

theorem pool_target (S T z j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length T)) : Γ ⊢[PRAAx]
    entry (pool S T z) (length S+j) ≐ entry T j := by
  have inner : Γ ⊢[PRAAx] lt j (length (append T (singleton z))) :=
    lt_congr (.eqRefl _) (append_length _ _).eqSymm (lt_of_lt_of_le hj (le_add_right _ _))
  exact (append_right (a := S) inner).eqTrans (append_left hj)

theorem pool_query (S T z : PTm n) : Γ ⊢[PRAAx] entry (pool S T z) (length S+length T) ≐ z := by
  have zeroBound : Γ ⊢[PRAAx] lt zero (length (singleton z)) :=
    lt_congr (.eqRefl _) (singleton_length z).eqSymm (zero_lt_succ zero)
  have inner : Γ ⊢[PRAAx] lt (length T+zero) (length (append T (singleton z))) :=
    lt_congr (.eqRefl _) (append_length _ _).eqSymm (Foundations.SequenceComposition.add_lt_left _ zeroBound)
  exact (entry_congr (.eqRefl _) (congrAdd (.eqRefl _) (add_zero (length T))).eqSymm).eqTrans
    ((append_right (a := S) inner).eqTrans ((append_right (a := T) zeroBound).eqTrans (singleton_lookup z)))

theorem commonD_positive (S T z : PTm n) : Γ ⊢[PRAAx] le one (commonD S T z) := denominator_positive _
theorem source_length (S T z : PTm n) : Γ ⊢[PRAAx] length (sourceNumerators S T z) ≐ length S := numeratorList_length _ _ _
theorem target_length (S T z : PTm n) : Γ ⊢[PRAAx] length (targetNumerators S T z) ≐ length T := numeratorList_length _ _ _

theorem source_lookup (S T z j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length S)) : Γ ⊢[PRAAx]
    entry (sourceNumerators S T z) j ≐ clearPoint (pool S T z) j :=
  (numeratorList_lookup _ _ _ _ hj).eqTrans (by
    have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (clearPoint (var 0) (var 1) : PTm 2)
      (σ := ![pool S T z,zero+j]) (σ' := ![pool S T z,j])
      (fun i => by fin_cases i; exact .eqRefl _; exact zero_add _)
    simpa only [subst_clearPoint,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using e)

theorem target_lookup (S T z j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length T)) : Γ ⊢[PRAAx]
    entry (targetNumerators S T z) j ≐ clearPoint (pool S T z) (length S+j) := numeratorList_lookup _ _ _ _ hj

theorem source_clearing (S T z j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length S)) : Γ ⊢[PRAAx]
    clearing (commonD S T z) (entry (sourceNumerators S T z) j) (entry S j) :=
  clearing_congr (source_lookup S T z j hj)
    (clearPoint_clearing _ _ _ (source_bound S T z j hj) (pool_source S T z j hj))
theorem target_clearing (S T z j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length T)) : Γ ⊢[PRAAx]
    clearing (commonD S T z) (entry (targetNumerators S T z) j) (entry T j) :=
  clearing_congr (target_lookup S T z j hj)
    (clearPoint_clearing _ _ _ (target_bound S T z j hj) (pool_target S T z j hj))
theorem query_clearing (S T z : PTm n) : Γ ⊢[PRAAx] clearing (commonD S T z) (queryNumerator S T z) z :=
  clearPoint_clearing _ _ _ (query_bound S T z) (pool_query S T z)

/-! ## Fixed primitive recursive programs and universally closed contracts -/

def denominatorF : PR 1 := PTm.toPR (denominator (var 0))
def clearPointF : PR 2 := PTm.toPR (clearPoint (var 0) (var 1))
def numeratorListF : PR 3 := PTm.toPR (numeratorList (var 0) (var 1) (var 2))
def program (S T z : PTm n) : PTm n :=
  pairT (commonD S T z) (pairT (sourceNumerators S T z) (pairT (targetNumerators S T z) (queryNumerator S T z)))
def programF : PR 3 := PTm.toPR (program (var 0) (var 1) (var 2))

@[simp] theorem subst_program {m : ℕ} (σ : Fin n → PTm m) (S T z : PTm n) :
    Syn.subst σ (program S T z) = program (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ z) := by
  simp only [program,subst_pairT,subst_commonD,subst_sourceNumerators,subst_targetNumerators,subst_queryNumerator]

theorem denominator_at (P : PTm n) : Γ ⊢[PRAAx] ap1 denominatorF P ≐ denominator P := by
  simpa only [denominatorF,ap1,subst_denominator,Syn.subst_var,Matrix.cons_val_zero] using
    toPR_eq (Γ := Γ) (denominator (var 0) : PTm 1) ![P]
theorem clearPoint_at (P j : PTm n) : Γ ⊢[PRAAx] ap2 clearPointF P j ≐ clearPoint P j := by
  simpa only [clearPointF,ap2,subst_clearPoint,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (clearPoint (var 0) (var 1) : PTm 2) ![P,j]
theorem numeratorList_at (P start N : PTm n) : Γ ⊢[PRAAx] ap3 numeratorListF P start N ≐ numeratorList P start N := by
  simpa only [numeratorListF,ap3,subst_numeratorList,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (numeratorList (var 0) (var 1) (var 2) : PTm 3) ![P,start,N]
theorem program_at (S T z : PTm n) : Γ ⊢[PRAAx] ap3 programF S T z ≐ program S T z := by
  simpa only [programF,ap3,subst_program,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (program (var 0) (var 1) (var 2) : PTm 3) ![S,T,z]

theorem denominator_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (denominator (var 0))) := closeUniv 1 (denominator_positive _)

theorem denominator_empty_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (length (var 0) ≐ zero ⟶ denominator (var 0) ≐ one) :=
  closeUniv 1 (.impI (denominator_empty _ Prf.hyp0))

theorem component_clearing_closed (s : Component) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (length (var 0)) ⟶
      ZT.eq (part s (clearPoint (var 0) (var 1))*ZT.ofNat (denominatorOf (scalar s (entry (var 0) (var 1)))))
        (numeratorOf (scalar s (entry (var 0) (var 1)))*ZT.ofNat (denominator (var 0)))) :=
  closeUniv 2 (.impI (component_clearing s _ _ Prf.hyp0))

theorem slice_clearing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 2) ⟶ lt (var 1+var 3) (length (var 0)) ⟶
      clearing (denominator (var 0)) (entry (numeratorList (var 0) (var 1) (var 2)) (var 3))
        (entry (var 0) (var 1+var 3))) :=
  closeUniv 4 (.impI (.impI (numeratorList_clearing _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem slice_metadata_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (numeratorList (var 0) (var 1) (var 2)) ≐ var 2) ⋏
      (lt (var 3) (var 2) ⟶ entry (numeratorList (var 0) (var 1) (var 2)) (var 3) ≐ clearPoint (var 0) (var 1+var 3))) :=
  closeUniv 4 (.andI (numeratorList_length _ _ _) (.impI (numeratorList_lookup _ _ _ _ Prf.hyp0)))

theorem source_clearing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (length (var 0)) ⟶ clearing (commonD (var 0) (var 1) (var 2))
      (entry (sourceNumerators (var 0) (var 1) (var 2)) (var 3)) (entry (var 0) (var 3))) :=
  closeUniv 4 (.impI (source_clearing _ _ _ _ Prf.hyp0))

theorem target_clearing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (length (var 1)) ⟶ clearing (commonD (var 0) (var 1) (var 2))
      (entry (targetNumerators (var 0) (var 1) (var 2)) (var 3)) (entry (var 1) (var 3))) :=
  closeUniv 4 (.impI (target_clearing _ _ _ _ Prf.hyp0))

theorem joint_properties_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (commonD (var 0) (var 1) (var 2)) ⋏
      ((length (sourceNumerators (var 0) (var 1) (var 2)) ≐ length (var 0)) ⋏
        ((length (targetNumerators (var 0) (var 1) (var 2)) ≐ length (var 1)) ⋏
          clearing (commonD (var 0) (var 1) (var 2)) (queryNumerator (var 0) (var 1) (var 2)) (var 2)))) :=
  closeUniv 3 (.andI (commonD_positive _ _ _) (.andI (source_length _ _ _)
    (.andI (target_length _ _ _) (query_clearing _ _ _))))

theorem normalization_programs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap1 denominatorF (var 0) ≐ denominator (var 0)) ⋏
      ((ap2 clearPointF (var 0) (var 1) ≐ clearPoint (var 0) (var 1)) ⋏
        (ap3 numeratorListF (var 0) (var 1) (var 2) ≐ numeratorList (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (denominator_at _) (.andI (clearPoint_at _ _) (numeratorList_at _ _ _)))

theorem joint_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 programF (var 0) (var 1) (var 2) ≐ program (var 0) (var 1) (var 2)) :=
  closeUniv 3 (program_at _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalNormalization
