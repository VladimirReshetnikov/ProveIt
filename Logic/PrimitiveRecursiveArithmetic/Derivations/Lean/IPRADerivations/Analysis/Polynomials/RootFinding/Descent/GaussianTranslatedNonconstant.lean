import IPRADerivations.Analysis.RationalArithmetic.Translations.GaussianRationalTranslation
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalL1
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianMonicNonconstant
import IPRADerivations.Foundations.BoundedSyntaxInduction
import IPRADerivations.Core.Search

/-!
# Actual preservation of nonconstant Gaussian-rational coefficients

The first nonzero descending coefficient is selected by a bounded numerical
search. Genuine finite Horner and synthetic-quotient inductions show that its
value survives in the actual translated coefficient list. Raw input codes
are recoded canonically, rather than incorrectly identified with their
normalizations. Every list, degree, index and translation point is internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul horner evaluate represents canonical positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (quotient)
open LeanProofs.IPRA.Analysis.GaussianRationalTranslationStages (stage remaining)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq normSq_eval zeroCode)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra (equal equal_of_values re_add im_add re_zero im_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def recode (q : PTm n) : PTm n := qadd qzero q
def rawNorm (q : PTm n) : PTm n := normSq (rawGaussian q)

@[simp] theorem subst_recode {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (recode q) = recode (Syn.subst σ q) := by simp [recode]
@[simp] theorem subst_rawNorm {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (rawNorm q) = rawNorm (Syn.subst σ q) := by simp [rawNorm]

theorem recode_canonical (q : PTm n) : Γ ⊢[PRAAx] canonical (recode q) :=
  GaussianRationalHorner.qadd_canonical _ _

theorem recode_represents (q : PTm n) : Γ ⊢[PRAAx]
    represents (recode q) (rawGaussian q) (rawDen q) := by
  apply GaussianRationalHorner.represents_congr (.eqRefl _) (hAB := .eqRefl _)
    (h := GaussianRationalHorner.qadd_represents qzero q zeroCode (rawGaussian q) (rawDen q)
      (raw_den_positive q) (GaussianRationalHorner.zero_represents _) (raw_represents q))
  apply equal_of_values <;> simp only [re_add,im_add,re_zero,im_zero] <;> ring

theorem recode_eq (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] recode q ≐ q :=
  GaussianRationalSyntheticDivision.qzero_add q hq

theorem recode_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx] recode q ≐ recode r :=
  GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) h

theorem raw_zero_value (q : PTm n) (h : Γ ⊢[PRAAx] rawNorm q ≐ zero) : Γ ⊢[PRAAx]
    equal (rawGaussian q) zeroCode := by
  have square_zero (a : PTm n) (ha : Γ ⊢[PRAAx] a*a ≐ zero) : Γ ⊢[PRAAx] a ≐ zero :=
    .orE (zero_or_zero_of_mul ha) Prf.hyp0 Prf.hyp0
  have r := square_zero _ (add_eq_zero_left h)
  have i := square_zero _ (add_eq_zero_right h)
  have rz := le_antisymm (add_eq_zero_left r) (add_eq_zero_right r)
  have iz := le_antisymm (add_eq_zero_left i) (add_eq_zero_right i)
  apply equal_of_values
  · rw [re_zero]
    simp only [ZT.toZ]
    rw [natEq rz]
    ring
  · rw [im_zero]
    simp only [ZT.toZ]
    rw [natEq iz]
    ring

theorem recode_zero (q : PTm n) (h : Γ ⊢[PRAAx] rawNorm q ≐ zero) : Γ ⊢[PRAAx] recode q ≐ qzero :=
  GaussianRationalHorner.canonical_unique _ _ zeroCode (rawDen q) (recode_canonical q)
    (GaussianRationalHorner.ofGaussian_canonical zeroCode one (le_refl _)) (raw_den_positive q)
    (GaussianRationalHorner.represents_congr (.eqRefl _) (raw_zero_value q h) (.eqRefl _) (recode_represents q))
    (GaussianRationalHorner.zero_represents _)

/-- A leading zero block is stated using canonical recoding, so it applies
to arbitrary raw stored input fractions. -/
def zeroPrefix (C e : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift e) ⟶ recode (entry (Syn.shift C) (var 0)) ≐ qzero)

@[simp] theorem subst_zeroPrefix {m : ℕ} (σ : Fin n → PTm m) (C e : PTm n) :
    (zeroPrefix C e).subst σ = zeroPrefix (Syn.subst σ C) (Syn.subst σ e) := by
  simp [zeroPrefix,Syn.subst_shift,Syn.shift_subst]

theorem zero_prefix_at (C e i : PTm n) (h : Γ ⊢[PRAAx] zeroPrefix C e)
    (hi : Γ ⊢[PRAAx] lt i e) : Γ ⊢[PRAAx] recode (entry C i) ≐ qzero := by
  have r : Γ ⊢[PRAAx] lt i e ⟶ recode (entry C i) ≐ qzero := by
    simpa only [zeroPrefix,Fm.subst_imp,Fm.subst_eq,subst_lt,subst_recode,subst_entry,
      GaussianRationalHorner.subst_qzero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE r hi

def hornerZeroLaw (C z e k : PTm n) : Fm PTm n :=
  le k e ⟶ horner C z k ≐ qzero
@[simp] theorem subst_hornerZeroLaw {m : ℕ} (σ : Fin n → PTm m) (C z e k : PTm n) :
    (hornerZeroLaw C z e k).subst σ = hornerZeroLaw (Syn.subst σ C) (Syn.subst σ z)
      (Syn.subst σ e) (Syn.subst σ k) := by simp [hornerZeroLaw]

theorem zero_prefix_horner (C z e k : PTm n) (h : Γ ⊢[PRAAx] zeroPrefix C e)
    (hk : Γ ⊢[PRAAx] le k e) : Γ ⊢[PRAAx] horner C z k ≐ qzero := by
  have all : Γ ⊢[PRAAx] .all (hornerZeroLaw (Syn.shift C) (Syn.shift z) (Syn.shift e) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_hornerZeroLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (GaussianRationalHorner.horner_zero C z)
    · simp only [subst_hornerZeroLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let I := hornerZeroLaw (Syn.shift C) (Syn.shift z) (Syn.shift e) (var 0)
      let Δ := le (succ (var 0)) (Syn.shift e) :: I :: Γ.map Fm.shift
      have hp : Δ ⊢[PRAAx] zeroPrefix (Syn.shift C) (Syn.shift e) := by
        simpa only [Fm.shift,subst_zeroPrefix,Syn.shift] using h.shift.wk.wk
      have ih : Δ ⊢[PRAAx] horner (Syn.shift C) (Syn.shift z) (var 0) ≐ qzero :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      exact (GaussianRationalHorner.horner_succ _ _ _).eqTrans
        ((GaussianRationalSyntheticDivision.qadd_congr
          ((GaussianRationalSyntheticDivision.qmul_congr ih (.eqRefl _)).eqTrans
            (GaussianRationalSyntheticDivision.qmul_zero_left _)) (.eqRefl _)).eqTrans
          (zero_prefix_at _ _ _ hp Prf.hyp0))
  have here : Γ ⊢[PRAAx] hornerZeroLaw C z e k := by
    simpa only [subst_hornerZeroLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE here hk

theorem boundary_horner (C z e : PTm n) (h : Γ ⊢[PRAAx] zeroPrefix C e) : Γ ⊢[PRAAx]
    horner C z (succ e) ≐ recode (entry C e) :=
  (GaussianRationalHorner.horner_succ C z e).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr
      ((GaussianRationalSyntheticDivision.qmul_congr (zero_prefix_horner C z e e h (le_refl _)) (.eqRefl _)).eqTrans
        (GaussianRationalSyntheticDivision.qmul_zero_left _)) (.eqRefl _))

def flat (C e a : PTm n) : Fm PTm n := zeroPrefix C e ⋏ recode (entry C e) ≐ a
@[simp] theorem subst_flat {m : ℕ} (σ : Fin n → PTm m) (C e a : PTm n) :
    (flat C e a).subst σ = flat (Syn.subst σ C) (Syn.subst σ e) (Syn.subst σ a) := by simp [flat]

theorem flat_congr {C D e a : PTm n} (h : Γ ⊢[PRAAx] C ≐ D)
    (hf : Γ ⊢[PRAAx] flat C e a) : Γ ⊢[PRAAx] flat D e a := by
  have rule := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (flat (var 0) (var 1) (var 2) : Fm PTm 3)
    ![C,e,a] ![D,e,a] (fun i => by fin_cases i; exact h; exact .eqRefl _; exact .eqRefl _)
    (by simpa using hf)
  simpa using rule

theorem quotient_flat (C z M e a : PTm n) (he : Γ ⊢[PRAAx] lt e M)
    (h : Γ ⊢[PRAAx] flat C e a) : Γ ⊢[PRAAx] flat (quotient C z M) e a := by
  refine .andI (.allI (.impI ?_)) ?_
  · let Δ := lt (var 0) (Syn.shift e) :: Γ.map Fm.shift
    have hp : Δ ⊢[PRAAx] zeroPrefix (Syn.shift C) (Syn.shift e) := by
      simpa only [Fm.shift,subst_zeroPrefix,Syn.shift] using (Prf.andE₁ h).shift.wk
    have hM : Δ ⊢[PRAAx] lt (var 0) (Syn.shift M) :=
      lt_of_lt_of_le Prf.hyp0 (le_of_lt (by simpa only [Fm.shift,subst_lt,Syn.shift] using he.shift.wk))
    have here := (GaussianRationalSyntheticDivision.quotient_lookup (Syn.shift C) (Syn.shift z)
      (Syn.shift M) (var 0) hM).eqTrans (zero_prefix_horner _ _ _ _ hp Prf.hyp0)
    simpa only [Δ,Syn.shift,GaussianRationalSyntheticDivision.subst_quotient] using
      (recode_congr here).eqTrans (recode_eq qzero
        (GaussianRationalHorner.ofGaussian_canonical zeroCode one (le_refl _)))
  · exact (recode_congr (GaussianRationalSyntheticDivision.quotient_lookup C z M e he)).eqTrans
      ((recode_eq _ (GaussianRationalHorner.horner_canonical C z (succ e))).eqTrans
        ((boundary_horner C z e (Prf.andE₁ h)).eqTrans (Prf.andE₂ h)))

def flatSyntax (C e a : PTm n) : BFm n := .and
  (.all e (.eq (recode (entry (Syn.shift C) (var 0))) qzero)) (.eq (recode (entry C e)) a)
theorem flat_formula (C e a : PTm n) : formula (flatSyntax C e a) = flat C e a := rfl

def stageLaw (C N z e a j : PTm n) : Fm PTm n :=
  le (j+e) N ⟶ flat (stage C N z j) e a
@[simp] theorem subst_stageLaw {m : ℕ} (σ : Fin n → PTm m) (C N z e a j : PTm n) :
    (stageLaw C N z e a j).subst σ = stageLaw (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ e) (Syn.subst σ a) (Syn.subst σ j) := by simp [stageLaw]
def stageSyntax (C N z e a j : PTm n) : BFm n :=
  .imp (.le (j+e) N) (flatSyntax (stage C N z j) e a)
theorem stage_formula (C N z e a j : PTm n) : formula (stageSyntax C N z e a j) = stageLaw C N z e a j := rfl

theorem room_after (N j e : PTm n) (h : Γ ⊢[PRAAx] le (succ j+e) N) : Γ ⊢[PRAAx]
    lt e (remaining N j) := by
  have shape : Γ ⊢[PRAAx] N ≐ j+(succ e+monus N (succ j+e)) :=
    (eq_add_of_le h).eqTrans (by ipra_ring)
  have rem := (congrMonus shape (.eqRefl _)).eqTrans (add_monus' _ _)
  exact le_of_eq_add rem

/-- The genuine bounded induction is applied to the compiled QF bit. Its
reflected leading-block invariant retains arbitrary runtime indices. -/
theorem stages_flat (C N z e a j : PTm n) (h : Γ ⊢[PRAAx] flat C e a)
    (hj : Γ ⊢[PRAAx] le (j+e) N) : Γ ⊢[PRAAx] flat (stage C N z j) e a := by
  have all : Γ ⊢[PRAAx] .all (stageLaw (Syn.shift C) (Syn.shift N) (Syn.shift z)
      (Syn.shift e) (Syn.shift a) (var 0)) := by
    simpa only [stage_formula] using (Foundations.BoundedSyntaxInduction.induction
      (stageSyntax (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift e) (Syn.shift a) (var 0))
      (Γ := Γ)
      (by
        simp only [stage_formula,subst_stageLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
        exact .impI (flat_congr (GaussianRationalTranslationStages.stage_zero C N z).eqSymm h.wk))
      (by
        simp only [stage_formula,subst_stageLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
        refine .impI ?_
        let I := stageLaw (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift e) (Syn.shift a) (var 0)
        let Δ := le (succ (var 0)+Syn.shift e) (Syn.shift N) :: I :: Γ.map Fm.shift
        have prev : Δ ⊢[PRAAx] flat (stage (Syn.shift C) (Syn.shift N) (Syn.shift z) (var 0))
            (Syn.shift e) (Syn.shift a) := .impE Prf.hyp1 (le_trans
              (le_of_eq_add (d := one) (by ipra_ring)) Prf.hyp0)
        exact flat_congr (GaussianRationalTranslationStages.stage_succ _ _ _ _).eqSymm
          (quotient_flat _ _ _ _ _ (room_after _ _ _ Prf.hyp0) prev)))
  have rule : Γ ⊢[PRAAx] stageLaw C N z e a j := by
    simpa only [subst_stageLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

/-- The first potentially nonzero descending coefficient survives actual
translation. The RHS is its canonical value, not its possibly raw code. -/
theorem translated_boundary (C N z e : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (he : Γ ⊢[PRAAx] le e N) (hZero : Γ ⊢[PRAAx] zeroPrefix C e) : Γ ⊢[PRAAx]
    entry (GaussianRationalTranslation.translated C N z) e ≐ recode (entry C e) := by
  have sum : Γ ⊢[PRAAx] monus N e+e ≐ N := (add_comm _ _).eqTrans (eq_add_of_le he).eqSymm
  have hj : Γ ⊢[PRAAx] le (monus N e) N := le_of_eq_add (d := e) sum.eqSymm
  have block := stages_flat C N z e (recode (entry C e)) (monus N e)
    (.andI hZero (.eqRefl _)) (le_congr sum.eqSymm (.eqRefl _) (le_refl N))
  have rem : Γ ⊢[PRAAx] remaining N (monus N e) ≐ e := by
    have shape : Γ ⊢[PRAAx] N ≐ monus N e+e := sum.eqSymm
    exact (congrMonus shape (.eqRefl _)).eqTrans (add_monus' _ _)
  have len := (GaussianRationalTranslationStages.stage_length C N z (monus N e) hLen hj).eqTrans (congrSucc rem)
  have ev : Γ ⊢[PRAAx] evaluate (stage C N z (monus N e)) z ≐ recode (entry C e) :=
    (congrAp3 GaussianRationalHorner.hornerF len (.eqRefl _) (.eqRefl _)).eqTrans
      ((boundary_horner _ z e (Prf.andE₁ block)).eqTrans (Prf.andE₂ block))
  exact (GaussianRationalTranslation.translated_lookup C N z e he).eqTrans ev

theorem represented_positive (q a D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hrep : Γ ⊢[PRAAx] represents q a D) (ha : Γ ⊢[PRAAx] le one (normSq a)) :
    Γ ⊢[PRAAx] le one (rawNorm q) := by
  have cmp := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (GaussianRationalMetric.qnormSq_represents q a D hD hrep)
    (GaussianRationalMetric.qnormSq_represents q (rawGaussian q) (rawDen q) (raw_den_positive q) (raw_represents q))
    (RationalArgmin.reflexive _)
  refine .orE (zero_or_succ (rawNorm q)) ?_ ?_
  · have positive := positive_product _ _
      (positive_product _ _ (raw_den_positive q) (raw_den_positive q)) ha
    have rhs : (rawNorm q ≐ zero)::Γ ⊢[PRAAx] normSq (rawGaussian q)*(D*D) ≐ zero :=
      (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
    exact lt_zero_absurd _ (le_trans positive.wk
      (le_congr (.eqRefl _) rhs cmp.wk))
  · exact le_of_eq_add (d := pred (rawNorm q)) (Prf.hyp0.eqTrans (by ipra_ring))

theorem recode_positive (q : PTm n) (h : Γ ⊢[PRAAx] le one (rawNorm q)) : Γ ⊢[PRAAx]
    le one (rawNorm (recode q)) := represented_positive _ _ _ (raw_den_positive q) (recode_represents q) h

/-- The actual least nonzero descending position, searching precisely the
positive-degree coefficient range 0,...,N-1. -/
def searchBody : PTm 2 := eqb (rawNorm (entry (var 1) (var 0))) zero
def first (C N : PTm n) : PTm n := Search.mu searchBody N C
def degree (C N : PTm n) : PTm n := monus N (first C N)
@[simp] theorem subst_first {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (first C N) = first (Syn.subst σ C) (Syn.subst σ N) := by simp [first,Search.mu,subst_ap2]
@[simp] theorem subst_degree {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (degree C N) = degree (Syn.subst σ C) (Syn.subst σ N) := by simp [degree]

theorem search_at (C i : PTm n) : inst2 searchBody i C = eqb (rawNorm (entry C i)) zero := by
  simp [inst2,searchBody]

theorem first_before (C N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N)
    (hp : Γ ⊢[PRAAx] le one (rawNorm (entry C i))) : Γ ⊢[PRAAx]
    lt (first C N) N := by
  have h : Γ ⊢[PRAAx] inst2 searchBody i C ≐ zero := by
    rw [search_at]
    exact eqb_zero_of_gt hp
  exact Prf.andE₁ (Search.search_found h hi)

theorem first_positive (C N : PTm n) (h : Γ ⊢[PRAAx] lt (first C N) N) : Γ ⊢[PRAAx]
    le one (rawNorm (entry C (first C N))) := by
  have found : Γ ⊢[PRAAx] eqb (rawNorm (entry C (first C N))) zero ≐ zero := by
    have hit : Γ ⊢[PRAAx] inst2 searchBody (first C N) C ≐ zero :=
      .impE (Prf.andE₁ (Prf.andE₂ (Search.search_spec (f := searchBody) N zero C))) h
    simpa only [search_at] using hit
  refine .orE (zero_or_succ (rawNorm (entry C (first C N)))) ?_ ?_
  · exact .botE _ (succ_ne_zero (a := zero) ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans found.wk))
  · exact le_of_eq_add (d := pred (rawNorm (entry C (first C N)))) (Prf.hyp0.eqTrans (by ipra_ring))

theorem before_first_zero (C N i : PTm n) (hi : Γ ⊢[PRAAx] lt i (first C N)) : Γ ⊢[PRAAx]
    rawNorm (entry C i) ≐ zero := by
  have minimal : Γ ⊢[PRAAx] neg (eqb (rawNorm (entry C i)) zero ≐ zero) := by
    simpa only [search_at] using Search.search_minimal (f := searchBody) hi
  refine .orE (zero_or_succ (rawNorm (entry C i))) Prf.hyp0 ?_
  have pos : (rawNorm (entry C i) ≐ succ (pred (rawNorm (entry C i))))::Γ ⊢[PRAAx]
      le one (rawNorm (entry C i)) :=
    le_of_eq_add (d := pred (rawNorm (entry C i))) (Prf.hyp0.eqTrans (by ipra_ring))
  exact .botE _ (.impE minimal.wk (eqb_zero_of_gt pos))

theorem first_zero_prefix (C N : PTm n) : Γ ⊢[PRAAx] zeroPrefix C (first C N) := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_first] using recode_zero (entry (Syn.shift C) (var 0))
    (before_first_zero (Syn.shift C) (Syn.shift N) (var 0) Prf.hyp0)

theorem first_from_nonconstant (C N : PTm n) (h : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.nonconstant C N) :
    Γ ⊢[PRAAx] lt (first C N) N := by
  refine .exE h ?_
  let Δ := (le one (var 0) ⋏ (le (var 0) (Syn.shift N) ⋏
    le one (GaussianBalancedRadiusSyntax.numerator (Syn.shift C) (Syn.shift N) (var 0)))) :: Γ.map Fm.shift
  have hk : Δ ⊢[PRAAx] le one (var 0) := Prf.andE₁ Prf.hyp0
  have hkN : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := Prf.andE₁ (Prf.andE₂ Prf.hyp0)
  have shape : Δ ⊢[PRAAx] Syn.shift N ≐ succ (monus (Syn.shift N) (var 0))+pred (var 0) :=
    ((eq_add_of_le hkN).eqTrans (congrAdd (RationalIntegerNormalization.positive_form hk) (.eqRefl _))).eqTrans (by ipra_ring)
  have idx : Δ ⊢[PRAAx] lt (monus (Syn.shift N) (var 0)) (Syn.shift N) := le_of_eq_add shape
  have hp : Δ ⊢[PRAAx] le one (rawNorm (entry (Syn.shift C) (monus (Syn.shift N) (var 0)))) :=
    Prf.andE₂ (Prf.andE₂ Prf.hyp0)
  simpa only [Δ,Fm.shift,subst_lt,subst_first,Syn.shift] using first_before _ _ _ idx hp

theorem degree_bounds (C N : PTm n) (h : Γ ⊢[PRAAx] lt (first C N) N) : Γ ⊢[PRAAx]
    le one (degree C N) ⋏ le (degree C N) N := by
  have p := GaussianRationalTranslationStages.remaining_positive N (first C N) h
  exact .andI p (le_of_eq_add (d := first C N) ((eq_add_of_le (le_of_lt h)).eqTrans (add_comm _ _)))

/-- A numerical original nonconstant witness is converted into an actual
positive-degree witness in the produced translated coefficient list. -/
theorem translated_nonconstant (C N z : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (h : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.nonconstant C N) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.nonconstant (GaussianRationalTranslation.translated C N z) N := by
  have hf := first_from_nonconstant C N h
  have hd := degree_bounds C N hf
  have boundary := translated_boundary C N z (first C N) hLen (le_of_lt hf) (first_zero_prefix C N)
  have original := recode_positive (entry C (first C N)) (first_positive C N hf)
  have index : Γ ⊢[PRAAx] monus N (degree C N) ≐ first C N := by
    have shape := (eq_add_of_le (le_of_lt hf)).eqTrans (add_comm _ _)
    exact (congrMonus shape (.eqRefl _)).eqTrans (add_monus' _ _)
  have value := (entry_congr (.eqRefl (GaussianRationalTranslation.translated C N z)) index).eqTrans boundary
  have positive : Γ ⊢[PRAAx] le one
      (GaussianBalancedRadiusSyntax.numerator (GaussianRationalTranslation.translated C N z) N (degree C N)) :=
    le_congr (.eqRefl _) (GaussianMonicNonconstant.raw_norm_congr value).eqSymm original
  refine .exI (degree C N) ?_
  simpa [GaussianBalancedRadiusSyntax.nonconstant] using Prf.andI (Prf.andE₁ hd) (Prf.andI (Prf.andE₂ hd) positive)

theorem translated_represents (C N z : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (h : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.nonconstant C N) : Γ ⊢[PRAAx]
    represents (entry (GaussianRationalTranslation.translated C N z) (first C N))
      (rawGaussian (entry C (first C N))) (rawDen (entry C (first C N))) :=
  GaussianRationalHorner.represents_congr
    (translated_boundary C N z (first C N) hLen (le_of_lt (first_from_nonconstant C N h))
      (first_zero_prefix C N)).eqSymm
    (GaussianRootAlgebra.equal_refl _) (.eqRefl _) (recode_represents _)

theorem radius_input (C N z : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.nonconstant C N) :
    Γ ⊢[PRAAx] GaussianBalancedRadius.inputContract (GaussianRationalTranslation.translated C N z) N :=
  .andI (GaussianRationalTranslation.translated_length C N z) (.andI hN (translated_nonconstant C N z hLen h))

theorem translated_radius_input (C N z : PTm n) (h : Γ ⊢[PRAAx] GaussianBalancedRadius.inputContract C N) :
    Γ ⊢[PRAAx] GaussianBalancedRadius.inputContract (GaussianRationalTranslation.translated C N z) N :=
  radius_input C N z (Prf.andE₁ h) (Prf.andE₁ (Prf.andE₂ h)) (Prf.andE₂ (Prf.andE₂ h))

def output (C N z : PTm n) : PTm n := pairT (first C N)
  (pairT (degree C N) (pairT (entry C (first C N))
    (entry (GaussianRationalTranslation.translated C N z) (first C N))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C N z : PTm n) : PTm n := ap3 outputF C N z
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C N z : PTm n) :
    Syn.subst σ (output C N z) = output (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C N z : PTm n) :
    Syn.subst σ (run C N z) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) := by simp [run]

theorem program_at (C N z : PTm n) : Γ ⊢[PRAAx] run C N z ≐ output C N z := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,N,z]
theorem returned_first (C N z : PTm n) : Γ ⊢[PRAAx] fstT (run C N z) ≐ first C N :=
  (congrFst (program_at C N z)).eqTrans (fst_pair _ _)
theorem returned_degree (C N z : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N z)) ≐ degree C N :=
  ((congrFst (congrSnd (program_at C N z))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_original (C N z : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run C N z))) ≐ entry C (first C N) :=
  ((congrFst (congrSnd (congrSnd (program_at C N z)))).eqTrans
    ((congrFst (congrSnd (snd_pair _ _))).eqTrans (congrFst (snd_pair _ _)))).eqTrans (fst_pair _ _)
theorem returned_translated (C N z : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run C N z))) ≐ entry (GaussianRationalTranslation.translated C N z) (first C N) :=
  ((congrSnd (congrSnd (congrSnd (program_at C N z)))).eqTrans
    ((congrSnd (congrSnd (snd_pair _ _))).eqTrans (congrSnd (snd_pair _ _)))).eqTrans (snd_pair _ _)

theorem returned_value (C N z : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (h : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.nonconstant C N) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run C N z))) ≐ recode (fstT (sndT (sndT (run C N z)))) :=
  (returned_translated C N z).eqTrans ((translated_boundary C N z (first C N) hLen
    (le_of_lt (first_from_nonconstant C N h)) (first_zero_prefix C N)).eqTrans
      (recode_congr (returned_original C N z)).eqSymm)

theorem returned_positive (C N z : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (h : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.nonconstant C N) : Γ ⊢[PRAAx]
    le one (rawNorm (sndT (sndT (sndT (run C N z))))) := by
  have e := returned_value C N z hLen h
  have hp := recode_positive (entry C (first C N)) (first_positive C N (first_from_nonconstant C N h))
  have code := e.eqTrans (recode_congr (returned_original C N z))
  exact le_congr (.eqRefl _) (GaussianMonicNonconstant.raw_norm_congr code).eqSymm hp

theorem translated_boundary_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ le (var 3) (var 1) ⟶ zeroPrefix (var 0) (var 3) ⟶
      entry (GaussianRationalTranslation.translated (var 0) (var 1) (var 2)) (var 3) ≐ recode (entry (var 0) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (translated_boundary _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem translated_nonconstant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ GaussianBalancedRadiusSyntax.nonconstant (var 0) (var 1) ⟶
      GaussianBalancedRadiusSyntax.nonconstant (GaussianRationalTranslation.translated (var 0) (var 1) (var 2)) (var 1)) :=
  closeUniv 3 (.impI (.impI (translated_nonconstant _ _ _ Prf.hyp1 Prf.hyp0)))
theorem translated_radius_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianBalancedRadius.inputContract (var 0) (var 1) ⟶
      GaussianBalancedRadius.inputContract (GaussianRationalTranslation.translated (var 0) (var 1) (var 2)) (var 1)) :=
  closeUniv 3 (.impI (translated_radius_input _ _ _ Prf.hyp0))
theorem program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem returned_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ GaussianBalancedRadiusSyntax.nonconstant (var 0) (var 1) ⟶
      sndT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ recode (fstT (sndT (sndT (run (var 0) (var 1) (var 2)))))) :=
  closeUniv 3 (.impI (.impI (returned_value _ _ _ Prf.hyp1 Prf.hyp0)))
theorem returned_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ GaussianBalancedRadiusSyntax.nonconstant (var 0) (var 1) ⟶
      le one (rawNorm (sndT (sndT (sndT (run (var 0) (var 1) (var 2))))))) :=
  closeUniv 3 (.impI (.impI (returned_positive _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant
