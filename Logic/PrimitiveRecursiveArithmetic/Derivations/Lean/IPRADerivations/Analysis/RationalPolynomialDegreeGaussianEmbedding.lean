import IPRADerivations.Analysis.RationalPolynomialBuffersGaussianEmbedding
import IPRADerivations.Analysis.GaussianRationalPolynomialDegree

/-!
# Original rational nonvanishing test and numerical degree

The rational program scans the original coefficients for the first
nonzero scalar value. Bounded coefficient embedding makes the actual
Gaussian scan return the same original index, including the sentinel.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialDegreeGaussianEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed scalarZero embed_canonical scalar_recode_zero)
open RationalPolynomialBuffersGaussianEmbedding (embeddedEntries)
open GaussianRationalHorner (qzero)
open GaussianTranslatedNonconstant (recode recode_congr recode_eq)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def zeroBit : PTm 2 := eqb (RationalArithmetic.recode (entry (var 1) (var 0))) scalarZero
def first (C N : PTm n) : PTm n := Search.mu zeroBit (succ N) C
def flag (C N : PTm n) : PTm n := Signum.sg (monus (succ N) (first C N))
def degree (C N : PTm n) : PTm n := monus N (first C N)

@[simp] theorem subst_first {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (first C N) = first (Syn.subst σ C) (Syn.subst σ N) := by simp [first,Search.mu]
@[simp] theorem subst_flag {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (flag C N) = flag (Syn.subst σ C) (Syn.subst σ N) := by simp [flag,Signum.sg]
@[simp] theorem subst_degree {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (degree C N) = degree (Syn.subst σ C) (Syn.subst σ N) := by simp [degree]

theorem zero_bit_at (C i : PTm n) :
    inst2 zeroBit i C = eqb (RationalArithmetic.recode (entry C i)) scalarZero := by simp [zeroBit,inst2]

theorem first_bound (C N : PTm n) : Γ ⊢[PRAAx] le (first C N) (succ N) :=
  .andE₁ (Search.search_spec (f := zeroBit) (succ N) zero C)

theorem first_nonzero (C N : PTm n) (hi : Γ ⊢[PRAAx] lt (first C N) (succ N)) :
    Γ ⊢[PRAAx] neg (RationalArithmetic.recode (entry C (first C N)) ≐ scalarZero) := by
  have hit : Γ ⊢[PRAAx] eqb (RationalArithmetic.recode (entry C (first C N))) scalarZero ≐ zero := by
    simpa only [zero_bit_at,first] using
      Prf.impE (.andE₁ (.andE₂ (Search.search_spec (f := zeroBit) (succ N) zero C))) hi
  exact .impI (succ_ne_zero ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans hit.wk))

theorem first_from_witness (C N i : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ N))
    (hz : Γ ⊢[PRAAx] neg (RationalArithmetic.recode (entry C i) ≐ scalarZero)) :
    Γ ⊢[PRAAx] le (first C N) i := by
  have hit : Γ ⊢[PRAAx] inst2 zeroBit i C ≐ zero := by simpa only [zero_bit_at] using eqb_of_ne hz
  exact .andE₂ (.andE₂ (Search.search_found hit hi))

theorem bounded_entry (C D N i : PTm n) (h : Γ ⊢[PRAAx] embeddedEntries C D (succ N))
    (hi : Γ ⊢[PRAAx] lt i (succ N)) : Γ ⊢[PRAAx] embed (entry C i) ≐ entry D i := by
  have law : Γ ⊢[PRAAx] lt i (succ N) ⟶ embed (entry C i) ≐ entry D i := by
    simpa [embeddedEntries] using h.allE i
  exact .impE law hi

theorem zero_iff_at (C D N i : PTm n) (h : Γ ⊢[PRAAx] embeddedEntries C D (succ N))
    (hi : Γ ⊢[PRAAx] lt i (succ N)) : Γ ⊢[PRAAx] Fm.iff
      (RationalArithmetic.recode (entry C i) ≐ scalarZero) (recode (entry D i) ≐ qzero) := by
  let e := entry C i
  have aligned : Γ ⊢[PRAAx] recode (entry D i) ≐ embed e :=
    (recode_congr (bounded_entry C D N i h hi).eqSymm).eqTrans (recode_eq _ (embed_canonical e))
  refine .andI (.impI ?_) (.impI ?_)
  · exact aligned.wk.eqTrans ((RationalGaussianEmbedding.zero_iff e).iffMpr
      (RationalGaussianEmbedding.rational_equal_of_scalar_recode e scalarZero
        (Prf.hyp0.eqTrans scalar_recode_zero.eqSymm)))
  · exact (RationalGaussianEmbedding.scalar_recode_equal e scalarZero
      ((RationalGaussianEmbedding.zero_iff e).iffMp (aligned.wk.eqSymm.eqTrans Prf.hyp0))).eqTrans scalar_recode_zero

theorem first_conjugacy (C D N : PTm n) (h : Γ ⊢[PRAAx] embeddedEntries C D (succ N)) :
    Γ ⊢[PRAAx] first C N ≐ GaussianRationalPolynomialDegree.first D N := by
  let i := first C N
  let j := GaussianRationalPolynomialDegree.first D N
  refine .orE (lt_or_le i j) ?_ ?_
  · let Δ := lt i j :: Γ
    have hi : Δ ⊢[PRAAx] lt i (succ N) := lt_of_lt_of_le Prf.hyp0 (GaussianRationalPolynomialDegree.first_bound D N)
    have z := first_nonzero C N hi
    have ng : Δ ⊢[PRAAx] neg (recode (entry D i) ≐ qzero) :=
      .impI (.impE z.wk ((zero_iff_at C D N i h.wk hi).wk.iffMpr Prf.hyp0))
    exact le_lt_absurd _ (.andE₂ (GaussianRationalPolynomialDegree.first_from_witness D N i hi ng)) Prf.hyp0
  · refine .orE (lt_or_eq_of_le (Prf.hyp0 : le j i :: Γ ⊢[PRAAx] le j i)) ?_ Prf.hyp0.eqSymm
    let Δ := lt j i :: le j i :: Γ
    have hj : Δ ⊢[PRAAx] lt j (succ N) := lt_of_lt_of_le Prf.hyp0 (first_bound C N)
    have z := GaussianRationalPolynomialDegree.first_nonzero D N hj
    have nr : Δ ⊢[PRAAx] neg (RationalArithmetic.recode (entry C j) ≐ scalarZero) :=
      .impI (.impE z.wk ((zero_iff_at C D N j h.wk.wk hj).wk.iffMp Prf.hyp0))
    exact le_lt_absurd _ (first_from_witness C N j hj nr) Prf.hyp0

theorem flag_conjugacy (C D N : PTm n) (h : Γ ⊢[PRAAx] embeddedEntries C D (succ N)) :
    Γ ⊢[PRAAx] flag C N ≐ GaussianRationalPolynomialDegree.flag D N :=
  congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (first_conjugacy C D N h)))
theorem degree_conjugacy (C D N : PTm n) (h : Γ ⊢[PRAAx] embeddedEntries C D (succ N)) :
    Γ ⊢[PRAAx] degree C N ≐ GaussianRationalPolynomialDegree.degree D N :=
  congrMonus (.eqRefl _) (first_conjugacy C D N h)

def result (C N : PTm n) : PTm n := pairT (flag C N) (degree C N)
def resultF : PR 2 := PTm.toPR (result (var 0) (var 1))

@[simp] theorem subst_result {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (result C N) = result (Syn.subst σ C) (Syn.subst σ N) := by simp [result]

theorem result_at (C N : PTm n) : Γ ⊢[PRAAx] ap2 resultF C N ≐ result C N := by
  simpa [resultF,ap2] using toPR_eq (Γ := Γ) (result (var 0) (var 1) : PTm 2) ![C,N]

theorem actual_original_rational_degree_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 resultF (var 0) (var 1) ≐ pairT (flag (var 0) (var 1)) (degree (var 0) (var 1))) :=
  closeUniv 2 (result_at _ _)

theorem actual_rational_degree_conjugacy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (embeddedEntries (var 0) (var 1) (succ (var 2)) ⟶
      (flag (var 0) (var 2) ≐ GaussianRationalPolynomialDegree.flag (var 1) (var 2) ⋏
        degree (var 0) (var 2) ≐ GaussianRationalPolynomialDegree.degree (var 1) (var 2))) :=
  closeUniv 3 (.impI (.andI (flag_conjugacy _ _ _ Prf.hyp0) (degree_conjugacy _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalPolynomialDegreeGaussianEmbedding
