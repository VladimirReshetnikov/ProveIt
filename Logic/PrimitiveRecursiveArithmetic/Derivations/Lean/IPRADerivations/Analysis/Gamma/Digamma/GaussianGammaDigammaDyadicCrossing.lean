import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaNative
import IPRADerivations.Analysis.RationalArithmetic.GaussianPositiveRealArithmetic
import IPRADerivations.Core.Search

/-!
# Adjacent opposite signs on a digamma grid

Sample the original digamma name at the grid points `(N+i)/N` with one
fixed observation clock. A bounded search finds the first nonnegative
rational observation if the final sample is nonnegative. If the first
sample is negative, the immediately preceding sample is negative.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaDyadicCrossing

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaDigammaNative (nameF data)
open GaussianPositiveRealArithmetic (sign)
open RationalSupMetric (numeratorOf)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sample (p N i : PTm n) : PTm n := fstT (ap2 nameF p (data (N+i) N))

def test (p N i : PTm n) : PTm n :=
  monus (numeratorOf (sample p N i)).neg (numeratorOf (sample p N i)).pos

def input (p N : PTm n) : PTm n := pairT p N
def body : PTm 2 := test (fstT (var 1)) (sndT (var 1)) (var 0)
def first (p N : PTm n) : PTm n := Search.mu body (succ N) (input p N)
def leftIndex (p N : PTm n) : PTm n := pred (first p N)

@[simp] theorem subst_sample {k : ℕ} (σ : Fin n → PTm k) (p N i : PTm n) :
    Syn.subst σ (sample p N i) = sample (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ i) := by
  simp only [sample, subst_fstT, subst_ap2, GaussianGammaDigammaNative.subst_data, PTm.subst_add]

@[simp] theorem subst_test {k : ℕ} (σ : Fin n → PTm k) (p N i : PTm n) :
    Syn.subst σ (test p N i) = test (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ i) := by
  simp [test, numeratorOf]

@[simp] theorem subst_first {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (first p N) = first (Syn.subst σ p) (Syn.subst σ N) := by
  simp [first, input]

@[simp] theorem subst_leftIndex {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (leftIndex p N) = leftIndex (Syn.subst σ p) (Syn.subst σ N) := by
  simp only [leftIndex, PTm.subst_pred, subst_first]

theorem test_congr {p p' N N' i i' : PTm n} (hp : Γ ⊢[PRAAx] p ≐ p')
    (hN : Γ ⊢[PRAAx] N ≐ N') (hi : Γ ⊢[PRAAx] i ≐ i') :
    Γ ⊢[PRAAx] test p N i ≐ test p' N' i' := by
  simpa only [subst_test, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
    (Prf.eqCongr (test (var 0) (var 1) (var 2)) (σ := ![p,N,i]) (σ' := ![p',N',i'])
      (fun j => by fin_cases j; exacts [hp,hN,hi]))

theorem body_at (p N i : PTm n) : Γ ⊢[PRAAx] inst2 body i (input p N) ≐ test p N i := by
  simpa only [inst2, body, input, subst_test, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one] using
    test_congr (fst_pair (Γ := Γ) p N) (snd_pair p N) (.eqRefl i)

theorem first_found (p N : PTm n) (hN : Γ ⊢[PRAAx] sign (sample p N N)) :
    Γ ⊢[PRAAx] le (first p N) N ⋏ sign (sample p N (first p N)) := by
  have hz : Γ ⊢[PRAAx] test p N N ≐ zero := hN
  have found := Search.search_found (N := succ N) ((body_at p N N).eqTrans hz) (le_refl (succ N))
  exact .andI (Prf.andE₂ (Prf.andE₂ found))
    ((body_at p N _).eqSymm.eqTrans (Prf.andE₁ (Prf.andE₂ found)))

theorem first_successor (p N : PTm n) (h0 : Γ ⊢[PRAAx] neg (sign (sample p N zero)))
    (hN : Γ ⊢[PRAAx] sign (sample p N N)) :
    Γ ⊢[PRAAx] first p N ≐ succ (leftIndex p N) := by
  have hit : Γ ⊢[PRAAx] test p N (first p N) ≐ zero := (first_found p N hN).andE₂
  refine .orE (zero_or_succ (first p N)) ?_ Prf.hyp0
  have e : ((first p N ≐ zero) :: Γ) ⊢[PRAAx] test p N (first p N) ≐ test p N zero :=
    test_congr (.eqRefl _) (.eqRefl _) Prf.hyp0
  exact .botE _ (.impE h0.wk (e.eqSymm.eqTrans hit.wk))

theorem before_first (p N i : PTm n) (hi : Γ ⊢[PRAAx] lt i (first p N)) :
    Γ ⊢[PRAAx] neg (sign (sample p N i)) := by
  have minimal := Search.search_minimal (f := body) (N := succ N) (x := input p N) hi
  exact .impI (.impE minimal.wk ((body_at p N i).wk.eqTrans Prf.hyp0))

theorem adjacent_samples (p N : PTm n) (h0 : Γ ⊢[PRAAx] neg (sign (sample p N zero)))
    (hN : Γ ⊢[PRAAx] sign (sample p N N)) :
    Γ ⊢[PRAAx] lt (leftIndex p N) N ⋏
      (neg (sign (sample p N (leftIndex p N))) ⋏ sign (sample p N (succ (leftIndex p N)))) := by
  have found := first_found p N hN
  have e := first_successor p N h0 hN
  have before : Γ ⊢[PRAAx] lt (leftIndex p N) (first p N) :=
    lt_congr (.eqRefl _) e.eqSymm (le_refl _)
  have right : Γ ⊢[PRAAx] test p N (first p N) ≐ zero := found.andE₂
  exact .andI (le_congr e (.eqRefl _) found.andE₁)
    (.andI (before_first p N _ before) ((test_congr (.eqRefl _) (.eqRefl _) e).eqSymm.eqTrans right))

def cellF : PR 2 := PTm.toPR (leftIndex (var 0) (var 1))

theorem program_at (p N : PTm n) : Γ ⊢[PRAAx] ap2 cellF p N ≐ leftIndex p N := by
  simpa only [cellF, ap2, subst_leftIndex, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one]
    using (toPR_eq (Γ := Γ) (leftIndex (var 0) (var 1)) ![p,N])

theorem original_digamma_grid_samples_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((neg (sign (sample (var 0) (var 1) zero)) ⋏ sign (sample (var 0) (var 1) (var 1))) ⟶
      lt (leftIndex (var 0) (var 1)) (var 1) ⋏
        (neg (sign (sample (var 0) (var 1) (leftIndex (var 0) (var 1)))) ⋏
          sign (sample (var 0) (var 1) (succ (leftIndex (var 0) (var 1)))))) :=
  closeUniv 2 (.impI (adjacent_samples _ _ (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaDyadicCrossing
