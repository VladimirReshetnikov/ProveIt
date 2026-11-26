import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerFullHeadInverse
import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.GaussianGammaGaussEulerHeads
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaGaussReferenceProduct
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductFamily
import IPRADerivations.Analysis.Gamma.GaussianGammaCompactCutoffSplit

/-!
# The full-head Euler exponential families

The shifted and reference products use the exponent programs from the
full-head factorization of the original Euler approximations. The
packed inputs are also used by the corresponding rational head folds.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerFactorFamilies

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEulerDenominatorGrouping (shiftedNumerator shiftedData)
open GaussianGammaEulerFullHeadInverse (negExpF negExpData subst_negExpData negative_exponential_regular)
open GaussianGammaGaussReferenceProduct (argument)
open GaussianNamedFiniteProductFamily (regularRows rowF productData)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def shiftedExpBody : PTm 2 :=
  let x : PTm 2 := var 1
  let m := fstT (sndT x)
  let z := fstT (sndT (sndT x))
  let B := sndT (sndT (sndT x))
  negExpData (shiftedNumerator z B m (var 0)) (B*m) (fstT x)

def referenceExpBody : PTm 2 := negExpData (argument (var 0)) (fstT (var 1)) (sndT (var 1))

abbrev shiftedF : PR 2 := GaussianNamedFiniteProductName.nameF (rowF negExpF shiftedExpBody)
abbrev referenceF : PR 2 := GaussianNamedFiniteProductName.nameF (rowF negExpF referenceExpBody)
def shiftedExpData (z B m N : PTm n) : PTm n := productData negExpF shiftedExpBody m (shiftedData z B m N)
def referenceExpData (m N : PTm n) : PTm n := productData negExpF referenceExpBody m (pairT m N)

@[simp] theorem subst_shiftedExpData {l : ℕ} (σ : Fin n → PTm l) (z B m N : PTm n) :
    Syn.subst σ (shiftedExpData z B m N) =
      shiftedExpData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ N) := by
  simp [shiftedExpData,productData,one]

@[simp] theorem subst_referenceExpData {l : ℕ} (σ : Fin n → PTm l) (m N : PTm n) :
    Syn.subst σ (referenceExpData m N) = referenceExpData (Syn.subst σ m) (Syn.subst σ N) := by
  simp [referenceExpData,productData,one]

theorem shifted_exp_at (r z B m N : PTm n) : Γ ⊢[PRAAx]
    inst2 shiftedExpBody r (shiftedData z B m N) ≐ negExpData (shiftedNumerator z B m r) (B*m) N := by
  let x := shiftedData z B m N
  have tail := snd_pair (Γ := Γ) N (pairT m (pairT z B))
  have fields := (congrSnd tail).eqTrans (snd_pair _ _)
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (negExpData (shiftedNumerator (var 0) (var 1) (var 2) (var 3)) (var 1*var 2) (var 4) : PTm 5)
    (σ := ![fstT (sndT (sndT x)),sndT (sndT (sndT x)),fstT (sndT x),r,fstT x])
    (σ' := ![z,B,m,r,N]) (fun i => by
      fin_cases i
      · exact (congrFst fields).eqTrans (fst_pair _ _)
      · exact (congrSnd fields).eqTrans (snd_pair _ _)
      · exact (congrFst tail).eqTrans (fst_pair _ _)
      · exact .eqRefl _
      · exact fst_pair _ _)
  simpa [shiftedExpBody, shiftedNumerator, inst2, x] using e

theorem reference_exp_at (r m N : PTm n) : Γ ⊢[PRAAx]
    inst2 referenceExpBody r (pairT m N) ≐ negExpData (argument r) m N := by
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (negExpData (argument (var 0)) (var 1) (var 2) : PTm 3)
    (σ := ![r,fstT (pairT m N),sndT (pairT m N)]) (σ' := ![r,m,N]) (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact snd_pair _ _)
  simpa only [referenceExpBody, inst2, subst_negExpData, GaussianGammaGaussReferenceProduct.subst_argument,
    subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using e

theorem shifted_exp_regular (z B m N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] regularRows negExpF shiftedExpBody m (shiftedData z B m N) := by
  refine .allI (.impI ?_)
  let sh (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (sh m) :: Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ, sh, Fm.shift, Syn.shift, one] using hN.shift.wk
  simpa [Δ, sh, Syn.shift] using GaussianGammaCompactCutoffSplit.point_data_congr negExpF _ _
    (shifted_exp_at (Γ := Δ) (var 0) (sh z) (sh B) (sh m) (sh N)).eqSymm
    (negative_exponential_regular (shiftedNumerator (sh z) (sh B) (sh m) (var 0)) (sh B*sh m) (sh N) h)

theorem reference_exp_regular (m N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] regularRows negExpF referenceExpBody m (pairT m N) := by
  refine .allI (.impI ?_)
  let sh (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (sh m) :: Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ, sh, Fm.shift, Syn.shift, one] using hN.shift.wk
  simpa [Δ, sh, Syn.shift] using GaussianGammaCompactCutoffSplit.point_data_congr negExpF _ _
    (reference_exp_at (Γ := Δ) (var 0) (sh m) (sh N)).eqSymm
    (negative_exponential_regular (argument (var 0)) (sh m) (sh N) h)

end LeanProofs.IPRA.Analysis.GaussianGaussEulerFactorFamilies
