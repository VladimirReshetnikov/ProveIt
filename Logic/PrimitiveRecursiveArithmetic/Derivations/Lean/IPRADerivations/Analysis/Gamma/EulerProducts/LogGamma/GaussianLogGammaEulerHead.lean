import IPRADerivations.Analysis.Logarithm.RightHalfPlane.GaussianRightHalfPlaneLogarithm
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteSumFamily

/-!
# Finite Euler heads of canonical log-Gamma

On the encoded right half-plane, build the actual expression
log(N!) + z log(N) − Σ_{0 ≤ k ≤ N} Log(z+k).
Each term uses the same right-half-plane branch with the shifted real
numerator A+kD. The finite family has a regular common-clock sampler.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerHead

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (negativeF negativeData negative_fast)
open GaussianNamedFiniteProductFamily (regularRows)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalHorner (ofGaussian)
open GaussianRightHalfPlaneLogarithm (source)
open ComplexLogarithmRemainder (code)
open RationalArithmetic (select)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianRightHalfPlaneLogarithm.nameF
local notation "P" => GaussianRightHalfPlaneLogarithm.data
local notation "L" => GaussianPositiveRationalLogarithm.data

def argument (A B D neg : PTm n) : PTm n :=
  ofGaussian (code (ZT.ofNat A) ⟨select neg B zero, select neg zero B⟩) D

def rowData (A B D neg : PTm n) : PTm n := pairT A (pairT B (pairT D neg))

def rowBody : PTm 2 :=
  P (fstT (var 1)+var 0*fstT (sndT (sndT (var 1)))) (fstT (sndT (var 1)))
    (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1))))

def sumF : PR 2 := GaussianNamedFiniteSumFamily.nameF F rowBody
def sumData (A B D neg N : PTm n) : PTm n := GaussianNamedFiniteSumFamily.data (succ N) (rowData A B D neg)
def productF : PR 2 := multiplyF constantF logF
def productData (A B D neg N : PTm n) : PTm n := multiplyData constantF logF (argument A B D neg) (L N one)
def nameF : PR 2 := addF (addF logF productF) (negativeF sumF)
def data (A B D neg N : PTm n) : PTm n :=
  addData (addData (L (fact N) one) (productData A B D neg N)) (negativeData (sumData A B D neg N))

ipra_subst rowData

theorem row_at (i A B D neg : PTm n) :
    Γ ⊢[PRAAx] inst2 rowBody i (rowData A B D neg) ≐ P (A+i*D) B D neg := by
  let x := rowData A B D neg
  let e₁ := fst_pair (Γ := Γ) A (pairT B (pairT D neg))
  let e₂ := snd_pair (Γ := Γ) A (pairT B (pairT D neg))
  let e₃ := (congrSnd e₂).eqTrans (snd_pair B (pairT D neg))
  have h := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (P (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT x + i*fstT (sndT (sndT x)),fstT (sndT x),fstT (sndT (sndT x)),sndT (sndT (sndT x))])
    (σ' := ![A+i*D,B,D,neg]) (fun k => by
      fin_cases k
      · exact congrAdd e₁ (congrMul (.eqRefl _) ((congrFst e₃).eqTrans (fst_pair _ _)))
      · exact (congrFst e₂).eqTrans (fst_pair _ _)
      · exact (congrFst e₃).eqTrans (fst_pair _ _)
      · exact (congrSnd e₃).eqTrans (snd_pair _ _))
  simpa [rowBody,inst2,x] using h

theorem shifted_source (i A D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] source (A+i*D) D neg :=
  .andI (.andI (le_trans h.andE₁.andE₁ (le_add_right _ _)) h.andE₁.andE₂) h.andE₂

theorem sum_rows (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] regularRows F rowBody (succ N) (rowData A B D neg) := by
  refine .allI (.impI ?_)
  let sh (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh A) (sh D) (sh neg) := by
    simpa [Fm.shift,Syn.shift,sh,Δ,source,GaussianRightHalfPlaneArgument.source] using h.shift.wk
  have reg := GaussianRightHalfPlaneLogarithm.regular (sh A+var 0*sh D) (sh B) (sh D) (sh neg)
    (shifted_source (var 0) (sh A) (sh D) (sh neg) hs)
  have binding := row_at (Γ := Δ) (var 0) (sh A) (sh B) (sh D) (sh neg)
  let x := inst2 rowBody (var 0) (rowData (sh A) (sh B) (sh D) (sh neg))
  let y := P (sh A+var 0*sh D) (sh B) (sh D) (sh neg)
  have result : Δ ⊢[PRAAx] pointCN F x := by
    simpa only [GaussianEuclideanDistanceName.subst_pointCN,Syn.subst_var,Matrix.cons_val_zero] using
      Prf.eqSubst (Γ := Δ) (Ax := PRAAx) (pointCN F (var 0) : Fm PTm 1) ![y] ![x]
        (fun k => by fin_cases k; exact binding.eqSymm)
        (by simpa only [GaussianEuclideanDistanceName.subst_pointCN,Syn.subst_var,Matrix.cons_val_zero,y] using reg)
  simpa only [regularRows,Syn.shift,subst_rowData,sh,x,Δ] using result

theorem sum_regular (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] pointCN sumF (sumData A B D neg N) :=
  GaussianNamedFiniteSumFamily.regular F rowBody _ _ (sum_rows A B D neg N h)

theorem regular (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN nameF (data A B D neg N) := by
  have hf := GaussianPositiveRationalLogarithm.name_regular (Γ := Γ) (fact N) one
    (.andI (GammaEulerMesh.factorial_positive N) (le_refl one))
  have hn := GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one))
  have hp := multiply_fast constantF logF (argument A B D neg) (L N one) (constant_regular _) hn
  have hs := negative_fast sumF (sumData A B D neg N) (sum_regular A B D neg N h)
  exact add_fast (addF logF productF) (negativeF sumF) _ _ (add_fast logF productF _ _ hf hp) hs

theorem actual_log_Gamma_finite_Euler_head_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 2) (var 3) ⟶ le one (var 4) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (regular _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerHead
