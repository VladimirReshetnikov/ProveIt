import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerFactorSum
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaFactorialLogSum
import IPRADerivations.Analysis.Gamma.BohrMollerup.Uniqueness.GaussianBohrMollerupDifference
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness

/-!
# Cancel the factorial logarithm in the finite Euler head

The actual denominator split supplies the finite sum of integer
logarithms and the canonical rows at 1+z/k. Identify the integer sum
with the original log(N!) and move that term to the same position in
both operands. The existing cancellation law gives the normalized
finite Euler head at arbitrary independent observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNormalizedHead

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLogGammaEulerHead (argument productF productData rowData sumData)
open GaussianLogGammaEulerFactorSum (integerF integerBody residualF residualBody tailF)
open GaussianNameArithmetic (addF addData add_fast multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative add_commutative)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRightHalfPlaneLogarithm (source)
open Products (fact)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "P" => GaussianRightHalfPlaneLogarithm.data
local notation "L" => GaussianPositiveRationalLogarithm.data
local notation "sd" => GaussianNamedFiniteSumFamily.data
local notation "diffF" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data

def denominatorF : PR 2 := addF G residualF

def denominatorData (A B D neg N : PTm n) : PTm n :=
  addData (P A B D neg) (sd N (rowData A B D neg))

def nameF : PR 2 := diffF productF denominatorF

def data (A B D neg N : PTm n) : PTm n :=
  diffData (productData A B D neg N) (denominatorData A B D neg N)

@[simp] theorem subst_denominatorData {m : ℕ} (σ : Fin n → PTm m) (A B D neg N : PTm n) :
    Syn.subst σ (denominatorData A B D neg N) =
      denominatorData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ N) := by
  simp [denominatorData]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A B D neg N : PTm n) :
    Syn.subst σ (data A B D neg N) =
      data (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ N) := by
  simp [data,productData,argument,ZT.subst,ZT.ofNat,one]

theorem product_regular (A B D neg N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN productF (productData A B D neg N) :=
  multiply_fast constantF logF (argument A B D neg) (L N one) (constant_regular _)
    (GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one)))

theorem denominator_regular (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] pointCN denominatorF (denominatorData A B D neg N) :=
  add_fast G residualF _ _
    (GaussianRightHalfPlaneLogarithm.regular A B D neg h)
    (GaussianNamedFiniteSumFamily.regular G residualBody N (rowData A B D neg)
      (GaussianLogGammaEulerFactorSum.residual_rows A B D neg N h))

theorem regular (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] pointCN nameF (data A B D neg N) :=
  GaussianNamedDifference.name_regular _ _ _ _ (product_regular A B D neg N hN) (denominator_regular A B D neg N h)

private theorem swap_middle (F H J : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hh : Γ ⊢[PRAAx] pointCN H y) (hj : Γ ⊢[PRAAx] pointCN J z) :
    Γ ⊢[PRAAx] crossEquivalent (addF F (addF H J)) (addF H (addF F J))
      (addData x (addData y z)) (addData y (addData x z)) := by
  have first := cross_symm _ _ _ _ (add_associative F H J x y z hf hh hj)
  have middle := add_cross (addF F H) (addF H F) J J (addData x y) (addData y x) z z
    (add_fast _ _ _ _ hf hh) (add_fast _ _ _ _ hh hf) hj hj
    (add_commutative F H x y hf hh) (cross_refl _ _ hj)
  exact cross_trans _ _ _ _ _ _ first
    (cross_trans _ _ _ _ _ _ middle (add_associative H F J y x z hh hf hj))

theorem denominator_with_factorial (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent GaussianLogGammaEulerHead.sumF (addF logF denominatorF) (sumData A B D neg N)
      (addData (L (fact N) one) (denominatorData A B D neg N)) := by
  let x := rowData A B D neg
  let s := sd N x
  let z := P A B D neg
  let a := L (fact N) one
  have hZ := GaussianRightHalfPlaneLogarithm.regular A B D neg h
  have hA := GaussianPositiveRationalLogarithm.name_regular (fact N) one
    (.andI (GammaEulerMesh.factorial_positive (Γ := Γ) N) (le_refl one))
  have hI : Γ ⊢[PRAAx] pointCN integerF s := GaussianNamedFiniteSumFamily.regular logF integerBody N x
    (GaussianLogGammaEulerFactorSum.integer_rows N x)
  have hR : Γ ⊢[PRAAx] pointCN residualF s := GaussianNamedFiniteSumFamily.regular G residualBody N x
    (GaussianLogGammaEulerFactorSum.residual_rows A B D neg N h)
  have factEq : Γ ⊢[PRAAx] crossEquivalent logF integerF a s :=
    GaussianLogGammaFactorialLogSum.factorial_logarithm_cross N x
  have inner := add_cross integerF logF residualF residualF s a s s hI hA hR hR
    (cross_symm _ _ _ _ factEq) (cross_refl _ _ hR)
  have replace := add_cross G G tailF (addF logF residualF) z z (addData s s) (addData a s)
    hZ hZ (add_fast _ _ _ _ hI hR) (add_fast _ _ _ _ hA hR) (cross_refl _ _ hZ) inner
  exact cross_trans _ _ _ _ _ _ (GaussianLogGammaEulerFactorSum.denominator_split A B D neg N h)
    (cross_trans _ _ _ _ _ _ replace (swap_middle G logF residualF z a s hZ hA hR))

theorem equivalent (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent GaussianLogGammaEulerHead.nameF nameF
      (GaussianLogGammaEulerHead.data A B D neg N) (data A B D neg N) := by
  let a := L (fact N) one
  let x := productData A B D neg N
  let y := denominatorData A B D neg N
  let s := sumData A B D neg N
  have ha := GaussianPositiveRationalLogarithm.name_regular (fact N) one
    (.andI (GammaEulerMesh.factorial_positive (Γ := Γ) N) (le_refl one))
  have hx := product_regular A B D neg N hN
  have hy := denominator_regular A B D neg N h
  have hs := GaussianLogGammaEulerHead.sum_regular A B D neg N h
  have hax := add_fast logF productF a x ha hx
  have hay := add_fast logF denominatorF a y ha hy
  have first := GaussianNamedDifferenceQuotientProperness.difference_proper
    (addF logF productF) (addF logF productF) GaussianLogGammaEulerHead.sumF (addF logF denominatorF)
    (addData a x) (addData a x) s (addData a y) hax hax hs hay (cross_refl _ _ hax)
    (denominator_with_factorial A B D neg N h)
  exact cross_trans _ _ _ _ _ _ first
    (GaussianBohrMollerupDifference.cancel_common logF productF denominatorF a x y ha hx hy)

theorem actual_finite_Euler_logarithm_normalized_head_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 2) (var 3) ⟶ le one (var 4) ⟶
        crossEquivalent GaussianLogGammaEulerHead.nameF nameF
          (GaussianLogGammaEulerHead.data (var 0) (var 1) (var 2) (var 3) (var 4))
          (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (equivalent _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNormalizedHead
