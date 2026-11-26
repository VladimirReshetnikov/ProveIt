import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalHigherCofinal
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianBoundedConstantProductName

/-!
# Factorial-scaled higher Barnes logarithmic coefficients

Scale the literal finite coefficient sums by the encoded degree
factorial. The corresponding normalized name retains exactly a
finite sum of the original factorial-scaled rows at its own clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherDerivative

open_ipra
open GaussianBarnesCanonicalHigherRows (degree derivative factorial_binding)
open GaussianBarnesCanonicalHigherCofinal (length sample)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (qmul)
open GaussianRationalFiniteSum (sum termsEqual multiplyBody multiply_body_at sum_multiply)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qmul_congr)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def body : PTm 2 :=
  derivative (fstT (fstT (var 1))) (sndT (fstT (var 1)))
    (succ (fstT (sndT (var 1))+var 0)) (sndT (sndT (var 1)))

def value (z B N j r : PTm n) : PTm n :=
  sum body r (GaussianBarnesCanonicalHigherTail.data z B N j)

def factorSize (j : PTm n) : PTm n := fact (degree j)

def factor (j : PTm n) : PTm n := radiusPoint (factorSize j) one

def nameF : PR 2 := GaussianBoundedConstantProductName.nameF GaussianBarnesCanonicalHigherCofinal.nameF

def data (z R B j : PTm n) : PTm n :=
  GaussianBoundedConstantProductName.data (factorSize j) (factor j)
    (GaussianBarnesCanonicalHigherCofinal.data z R B j)

def clock (p j : PTm n) : PTm n := GaussianBoundedConstantProductName.clock p (factorSize j)

@[simp] theorem subst_factorSize {m : ℕ} (σ : Fin n → PTm m) (j : PTm n) :
    Syn.subst σ (factorSize j) = factorSize (Syn.subst σ j) := by simp [factorSize]

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (z B N j r : PTm n) :
    Syn.subst σ (value z B N j r) = value (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N)
      (Syn.subst σ j) (Syn.subst σ r) := by simp [value]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B j : PTm n) :
    Syn.subst σ (data z R B j) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ j) := by
  simp [data,factor,GaussianBarnesCanonicalHigherCofinal.data]

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p j : PTm n) :
    Syn.subst σ (clock p j) = clock (Syn.subst σ p) (Syn.subst σ j) := by simp [clock]

theorem body_at (z B N j i : PTm n) :
    Γ ⊢[PRAAx] inst2 body i (GaussianBarnesCanonicalHigherTail.data z B N j) ≐ derivative z B (succ (N+i)) j := by
  let x := GaussianBarnesCanonicalHigherTail.data z B N j
  have u : Γ ⊢[PRAAx] fstT x ≐ pairT z B := fst_pair _ _
  have v : Γ ⊢[PRAAx] sndT x ≐ pairT N j := snd_pair _ _
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (derivative (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (fstT x),sndT (fstT x),succ (fstT (sndT x)+i),sndT (sndT x)])
    (σ' := ![z,B,succ (N+i),j]) (fun p => by
      fin_cases p
      · exact (congrFst u).eqTrans (fst_pair _ _)
      · exact (congrSnd u).eqTrans (snd_pair _ _)
      · exact congrSucc (congrAdd ((congrFst v).eqTrans (fst_pair _ _)) (.eqRefl _))
      · exact (congrSnd v).eqTrans (snd_pair _ _))
  simpa [body,inst2,x] using e

theorem finite_binding (z B N j r : PTm n) :
    Γ ⊢[PRAAx] qmul (factor j) (GaussianBarnesCanonicalHigherTail.value z B N j r) ≐ value z B N j r := by
  let t := GaussianBarnesCanonicalHigherTail.body
  let x := GaussianBarnesCanonicalHigherTail.data z B N j
  have terms : Γ ⊢[PRAAx] termsEqual (multiplyBody t) body r (pairT (factor j) x) x := by
    refine .allI (.impI ?_)
    let sh (s : PTm n) := Syn.shift s
    let i : PTm (n+1) := var 0
    let Δ := lt i (sh r) :: Γ.map Fm.shift
    let X := GaussianBarnesCanonicalHigherTail.data (sh z) (sh B) (sh N) (sh j)
    let k := succ (sh N+i)
    let c := GaussianBarnesCanonicalHigherRows.coefficient (sh z) (sh B) k (sh j)
    have read : Δ ⊢[PRAAx] inst2 t i X ≐ c :=
      GaussianBarnesCanonicalHigherTail.body_at (sh z) (sh B) (sh N) (sh j) i
    have scale : Δ ⊢[PRAAx] qmul c (factor (sh j)) ≐ derivative (sh z) (sh B) k (sh j) :=
      factorial_binding (sh z) (sh B) k (sh j) (zero_lt_succ _)
    have raw := multiply_body_at (Γ := Δ) t (factor (sh j)) i X
    have readProduct := qmul_congr (show Δ ⊢[PRAAx] factor (sh j) ≐ factor (sh j) from .eqRefl _) read
    have exchange := qmul_commutative (Γ := Δ) (factor (sh j)) c
    have out := body_at (Γ := Δ) (sh z) (sh B) (sh N) (sh j) i
    have row : Δ ⊢[PRAAx] inst2 (multiplyBody t) i (pairT (factor (sh j)) X) ≐ inst2 body i X :=
      raw.eqTrans (readProduct.eqTrans (exchange.eqTrans (scale.eqTrans out.eqSymm)))
    simpa only [termsEqual,Syn.shift,sh,Δ,i,x,X,subst_pairT,factor,subst_factorSize,
      GaussianDominantPairAlgebra.subst_radiusPoint,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,
      GaussianBarnesCanonicalHigherTail.subst_data] using row
  exact (sum_multiply t (factor j) r x).eqSymm.eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms)

theorem regular (z R B j : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B j) :=
  GaussianBoundedConstantProductName.name_regular _ _ _ _
    (.andI (GaussianBarnesCanonicalHigherCofinal.regular z R B j hs) (radius_bounded _ _ (le_refl one)))

theorem sample_at (p z R B j : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data z R B j) ≐ value z B (initial R) j (length (clock p j) j) := by
  have e := GaussianBoundedConstantProductName.sample_at (Γ := Γ) GaussianBarnesCanonicalHigherCofinal.nameF
    p (factorSize j) (factor j) (GaussianBarnesCanonicalHigherCofinal.data z R B j)
  exact e.eqTrans
    ((qmul_congr (.eqRefl _) (GaussianBarnesCanonicalHigherCofinal.sample_at (clock p j) z R B j)).eqTrans
      (finite_binding z B (initial R) j (length (clock p j) j)))

theorem actual_Barnes_all_higher_derivative_samples_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let p := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let j := var 4
     ap2 nameF p (data z R B j) ≐ value z B (initial R) j (length (clock p j) j)) :=
  closeUniv 5 (sample_at _ _ _ _ _)

theorem actual_Barnes_all_higher_derivative_names_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (regular _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherDerivative
