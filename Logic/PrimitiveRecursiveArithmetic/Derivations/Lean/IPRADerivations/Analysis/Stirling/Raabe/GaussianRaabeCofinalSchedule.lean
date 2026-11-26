import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeStirlingMesh
import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeRightSide
import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeUnitGridShift

/-!
# Explicit cofinal choices for the original Raabe unit quadrature

The distant argument is chosen before the grid, and the grid before
the observation clock. Each comparison is put over one common
dyadic denominator using these choices.
-/

set_option autoImplicit false
set_option maxHeartbeats 880000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeCofinalSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianRaabeLogPrimitiveCell (primitive)
open GaussianRaabeStirlingMesh (biasCost)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def farStart (h A D : PTm n) : PTm n := A+unit h*D

def count (h A D : PTm n) : PTm n :=
  one+(two*unit h*farStart h A D*D+biasCost (farStart h A D))*unit h

def clockCost (J N R A D : PTm n) : PTm n :=
  one+num 8*J+two*J*R*N+(num 4*R+one)+(num 18+two*((R+D)*N))+
    two*A+GaussianRaabeRightSide.cost A

def clockFor (h N A D : PTm n) : PTm n :=
  exponent (clockCost (unit h) N (farStart h A D) A D) h

def clock (h A D : PTm n) : PTm n := clockFor h (count h A D) A D

@[simp] theorem subst_farStart {m : ℕ} (σ : Fin n → PTm m) (h A D : PTm n) :
    Syn.subst σ (farStart h A D) = farStart (Syn.subst σ h) (Syn.subst σ A) (Syn.subst σ D) := by
  simp [farStart]

@[simp] theorem subst_count {m : ℕ} (σ : Fin n → PTm m) (h A D : PTm n) :
    Syn.subst σ (count h A D) = count (Syn.subst σ h) (Syn.subst σ A) (Syn.subst σ D) := by
  simp [count,biasCost,GaussianCompactLogarithmBounds.radius,two,one]

@[simp] theorem subst_clockCost {m : ℕ} (σ : Fin n → PTm m) (J N R A D : PTm n) :
    Syn.subst σ (clockCost J N R A D) =
      clockCost (Syn.subst σ J) (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ D) := by
  simp [clockCost,GaussianRaabeRightSide.cost,one,two]

@[simp] theorem subst_clockFor {m : ℕ} (σ : Fin n → PTm m) (h N A D : PTm n) :
    Syn.subst σ (clockFor h N A D) =
      clockFor (Syn.subst σ h) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ D) := by simp [clockFor]

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (h A D : PTm n) :
    Syn.subst σ (clock h A D) = clock (Syn.subst σ h) (Syn.subst σ A) (Syn.subst σ D) := by simp [clock]

theorem clockFor_later (h N A D : PTm n) : Γ ⊢[PRAAx] le h (clockFor h N A D) := le_add_right _ _

theorem clock_later (h A D : PTm n) : Γ ⊢[PRAAx] le h (clock h A D) := clockFor_later _ _ _ _

theorem count_positive (h A D : PTm n) : Γ ⊢[PRAAx] le one (count h A D) := le_add_right _ _

theorem far_budget (h A D : PTm n) : Γ ⊢[PRAAx] le (D*unit h) (farStart h A D) :=
  le_congr (mul_comm _ _) (.eqRefl _) (le_add_left (unit h*D) A)

theorem far_admitted (h A D : PTm n) : Γ ⊢[PRAAx] le D (farStart h A D) :=
  le_trans (le_congr (one_mul D) (mul_comm _ _) (mul_le_mul_right D (unit_positive h))) (far_budget h A D)

private theorem mesh_allowances (h N A D : PTm n) (hn : Γ ⊢[PRAAx] le (count h A D) N) :
    let R := farStart h A D
    Γ ⊢[PRAAx] le ((two*unit h*R*D)*unit h) N ⋏ le (biasCost R*unit h) (two*N) := by
  let J := unit h
  let R := farStart h A D
  let T := two*J*R*D
  let V := biasCost R
  have x : Γ ⊢[PRAAx] le (T*J) (count h A D) := by
    change Γ ⊢[PRAAx] le (T*J) (one+(T+V)*J)
    ipra_le 1+𝔞(V)*𝔞(J)
  have y : Γ ⊢[PRAAx] le (V*J) (two*count h A D) := by
    change Γ ⊢[PRAAx] le (V*J) (two*(one+(T+V)*J))
    ipra_le 2+2*𝔞(T)*𝔞(J)+𝔞(V)*𝔞(J)
  exact .andI (le_trans x hn) (le_trans y (le_mul_mono (le_refl two) hn))

private theorem clock_allowances (h N A D : PTm n) :
    let J := unit h
    let R := farStart h A D
    let U := unit (clockFor h N A D)
    Γ ⊢[PRAAx] (le (num 8*J*J) U ⋏ le (two*J*R*N*J) U) ⋏
      ((le ((num 4*R+one)*J) U ⋏ le ((num 18+two*((R+D)*N))*J) U) ⋏
        (le (two*A*J) U ⋏ le (GaussianRaabeRightSide.cost A*J) U)) := by
  let J := unit h
  let R := farStart h A D
  let C := num 18+two*((R+D)*N)
  let S := GaussianRaabeRightSide.cost A
  let P := clockCost J N R A D
  have paid : Γ ⊢[PRAAx] le (P*J) (unit (clockFor h N A D)) := query_budget P h
  have a : Γ ⊢[PRAAx] le (num 8*J) P := by
    change Γ ⊢[PRAAx] le (num 8*J) (one+num 8*J+two*J*R*N+(num 4*R+one)+C+two*A+S)
    ipra_le 2+2*𝔞(J)*𝔞(R)*𝔞(N)+4*𝔞(R)+𝔞(C)+2*𝔞(A)+𝔞(S)
  have b : Γ ⊢[PRAAx] le (two*J*R*N) P := by
    change Γ ⊢[PRAAx] le (two*J*R*N) (one+num 8*J+two*J*R*N+(num 4*R+one)+C+two*A+S)
    ipra_le 2+8*𝔞(J)+4*𝔞(R)+𝔞(C)+2*𝔞(A)+𝔞(S)
  have c : Γ ⊢[PRAAx] le (num 4*R+one) P := by
    change Γ ⊢[PRAAx] le (num 4*R+one) (one+num 8*J+two*J*R*N+(num 4*R+one)+C+two*A+S)
    ipra_le 1+8*𝔞(J)+2*𝔞(J)*𝔞(R)*𝔞(N)+𝔞(C)+2*𝔞(A)+𝔞(S)
  have d : Γ ⊢[PRAAx] le C P := by
    change Γ ⊢[PRAAx] le C (one+num 8*J+two*J*R*N+(num 4*R+one)+C+two*A+S)
    ipra_le 2+8*𝔞(J)+2*𝔞(J)*𝔞(R)*𝔞(N)+4*𝔞(R)+2*𝔞(A)+𝔞(S)
  have e : Γ ⊢[PRAAx] le (two*A) P := by
    change Γ ⊢[PRAAx] le (two*A) (one+num 8*J+two*J*R*N+(num 4*R+one)+C+two*A+S)
    ipra_le 2+8*𝔞(J)+2*𝔞(J)*𝔞(R)*𝔞(N)+4*𝔞(R)+𝔞(C)+𝔞(S)
  have f : Γ ⊢[PRAAx] le S P := le_add_left _ _
  exact .andI (.andI (le_trans (mul_le_mul_right J a) paid) (le_trans (mul_le_mul_right J b) paid))
    (.andI (.andI (le_trans (mul_le_mul_right J c) paid) (le_trans (mul_le_mul_right J d) paid))
      (.andI (le_trans (mul_le_mul_right J e) paid) (le_trans (mul_le_mul_right J f) paid)))

theorem shift_budget_for (h N A D : PTm n) (hn : Γ ⊢[PRAAx] le (count h A D) N)
    (ha : Γ ⊢[PRAAx] le one A) (hd : Γ ⊢[PRAAx] le one D) :
    let J := unit h
    let p := clockFor h N A D
    Γ ⊢[PRAAx] le ((J*GaussianRaabeUnitGridShift.numerator p N A D J)*unit h)
      (num 3*GaussianRaabeUnitGridShift.denominator p N A D) := by
  let J := unit h
  let R := farStart h A D
  let p := clockFor h N A D
  let U := unit p
  have budgets := clock_allowances (Γ := Γ) h N A D
  have hm := mesh_allowances h N A D hn
  have a : Γ ⊢[PRAAx] le (num 8*J*J) U := budgets.andE₁.andE₁
  have b : Γ ⊢[PRAAx] le (two*J*R*D*J) ((A*A)*N) :=
    le_trans hm.andE₁ (le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N (positive_product _ _ ha ha)))
  have c : Γ ⊢[PRAAx] le (two*J*R*N*J) (D*U) :=
    le_trans budgets.andE₁.andE₂ (le_congr (one_mul U) (.eqRefl _) (mul_le_mul_right U hd))
  change Γ ⊢[PRAAx]
    le ((J*(num 8*(D*(A*A)*N)+two*R*(D*D)*U+two*R*(A*A)*(N*N)))*J) (num 3*(D*(A*A)*N*U))
  ipra_le 𝔞(D*(A*A)*N)*sl a+𝔞(D*U)*sl b+𝔞((A*A)*N)*sl c

theorem elementary_budget_for (h N A D : PTm n) (hn : Γ ⊢[PRAAx] le (count h A D) N)
    (hd : Γ ⊢[PRAAx] le one D) :
    let R := farStart h A D
    let p := clockFor h N A D
    Γ ⊢[PRAAx] le (GaussianRaabeStirlingMesh.errorNumerator p N R D*unit h)
      (num 6*GaussianRaabeStirlingMesh.errorDenominator p N R D) := by
  let J := unit h
  let R := farStart h A D
  let p := clockFor h N A D
  let U := unit p
  let B := biasCost R
  let X := two*N
  have a : Γ ⊢[PRAAx] le (D*J) R := far_budget h A D
  have enlarge : Γ ⊢[PRAAx] le (num 4*R+D) (D*(num 4*R+one)) := by
    ipra_le 𝔞(num 4*R)*sl hd
  have scaled : Γ ⊢[PRAAx] le ((num 4*R+D)*J) (D*((num 4*R+one)*J)) :=
    le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right J enlarge)
  have b : Γ ⊢[PRAAx] le ((num 4*R+D)*J) (D*U) :=
    le_trans scaled (le_mul_mono (le_refl D) (clock_allowances h N A D).andE₂.andE₁.andE₁)
  have c : Γ ⊢[PRAAx] le (B*J) X := (mesh_allowances h N A D hn).andE₂
  change Γ ⊢[PRAAx]
    le (((num 4*(D*D)*U+num 4*(R*R)+R*D)*X+B*(R*D*U))*J) (num 6*((R*D*U)*X))
  ipra_le 𝔞(num 4*D*U*X)*sl a+𝔞(R*X)*sl b+𝔞(R*D*U)*sl c

theorem remainder_budget_for (h N A D : PTm n) :
    let R := farStart h A D
    let p := clockFor h N A D
    Γ ⊢[PRAAx] le ((two*D*unit p+(num 18+two*((R+D)*N))*R)*unit h) (num 3*(R*unit p)) := by
  let J := unit h
  let R := farStart h A D
  let U := unit (clockFor h N A D)
  let C := num 18+two*((R+D)*N)
  have a : Γ ⊢[PRAAx] le (D*J) R := far_budget h A D
  have b : Γ ⊢[PRAAx] le (C*J) U := (clock_allowances h N A D).andE₂.andE₁.andE₂
  change Γ ⊢[PRAAx] le ((two*D*U+C*R)*J) (num 3*(R*U))
  ipra_le 𝔞(two*U)*sl a+𝔞(R)*sl b

theorem endpoint_budgets_for (h N A D : PTm n) :
    Γ ⊢[PRAAx] le (two*A*unit h) (unit (clockFor h N A D)) ⋏
      le (GaussianRaabeRightSide.cost A*unit h) (unit (clockFor h N A D)) :=
  (clock_allowances h N A D).andE₂.andE₂

theorem shift_budget (h A D : PTm n) (ha : Γ ⊢[PRAAx] le one A) (hd : Γ ⊢[PRAAx] le one D) :
    let J := unit h
    let N := count h A D
    let p := clock h A D
    Γ ⊢[PRAAx] le ((J*GaussianRaabeUnitGridShift.numerator p N A D J)*unit h)
      (num 3*GaussianRaabeUnitGridShift.denominator p N A D) :=
  shift_budget_for h (count h A D) A D (le_refl _) ha hd

theorem elementary_budget (h A D : PTm n) (hd : Γ ⊢[PRAAx] le one D) :
    let R := farStart h A D
    let N := count h A D
    let p := clock h A D
    Γ ⊢[PRAAx] le (GaussianRaabeStirlingMesh.errorNumerator p N R D*unit h)
      (num 6*GaussianRaabeStirlingMesh.errorDenominator p N R D) :=
  elementary_budget_for h (count h A D) A D (le_refl _) hd

theorem remainder_budget (h A D : PTm n) :
    let R := farStart h A D
    let N := count h A D
    let p := clock h A D
    Γ ⊢[PRAAx] le ((two*D*unit p+(num 18+two*((R+D)*N))*R)*unit h) (num 3*(R*unit p)) :=
  remainder_budget_for h (count h A D) A D

theorem endpoint_budgets (h A D : PTm n) :
    Γ ⊢[PRAAx] le (two*A*unit h) (unit (clock h A D)) ⋏
      le (GaussianRaabeRightSide.cost A*unit h) (unit (clock h A D)) :=
  endpoint_budgets_for h (count h A D) A D

end LeanProofs.IPRA.Analysis.GaussianRaabeCofinalSchedule
