import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondWeightedSineGrid
import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseFrozenOrigin

/-!
# The scheduled sine approximation to the shared frozen Bose prefix

The exact zero-origin readback identifies the old matrix with a finite
sum over the original positive geometric indices. Use the same indices
and frozen pi parameters for the weighted sine columns.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSinePrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetBoseFrozenMatrix (subst_frozenPiNumerator subst_piDenominator)
open GaussianBinetSecondDecayPointwise (frozenPiNumerator)
open GaussianBinetSecondWeightedSineGrid (parameters)
open GaussianBinetSecondWeightedSinePoint (cost subst_cost)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName
  (sampleData field0 field1 field2 field3 field5
    field0_at field1_at field2_at field3_at field5_at
    subst_field0 subst_field1 subst_field2 subst_field3 subst_field5)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalFiniteSum (sum)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (leftSum termsDistance sum_distance)
open GaussianStirlingConstant (piDenominator)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Frozen" => GaussianBinetBoseFrozenMatrix.value
local notation "frozenBody" => GaussianBinetSecondDecayFrozenTail.body
local notation "frozenData" => GaussianBinetSecondDecaySharedTail.data
local notation "SineGrid" => GaussianBinetSecondWeightedSineGrid.value

private def columnTerm (j q M T k z : PTm n) : PTm n :=
  leftSum GaussianBinetSecondWeightedSineGrid.body M
    (sampleData q M T (frozenPiNumerator (succ j) k) (piDenominator k) z) T one

@[simp] private theorem subst_columnTerm {m : ℕ} (σ : Fin n → PTm m) (j q M T k z : PTm n) :
    Syn.subst σ (columnTerm j q M T k z) =
      columnTerm (Syn.subst σ j) (Syn.subst σ q) (Syn.subst σ M) (Syn.subst σ T) (Syn.subst σ k) (Syn.subst σ z) := by
  simp [columnTerm,one]

def body : PTm 2 :=
  columnTerm (var 0) (field0 (var 1)) (field1 (var 1)) (field2 (var 1)) (field3 (var 1)) (field5 (var 1))

def data (q k M T X Y D sign R K : PTm n) : PTm n :=
  sampleData q M T k zero (parameters X Y D sign R K)

def value (q k N M T X Y D sign R K : PTm n) : PTm n :=
  sum body N (data q k M T X Y D sign R K)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (q k M T X Y D sign R K : PTm n) :
    Syn.subst σ (data q k M T X Y D sign R K) =
      data (Syn.subst σ q) (Syn.subst σ k) (Syn.subst σ M) (Syn.subst σ T)
        (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ R) (Syn.subst σ K) := by
  simp [data]

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (q k N M T X Y D sign R K : PTm n) :
    Syn.subst σ (value q k N M T X Y D sign R K) =
      value (Syn.subst σ q) (Syn.subst σ k) (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ T)
        (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ R) (Syn.subst σ K) := by
  simp [value]

theorem column_at (j q k M T X Y D sign R K : PTm n) :
    Γ ⊢[PRAAx] inst2 body j (data q k M T X Y D sign R K) ≐
      SineGrid q M T (frozenPiNumerator (succ j) k) (piDenominator k) X Y D sign R K := by
  let d := data q k M T X Y D sign R K
  let x := parameters X Y D sign R K
  have read : inst2 body j d = columnTerm j (field0 d) (field1 d) (field2 d) (field3 d) (field5 d) := by
    simp only [inst2,body,subst_columnTerm,subst_field0,subst_field1,subst_field2,subst_field3,subst_field5,
      Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [read]
  change Γ ⊢[PRAAx] columnTerm j (field0 d) (field1 d) (field2 d) (field3 d) (field5 d) ≐ columnTerm j q M T k x
  let a : Fin 6 → PTm n := ![j,field0 d,field1 d,field2 d,field3 d,field5 d]
  let b : Fin 6 → PTm n := ![j,q,M,T,k,x]
  let f : PTm 6 := columnTerm (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
  have raw := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) f (σ := a) (σ' := b) (fun i => by
    fin_cases i
    · exact .eqRefl _
    · exact field0_at q M T k zero x
    · exact field1_at q M T k zero x
    · exact field2_at q M T k zero x
    · exact field3_at q M T k zero x
    · exact field5_at q M T k zero x)
  have left : Syn.subst a f = columnTerm j (field0 d) (field1 d) (field2 d) (field3 d) (field5 d) := by
    dsimp only [f]
    rw [subst_columnTerm]
    rfl
  have right : Syn.subst b f = columnTerm j q M T k x := by
    dsimp only [f]
    rw [subst_columnTerm]
    rfl
  rw [left,right] at raw
  exact raw

private theorem original_column (j q k M T X Y D sign : PTm n) :
    Γ ⊢[PRAAx] inst2 frozenBody j (frozenData q M T k zero X Y D sign) ≐
      GaussianBinetSecondDecayGrid.value q M T (frozenPiNumerator (succ j) k) (piDenominator k) X Y D sign := by
  let h := frozenPiNumerator (succ (zero+j)) k
  let H := frozenPiNumerator (succ j) k
  let J := piDenominator k
  let s (v : PTm n) := Syn.shift v
  have e : Γ ⊢[PRAAx] h ≐ H := congrMul (congrSucc (zero_add j)) (.eqRefl _)
  have code : Γ ⊢[PRAAx] GaussianBinetSecondDecayGrid.value q M T h J X Y D sign ≐
      GaussianBinetSecondDecayGrid.value q M T H J X Y D sign := by
    simpa only [s,GaussianBinetSecondDecayGrid.subst_value,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (GaussianBinetSecondDecayGrid.value (s q) (s M) (s T) (var 0) (s J) (s X) (s Y) (s D) (s sign)) e
  exact (GaussianBinetSecondDecaySharedTail.row_at j q M T k zero X Y D sign).eqTrans code

theorem prefix_error (q k N M T X Y D sign R K : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hm : Γ ⊢[PRAAx] le one M) (hk : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] distanceBounded (Frozen q k N M X Y D sign zero T one)
      (value q k N M T X Y D sign R K) (N*(T*cost K T)) (unit q) := by
  let x := frozenData q M T k zero X Y D sign
  let y := data q k M T X Y D sign R K
  have rows : Γ ⊢[PRAAx] termsDistance frozenBody body N x y (T*cost K T) (unit q) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let j : PTm (n+1) := var 0
    let Δ := lt j (s N)::Γ.map Fm.shift
    let H := frozenPiNumerator (succ j) (s k)
    let J := piDenominator (s k)
    have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) :=
      by simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift.wk
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hm.shift.wk
    have ks : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hk.shift.wk
    have js : Δ ⊢[PRAAx] le one J := GaussianBinetKernelPi.denominator_positive (s k)
    have row := GaussianBinetSecondWeightedSineGrid.grid_error (s q) (s M) (s T) H J
      (s X) (s Y) (s D) (s sign) (s R) (s K) hs ms js ks
    have old := original_column (Γ := Δ) j (s q) (s k) (s M) (s T) (s X) (s Y) (s D) (s sign)
    have new := column_at (Γ := Δ) j (s q) (s k) (s M) (s T) (s X) (s Y) (s D) (s sign) (s R) (s K)
    simpa only [Δ,s,j,x,y,Syn.shift,GaussianBinetSecondDecaySharedTail.subst_data,subst_data,subst_cost,
      PTm.subst_mul,GaussianCoefficientNameBounds.subst_unit,ConciseIPRA.PTm.subst_zero] using
      distance_congr old.eqSymm new.eqSymm (.eqRefl _) (.eqRefl _) row
  exact distance_congr (GaussianBinetBoseFrozenOrigin.zero_origin q k N M X Y D sign T).eqSymm (.eqRefl _)
    (.eqRefl _) (.eqRefl _) (sum_distance _ _ _ _ _ _ _ (unit_positive q) rows)

theorem actual_second_Binet_frozen_prefix_sine_substitution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (let q := var 0
     let k := var 1
     let N := var 2
     let M := var 3
     let T := var 4
     let X := var 5
     let Y := var 6
     let D := var 7
     let sign := var 8
     let R := var 9
     let K := var 10
     (source X Y D sign R ⋏ le one M) ⋏ le D (K*X) ⟶
       distanceBounded (Frozen q k N M X Y D sign zero T one)
         (value q k N M T X Y D sign R K) (N*(T*cost K T)) (unit q)) :=
  closeUniv 11 (.impI (prefix_error _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSinePrefix
