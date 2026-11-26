import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupBlockChord
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelBoundary
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteSumFamily
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaFactorialLogSum

/-!
# The literal finite Bohr–Mollerup brackets

For n=j+1, the common term of the two original names is
log(j!) - sum_{i=0}^j log(x+i). The remaining arguments are j and
j+B. Named algebra and the actual logarithm product law reduce the
literal difference to x*log((j+B)/j).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupBracketEndpoints

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaRationalWendelBoundary (difference_cross)
open GaussianGammaStrongLogConvexityAlgebra (swap_first)
open GaussianNamedFiniteProductFamily (regularRows)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedRealOrderLinear (fractionData fractional_regular)
open GaussianNaturalScaleProductName (productF)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianStirlingGammaLogarithm (source)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "logData" => GaussianHarmonicLogarithmName.data
local notation "D" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "R" => productF H

def rowBody : PTm 2 :=
  logData (fstT (var 1)+sndT (var 1)*var 0) (sndT (var 1))

abbrev sumF : PR 2 := GaussianNamedFiniteSumFamily.nameF H rowBody
def sumData (a b N : PTm n) : PTm n := GaussianNamedFiniteSumFamily.data N (pairT a b)

@[simp] theorem subst_sumData {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (sumData a b N) = sumData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [sumData]

theorem row_at (i a b : PTm n) :
    Γ ⊢[PRAAx] inst2 rowBody i (pairT a b) ≐ logData (a+b*i) b := by
  have ha := fst_pair (Γ := Γ) a b
  have hb := snd_pair (Γ := Γ) a b
  simpa only [inst2,rowBody,GaussianHarmonicLogarithmName.data,subst_pairT,PTm.subst_add,PTm.subst_mul,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val] using
    congrPairT (congrAdd ha (congrMul hb (.eqRefl i))) hb

theorem sum_regular (a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN sumF (sumData a b N) := by
  apply GaussianNamedFiniteSumFamily.regular H rowBody
  refine .allI (.impI ?_)
  let s (v : PTm n) := Syn.shift v
  let Δ := lt (var 0) (s N)::Γ.map Fm.shift
  let j : PTm (n+1) := var 0
  have h : Δ ⊢[PRAAx] source (s a) (s b) := by simpa [Δ,s,Fm.shift,Syn.shift] using hs.shift.wk
  have hh := GaussianHarmonicLogarithmName.name_regular (s a+s b*j) (s b)
    (.andI (le_trans h.andE₁ (le_add_right _ _)) h.andE₂)
  have e := row_at (Γ := Δ) j (s a) (s b)
  simpa only [Δ,s,j,Syn.shift,subst_pairT] using
    GaussianGammaCompactCutoffSplit.point_data_congr H _ _ e.eqSymm hh

abbrev baseF : PR 2 := D H sumF
def baseData (a b j : PTm n) : PTm n := dd (logData (fact j) one) (sumData a b (succ j))
abbrev bracketF : PR 2 := addF baseF R
def endpointData (a b j r : PTm n) : PTm n :=
  addData (baseData a b j) (fractionData H a b (logData r one))
def lowerData (a b j : PTm n) : PTm n := endpointData a b j j
def upperData (a b B j : PTm n) : PTm n := endpointData a b j (j+B)
def ratioData (a b B j : PTm n) : PTm n := fractionData H a b (logData (j+B) j)
abbrev widthF : PR 2 := D bracketF bracketF
def widthData (a b B j : PTm n) : PTm n := dd (upperData a b B j) (lowerData a b j)

@[simp] theorem subst_baseData {m : ℕ} (σ : Fin n → PTm m) (a b j : PTm n) :
    Syn.subst σ (baseData a b j) = baseData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ j) := by simp [baseData,one]
@[simp] theorem subst_ratioData {m : ℕ} (σ : Fin n → PTm m) (a b B j : PTm n) :
    Syn.subst σ (ratioData a b B j) = ratioData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ B) (Syn.subst σ j) := by
  simp [ratioData,fractionData]
@[simp] theorem subst_endpointData {m : ℕ} (σ : Fin n → PTm m) (a b j r : PTm n) :
    Syn.subst σ (endpointData a b j r) = endpointData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ j) (Syn.subst σ r) := by
  simp [endpointData,fractionData,one]
@[simp] theorem subst_lowerData {m : ℕ} (σ : Fin n → PTm m) (a b j : PTm n) :
    Syn.subst σ (lowerData a b j) = lowerData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ j) := by simp [lowerData]
@[simp] theorem subst_upperData {m : ℕ} (σ : Fin n → PTm m) (a b B j : PTm n) :
    Syn.subst σ (upperData a b B j) = upperData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ B) (Syn.subst σ j) := by simp [upperData]
@[simp] theorem subst_widthData {m : ℕ} (σ : Fin n → PTm m) (a b B j : PTm n) :
    Syn.subst σ (widthData a b B j) = widthData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ B) (Syn.subst σ j) := by simp [widthData]

theorem base_regular (a b j : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN baseF (baseData a b j) :=
  GaussianNamedDifference.name_regular _ _ _ _
    (GaussianHarmonicLogarithmName.name_regular (fact j) one
      (.andI (GammaEulerMesh.factorial_positive j) (le_refl one))) (sum_regular a b (succ j) hs)

theorem endpoint_regular (a b j r : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] pointCN bracketF (endpointData a b j r) :=
  add_fast _ _ _ _ (base_regular a b j hs)
    (fractional_regular H a b _ (GaussianHarmonicLogarithmName.name_regular r one (.andI hr (le_refl one))))

theorem ratio_regular (a b B j : PTm n) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] pointCN R (ratioData a b B j) :=
  fractional_regular H a b _ (GaussianHarmonicLogarithmName.name_regular (j+B) j
    (.andI (le_trans hj (le_add_right _ _)) hj))

private theorem ratio_plus_lower (a b B j : PTm n) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] crossEquivalent (addF R R) R
      (addData (ratioData a b B j) (fractionData H a b (logData j one)))
      (fractionData H a b (logData (j+B) one)) := by
  let u := logData (j+B) j
  let v := logData j one
  let w := logData (j+B) one
  let c := fraction a b
  have hJ := le_trans hj (le_add_right j B)
  have hc := constant_regular (Γ := Γ) c
  have hu := GaussianHarmonicLogarithmName.name_regular (j+B) j (.andI hJ hj)
  have hv := GaussianHarmonicLogarithmName.name_regular j one (.andI hj (le_refl one))
  have hw := GaussianHarmonicLogarithmName.name_regular (j+B) one (.andI hJ (le_refl one))
  have distribution := GaussianNameRingLaws.distributive constantF H H c u v hc hu hv
  have fold := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF (addF H H) H c c (addData u v) w
    hc hc (add_fast _ _ _ _ hu hv) hw (cross_refl _ _ hc) (GaussianGammaRationalLogWendel.log_ratio_sum (j+B) j one hJ hj (le_refl one))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ distribution) fold

theorem upper_decomposition (a b B j : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] crossEquivalent (addF R bracketF) bracketF (addData (ratioData a b B j) (lowerData a b j)) (upperData a b B j) := by
  let x := baseData a b j
  let y := fractionData H a b (logData j one)
  let z := fractionData H a b (logData (j+B) one)
  let u := ratioData a b B j
  have hx := base_regular a b j hs
  have hy := fractional_regular H a b (logData j one) (GaussianHarmonicLogarithmName.name_regular j one (.andI hj (le_refl one)))
  have hz := fractional_regular H a b _ (GaussianHarmonicLogarithmName.name_regular (j+B) one
    (.andI (le_trans hj (le_add_right j B)) (le_refl one)))
  have hu := ratio_regular a b B j hj
  have swap := swap_first R baseF R u x y hu hx hy
  have combine := add_cross baseF baseF (addF R R) R x x (addData u y) z
    hx hx (add_fast _ _ _ _ hu hy) hz (cross_refl _ _ hx) (ratio_plus_lower a b B j hj)
  exact cross_trans _ _ _ _ _ _ swap combine

theorem width_identity (a b B j : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] crossEquivalent widthF R (widthData a b B j) (ratioData a b B j) := by
  let x := lowerData a b j
  let z := upperData a b B j
  let w := ratioData a b B j
  have hx := endpoint_regular a b j j hs hj
  have hz := endpoint_regular a b j (j+B) hs (le_trans hj (le_add_right j B))
  have hw := ratio_regular a b B j hj
  have h := upper_decomposition a b B j hs hj
  have first := difference_cross bracketF (addF R bracketF) bracketF bracketF z (addData w x) x x
    hz (add_fast _ _ _ _ hw hx) hx hx (cross_symm _ _ _ _ h) (cross_refl _ _ hx)
  exact cross_trans _ _ _ _ _ _ first (GaussianNamedStrictOrderDifference.sum_sub_right R bracketF w x hw hx)

theorem actual_literal_Bohr_Mollerup_bracket_width_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) ⟶ le one (var 3) ⟶
      crossEquivalent widthF R (widthData (var 0) (var 1) (var 2) (var 3)) (ratioData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (width_identity _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupBracketEndpoints
