import IPRADerivations.Analysis.Stirling.Binet.Laplace.Rectangles.GaussianBinetLaplaceWeightedGridProduct
import IPRADerivations.Analysis.Stirling.Binet.ExponentialIntegrals.GaussianBinetExponentialRectangleEvaluation

/-!
# Compare the common Binet strip grid with the original rectangle

The comparison uses literal left-cell readback for both strip
evaluators and the actual finite rectangle row. Its bound is uniform
in the number of outer time cells.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceWeightedGridRectangle

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceWeightedGridProduct (rowBudget difference_to_row)
open GaussianBinetLaplaceWeightedGridReadback (cell_samples)
open GaussianBinetLaplaceStrip (evaluatorF fixedData)
open GaussianBinetExponentialRectangle (outerBody outer_at)
open GaussianBinetExponentialRectangleEvaluation (rectangle)
open GaussianCompactRiemannName (sampleBody sampleData quadrature fraction_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerHead (argument)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub qnegative)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at weighted_difference)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound leftSum)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => evaluatorF GaussianBinetLaplaceStrip.Kernel.cofinal
local notation "domain" => GaussianLogGammaEulerResidualDomain.source
local notation "rectData" => GaussianBinetExponentialRectangle.data

def panelData (q N X Y D sign R T : PTm n) : PTm n :=
  sampleData q N (one+zero) T one (fixedData X Y D sign R T zero)

@[simp] theorem subst_panelData {m : ℕ} (σ : Fin n → PTm m) (q N X Y D sign R T : PTm n) :
    Syn.subst σ (panelData q N X Y D sign R T) =
      panelData (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D)
        (Syn.subst σ sign) (Syn.subst σ R) (Syn.subst σ T) := by
  simp [panelData,one]

private theorem subst_argument {m : ℕ} (σ : Fin n → PTm m) (X Y D sign : PTm n) :
    Syn.subst σ (argument X Y D sign) =
      argument (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) := by
  simp [argument, ZT.subst, ZT.ofNat]

private theorem subst_rowBudget {m : ℕ} (σ : Fin n → PTm m) (q M T : PTm n) :
    Syn.subst σ (rowBudget q M T) = rowBudget (Syn.subst σ q) (Syn.subst σ M) (Syn.subst σ T) := by
  simp [rowBudget, GaussianBinetLaplaceWeightedGridProduct.baseCost, two]

theorem row_distance (j q N M X Y D sign R S T : PTm n)
    (h : Γ ⊢[PRAAx] domain X Y D sign R) (hs : Γ ⊢[PRAAx] domain (X+D) Y D sign S)
    (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le one M) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (differenceBody (sampleBody F) (sampleBody F)) j
        (pairT (panelData q N X Y D sign R T) (panelData q N (X+D) Y D sign S T)))
      (inst2 outerBody j (rectData q (qnegative (argument X Y D sign)) (R*T) T N M))
      (rowBudget q M T) (M*unit q) := by
  have guard : Γ ⊢[PRAAx] le (T*j) (T*N) :=
    le_congr (mul_comm j T) (mul_comm N T) (mul_le_mul_right T (le_of_lt hj))
  have exactLeft := (difference_body_at (Γ := Γ) (sampleBody F) (sampleBody F) j
    (panelData q N X Y D sign R T) (panelData q N (X+D) Y D sign S T)).eqTrans
    (cell_samples j q N X Y D sign R S T)
  exact distance_congr exactLeft.eqSymm (outer_at j q (qnegative (argument X Y D sign)) (R*T) T N M).eqSymm
    (.eqRefl _) (.eqRefl _)
    (difference_to_row q M X Y D sign R S T (T*j) N (.andI h (.andI hN guard)) (.andI hs (.andI hN guard)) hM)

theorem quadrature_distance (q N M X Y D sign R S T : PTm n)
    (h : Γ ⊢[PRAAx] domain X Y D sign R) (hs : Γ ⊢[PRAAx] domain (X+D) Y D sign S)
    (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (quadrature F q N (one+zero) T one (fixedData X Y D sign R T zero))
        (quadrature F q N (one+zero) T one (fixedData (X+D) Y D sign S T zero)))
      (rectangle q X Y D sign R T N M) (T*rowBudget q M T) (M*unit q) := by
  let f := differenceBody (sampleBody F) (sampleBody F)
  let x := panelData q N X Y D sign R T
  let y := panelData q N (X+D) Y D sign S T
  let z := rectData q (qnegative (argument X Y D sign)) (R*T) T N M
  let B := rowBudget q M T
  let E := M*unit q
  have rows : Γ ⊢[PRAAx] termsDistance f outerBody N (pairT x y) z B E := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := Γ.map Fm.shift
    have hf : Δ ⊢[PRAAx] domain (s X) (s Y) (s D) (s sign) (s R) := by
      simpa only [s,Δ,Fm.shift,Syn.shift,GaussianLogGammaEulerResidualDomain.subst_source] using h.shift
    have hg : Δ ⊢[PRAAx] domain (s X+s D) (s Y) (s D) (s sign) (s S) := by
      simpa only [s,Δ,Fm.shift,Syn.shift,GaussianLogGammaEulerResidualDomain.subst_source,PTm.subst_add] using hs.shift
    have hn : Δ ⊢[PRAAx] le one (s N) := by simpa [s,Δ,Fm.shift,Syn.shift] using hN.shift
    have hm : Δ ⊢[PRAAx] le one (s M) := by simpa [s,Δ,Fm.shift,Syn.shift] using hM.shift
    simpa only [termsDistance, f, x, y, z, B, E, s, Δ, Syn.shift, subst_pairT, subst_panelData,
      GaussianBinetExponentialRectangle.subst_data, subst_argument, GaussianRationalMetric.subst_qnegative,
      subst_rowBudget, GaussianCoefficientNameBounds.subst_unit, PTm.subst_add, PTm.subst_mul] using
      row_distance (var 0) (s q) (s N) (s M) (s X) (s Y) (s D) (s sign) (s R) (s S) (s T)
        hf.wk hg.wk hn.wk hm.wk Prf.hyp0
  have he := positive_product M (unit q) hM (unit_positive q)
  have en := positive_product one N (le_refl one) hN
  have bound := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ en he
    (weight_bound T one N (le_refl _) hN) (sum_distance f outerBody N (pairT x y) z B E he rows)
  have old : Γ ⊢[PRAAx] distanceBounded (leftSum f N (pairT x y) T one) (leftSum outerBody N z T one)
      (T*(N*B)) ((one*N)*E) :=
    GaussianRationalReciprocal.bound_congr
      (GaussianRationalRoundedPower.multiplication_difference (weight T one N) _ _).eqSymm (.eqRefl _) (.eqRefl _) bound
  have eq := weighted_difference (Γ := Γ) (sampleBody F) (sampleBody F) N x y T one
  have eqRect : Γ ⊢[PRAAx] leftSum outerBody N z T one ≐ rectangle q X Y D sign R T N M :=
    GaussianRationalSyntheticDivision.qmul_congr (fraction_congr _ _ _ _ (.eqRefl T) (one_mul N)) (.eqRefl _)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ en he) he
    (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_congr eq.eqSymm eqRect (.eqRefl _) (.eqRefl _) old)

theorem actual_Binet_difference_grid_to_literal_rectangle_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let q := var 0
     let N := var 1
     let M := var 2
     let X := var 3
     let Y := var 4
     let D := var 5
     let sign := var 6
     let R := var 7
     let S := var 8
     let T := var 9
     (domain X Y D sign R ⋏ domain (X+D) Y D sign S) ⋏ (le one N ⋏ le one M) ⟶
       distanceBounded
         (qsub (quadrature F q N (one+zero) T one (fixedData X Y D sign R T zero))
           (quadrature F q N (one+zero) T one (fixedData (X+D) Y D sign S T zero)))
         (rectangle q X Y D sign R T N M) (T*rowBudget q M T) (M*unit q)) :=
  closeUniv 10 (.impI (quadrature_distance _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceWeightedGridRectangle
