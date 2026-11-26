import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceIntegrand
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianApproximateInverseDistance
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedProductObservationBound
import IPRADerivations.Analysis.Integration.RiemannSums.GaussianRationalRiemannRefinement

/-!
# Finite Binet kernel rows at one π observation

The literal prefix uses the original finite Gaussian sum at a shared
row clock. A cutoff and clock budget give a uniform comparison with
the original cofinal Binet kernel, including after multiplication
by the original Gaussian Laplace exponential.
-/

set_option autoImplicit false
set_option maxHeartbeats 780000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelFrozenPrefix

open_ipra
open GaussianBinetKernelRows (inputData rowF rowBody row_at row_sample regular_rows)
open GaussianBinetKernelTail (finiteF finiteData)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianRootApproximationWitness (pointBounds)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "K" => GaussianBinetKernelCofinal.nameF
local notation "Exp" => GaussianBinetLaplaceExponential.nameF
local notation "expData" => GaussianBinetLaplaceExponential.data
local notation "cofinalF" => GaussianBinetLaplaceIntegrand.cofinalF
local notation "cofinalData" => GaussianBinetLaplaceIntegrand.cofinalData
local notation "input" => GaussianBinetLaplaceIntegrand.input

abbrev body : PTm 2 := GaussianNamedFiniteSumFamily.body rowF rowBody
def data (k A B : PTm n) : PTm n := pairT k (inputData A B)
def value (k N A B : PTm n) : PTm n := sum body N (data k A B)

ipra_subst data

ipra_subst value

theorem term_at (i k A B : PTm n) : Γ ⊢[PRAAx] inst2 body i (data k A B) ≐ GaussianBinetKernelRows.value k (succ i) A B :=
  (GaussianNamedFiniteSumFamily.term_at rowF rowBody i k (inputData A B)).eqTrans
    ((congrAp2 rowF (.eqRefl _) (row_at i A B)).eqTrans (row_sample k i A B))

theorem named_at (p N A B : PTm n) :
    Γ ⊢[PRAAx] ap2 finiteF p (finiteData N A B) ≐ value (GaussianFastValueCut.exponent N p) N A B :=
  GaussianNamedFiniteSumFamily.sample_at rowF rowBody p N (inputData A B)

theorem kernel_error (p k N A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le (unit p) N) (hk : Γ ⊢[PRAAx] le (N*unit p) (unit k)) :
    Γ ⊢[PRAAx] distanceBounded (value k N A B) (ap2 K p (inputData A B)) (num 4) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have frozen := GaussianNamedFiniteSumFamilySplit.finite_sample_distance rowF rowBody k p N (inputData A B)
    (regular_rows N A B hB) hk
  have tail := GaussianBinetKernelCofinal.late_observations p p N A B hN hB
  have tail' := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) tail
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp frozen (distance_symmetric _ _ _ _ hp tail'))

abbrev dampedBody : PTm 2 := multiplyBody body
def dampedData (c k A B : PTm n) : PTm n := pairT c (data k A B)
def dampedValue (c k N A B : PTm n) : PTm n := qmul c (value k N A B)

ipra_subst dampedData

theorem damped_term (i c k A B : PTm n) : Γ ⊢[PRAAx]
    inst2 dampedBody i (dampedData c k A B) ≐ qmul c (GaussianBinetKernelRows.value k (succ i) A B) :=
  (multiply_body_at body c i (data k A B)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (term_at i k A B))

theorem damped_sum (c k N A B : PTm n) : Γ ⊢[PRAAx]
    sum dampedBody N (dampedData c k A B) ≐ dampedValue c k N A B :=
  sum_multiply body c N (data k A B)

private theorem exp_bound (p X Y D sign R T A B : PTm n) (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] bounded (ap2 Exp p (expData X Y D sign R T A B)) two one := by
  have hp := unit_positive (Γ := Γ) p
  exact bounded_radius_mono _ _ _ _ _ hp (le_refl one) (by ipra_le sl hp)
    (GaussianBinetLaplaceExponential.unit_bound p X Y D sign R T A B h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)

theorem damped_error (p k N X Y D sign R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T A B)
    (hN : Γ ⊢[PRAAx] le (unit p) N) (hk : Γ ⊢[PRAAx] le (N*unit p) (unit k)) :
    Γ ⊢[PRAAx] distanceBounded
      (dampedValue (ap2 Exp p (expData X Y D sign R T A B)) k N A B)
      (ap2 cofinalF p (cofinalData X Y D sign R T A B)) (num 14) (unit p) := by
  let x := expData X Y D sign R T A B
  let y := inputData A B
  let c := ap2 Exp p x
  have hp := unit_positive (Γ := Γ) p
  have baseExp := GaussianBinetLaplaceExponential.regular X Y D sign R T A B h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂
  have baseKernel := GaussianBinetKernelCofinal.regular A B h.andE₂.andE₁
  have frozen := GaussianApproximateInverseDistance.multiply_distance c _ _ two _ (unit p) hp
    (exp_bound p X Y D sign R T A B h) (kernel_error p k N A B h.andE₂.andE₁ hN hk)
  have boundsExp : Γ ⊢[PRAAx] pointBounds Exp two x := by
    refine .allI ?_
    let s (z : PTm n) := Syn.shift z
    have hs : Γ.map Fm.shift ⊢[PRAAx] input (s X) (s Y) (s D) (s sign) (s R) (s T) (s A) (s B) := by
      simpa only [Fm.shift,Syn.shift,s,GaussianBinetLaplaceIntegrand.subst_input] using h.shift
    simpa only [pointBounds,x,Syn.shift,s,GaussianBinetLaplaceExponential.subst_data,two,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using exp_bound (var 0) _ _ _ _ _ _ _ _ hs
  have boundsKernel : Γ ⊢[PRAAx] pointBounds K one y := by
    refine .allI ?_
    let s (z : PTm n) := Syn.shift z
    have hb : Γ.map Fm.shift ⊢[PRAAx] le one (s B) := by simpa [Fm.shift,Syn.shift,s] using h.andE₂.andE₁.shift
    have small := GaussianBinetKernelCoarseBound.cofinal_at (var 0) (s A) (s B) hb
    have bound := bounded_radius_mono _ one (num 4) one one (by ipra_le 3) (le_refl one) (by ipra_le 3) small
    simpa only [pointBounds,y,Syn.shift,s,GaussianBinetKernelRows.subst_inputData,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using bound
  have original := GaussianNamedProductObservationBound.sample_error Exp K x y p two one baseExp baseKernel boundsExp boundsKernel
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp frozen (distance_symmetric _ _ _ _ hp original))

/-- Accumulate a common finite transform error and then pass to the original Laplace integrand. -/
theorem transformed_sum_error (f : PTm 2) (x E p k N X Y D sign R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T A B)
    (hN : Γ ⊢[PRAAx] le (unit p) N) (hk : Γ ⊢[PRAAx] le (N*unit p) (unit k))
    (rows : Γ ⊢[PRAAx] termsDistance f dampedBody N x
      (dampedData (ap2 Exp p (expData X Y D sign R T A B)) k A B) E (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (sum f N x) (ap2 cofinalF p (cofinalData X Y D sign R T A B))
      (N*E+num 14) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have transformed := distance_congr (.eqRefl _) (damped_sum _ _ _ _ _) (.eqRefl _) (.eqRefl _)
    (sum_distance f dampedBody N x _ E (unit p) hp rows)
  exact distance_triangle_same _ _ _ _ _ _ hp transformed (damped_error p k N X Y D sign R T A B h hN hk)

end LeanProofs.IPRA.Analysis.GaussianBinetKernelFrozenPrefix
