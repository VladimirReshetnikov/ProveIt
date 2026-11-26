import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelFrozenStrip

/-!
# Independent clocks for the finite Binet kernel

A fixed kernel cutoff controls the tail while the exponential and
cofinal product observations can be refined independently. The π clock
only has to accommodate the fixed number of retained rows.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelFrozenIndependent

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetKernelRows (inputData rowF rowBody regular_rows)
open GaussianBinetKernelTail (finiteF finiteData)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNameEquivalence (point_at)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRootApproximationWitness (pointBounds)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "K" => GaussianBinetKernelCofinal.nameF
local notation "Exp" => GaussianBinetLaplaceExponential.nameF
local notation "expData" => GaussianBinetLaplaceExponential.data
local notation "cofinalF" => GaussianBinetLaplaceIntegrand.cofinalF
local notation "cofinalData" => GaussianBinetLaplaceIntegrand.cofinalData
local notation "input" => GaussianBinetLaplaceIntegrand.input

def errorDenominator (p q I : PTm n) : PTm n := I*unit p*unit q
def kernelNumerator (p q I : PTm n) : PTm n := unit p*unit q+I*(num 3*unit q+unit p)
def dampedNumerator (p q I : PTm n) : PTm n :=
  two*(unit p*unit q)+I*(num 7*unit q+num 9*unit p)

@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (p q I : PTm n) :
    Syn.subst σ (errorDenominator p q I) =
      errorDenominator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ I) := by simp [errorDenominator]

@[simp] theorem subst_kernelNumerator {m : ℕ} (σ : Fin n → PTm m) (p q I : PTm n) :
    Syn.subst σ (kernelNumerator p q I) =
      kernelNumerator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ I) := by simp [kernelNumerator]

@[simp] theorem subst_dampedNumerator {m : ℕ} (σ : Fin n → PTm m) (p q I : PTm n) :
    Syn.subst σ (dampedNumerator p q I) =
      dampedNumerator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ I) := by simp [dampedNumerator]

theorem error_denominator_positive (p q I : PTm n) (hI : Γ ⊢[PRAAx] le one I) :
    Γ ⊢[PRAAx] le one (errorDenominator p q I) :=
  denominator_positive I p q hI

/-- The tail term is at most `1/I` with no comparison between `I` and either observation clock. -/
theorem kernel_error (p q k I A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hI : Γ ⊢[PRAAx] le one I) (hk : Γ ⊢[PRAAx] le (I*unit p) (unit k)) :
    Γ ⊢[PRAAx] distanceBounded (GaussianBinetKernelFrozenPrefix.value k I A B)
      (ap2 K q (inputData A B)) (kernelNumerator p q I) (errorDenominator p q I) := by
  let U := unit p
  let V := unit q
  let C := errorDenominator p q I
  let H := num 8*I
  have hU := unit_positive (Γ := Γ) p
  have hC := error_denominator_positive p q I hI
  have hH := positive_product _ _ (GaussianBinetKernelTailMajorant.eight_positive (Γ := Γ)) hI
  have hD := denominator_positive H q p hH
  have literal := GaussianNamedFiniteSumFamilySplit.finite_sample_distance rowF rowBody k p I
    (inputData A B) (regular_rows I A B hB) hk
  have a := distance_radius_mono _ _ two U (two*I*V) C hU hC
    (le_of_eq_add (d := zero) (by dsimp only [C,errorDenominator,U,V]; ipra_ring)) literal
  have named := rate_at K finiteF (inputData A B) (finiteData I A B) one H q p
    (GaussianBinetKernelCofinal.cutoff_rate I A B hI hB)
  have widen : Γ ⊢[PRAAx] le (rateNumerator one H q p*C)
      ((U*V+I*(U+V))*rateDenominator H q p) :=
    le_of_eq_add (d := num 7*I*(U*V)*(U*V))
      (by dsimp only [rateNumerator,rateDenominator,C,errorDenominator,H,U,V]; ipra_ring)
  have b := distance_radius_mono _ _ _ _ (U*V+I*(U+V)) C hD hC widen
    (distance_symmetric _ _ _ _ hD named)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [kernelNumerator,U,V]; ipra_ring) (.eqRefl C)
    (distance_triangle_same _ _ _ _ _ _ hC a b)

private theorem exp_bound (p X Y D sign R T A B : PTm n) (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] bounded (ap2 Exp p (expData X Y D sign R T A B)) two one := by
  have hp := unit_positive (Γ := Γ) p
  exact bounded_radius_mono _ _ _ _ _ hp (le_refl one) (by ipra_le sl hp)
    (GaussianBinetLaplaceExponential.unit_bound p X Y D sign R T A B h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)

private theorem kernel_bound (q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (ap2 K q (inputData A B)) one one :=
  bounded_radius_mono _ one (num 4) one one (by ipra_le 3) (le_refl one) (by ipra_le 3)
    (GaussianBinetKernelCoarseBound.cofinal_at q A B hB)

/-- The actual damped prefix differs from the original product observation by
`2/I + 7/2^p + 9/2^q` even when the exponential is sampled at a later clock `r`. -/
theorem late_damped_error (r p q k I X Y D sign R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T A B)
    (hI : Γ ⊢[PRAAx] le one I) (hk : Γ ⊢[PRAAx] le (I*unit p) (unit k))
    (hr : Γ ⊢[PRAAx] le p r) :
    Γ ⊢[PRAAx] distanceBounded (GaussianBinetKernelFrozenStrip.rowValue r k I X Y D sign R T A B)
      (ap2 cofinalF q (cofinalData X Y D sign R T A B))
      (dampedNumerator p q I) (errorDenominator p q I) := by
  let x := expData X Y D sign R T A B
  let y := inputData A B
  let U := unit p
  let V := unit q
  let C := errorDenominator p q I
  have hB := h.andE₂.andE₁
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hC := error_denominator_positive p q I hI
  have regExp := GaussianBinetLaplaceExponential.regular X Y D sign R T A B h.andE₁ hB h.andE₂.andE₂
  have regKernel := GaussianBinetKernelCofinal.regular A B hB
  have expBounds : Γ ⊢[PRAAx] pointBounds Exp two x := by
    refine .allI ?_
    let s (z : PTm n) := Syn.shift z
    have hs : Γ.map Fm.shift ⊢[PRAAx] input (s X) (s Y) (s D) (s sign) (s R) (s T) (s A) (s B) := by
      simpa only [Fm.shift,Syn.shift,s,GaussianBinetLaplaceIntegrand.subst_input] using h.shift
    simpa only [pointBounds,x,Syn.shift,s,GaussianBinetLaplaceExponential.subst_data,two,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using exp_bound (var 0) _ _ _ _ _ _ _ _ hs
  have kernelBounds : Γ ⊢[PRAAx] pointBounds K one y := by
    refine .allI ?_
    let s (z : PTm n) := Syn.shift z
    have hb : Γ.map Fm.shift ⊢[PRAAx] le one (s B) := by simpa [Fm.shift,Syn.shift,s] using hB.shift
    simpa only [pointBounds,y,Syn.shift,s,GaussianBinetKernelRows.subst_inputData,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using kernel_bound (var 0) (s A) (s B) hb
  have frozen := GaussianApproximateInverseDistance.multiply_distance (ap2 Exp r x) _ _ two
    (kernelNumerator p q I) C hC (exp_bound r X Y D sign R T A B h)
    (kernel_error p q k I A B hB hI hk)
  have late := GaussianExponentialReference.unit_monotone hr
  have clock := distance_radius_mono _ _ _ _ (U+V) (U*V)
    (positive_product _ _ (unit_positive r) hq) (positive_product _ _ hp hq)
    (by change Γ ⊢[PRAAx] le ((unit r+V)*(U*V)) ((U+V)*(unit r*V))
        ipra_le 𝔞(V)*𝔞(V)*sl late)
    (point_at Exp x r q regExp)
  have expMove := GaussianApproximateInverseDistance.multiply_distance (ap2 K q y) _ _ one
    (U+V) (U*V) (positive_product _ _ hp hq) (kernel_bound q A B hB)
    clock
  have move := distance_radius_mono _ _ _ _ (I*(U+V)) C (positive_product _ _ hp hq) hC
    (le_of_eq_add (d := zero) (by dsimp only [C,errorDenominator,U,V]; ipra_ring))
    (distance_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _)
      (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _) (.eqRefl _) expMove)
  have observed := GaussianNamedProductObservationBound.sample_error Exp K x y q two one
    regExp regKernel expBounds kernelBounds
  have original := distance_radius_mono _ _ _ _ (num 6*I*U) C hq hC
    (le_of_eq_add (d := zero) (by dsimp only [C,errorDenominator,U,V]; ipra_ring))
    (distance_symmetric _ _ _ _ hq observed)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [dampedNumerator,kernelNumerator,U,V]; ipra_ring) (.eqRefl C)
    (distance_triangle_same _ _ _ _ _ _ hC (distance_triangle_same _ _ _ _ _ _ hC frozen move) original)

theorem damped_error (p q k I X Y D sign R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T A B)
    (hI : Γ ⊢[PRAAx] le one I) (hk : Γ ⊢[PRAAx] le (I*unit p) (unit k)) :
    Γ ⊢[PRAAx] distanceBounded (GaussianBinetKernelFrozenStrip.rowValue p k I X Y D sign R T A B)
      (ap2 cofinalF q (cofinalData X Y D sign R T A B))
      (dampedNumerator p q I) (errorDenominator p q I) :=
  late_damped_error p p q k I X Y D sign R T A B h hI hk (le_refl p)

end LeanProofs.IPRA.Analysis.GaussianBinetKernelFrozenIndependent
