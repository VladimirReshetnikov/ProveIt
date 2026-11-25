import IPRADerivations.Analysis.GaussianBinetArctangentSineGridComparison
import IPRADerivations.Analysis.GaussianCompactMeshIndependence
import IPRADerivations.Analysis.GaussianFastValueCut
import IPRADerivations.AnalyticNumberTheory.ZetaFiniteContract

/-!
# A common damped sine schedule for the actual arctangent sampler

Using a legitimate physical horizon instead of the raw angle numerator
makes the auxiliary angular mesh independent of the rational tag. The
damping mesh is a multiple of four. Its observation clock absorbs the
quadratic mesh factor in the original cleared sine error.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetArctangentSineUniform

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentQuadrature (evaluatorF fixedData nameF data)
open GaussianBinetArctangentSineGridComparison
  (cosineDenominator sineDenominator combinedDenominator combinedNumerator)
open GaussianBinetArctangentCosineLaplace (error)
open GaussianBinetExponentialIntegral (uniformCost numerator)
open GaussianBinetOscillatorySineRows (numeratorBound)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (quadrature mesh mesh_positive precision)
open GaussianFastValueCut (exponent query_budget)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "Sine" => GaussianBinetOscillatorySineRectangle.value

def cutoff (k U K : PTm n) : PTm n := succ (exponent (num 5*U*K) k)
def cellFactor (k T U : PTm n) : PTm n :=
  unit k*(one+U*T+num 4*T*((U*T)*(U*T)))
def angularScale (k D U T : PTm n) : PTm n := cellFactor k T U*mesh k (D*D) U
def roundingCost (k D R U K T : PTm n) : PTm n :=
  U*K*uniformCost (R+U) T+num 10*T*U+(num 20*num 16)*T*angularScale k D U T
def clock (k D R U K : PTm n) : PTm n :=
  let L := cutoff k U K
  L+exponent (roundingCost k D R U K (D*L)) k
def count (k D R U K : PTm n) : PTm n :=
  num 4*((R+U)*(D*cutoff k U K)+unit (clock k D R U K))
def angleMesh (k D U T N : PTm n) : PTm n := (N*cellFactor k T U)*mesh k (D*D) U

@[simp] theorem subst_cutoff {m : ℕ} (σ : Fin n → PTm m) (k U K : PTm n) :
    Syn.subst σ (cutoff k U K) = cutoff (Syn.subst σ k) (Syn.subst σ U) (Syn.subst σ K) := by
  simp [cutoff]
@[simp] theorem subst_cellFactor {m : ℕ} (σ : Fin n → PTm m) (k T U : PTm n) :
    Syn.subst σ (cellFactor k T U) = cellFactor (Syn.subst σ k) (Syn.subst σ T) (Syn.subst σ U) := by
  simp [cellFactor,one]
@[simp] theorem subst_angularScale {m : ℕ} (σ : Fin n → PTm m) (k D U T : PTm n) :
    Syn.subst σ (angularScale k D U T) = angularScale (Syn.subst σ k) (Syn.subst σ D) (Syn.subst σ U) (Syn.subst σ T) := by
  simp [angularScale]
@[simp] theorem subst_roundingCost {m : ℕ} (σ : Fin n → PTm m) (k D R U K T : PTm n) :
    Syn.subst σ (roundingCost k D R U K T) =
      roundingCost (Syn.subst σ k) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ U) (Syn.subst σ K) (Syn.subst σ T) := by
  simp [roundingCost,uniformCost,two]
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (k D R U K : PTm n) :
    Syn.subst σ (clock k D R U K) = clock (Syn.subst σ k) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ U) (Syn.subst σ K) := by
  simp [clock]
@[simp] theorem subst_count {m : ℕ} (σ : Fin n → PTm m) (k D R U K : PTm n) :
    Syn.subst σ (count k D R U K) = count (Syn.subst σ k) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ U) (Syn.subst σ K) := by
  simp [count]
@[simp] theorem subst_angleMesh {m : ℕ} (σ : Fin n → PTm m) (k D U T N : PTm n) :
    Syn.subst σ (angleMesh k D U T N) =
      angleMesh (Syn.subst σ k) (Syn.subst σ D) (Syn.subst σ U) (Syn.subst σ T) (Syn.subst σ N) := by
  simp [angleMesh]

theorem cutoff_positive (k U K : PTm n) : Γ ⊢[PRAAx] le one (cutoff k U K) := zero_lt_succ _
theorem cutoff_le_clock (k D R U K : PTm n) : Γ ⊢[PRAAx] le (cutoff k U K) (clock k D R U K) :=
  le_add_right _ _

theorem cutoff_budget (k U K : PTm n) : Γ ⊢[PRAAx] le ((num 5*U*K)*unit k) (unit (cutoff k U K)) :=
  le_trans (query_budget _ _) (GaussianExponentialReference.unit_monotone (le_succ_self _))

theorem clock_budget (k D R U K : PTm n) : Γ ⊢[PRAAx]
    le (roundingCost k D R U K (D*cutoff k U K)*unit k) (unit (clock k D R U K)) :=
  le_trans (query_budget _ _) (GaussianExponentialReference.unit_monotone (le_add_left _ _))

theorem count_dominates (k D R U K : PTm n) : Γ ⊢[PRAAx]
    le ((R+U)*(D*cutoff k U K)) (count k D R U K) ⋏ le (unit (clock k D R U K)) (count k D R U K) := by
  let base := (R+U)*(D*cutoff k U K)+unit (clock k D R U K)
  have grow : Γ ⊢[PRAAx] le base (count k D R U K) := by
    change Γ ⊢[PRAAx] le base (num 4*base)
    ipra_le 3*𝔞(base)
  exact .andI (le_trans (le_add_right _ _) grow) (le_trans (le_add_left _ _) grow)

private theorem square_count (j : PTm n) : Γ ⊢[PRAAx] le ((num 4*j)*(num 4*j)) (num 16*unit (num 4*j)) := by
  have half : Γ ⊢[PRAAx] le (j+j) (num 4*j) := by ipra_le 2*𝔞(j)
  have square := sq_le_sq (LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract.le_pow_self (Γ := Γ) j)
  have exponential := le_trans (le_congr (.eqRefl _) (pw_add two j j).eqSymm square)
    (GaussianExponentialReference.unit_monotone half)
  exact le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (num 16)) exponential)

private theorem factor_positive (k T U : PTm n) : Γ ⊢[PRAAx] le one (cellFactor k T U) :=
  positive_product _ _ (unit_positive k) (le_trans (le_add_right _ _) (le_add_right _ _))

private theorem angular_budget (k D U T N : PTm n) (hn : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le (U*T) (angleMesh k D U T N) ⋏
      le (num 4*T*N*((U*T)*(U*T))*unit k) (angleMesh k D U T N) := by
  let C := U*T
  let F := num 4*T*(C*C)
  let H := one+C+F
  let V := mesh k (D*D) U
  have hV : Γ ⊢[PRAAx] le one V := mesh_positive _ _ _
  have hk := unit_positive (Γ := Γ) k
  have f : Γ ⊢[PRAAx] le F H := le_add_left F (one+C)
  have c : Γ ⊢[PRAAx] le C H := le_trans (le_add_left C one) (le_add_right (one+C) F)
  have right : Γ ⊢[PRAAx] le (N*unit k*H) (angleMesh k D U T N) := by
    have grow := le_mul_mono (le_refl (N*(unit k*H))) hV
    exact le_congr (by ipra_ring) (.eqRefl _) grow
  have first : Γ ⊢[PRAAx] le C (N*unit k*H) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (positive_product _ _ hn hk) c)
  have last : Γ ⊢[PRAAx] le (num 4*T*N*(C*C)*unit k) (N*unit k*H) :=
    le_congr (by dsimp only [F]; ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (N*unit k)) f)
  exact .andI (le_trans first right) (le_trans last right)

private theorem cosine_budget (p k A B R U K T L : PTm n)
    (hA : Γ ⊢[PRAAx] le A (B*U))
    (hp : Γ ⊢[PRAAx] le (U*K*uniformCost (R+U) T*unit k) (unit p))
    (hl : Γ ⊢[PRAAx] le ((num 5*U*K)*unit k) (unit L)) :
    Γ ⊢[PRAAx] le (A*error p R U K T L*unit k) (two*cosineDenominator p B L) := by
  unfold error cosineDenominator
  ipra_le
    𝔞(K*(uniformCost (R+U) T*unit L+num 5*unit p)*unit k)*sl hA+
    𝔞(B*unit L)*sl hp+𝔞(B*unit p)*sl hl

private theorem sine_budget (p k M D A B U L N : PTm n)
    (hA : Γ ⊢[PRAAx] le A (B*U))
    (hround₁ : Γ ⊢[PRAAx] le (num 10*(D*L)*U*unit k) (unit (p+N)))
    (hround₂ : Γ ⊢[PRAAx] le (num 20*(D*L)*N*M*unit k) (unit (p+N)))
    (hdisc : Γ ⊢[PRAAx] le (num 4*(D*L)*N*((U*(D*L))*(U*(D*L)))*unit k) M) :
    Γ ⊢[PRAAx] le ((D*L)*numeratorBound p M D A B U L N*unit k) (num 3*sineDenominator p B M N) := by
  unfold numeratorBound numerator sineDenominator
  ipra_le
    𝔞(num 10*(D*L)*M*unit k)*sl hA+
    𝔞(B*M)*sl hround₁+𝔞(B*M)*sl hround₂+𝔞(B*unit (p+N))*sl hdisc

private theorem compare_mesh (k M X Y D sign A B R U N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hb : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le A (B*U)) (hM : Γ ⊢[PRAAx] M ≐ N*mesh k (D*D) U)
    (hn : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF k (data X Y D sign A B))
      (quadrature evaluatorF (precision k U) M (B+zero) A B (fixedData X Y D sign)) (num 5) (unit k) := by
  let x := fixedData X Y D sign
  let F := evaluatorF
  let w := GaussianCompactRiemannName.data (B+zero) A B (D*D) U x
  let q := ap2 nameF k w
  let z := ap2 nameF k (data X Y D sign A B)
  let v := quadrature F (precision k U) M (B+zero) A B x
  have first := GaussianBinetArctangentQuadrature.compact_input X Y D sign A B hz.andE₁ hb
  have other : Γ ⊢[PRAAx] GaussianCompactRiemannName.input F (B+zero) A B (D*D) U x :=
    .andI first.andE₁ (.andI hb (.andI ha first.andE₂.andE₂.andE₂))
  have aligned := GaussianCompactMeshIndependence.name_independence F (B+zero) A B (D*D) A (D*D) U x (.andI first other)
  have hk := unit_positive (Γ := Γ) k
  have first' : Γ ⊢[PRAAx] distanceBounded z q two (unit k) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hk hk) hk
      (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianNameEquivalence.cross_at nameF nameF (data X Y D sign A B) w k k aligned)
  have raw := GaussianCompactMeshIndependence.arbitrary_refinement F k (precision k U) N (B+zero) A B (D*D) U x
    other hn (le_refl _)
  have last : Γ ⊢[PRAAx] distanceBounded v q (num 3) (unit (k+num 6)) :=
    distance_congr (GaussianCompactRiemannName.quadrature_index_congr F (precision k U) _ _ (B+zero) A B x hM.eqSymm)
      (GaussianCompactRiemannName.name_at F k (B+zero) A B (D*D) U x).eqSymm (.eqRefl _) (.eqRefl _) raw
  have wide := distance_radius_mono _ _ _ _ (num 3) (unit k) (unit_positive _) hk
    (le_mul_mono (le_refl (num 3)) (GaussianExponentialReference.unit_monotone (le_add_right k _))) last
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same z q v _ _ _ hk first' (distance_symmetric _ _ _ _ hk wide))

theorem sample_error (k X Y D sign A B R U K : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hb : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le A (B*U)) (hm : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF k (data X Y D sign A B))
      (Sine (clock k D R U K) X Y D sign A B R U (cutoff k U K) (count k D R U K))
      (num 10) (unit k) := by
  let L := cutoff k U K
  let T := D*L
  let p := clock k D R U K
  let N := count k D R U K
  let G := angularScale k D U T
  let M := angleMesh k D U T N
  let C := uniformCost (R+U) T
  let W := roundingCost k D R U K T
  let V := combinedDenominator p B M L N
  have hl : Γ ⊢[PRAAx] le one L := cutoff_positive _ _ _
  have hp := unit_positive (Γ := Γ) p
  have hk := unit_positive (Γ := Γ) k
  have orders := count_dominates (Γ := Γ) k D R U K
  have hn : Γ ⊢[PRAAx] le one N := le_trans hp orders.andE₂
  have hR : Γ ⊢[PRAAx] le one (N*cellFactor k T U) := positive_product _ _ hn (factor_positive _ _ _)
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hR (mesh_positive _ _ _)
  have MW : Γ ⊢[PRAAx] M ≐ N*G := by dsimp only [M,G,angleMesh,angularScale]; ipra_ring
  have hW : Γ ⊢[PRAAx] le (W*unit k) (unit p) := clock_budget _ _ _ _ _
  have cosCost : Γ ⊢[PRAAx] le (U*K*C*unit k) (unit p) := by
    have cost : Γ ⊢[PRAAx] le (U*K*C) W := by
      dsimp only [W,roundingCost,C]
      exact le_trans (le_add_right _ _) (le_add_right _ _)
    exact le_trans (le_mul_mono cost (le_refl (unit k))) hW
  have sineCost₁ : Γ ⊢[PRAAx] le (num 10*T*U*unit k) (unit (p+N)) := by
    have cost : Γ ⊢[PRAAx] le (num 10*T*U) W := by
      dsimp only [W,roundingCost]
      exact le_trans (le_add_left _ _) (le_add_right _ _)
    exact le_trans (le_trans (le_mul_mono cost (le_refl (unit k))) hW)
      (GaussianExponentialReference.unit_monotone (le_add_right p N))
  have sineCost₂ : Γ ⊢[PRAAx] le (num 20*T*N*M*unit k) (unit (p+N)) := by
    have hs : Γ ⊢[PRAAx] le (N*N) (num 16*unit N) := square_count _
    have first : Γ ⊢[PRAAx] le (num 20*T*N*(N*G)*unit k) (((num 20*num 16)*T*G*unit k)*unit N) := by
      ipra_le 𝔞(num 20*T*G*unit k)*sl hs
    have cost : Γ ⊢[PRAAx] le ((num 20*num 16)*T*G) W := by
      dsimp only [W,G,roundingCost]
      exact le_add_left _ _
    have scale := le_trans (le_mul_mono cost (le_refl (unit k))) hW
    exact le_trans (le_congr (by exact congrMul (congrMul (.eqRefl _) MW.eqSymm) (.eqRefl _)) (.eqRefl _) first)
      (le_congr (.eqRefl _) (pw_add two p N).eqSymm (le_mul_mono scale (le_refl (unit N))))
  have ang := angular_budget k D U T N hn
  have cos := cosine_budget p k A B R U K T L ha cosCost (cutoff_budget _ _ _)
  have sin := sine_budget p k M D A B U L N ha sineCost₁ sineCost₂ ang.andE₂
  have budget : Γ ⊢[PRAAx] le (combinedNumerator p M D A B R U K L N*unit k) (num 5*V) := by
    dsimp only [combinedNumerator,V,combinedDenominator]
    ipra_le 𝔞(sineDenominator p B M N)*sl cos+𝔞(cosineDenominator p B L)*sl sin
  have den : Γ ⊢[PRAAx] le one V :=
    positive_product _ _ (positive_product _ _ hb (positive_product _ _ hp (unit_positive L)))
      (positive_product _ _ (positive_product _ _ hb hM) (unit_positive (p+N)))
  have raw := GaussianBinetArctangentSineGridComparison.quadrature_error p (precision k U) M X Y D sign A B R U K L N
    hz hb hM ha hm hl (cutoff_le_clock _ _ _ _ _) orders.andE₁ orders.andE₂ ang.andE₁
  have last := distance_radius_mono _ _ _ _ (num 5) (unit k) den hk budget raw
  have first := compare_mesh k M X Y D sign A B R U (N*cellFactor k T U) hz hb ha (.eqRefl _) hR
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hk first last)

theorem actual_Binet_uniform_sine_rectangle_approximation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let k := var 0
     let X := var 1
     let Y := var 2
     let D := var 3
     let sign := var 4
     let A := var 5
     let B := var 6
     let R := var 7
     let U := var 8
     let K := var 9
     (source X Y D sign R ⋏ le one B) ⋏ (le A (B*U) ⋏ le D (K*X)) ⟶
       distanceBounded (ap2 nameF k (data X Y D sign A B))
         (Sine (clock k D R U K) X Y D sign A B R U (cutoff k U K) (count k D R U K)) (num 10) (unit k)) :=
  closeUniv 10 (.impI (sample_error _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetArctangentSineUniform
