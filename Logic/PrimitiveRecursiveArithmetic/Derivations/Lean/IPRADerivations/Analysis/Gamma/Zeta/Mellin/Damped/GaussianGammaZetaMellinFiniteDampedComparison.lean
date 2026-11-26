import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.GaussianGammaZetaMellinFiniteDampedGrid
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.GaussianGammaZetaMellinFiniteDampedModulus
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Compact.GaussianGammaZetaMellinCompact
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence
import IPRADerivations.Analysis.Names.Rates.Moduli.GaussianNamedLipschitzRate

/-!
# Finite damped and original Mellin names on a positive compact panel

The two original compact samplers are compared on a common product
mesh. The estimate retains the finite geometric error and pays the
observation allowances by late clocks. The number of needed damped
rows depends on the positive panel and the desired precision.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteDampedComparison

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (quadrature mesh precision)
open GaussianEulerCompactPowerMajorant (majorant)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaZetaMellinDampedPoint (cost)
open GaussianGammaZetaMellinDampedStrip (totalNumerator dampedValue)
open GaussianGammaZetaMellinDecayPrefix (errorNumerator errorDenominator)
open GaussianGammaZetaMellinStrip (window mellinValue gridBudget clock)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "F" => GaussianGammaZetaMellinFiniteDampedEvaluator.evaluatorF
local notation "X" => GaussianGammaZetaMellinFiniteDampedEvaluator.data
local notation "L" => GaussianGammaZetaMellinFiniteDampedModulus.lipschitz
local notation "G" => GaussianGammaZetaMellinGrid.evaluatorF
local notation "Y" => GaussianGammaZetaMellinGrid.fixedData
local notation "K" => GaussianGammaZetaMellinCompact.gain
local notation "Original" => GaussianGammaZetaMellinCompact.nameF
local notation "originalData" => GaussianGammaZetaMellinCompact.data
local notation "source" => GaussianGammaZetaMellinCompact.source

abbrev finiteF : PR 2 := GaussianCompactRiemannName.nameF F
def finiteData (z R B N Q a C E T : PTm n) : PTm n :=
  GaussianCompactRiemannName.data a C E (L N R E T) T (X z B N Q)
def finiteInput (z R B N Q a C E T : PTm n) : Fm PTm n :=
  GaussianCompactRiemannName.input F a C E (L N R E T) T (X z B N Q)

def numerator (R H T C : PTm n) : PTm n := C*majorant R H T*(H*H)
def denominator (E H N : PTm n) : PTm n := E*(H+N)
def clockCost (R H T C : PTm n) : PTm n := C*(majorant R H T+cost R H T)
def finiteClock (p R H T C : PTm n) : PTm n := exponent (clockCost R H T C) (precision p T)
def threshold (h R H T : PTm n) : PTm n := T*majorant R H T*(H*H)*unit h

ipra_subst finiteData
ipra_subst finiteInput
ipra_subst numerator [majorant, GaussianEulerCompactPowerMajorant.exponentRadius, one]
ipra_subst denominator
ipra_subst threshold [majorant, GaussianEulerCompactPowerMajorant.exponentRadius, one]

theorem denominator_positive (z R B N a C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B a C E H T) : Γ ⊢[PRAAx] le one (denominator E H N) :=
  positive_product _ _ hz.andE₂.andE₁.andE₂ (le_trans hz.andE₁.andE₂.andE₁ (le_add_right H N))

theorem finite_input (z R B N Q a C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B a C E H T) (hNQ : Γ ⊢[PRAAx] le N Q) :
    Γ ⊢[PRAAx] finiteInput z R B N Q a C E T := by
  have ha := hz.andE₂.andE₁.andE₁
  have hE := hz.andE₂.andE₁.andE₂
  have hT := le_congr (.eqRefl _) (mul_comm T E) hz.andE₂.andE₂.andE₂
  have original : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B a C E T :=
    .andI (.andI hz.andE₁.andE₁ (.andI hE hz.andE₁.andE₂.andE₂)) (.andI ha hT)
  exact .andI ha (.andI hE (.andI (le_trans (le_add_left C a) hT)
    (GaussianGammaZetaMellinFiniteDampedModulus.original_sampled_modulus z R B N Q a C E T original hNQ)))

/-- The finite evaluator may retain any admitted row-clock budget Q. -/
theorem grid_error (h s z R B M N Q a C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B a C E H T) (hM : Γ ⊢[PRAAx] le one M)
    (hNQ : Γ ⊢[PRAAx] le N Q) (hs : Γ ⊢[PRAAx] le h s) :
    let q := exponent Q s
    let p := clock q M N a C E
    Γ ⊢[PRAAx] distanceBounded (quadrature G p M a C E (Y z B))
      (quadrature F s M a C E (X z B N Q))
      (totalNumerator h H N R T C) (E*errorDenominator h H N) := by
  intro q p
  let P := majorant R H T
  let J := cost R H T
  let D := E*errorDenominator h H N
  let V := gridBudget M N a C E
  have hE := hz.andE₂.andE₁.andE₂
  have dq : Γ ⊢[PRAAx] le q p := le_add_right _ _
  have sq : Γ ⊢[PRAAx] le s q := le_add_right _ _
  have hv : Γ ⊢[PRAAx] le (V*unit h) (unit p) :=
    le_trans (mul_le_mul_right V (GaussianExponentialReference.unit_monotone (le_trans hs sq)) |>
      le_congr (mul_comm _ _) (mul_comm _ _)) (query_budget V q)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hE
    (positive_product _ _ (le_trans hz.andE₁.andE₂.andE₁ (le_add_right H N)) (unit_positive h))
  have geom := GaussianGammaZetaMellinStrip.quadrature_error p h z R B M N a C E H T hz.andE₁ hz.andE₂ hM hv
  have first := distance_symmetric _ _ _ D hD geom
  have rows := GaussianGammaZetaMellinDampedStrip.quadrature_error p q z R B M N a C E H T hz.andE₁ hz.andE₂ hM dq
  have budget : Γ ⊢[PRAAx] le (N*unit h) (unit q) :=
    le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono hNQ (GaussianExponentialReference.unit_monotone hs)) (query_budget Q s)
  have grow : Γ ⊢[PRAAx] le ((N*(C*J))*D) ((C*J*(H+N))*(E*unit q)) := by
    dsimp only [D,errorDenominator]
    ipra_le 𝔞(C*J*E*(H+N))*sl budget
  have read := GaussianGammaZetaMellinTranspose.transpose (Γ := Γ) p z B M N a C E
  have last := distance_radius_mono _ _ _ _ (C*J*(H+N)) D (positive_product _ _ hE (unit_positive q)) hD grow
    (distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) rows)
  exact distance_congr (GaussianGammaZetaMellinGrid.strip_grid_agreement p z B M N a C E)
    (GaussianGammaZetaMellinFiniteDampedGrid.strip_grid_agreement s z B M N a C E Q).eqSymm
    (by dsimp only [totalNumerator,errorNumerator,P,J]; ipra_ring) (.eqRefl D)
    (distance_triangle_same _ _ _ _ _ _ hD first last)

private theorem grid_error_at_precision (p z R B M N Q a C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B a C E H T) (hM : Γ ⊢[PRAAx] le one M) (hNQ : Γ ⊢[PRAAx] le N Q) :
    let s := finiteClock p R H T C
    let t := clock (exponent Q s) M N a C E
    Γ ⊢[PRAAx] distanceBounded (quadrature G t M a C E (Y z B)) (quadrature F s M a C E (X z B N Q))
      (diagonalNumerator (numerator R H T C) (denominator E H N) one p) (diagonalDenominator (denominator E H N) p) := by
  intro s t
  let D := denominator E H N
  let A := numerator R H T C
  let J := clockCost R H T C
  let V := H+N
  let U := unit p
  let W := unit s
  have hD := denominator_positive z R B N a C E H T hz
  have hp : Γ ⊢[PRAAx] le p (precision p T) := le_trans (le_add_right _ _) (le_add_right _ _)
  have move : Γ ⊢[PRAAx] le (J*U) W :=
    le_trans (mul_le_mul_right J (GaussianExponentialReference.unit_monotone hp) |>
      le_congr (mul_comm _ _) (mul_comm _ _)) (query_budget J (precision p T))
  have budget : Γ ⊢[PRAAx] le (J*U) (E*W) :=
    le_trans move (le_congr (one_mul W) (.eqRefl _) (mul_le_mul_right W hz.andE₂.andE₁.andE₂))
  have old := grid_error s s z R B M N Q a C E H T hz hM hNQ (le_refl s)
  have read := distance_congr (.eqRefl _) (.eqRefl _)
    (by show Γ ⊢[PRAAx] totalNumerator s H N R T C ≐ A*W+J*V
        dsimp only [totalNumerator,A,W,J,V,numerator,clockCost]; ipra_ring)
    (by show Γ ⊢[PRAAx] E*errorDenominator s H N ≐ D*W
        dsimp only [errorDenominator,D,W,denominator]; ipra_ring) old
  refine distance_radius_mono _ _ (A*W+J*V) (D*W) _ _
    (positive_product _ _ hD (unit_positive s)) (positive_product _ _ hD (unit_positive p)) ?_ read
  change Γ ⊢[PRAAx] le ((A*W+J*V)*((E*V)*U)) ((A*U+one*(E*V))*((E*V)*W))
  ipra_le 𝔞(E*V*V)*sl budget

theorem diagonal_observation (p z R B N Q a C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B a C E H T) (hf : Γ ⊢[PRAAx] finiteInput z R B N Q a C E T)
    (hNQ : Γ ⊢[PRAAx] le N Q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 finiteF p (finiteData z R B N Q a C E T))
      (ap2 Original p (originalData z R B a C E H T))
      (diagonalNumerator (numerator R H T C) (denominator E H N) (num 7) p) (diagonalDenominator (denominator E H N) p) := by
  let Lf := L N R E T
  let Lg := K R H T
  let Mf := mesh p Lf T
  let Mg := mesh p Lg T
  let M := Mg*Mf
  let s := finiteClock p R H T C
  let q := clock (exponent Q s) M N a C E
  let D := denominator E H N
  let A := numerator R H T C
  let U := unit p
  let W := unit (p+num 6)
  let x := X z B N Q
  let y := Y z B
  let f := ap2 finiteF p (finiteData z R B N Q a C E T)
  let g := ap2 Original p (originalData z R B a C E H T)
  let u := quadrature F s M a C E x
  let v := quadrature G q M a C E y
  have hMf := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p Lf T
  have hMg := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p Lg T
  have hM := positive_product _ _ hMg hMf
  have hD := denominator_positive z R B N a C E H T hz
  have d := positive_product _ _ hD (unit_positive (Γ := Γ) p)
  have hW := unit_positive (Γ := Γ) (p+num 6)
  have hs : Γ ⊢[PRAAx] le (precision p T) s := le_add_right _ _
  have hq : Γ ⊢[PRAAx] le (precision p T) q := le_trans hs (le_trans (le_add_right _ _) (le_add_right _ _))
  have gb := GaussianGammaZetaMellinCompact.compact_input z R B a C E H T hz
  have lr := GaussianCompactMeshIndependence.arbitrary_refinement F p s Mg a C E Lf T x hf hMg hs
  have rr := GaussianCompactMeshIndependence.arbitrary_refinement G p q Mf a C E Lg T y gb hMf hq
  have rightIndex : Γ ⊢[PRAAx] quadrature G q (Mf*Mg) a C E y ≐ v :=
    GaussianCompactRiemannName.quadrature_index_congr G q (Mf*Mg) M a C E y (mul_comm _ _)
  have left : Γ ⊢[PRAAx] distanceBounded f u (num 3) W :=
    distance_symmetric _ _ _ _ hW (distance_congr (.eqRefl _)
      (GaussianCompactRiemannName.name_at F p a C E Lf T x).eqSymm (.eqRefl _) (.eqRefl _) lr)
  have right : Γ ⊢[PRAAx] distanceBounded v g (num 3) W :=
    distance_congr rightIndex (GaussianCompactRiemannName.name_at G p a C E Lg T y).eqSymm (.eqRefl _) (.eqRefl _) rr
  have grow : Γ ⊢[PRAAx] le U W := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have widen : Γ ⊢[PRAAx] le (num 3*(D*U)) ((num 3*D)*W) := by ipra_le 𝔞(num 3*D)*sl grow
  have first := distance_radius_mono f u _ _ (num 3*D) (D*U) hW d widen left
  have middle := distance_symmetric v u _ _ d (grid_error_at_precision p z R B M N Q a C E H T hz hM hNQ)
  have last := distance_radius_mono v g _ _ (num 3*D) (D*U) hW d widen right
  have sum := distance_triangle_same f v g _ _ _ d (distance_triangle_same f u v _ _ _ d first middle) last
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by change Γ ⊢[PRAAx] num 3*D+(A*U+one*D)+num 3*D ≐ A*U+num 7*D; ipra_ring) (.eqRefl _) sum

theorem independent_rate (z R B N Q a C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B a C E H T) (hf : Γ ⊢[PRAAx] finiteInput z R B N Q a C E T)
    (hNQ : Γ ⊢[PRAAx] le N Q) :
    Γ ⊢[PRAAx] independentRate finiteF Original (finiteData z R B N Q a C E T) (originalData z R B a C E H T)
      (numerator R H T C) (denominator E H N) := by
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (num 7) (denominator_positive z R B N a C E H T hz)
    (GaussianCompactRiemannName.name_regular _ _ _ _ _ _ _ hf)
    (GaussianGammaZetaMellinCompact.regular z R B a C E H T hz)
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh H) (sh T) :=
    by simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift
  have ff : Δ ⊢[PRAAx] finiteInput (sh z) (sh R) (sh B) (sh N) (sh Q) (sh a) (sh C) (sh E) (sh T) :=
    by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift
  have nn : Δ ⊢[PRAAx] le (sh N) (sh Q) :=
    by simpa [Δ,sh,Fm.shift,Syn.shift] using hNQ.shift
  simpa [diagonalEnvelope,Δ,sh,Syn.shift,finiteData] using
    diagonal_observation (var 0) (sh z) (sh R) (sh B) (sh N) (sh Q) (sh a) (sh C) (sh E) (sh H) (sh T) hs ff nn

theorem threshold_budget (h z R B N a C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B a C E H T) (hN : Γ ⊢[PRAAx] le (threshold h R H T) N) :
    Γ ⊢[PRAAx] le (numerator R H T C*unit h) (denominator E H N) := by
  let J := majorant R H T*(H*H)*unit h
  have w : Γ ⊢[PRAAx] le C (E*T) :=
    le_congr (.eqRefl _) (mul_comm T E) (le_trans (le_add_left C a) hz.andE₂.andE₂.andE₂)
  have x : Γ ⊢[PRAAx] le (C*J) ((E*T)*J) := mul_le_mul_right J w
  have y : Γ ⊢[PRAAx] le (T*J) (H+N) :=
    le_congr (by unfold threshold J; ipra_ring) (.eqRefl _) (le_trans hN (le_add_left N H))
  exact le_trans (le_congr (by unfold numerator J; ipra_ring) (by ipra_ring) x)
    (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right E y))

theorem scheduled_observations (p q h z R B N Q a C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B a C E H T) (hf : Γ ⊢[PRAAx] finiteInput z R B N Q a C E T)
    (hNQ : Γ ⊢[PRAAx] le N Q) (hN : Γ ⊢[PRAAx] le (threshold h R H T) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 finiteF p (finiteData z R B N Q a C E T))
      (ap2 Original q (originalData z R B a C E H T))
      (rateNumerator one (unit h) p q) (rateDenominator (unit h) p q) := by
  let D := denominator E H N
  let A := numerator R H T C
  let U := unit p
  let V := unit q
  let W := unit h
  have rate := independent_rate z R B N Q a C E H T hz hf hNQ
  have raw := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q rate
  have hD := denominator_positive z R B N a C E H T hz
  have grow := threshold_budget h z R B N a C E H T hz hN
  refine distance_radius_mono _ _ _ _ _ _
    (GaussianNamedInverseRate.denominator_positive D p q hD)
    (GaussianNamedInverseRate.denominator_positive W p q (unit_positive h)) ?_ raw
  change Γ ⊢[PRAAx] le ((A*U*V+D*(U+V))*(W*U*V)) ((one*U*V+W*(U+V))*(D*U*V))
  ipra_le 𝔞(U*U*V*V)*sl grow

theorem actual_fixed_positive_panel_finite_damped_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 0) (var 1) (var 2) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      le (var 3) (var 4) ⟶
      independentRate finiteF Original (finiteData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 9))
        (originalData (var 0) (var 1) (var 2) (var 5) (var 6) (var 7) (var 8) (var 9))
        (numerator (var 1) (var 8) (var 9) (var 6)) (denominator (var 7) (var 8) (var 3))) :=
  closeUniv 10 (.impI (.impI (independent_rate _ _ _ _ _ _ _ _ _ _
    Prf.hyp1 (finite_input _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0) Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteDampedComparison
