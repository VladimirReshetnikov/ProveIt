import IPRADerivations.Analysis.GaussianEulerLogarithmicParameterTaylor
import IPRADerivations.Analysis.GaussianRationalQuadratureAffineRemainder

/-!
# The first-order remainder on the actual logarithmic Euler grid

All three evaluated compact clients use a common numerical grid. The
source guards imply the pointwise hypotheses at each actual sample time.
The original sum and weight integrate the resulting quadratic and
observation errors with exactly the interval length.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicTaylorGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianEulerLogarithmicParameterIncrement (curvature)
open GaussianEulerLogarithmicCompactName (evaluatorF fixedData raw_evaluator_at)
open GaussianEulerLogarithmicMultiplier (logRadius)
open GaussianCompactRiemannName (sampleBody sampleData quadrature grid grid_inside sample_body_at)
open GaussianEulerCompactAdditivity (intervalSource domain_of_inside)
open GaussianRationalQuadratureAffineRemainder (rowBody rowData row_at weighted_bound)
open GaussianRationalRiemannRefinement (termsDistance constantBody)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qadd qmul qzero ofGaussian positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B a C E T h D X Y : PTm n) : Fm PTm n :=
  intervalSource z R B a C E T ⋏
    (le one D ⋏ (le one Y ⋏ (le (logRadius E T*X) Y ⋏ bounded (ofGaussian h D) X Y)))
def perturbedClient (j z R B E T h D : PTm n) : PTm n := fixedData j (R+one) E T (shifted z B h D) (B*D)
def baseClient (j z R B E T : PTm n) : PTm n := fixedData j R E T z B
def linearClient (j z R B E T : PTm n) : PTm n := fixedData (succ j) R E T z B
def rowNumerator (p j R E T X Y : PTm n) : PTm n := curvature j R E T*X*X*unit p+num 3*(Y*Y)
def rowDenominator (p Y : PTm n) : PTm n := (Y*Y)*unit p

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B a C E T h D X Y : PTm n) :
    (source z R B a C E T h D X Y).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ a)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ X) (Syn.subst σ Y) := by simp [source]
@[simp] theorem subst_perturbedClient {m : ℕ} (σ : Fin n → PTm m) (j z R B E T h D : PTm n) :
    Syn.subst σ (perturbedClient j z R B E T h D) = perturbedClient (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ h) (Syn.subst σ D) := by simp [perturbedClient]
@[simp] theorem subst_baseClient {m : ℕ} (σ : Fin n → PTm m) (j z R B E T : PTm n) :
    Syn.subst σ (baseClient j z R B E T) = baseClient (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ E) (Syn.subst σ T) := by simp [baseClient]
@[simp] theorem subst_linearClient {m : ℕ} (σ : Fin n → PTm m) (j z R B E T : PTm n) :
    Syn.subst σ (linearClient j z R B E T) = linearClient (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ E) (Syn.subst σ T) := by simp [linearClient]
@[simp] theorem subst_rowNumerator {m : ℕ} (σ : Fin n → PTm m) (p j R E T X Y : PTm n) :
    Syn.subst σ (rowNumerator p j R E T X Y) = rowNumerator (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ R)
      (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ X) (Syn.subst σ Y) := by simp [rowNumerator]
@[simp] theorem subst_rowDenominator {m : ℕ} (σ : Fin n → PTm m) (p Y : PTm n) :
    Syn.subst σ (rowDenominator p Y) = rowDenominator (Syn.subst σ p) (Syn.subst σ Y) := by simp [rowDenominator]

private abbrev body := sampleBody evaluatorF
private def bodyData (p N a C E T j z R B h D : PTm n) : PTm n :=
  rowData (ofGaussian h D) (sampleData p N a C E (perturbedClient j z R B E T h D))
    (sampleData p N a C E (baseClient j z R B E T)) (sampleData p N a C E (linearClient j z R B E T))

theorem original_row_bound (i p N j z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (rowBody body body body) i (bodyData p N a C E T j z R B h D)) qzero
      (rowNumerator p j R E T X Y) (rowDenominator p Y) := by
  let t := grid i N a C E
  let c := ofGaussian h D
  let x := sampleData p N a C E (perturbedClient j z R B E T h D)
  let y := sampleData p N a C E (baseClient j z R B E T)
  let w := sampleData p N a C E (linearClient j z R B E T)
  have eint := grid_inside i N a C E hs.andE₁.andE₂.andE₁ hs.andE₁.andE₁.andE₂.andE₁ hN (le_of_lt hi)
  have ht := domain_of_inside t a C E T hs.andE₁.andE₂.andE₁ hs.andE₁.andE₁.andE₂.andE₁ hs.andE₁.andE₂.andE₂ eint
  have input : Γ ⊢[PRAAx] GaussianEulerLogarithmicParameterIncrement.source z R B E T (fstT t) (sndT t) h D X Y :=
    .andI (.andI hs.andE₁.andE₁ ht) hs.andE₂
  have tay := GaussianEulerLogarithmicParameterTaylor.original_parameter_taylor p p p j z R B E T (fstT t) (sndT t) h D X Y input
  have xx := (sample_body_at (Γ := Γ) evaluatorF i p N a C E (perturbedClient j z R B E T h D)).eqTrans
    (raw_evaluator_at p t j (R+one) E T (shifted z B h D) (B*D))
  have yy := (sample_body_at (Γ := Γ) evaluatorF i p N a C E (baseClient j z R B E T)).eqTrans
    (raw_evaluator_at p t j R E T z B)
  have ww := (sample_body_at (Γ := Γ) evaluatorF i p N a C E (linearClient j z R B E T)).eqTrans
    (raw_evaluator_at p t (succ j) R E T z B)
  have hp := unit_positive (Γ := Γ) p
  have hy := hs.andE₂.andE₂.andE₁
  have hY := positive_product _ _ hy hy
  have hNew := positive_product _ _ hY hp
  have hOld := positive_product _ _ hY (positive_product _ _ (positive_product _ _ hp hp) hp)
  have bound := distance_radius_mono _ _ (GaussianEulerLogarithmicParameterRemainder.numerator p p p j R E T X Y)
    (GaussianEulerLogarithmicParameterRemainder.denominator p p p Y) (rowNumerator p j R E T X Y) (rowDenominator p Y) hOld hNew
    (le_congr (.eqRefl _) (by
      unfold GaussianEulerLogarithmicParameterRemainder.numerator GaussianEulerLogarithmicParameterRemainder.denominator
        rowNumerator rowDenominator
      ipra_ring) (le_refl _)) tay
  have actual := distance_congr xx.eqSymm (qadd_congr yy (qmul_congr (.eqRefl _) ww)).eqSymm (.eqRefl _) (.eqRefl _) bound
  have exactRow := row_at (Γ := Γ) body body body i c x y w
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ hNew).iffMpr
    (GaussianRationalReciprocal.bound_congr exactRow.eqSymm (.eqRefl _) (.eqRefl _) actual)

theorem original_grid_bound (p N j z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF p N a C E (perturbedClient j z R B E T h D))
      (qadd (quadrature evaluatorF p N a C E (baseClient j z R B E T))
        (qmul (ofGaussian h D) (quadrature evaluatorF p N a C E (linearClient j z R B E T))))
      (C*rowNumerator p j R E T X Y) (E*rowDenominator p Y) := by
  let sh (x : PTm n) := Syn.shift x
  have src : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh T) (sh h) (sh D) (sh X) (sh Y) :=
    by simpa only [Fm.shift,Syn.shift,subst_source,sh] using hs.shift
  have npos : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,one,sh] using hN.shift
  have rows : Γ ⊢[PRAAx] termsDistance (rowBody body body body) constantBody N (bodyData p N a C E T j z R B h D) qzero
      (rowNumerator p j R E T X Y) (rowDenominator p Y) := by
    refine .allI (.impI ?_)
    simpa [termsDistance,bodyData,Syn.shift,sh] using original_row_bound (var 0) (sh p) (sh N) (sh j) (sh z) (sh R) (sh B)
      (sh a) (sh C) (sh E) (sh T) (sh h) (sh D) (sh X) (sh Y) src.wk npos.wk Prf.hyp0
  have hy := hs.andE₂.andE₂.andE₁
  exact weighted_bound body body body _ _ _ _ _ _ _ _ _ hN hs.andE₁.andE₁.andE₂.andE₁
    (positive_product _ _ (positive_product _ _ hy hy) (unit_positive p)) rows

theorem actual_original_logarithmic_Taylor_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) ⋏ le one (var 1)) ⟶
      distanceBounded (quadrature evaluatorF (var 0) (var 1) (var 6) (var 7) (var 8)
        (perturbedClient (var 2) (var 3) (var 4) (var 5) (var 8) (var 9) (var 10) (var 11)))
      (qadd (quadrature evaluatorF (var 0) (var 1) (var 6) (var 7) (var 8) (baseClient (var 2) (var 3) (var 4) (var 5) (var 8) (var 9)))
        (qmul (ofGaussian (var 10) (var 11)) (quadrature evaluatorF (var 0) (var 1) (var 6) (var 7) (var 8)
          (linearClient (var 2) (var 3) (var 4) (var 5) (var 8) (var 9)))))
      (var 7*rowNumerator (var 0) (var 2) (var 4) (var 8) (var 9) (var 12) (var 13)) (var 8*rowDenominator (var 0) (var 13))) :=
  closeUniv 14 (.impI (original_grid_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicTaylorGrid
