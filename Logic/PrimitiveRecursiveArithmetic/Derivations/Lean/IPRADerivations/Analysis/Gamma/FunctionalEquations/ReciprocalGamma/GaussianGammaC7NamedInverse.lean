import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaC7NamedFrozen
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaNamedPoleFreeFrozen
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedMultiplyRate

/-!
# The original named Gamma and reciprocal-Gamma multiply to one

On a common disk with a certified pole separation, the two named
evaluators freeze to the original matched rational inverse pair.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianGammaC7NamedInverse

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaC9Bound (majorant reciprocal_name_bound)
open GaussianGammaNamedPoleFree (encodedData source_at)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast equivalent_of_envelope)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianNamedMultiplyRate (leadingNumerator)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "P" => GaussianGammaC7Named.nameF
local notation "G" => GaussianGammaNamedPoleFree.nameF
local notation "C" => GaussianGammaC7Name.nameF
local notation "Z" => GaussianGammaReciprocalInverse.gammaF
local notation "dP" => GaussianGammaC7Named.data
local notation "dG" => GaussianGammaNamedPoleFree.data
local notation "domP" => GaussianGammaC7Named.source
local notation "domG" => GaussianGammaNamedPoleFree.source

abbrev productF (f : PR 2) : PR 2 := multiplyF (P f) (G f)

def productData (f : PR 2) (x R E : PTm n) : PTm n := multiplyData (P f) (G f) (dP x R) (dG x R E)

def cost (f : PR 2) (x R E : PTm n) : PTm n := U (G f) (dG x R E)*one+majorant R*one+two

@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x R E : PTm n) :
    Syn.subst σ (productData f x R E) = productData f (Syn.subst σ x) (Syn.subst σ R) (Syn.subst σ E) := by simp [productData]

@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x R E : PTm n) :
    Syn.subst σ (cost f x R E) = cost f (Syn.subst σ x) (Syn.subst σ R) (Syn.subst σ E) := by simp [cost,one,two]

private theorem comparison_at (f : PR 2) (p x R E : PTm n)
    (h : Γ ⊢[PRAAx] domP f x R) (hg : Γ ⊢[PRAAx] domG f x R E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (productF f) p (productData f x R E)) (ap2 oneF p x) (cost f x R E) (unit p) := by
  let a := GaussianGammaC7Named.clock p R
  let b := GaussianGammaNamedPoleFree.clock p R E
  let k := a+b
  let raw := ap2 f k x
  let z := rawGaussian raw
  let B := rawDen raw
  let X := dP x R
  let Y := dG x R E
  let V := GaussianGammaC7Name.data z R B
  let W := encodedData f k x R E
  let T := multiplyData C Z V W
  let M := U (G f) Y
  let N := majorant R
  let D := unit p
  have hd := unit_positive (Γ := Γ) p
  have hz := source_at f k x R E hg
  have hp := GaussianGammaC7Named.name_regular f x R h
  have hq := GaussianGammaNamedPoleFree.name_regular f x R E hg
  have fp := GaussianGammaC7NamedFrozen.frozen_rate f p k x R h (le_add_right a b)
  have fq := GaussianGammaNamedPoleFreeFrozen.original_frozen_rate f p k x R E hg (le_add_left b a)
  have mul := GaussianNamedMultiplyRate.independent_rate (P f) (G f) C Z X Y V W one D one D M N hd hd hp hq
    (GaussianGammaC7Name.name_regular z R B hz.andE₁) (GaussianGammaNamedPoleFree.encoded_regular f k x R E hg)
    (GaussianNameBounds.all_samples_bounded _ _ hq) (reciprocal_name_bound z R B hz.andE₁) fp fq
  have rounded := GaussianNamedRateRadius.weaken (productF f) (multiplyF C Z) (productData f x R E) T _ _ (M*one+N*one) D
    (positive_product D D hd hd) hd (le_of_eq_add (d := zero) (by unfold leadingNumerator; ipra_ring)) mul
  have identity := cross_trans _ _ _ _ _ _ (GaussianGammaReciprocalInverse.gamma_product z R B one E hz)
    (GaussianBoundedInverseApartness.ones_equivalent V x)
  have reg := multiply_fast (P f) (G f) X Y hp hq
  have joined := GaussianNamedRateTransport.transport (productF f) (multiplyF C Z) (productF f) oneF (productData f x R E) T
    (productData f x R E) x (M*one+N*one) D hd rounded (cross_refl _ _ reg)
    (cross_symm _ _ _ _ identity)
  let L := M*one+N*one
  have clear : Γ ⊢[PRAAx] le ((L*D+two*D)*D) ((L+two)*(D*D)) :=
    le_of_eq_add (d := zero) (by ipra_ring)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product D D hd hd) hd clear
    (diagonal_rate (productF f) oneF (productData f x R E) x (M*one+N*one) D p hd joined)

theorem inverse_product (f : PR 2) (x R E : PTm n) (h : Γ ⊢[PRAAx] domP f x R) (hg : Γ ⊢[PRAAx] domG f x R E) :
    Γ ⊢[PRAAx] crossEquivalent (productF f) oneF (productData f x R E) x := by
  refine equivalent_of_envelope (productF f) oneF (productData f x R E) x (cost f x R E)
    (multiply_fast (P f) (G f) _ _ (GaussianGammaC7Named.name_regular f x R h)
      (GaussianGammaNamedPoleFree.name_regular f x R E hg)) (one_fast x) (.allI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hp : Δ ⊢[PRAAx] domP f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift
  have hs : Δ ⊢[PRAAx] domG f (sh x) (sh R) (sh E) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_productData,subst_cost,Syn.shift,sh,Δ] using
    comparison_at f (var 0) (sh x) (sh R) (sh E) hp hs

theorem actual_original_C7_named_inverse_product_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let x := var 0
     let R := var 1
     let E := var 2
     domP f x R ⟶ domG f x R E ⟶ crossEquivalent (productF f) oneF (productData f x R E) x) :=
  closeUniv 3 (.impI (.impI (inverse_product f _ _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaC7NamedInverse
