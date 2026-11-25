import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsCaps

/-!
# Strict order for the original real exponential names

Antisymmetry uses the two real coordinate comparisons at the requested
independent clocks. The original exponential injectivity theorem then
rules out the reverse order for strictly ordered inputs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingMultiplicativeBoundsStrictOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianGammaEulerRationalLogOrder (order_refl)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRealNameExponentialInjectivity (axisSamples independent_radii_injective)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianStirlingMultiplicativeBoundsOrder (exponential_order)
open RationalValueBounds (upper_congr radius_of_upper)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData

def strictOrder (f g : PR 2) (x y : PTm n) : Fm PTm n :=
  realOrder f g x y ⋏ neg (realOrder g f y x)

private theorem real_axis (f : PR 2) (x : PTm n) (hr : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] axisSamples f x := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] realSamples f (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using hr.shift
  exact (real_sample_at f (Syn.shift x) (var 0) hs).andE₂

private theorem antisymmetry_at (f g : PR 2) (x y p q : PTm n)
    (hf : Γ ⊢[PRAAx] realSamples f x) (hg : Γ ⊢[PRAAx] realSamples g y)
    (hfg : Γ ⊢[PRAAx] realOrder f g x y) (hgf : Γ ⊢[PRAAx] realOrder g f y x) :
    Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded (ap2 f p x) (ap2 g q y) (unit p+unit q) (unit p*unit q) := by
  let a := ap2 f p x
  let b := ap2 g q y
  have ar := real_sample_at f x p hf
  have br := real_sample_at g y q hg
  have lr := real_order_at f g x y p q hfg
  have rr := upper_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _) (real_order_at g f y x q p hgf)
  have rad := radius_of_upper _ _ _ _ lr rr
  have base := RationalGaussianNameEmbedding.distance_from_radius (fstT a) (fstT b) _ _
    (positive_product _ _ (unit_positive p) (unit_positive q)) rad
  exact distance_congr (RationalGaussianEmbedding.canonical_axis_roundtrip a ar.andE₁ ar.andE₂)
    (RationalGaussianEmbedding.canonical_axis_roundtrip b br.andE₁ br.andE₂) (.eqRefl _) (.eqRefl _) base

theorem real_antisymmetry (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] realSamples f x) (hg : Γ ⊢[PRAAx] realSamples g y)
    (hfg : Γ ⊢[PRAAx] realOrder f g x y) (hgf : Γ ⊢[PRAAx] realOrder g f y x) :
    Γ ⊢[PRAAx] crossEquivalent f g x y := by
  refine .allI (.allI ?_)
  let sh (s : PTm n) := Syn.shift (Syn.shift s)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have fs : Δ ⊢[PRAAx] realSamples f (sh x) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hf.shift.shift
  have gs : Δ ⊢[PRAAx] realSamples g (sh y) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hg.shift.shift
  have fg : Δ ⊢[PRAAx] realOrder f g (sh x) (sh y) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hfg.shift.shift
  have gf : Δ ⊢[PRAAx] realOrder g f (sh y) (sh x) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hgf.shift.shift
  exact antisymmetry_at f g (sh x) (sh y) (var 1) (var 0) fs gs fg gf

theorem strict_exponential_order (f g : PR 2) (x y : PTm n)
    (fn : Γ ⊢[PRAAx] pointCN f x) (gn : Γ ⊢[PRAAx] pointCN g y)
    (fr : Γ ⊢[PRAAx] realSamples f x) (gr : Γ ⊢[PRAAx] realSamples g y)
    (h : Γ ⊢[PRAAx] strictOrder f g x y) :
    Γ ⊢[PRAAx] strictOrder (E f) (E g) (ed f x) (ed g y) := by
  have forward := exponential_order f g x y fn gn fr gr h.andE₁
  refine .andI forward (.impI ?_)
  have fs := GaussianEulerVerticalRealSamples.original_exponential_real_samples f (U f x) x fr
  have gs := GaussianEulerVerticalRealSamples.original_exponential_real_samples g (U g y) y gr
  have equality := real_antisymmetry (E f) (E g) (ed f x) (ed g y) fs.wk gs.wk forward.wk Prf.hyp0
  have e := independent_radii_injective f g (U f x) (U g y) x y (exponential_input _ _ fn.wk)
    (exponential_input _ _ gn.wk) (real_axis _ _ fr.wk) (real_axis _ _ gr.wk) equality
  have reverse := GaussianNamedRealOrderTransport.transport g f f f y x x x (cross_symm _ _ _ _ e)
    (cross_refl _ _ fn.wk) (order_refl _ _ fn.wk)
  exact h.andE₂.wk.impE reverse

theorem strict_transport (f f' g' g : PR 2) (x x' y' y : PTm n)
    (hf : Γ ⊢[PRAAx] crossEquivalent f f' x x') (hg : Γ ⊢[PRAAx] crossEquivalent g' g y' y)
    (h : Γ ⊢[PRAAx] strictOrder f' g' x' y') : Γ ⊢[PRAAx] strictOrder f g x y := by
  refine .andI (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ hf hg h.andE₁) (.impI ?_)
  exact h.andE₂.wk.impE (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ hg.wk hf.wk Prf.hyp0)

end LeanProofs.IPRA.Analysis.GaussianStirlingMultiplicativeBoundsStrictOrder
