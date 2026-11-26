import IPRADerivations.Analysis.Names.GaussianNamedNaturalScale
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaCanonicalExponent

/-!
# Natural scaling and multiplication by the constant name

The two actual programs use different observation clocks. At the
multiplication clock its canonical result is exactly the original
rational natural-scale operation. The two independent clock estimates
give the same regular name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNaturalScaleProductName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalNaturalScale (naturalPoint natScale natScale_as_product natScale_canonical)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (point_at crossEquivalent)
open GaussianRadiusExponentialName (input bounded_samples_at)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def productF (f : PR 2) : PR 2 := multiplyF constantF f
def productData (f : PR 2) (i x : PTm n) : PTm n := multiplyData constantF f (naturalPoint i) x
def clock (f : PR 2) (p i x : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (multiplyModulus constantF f (naturalPoint i) x) p
def sample (f : PR 2) (p i x : PTm n) : PTm n := ap2 (productF f) p (productData f i x)

@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (i x : PTm n) :
    Syn.subst σ (productData f i x) = productData f (Syn.subst σ i) (Syn.subst σ x) := by simp [productData]

theorem product_at (f : PR 2) (p i x : PTm n) : Γ ⊢[PRAAx]
    sample f p i x ≐ natScale i (ap2 f (clock f p i x) x) := by
  let t := clock f p i x
  let q := ap2 f t x
  have core := (GaussianRationalSyntheticDivision.qmul_congr (constant_at (Γ := Γ) t (naturalPoint i))
    (.eqRefl q)).eqTrans (natScale_as_product i q).eqSymm
  exact (GaussianNameArithmetic.multiply_at constantF f (naturalPoint i) x p).eqTrans
    ((GaussianNameArithmetic.recode_congr core).eqTrans (GaussianExponentialReference.recode_fixed _ (natScale_canonical _ _)))

theorem clock_later (f : PR 2) (p i x : PTm n) : Γ ⊢[PRAAx] le p (clock f p i x) :=
  le_add_right _ _

theorem same_precision (f : PR 2) (p E i R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded (GaussianNamedNaturalScale.sample f p E i x) (sample f p i x) (two*i) (unit p) := by
  let s := GaussianNamedNaturalScale.clock p E
  let t := clock f p i x
  let U := unit p
  let S := unit s
  let T := unit t
  have hS : Γ ⊢[PRAAx] le U S := GaussianBalancedRadiusArithmetic.unit_monotone p s (GaussianNamedNaturalScale.clock_later p E)
  have hT : Γ ⊢[PRAAx] le U T := GaussianBalancedRadiusArithmetic.unit_monotone p t (clock_later f p i x)
  have den := positive_product _ _ (unit_positive (Γ := Γ) s) (unit_positive t)
  have e := GaussianNamedNaturalScale.scaled_distance i _ _ _ _ R den (point_at f x s t h.andE₁)
    (bounded_samples_at f R x t h.andE₂)
  have budget : Γ ⊢[PRAAx] le ((i*(S+T))*U) ((two*i)*(S*T)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (mul_le_mul_right (i*S) hT) (mul_le_mul_right (i*T) hS))
  exact distance_congr (GaussianNamedNaturalScale.sample_at f p E i x).eqSymm (product_at f p i x).eqSymm
    (.eqRefl _) (.eqRefl _) (distance_radius_mono _ _ _ _ _ _ den (unit_positive p) budget e)

theorem scale_product_cross (f : PR 2) (E i R x : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hi : Γ ⊢[PRAAx] le i E) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedNaturalScale.nameF f) (productF f)
      (GaussianNamedNaturalScale.data E i x) (productData f i x) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (two*i)
    (GaussianNamedNaturalScale.name_regular f E i R x hf hi)
    (multiply_fast _ _ _ _ (constant_regular _) hf.andE₁) (.allI ?_)
  have h : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRadiusExponentialName.subst_input,Syn.shift] using hf.shift
  simpa only [Syn.shift,GaussianNamedNaturalScale.subst_data,subst_productData,GaussianNamedNaturalScale.sample,sample,
    PTm.subst_mul,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    same_precision f (var 0) (Syn.shift E) (Syn.shift i) (Syn.shift R) (Syn.shift x) h

theorem actual_natural_scale_product_name_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input f (var 2) (var 3) ⟶ le (var 1) (var 0) ⟶ crossEquivalent
      (GaussianNamedNaturalScale.nameF f) (productF f)
      (GaussianNamedNaturalScale.data (var 0) (var 1) (var 3)) (productData f (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (scale_product_cross f _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNaturalScaleProductName
