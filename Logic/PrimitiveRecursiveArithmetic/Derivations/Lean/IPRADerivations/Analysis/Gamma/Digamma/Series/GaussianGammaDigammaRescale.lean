import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaNative
import IPRADerivations.Analysis.Stirling.Telescoping.FiniteTelescopes.GaussianStirlingRationalTelescopers

/-!
# Rescaling the original rational digamma parameter

The same rational argument with a common positive scale has the same
original first Euler integral and the same reciprocal Gamma factor.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaRescale

open_ipra
open ComplexLogarithmRemainder (scale)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaDigammaNative (derivativeData derivative_regular reciprocalData reciprocal_regular nameF data)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianRationalHorner (positive_product)
open GaussianStirlingGammaLogarithm (arg source gamma_source euler_real_source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "PF" => GaussianGammaC7Name.nameF

theorem scaled_source (a b k : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] source (k*a) (k*b) :=
  .andI (positive_product _ _ hk hs.andE₁) (positive_product _ _ hk hs.andE₂)

theorem derivative_rescale (a b k : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] crossEquivalent IF IF (derivativeData (k*a) (k*b)) (derivativeData a b) := by
  have hx := scaled_source a b k hs hk
  have eq := GaussianStirlingRationalTelescopers.fraction_same (k*a) (k*b) a b hx.andE₂ hs.andE₂ (by ipra_ring)
  exact GaussianEulerLogarithmicImproperInputProperness.original_improper_proper one (arg (k*a)) (arg a)
    (k*a) a (k*b) b (k*b) b (.andI (euler_real_source _ _ hx).andE₁ (.andI (euler_real_source _ _ hs).andE₁ eq))

theorem reciprocal_rescale (a b k : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] crossEquivalent PF PF (reciprocalData (k*a) (k*b)) (reciprocalData a b) := by
  let z := arg a
  let w := scale k z
  let v := arg (k*a)
  let d := k*b
  have hs' := (gamma_source a b hs).andE₁
  have hw := GaussianGammaEncodingRescaling.rescaled_source z a b k hs' hk
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal w v := by
    apply GaussianRootAlgebra.equal_of_values <;> simp only [w,v,z,arg,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;>
      ipra_simps <;> ring
  have hv := GaussianGammaFiniteValueProperness.source_equal w v a d hw e
  have hx := (gamma_source (k*a) d (scaled_source a b k hs hk)).andE₁
  have first := GaussianGammaRadiusOverlap.original_P_overlap v (k*a) a d hx hv
  have second := cross_symm _ _ _ _ (GaussianGammaInputProperness.original_C7_proper w v a d hw e)
  exact cross_trans _ _ _ _ _ _ first
    (cross_trans _ _ _ _ _ _ second (GaussianGammaEncodingRescaling.original_C7_rescale z a b k hs' hk))

theorem native_rescale (a b k : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data (k*a) (k*b)) (data a b) := by
  have hx := scaled_source a b k hs hk
  exact multiply_cross PF PF IF IF _ _ _ _
    (reciprocal_regular _ _ hx) (reciprocal_regular _ _ hs) (derivative_regular _ _ hx) (derivative_regular _ _ hs)
    (reciprocal_rescale a b k hs hk) (derivative_rescale a b k hs hk)

theorem datum_congr {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] data a b ≐ data a' b' := by
  simpa only [GaussianGammaDigammaNative.subst_data,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (data (var 0) (var 1) : PTm 2) (σ := ![a,b]) (σ' := ![a',b'])
      (fun j => by fin_cases j; exact ha; exact hb)

theorem integer_rescale (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data (b*a) b) (data a one) :=
  GaussianGammaCompactCutoffAlignment.cross_data_congr nameF nameF _ _ _ _
    (datum_congr (.eqRefl _) (by ipra_ring)).eqSymm (.eqRefl _)
    (native_rescale a one b (.andI ha (le_refl _)) hb)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaRescale
