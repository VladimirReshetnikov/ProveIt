import IPRADerivations.Analysis.Trigonometry.Arctangent.Extension.GaussianArctangentNamedExtension
import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianEmbedding

/-!
# Exact imaginary axis of the original arctangent extension

At every encoded observation the original quadrature is a canonical
Gaussian rational with real coordinate exactly the canonical scalar zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentExtensionAxis

open_ipra
open ComplexLogarithmRemainder (scale eval_re_code)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentExponentialPrefix (prefixValue total)
open GaussianArctangentNamedExtension (nameF clock numerator denominator sample_at)
open GaussianArctangentPartialQuadrature (clearing mesh)
open GaussianRationalHorner (ofGaussian_canonical ofGaussian_represents scalar_congr)
open GaussianRootAlgebra (re_scale)
open RationalGaussianEmbedding (scalarZero scalar_zero_represents)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem prefix_axis_at (j M L : PTm n) : Γ ⊢[PRAAx] fstT (prefixValue j M L) ≐ scalarZero := by
  let a := scale (two*total j M L) imaginaryCode
  let F := fact L
  have hF := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) L
  have e : Γ ⊢[PRAAx] ZT.eq (ComplexLogarithmRemainder.re a) (ZT.ofNat zero) := by
    dsimp only [a]
    apply ZT.derive
    simp [re_scale,imaginaryCode,eval_re_code,ZT.toZ_ofNat,Q.mk_zero,map_zero]
  have h := scalar_congr (.eqRefl _) e (.eqRefl _) (ofGaussian_represents a F hF).andE₁
  apply RationalFiniteSum.canonical_equal _ _ _ _ F one
    (ofGaussian_canonical a F hF).andE₂.andE₁
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    h (scalar_zero_represents one) hF (le_refl one)
  apply ZT.derive
  simp [ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_zero, map_zero]

theorem extension_axis_at (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] fstT (ap2 (nameF f) p x) ≐ scalarZero := by
  let A := numerator f p x
  let B := denominator f p x
  let N := mesh (clock p)
  have e := (sample_at (Γ := Γ) f p x).eqTrans
    (GaussianArctangentPartialQuadrature.sample_at (clock p) A B)
  exact (congrFst e).eqTrans (prefix_axis_at (A*N) (B*N) (clearing (B*N)))

theorem actual_arctangent_extension_imaginary_axis_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (fstT (ap2 (nameF f) (var 0) (var 1)) ≐ scalarZero) :=
  closeUniv 2 (extension_axis_at f _ _)

end LeanProofs.IPRA.Analysis.GaussianArctangentExtensionAxis
