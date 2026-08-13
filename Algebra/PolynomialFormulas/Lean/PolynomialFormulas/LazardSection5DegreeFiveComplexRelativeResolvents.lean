import Mathlib.FieldTheory.IsAlgClosed.Basic
import PolynomialFormulas.Fin5DihedralRelativeCore
import PolynomialFormulas.LazardQuinticPrimitiveFifthRootTower
import PolynomialFormulas.LazardSection5DegreeFiveRelativeResolvents

/-!
# Lazard's Section 5 relative resolvents in a common complex field

The bare splitting field of a rational quintic need not contain a primitive
fifth root of unity.  This file maps its canonical complete root tuple into
`ℂ`, where the explicit two-square-root primitive fifth root is available.
The mapped elementary-symmetric identity proves that the tuple still belongs
to the original depressed quintic, so irreducibility gives epsilon
nonvanishing without any cyclotomic-containment certificate from the caller.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardSection5DegreeFiveRelativeResolvents

open LazardQuintic
open ComputableDummitCoefficients

set_option autoImplicit false

noncomputable section

/-- Every irreducible depressed rational quintic has one complete, injective
root tuple in `ℂ` on which the literal `T'`, `U'`, and epsilon two-coset
relative resolvents are all separable.  The primitive fifth root is the
explicit two-square-root value already constructed in `ℂ`; no assertion that
it belongs to the bare quintic splitting field is made. -/
theorem exists_complexRootTuple_section5_degreeFive_relativeOrbitResolvents_separable
    (c : DepressedQuintic ℚ) (hp : Irreducible c.polynomial) :
    ∃ x : Fin 5 → ℂ,
      Function.Injective x ∧
      elementaryTuple x =
        depressedElementary (c.map (algebraMap ℚ ℂ)) ∧
      (rootTPrimeC5D5RelativeResolvent x).Separable ∧
      (rootUPrimeC5D5RelativeResolvent x).Separable ∧
      (rootEpsilonD5F20RelativeResolvent
        squareRadicalFifthRootOfUnity x).Separable := by
  let φ : c.polynomial.SplittingField →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let x0 : Fin 5 → c.polynomial.SplittingField :=
    QuinticScalarGaloisBridge.rootTuple c.polynomial hp
      c.polynomial_natDegree
  let x : Fin 5 → ℂ := fun k ↦ φ (x0 k)
  have hx0 : Function.Injective x0 :=
    QuinticScalarGaloisBridge.rootTuple_injective c.polynomial hp
      c.polynomial_natDegree
  have hx : Function.Injective x := φ.injective.comp hx0
  have helementary0 :
      elementaryTuple x0 =
        depressedElementary
          (c.map (algebraMap ℚ c.polynomial.SplittingField)) := by
    simpa [x0] using elementaryTuple_rootTuple_eq_depressedElementary c hp
  have helementary : elementaryTuple x =
      depressedElementary (c.map (algebraMap ℚ ℂ)) := by
    calc
      elementaryTuple x = fun k ↦ φ (elementaryTuple x0 k) := by
        simpa [x] using elementaryTuple_map φ.toRingHom x0
      _ = fun k ↦ φ
          (depressedElementary
            (c.map (algebraMap ℚ c.polynomial.SplittingField)) k) := by
        rw [helementary0]
      _ = depressedElementary (c.map (algebraMap ℚ ℂ)) := by
        funext k
        fin_cases k <;>
          simp [depressedElementary, DepressedQuintic.map, φ]
  have hepsilon : rootEpsilon squareRadicalFifthRootOfUnity x ≠ 0 :=
    rootEpsilon_ne_zero_of_elementaryTuple_eq c hp x helementary
      squareRadicalFifthRootOfUnity
  exact ⟨x, hx, helementary,
    rootTPrime_C5_D5_relativeOrbitResolvent_separable hx (by norm_num),
    rootUPrime_C5_D5_relativeOrbitResolvent_separable hx (by norm_num),
    rootEpsilon_D5_F20_relativeOrbitResolvent_separable
      squareRadicalFifthRootOfUnity hepsilon (by norm_num)⟩

end

end LeanProofs.PolynomialFormulas.LazardSection5DegreeFiveRelativeResolvents
