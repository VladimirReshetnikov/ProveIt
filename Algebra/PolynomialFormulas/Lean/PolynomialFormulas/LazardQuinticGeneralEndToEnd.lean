import PolynomialFormulas.LazardQuinticEndToEnd
import PolynomialFormulas.LazardQuinticGeneralRootOriginBridge

/-!
# End-to-end formula for a general rational quintic

This file translates the completed depressed formula back by
`b / (5a)`.  It derives the exact five-linear-factor identity for the
original polynomial and proves that the translated values remain in the same
radical extension.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open IntermediateField
open ComputableDummitCoefficients

set_option autoImplicit false

noncomputable section

structure CompleteComplexGeneralLazardWitness (c : GeneralQuintic ℚ) where
  leading_ne_zero : c.a ≠ 0
  depressed : CompleteComplexLazardWitness (depress c)

namespace CompleteComplexGeneralLazardWitness

variable {c : GeneralQuintic ℚ}

/-- The five values for the original, untranslated quintic. -/
def rootValue (w : CompleteComplexGeneralLazardWitness c) (k : Fin 5) : ℂ :=
  solveDepressed (depressedOfRoots w.depressed.roots)
      (rootInvariants w.depressed.roots) w.depressed.formula.certificate
      squareRadicalFifthRootOfUnity k -
    algebraMap ℚ ℂ (c.b / (5 * c.a))

def radicalFormulaField (w : CompleteComplexGeneralLazardWitness c) :
    IntermediateField ℚ ℂ :=
  w.depressed.radicalFormulaField

theorem radicalFormulaField_isRadical
    (w : CompleteComplexGeneralLazardWitness c) :
    LazardOptimality.IsRadicalExtension ℚ ℂ
      (⊥ : IntermediateField ℚ ℂ) w.radicalFormulaField :=
  w.depressed.radicalFormulaField_isRadical

theorem rootValue_mem_radicalFormulaField
    (w : CompleteComplexGeneralLazardWitness c) (k : Fin 5) :
    w.rootValue k ∈ w.radicalFormulaField := by
  exact sub_mem (w.depressed.solveDepressed_mem_radicalFormulaField k)
    (w.radicalFormulaField.algebraMap_mem (c.b / (5 * c.a)))

/-- The five translated formula values are pairwise distinct. -/
theorem rootValue_injective
    (w : CompleteComplexGeneralLazardWitness c) :
    Function.Injective w.rootValue := by
  intro i j hij
  apply CompleteComplexLazardWitness.solveDepressed_injective w.depressed
  exact sub_left_injective (by simpa only [rootValue] using hij)

/-- Exact Vieta relations for the five translated formula values. -/
theorem fiveRootRelations
    (w : CompleteComplexGeneralLazardWitness c) :
    FiveRootRelations (c.map (algebraMap ℚ ℂ)) w.rootValue := by
  have hdep := w.depressed.formula.fiveRootRelations
    w.depressed.sum_eq_zero
  have hdep' : DepressedFiveRootRelations
      (depress (c.map (algebraMap ℚ ℂ)))
      (fun k ↦ solveDepressed (depressedOfRoots w.depressed.roots)
        (rootInvariants w.depressed.roots) w.depressed.formula.certificate
        squareRadicalFifthRootOfUnity k) := by
    rw [depress_map, ← w.depressed.depressedOfRoots_eq]
    exact hdep
  have htranslated := hdep'.translate (c.map (algebraMap ℚ ℂ))
    ((map_ne_zero_iff (algebraMap ℚ ℂ)
      (algebraMap ℚ ℂ).injective).2 w.leading_ne_zero)
  unfold rootValue
  simpa [GeneralQuintic.map] using htranslated

/-- The original general quintic factors by the five displayed radical
values, with multiplicity. -/
theorem factorization
    (w : CompleteComplexGeneralLazardWitness c) :
    (c.map (algebraMap ℚ ℂ)).polynomial =
      Polynomial.C (algebraMap ℚ ℂ c.a) *
        ∏ k : Fin 5, (Polynomial.X - Polynomial.C (w.rootValue k)) :=
  w.fiveRootRelations.factorization

/-- Every displayed value produced by the general Lazard witness is an
actual root of the original quintic after embedding its rational
coefficients into `ℂ`. -/
theorem eval_root
    (w : CompleteComplexGeneralLazardWitness c) (k : Fin 5) :
    (c.map (algebraMap ℚ ℂ)).eval (w.rootValue k) = 0 := by
  rw [w.fiveRootRelations.eval_factorization]
  apply mul_eq_zero_of_right
  exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _)

/-- Conversely, every complex root of the original nondegenerate quintic is
one of the five displayed values.  Together with `eval_root`, this is the
root-set form of the exact multiplicity-preserving factorization theorem. -/
theorem eval_eq_zero_iff_exists_rootValue
    (w : CompleteComplexGeneralLazardWitness c) (z : ℂ) :
    (c.map (algebraMap ℚ ℂ)).eval z = 0 ↔
      ∃ k : Fin 5, z = w.rootValue k := by
  constructor
  · intro hz
    exact w.fiveRootRelations.exists_eq_of_eval_eq_zero
      ((map_ne_zero_iff (algebraMap ℚ ℂ)
        (algebraMap ℚ ℂ).injective).2 w.leading_ne_zero) hz
  · rintro ⟨k, rfl⟩
    exact w.eval_root k

end CompleteComplexGeneralLazardWitness

/-- Conditional assembly interface pending only the unconditional raw-root
`P₂` theorem. -/
theorem exists_completeComplexGeneralLazardWitness_of_formula
    (c : GeneralQuintic ℚ) (ha : c.a ≠ 0)
    (hp : Irreducible c.polynomial)
    (hq : ∃ q : ℚ, (resolventPolynomial (depress c)).IsRoot q)
    (hformula : ∀ (x : Fin 5 → ℂ),
      Function.Injective x →
      elementaryTuple x = depressedElementary
        ((depress c).map (algebraMap ℚ ℂ)) →
      rootEpsilon squareRadicalFifthRootOfUnity x ≠ 0 →
      invariantE (depressedOfRoots x) (rootInvariants x) ≠ 0 →
      Nonempty (RootFourierCertificateWitness
        squareRadicalFifthRootOfUnity x)) :
    Nonempty (CompleteComplexGeneralLazardWitness c) := by
  have hpdep : Irreducible (depress c).polynomial :=
    (irreducible_polynomial_iff_depress_polynomial c ha).mp hp
  obtain ⟨w⟩ := exists_completeComplexLazardWitness_of_formula
    (depress c) hpdep hq hformula
  exact ⟨⟨ha, w⟩⟩

/-- Unconditional end-to-end witness for a general nondegenerate rational
quintic satisfying Lazard's rational-resolvent criterion. -/
theorem exists_completeComplexGeneralLazardWitness
    (c : GeneralQuintic ℚ) (ha : c.a ≠ 0)
    (hp : Irreducible c.polynomial)
    (hq : ∃ q : ℚ, (resolventPolynomial (depress c)).IsRoot q) :
    Nonempty (CompleteComplexGeneralLazardWitness c) := by
  have hpdep : Irreducible (depress c).polynomial :=
    (irreducible_polynomial_iff_depress_polynomial c ha).mp hp
  obtain ⟨w⟩ := exists_completeComplexLazardWitness (depress c) hpdep hq
  exact ⟨⟨ha, w⟩⟩

/-- Public semantic endpoint of the completed Lazard construction: under
the rational-resolvent criterion, the five distinct formula values lie in one
finite radical tower, give the exact multiplicity-sensitive linear-factor
product, and are exactly the complex roots of the original quintic.

The witness behind this existential is `CompleteComplexGeneralLazardWitness`,
so the values are the translated Lazard inverse-Fourier expressions rather
than an independently chosen enumeration of the roots. -/
theorem exists_radicalFormula_completeRootVector
    (c : GeneralQuintic ℚ) (ha : c.a ≠ 0)
    (hp : Irreducible c.polynomial)
    (hq : ∃ q : ℚ, (resolventPolynomial (depress c)).IsRoot q) :
    ∃ (roots : Fin 5 → ℂ) (L : IntermediateField ℚ ℂ),
      LazardOptimality.IsRadicalExtension ℚ ℂ
        (⊥ : IntermediateField ℚ ℂ) L ∧
      (∀ k, roots k ∈ L) ∧
      Function.Injective roots ∧
      ((c.map (algebraMap ℚ ℂ)).polynomial =
        Polynomial.C (algebraMap ℚ ℂ c.a) *
          ∏ k : Fin 5, (Polynomial.X - Polynomial.C (roots k))) ∧
      (∀ z : ℂ,
        (c.map (algebraMap ℚ ℂ)).eval z = 0 ↔
          ∃ k : Fin 5, z = roots k) := by
  obtain ⟨w⟩ := exists_completeComplexGeneralLazardWitness c ha hp hq
  exact ⟨w.rootValue, w.radicalFormulaField,
    w.radicalFormulaField_isRadical,
    w.rootValue_mem_radicalFormulaField,
    w.rootValue_injective,
    w.factorization,
    w.eval_eq_zero_iff_exists_rootValue⟩

end

end LeanProofs.PolynomialFormulas.LazardQuintic
