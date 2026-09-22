import Surreal.Surcomplex.Basic
import Surreal.Foundations.SignSequenceHahnEmbedding
import Surreal.Foundations.SignSequenceRealClosed
import Surreal.HahnSeries.ComplexNumbers
import Surreal.Algebra.Polynomial

/-!
# Algebraic closedness of the actual surcomplex field

The real Hahn embedding extends coordinatewise to the quadratic pair field.
Every surcomplex polynomial's real and imaginary coefficient normal forms
belong to one small divisible exponent workspace. The proved algebraic
closedness of its complex Hahn field supplies a root, which the injective
workspace embedding maps to an actual surcomplex root.

This constructs the algebraic-closedness clause of `found:prop:complex` and
the root and factorization clauses of `polynomial:thm:fta` without assuming
closedness of the actual field or a generic real-closed complexification
theorem.
-/

universe u v

namespace Surreal.Surcomplex

open Foundations Polynomial

noncomputable section

private def complexifyRingHom {R : Type*} [CommRing R]
    (f : R →+* SignSequence.{u}) : Complexify R →+* Surcomplex.{u} where
  toFun z := ⟨f z.re, f z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by
    apply ext
    · exact f.map_one
    · exact f.map_zero
  map_add' z w := by ext <;> simp
  map_mul' z w := by
    apply ext
    · simp only [Complexify.mul_re, map_sub, map_mul]
    · simp only [Complexify.mul_im, map_add, map_mul]

section Workspace

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Small.{u} Γ]

/-- The complete complex Hahn workspace embeds into actual surcomplex numbers. -/
def hahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    _root_.HahnSeries Γ ℂ →+* Surcomplex.{u} :=
  (complexifyRingHom (SignSequence.hahnEmbedding e he)).comp
    Surreal.HahnSeries.realComplexHahnEquiv.symm.toRingHom

/-- The complex workspace embedding extends the actual real embedding coordinatewise. -/
@[simp] theorem hahnEmbedding_realComplexHahnEquiv
    (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (z : Complexify (_root_.HahnSeries Γ ℝ)) :
    hahnEmbedding e he (Surreal.HahnSeries.realComplexHahnEquiv z) =
      ⟨SignSequence.hahnEmbedding e he z.re, SignSequence.hahnEmbedding e he z.im⟩ := by
  change complexifyRingHom (SignSequence.hahnEmbedding e he)
    (Surreal.HahnSeries.realComplexHahnEquiv.symm
      (Surreal.HahnSeries.realComplexHahnEquiv z)) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

/-- The actual complex embedding loses no Hahn coefficients. -/
theorem hahnEmbedding_injective (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    Function.Injective (hahnEmbedding e he) := (hahnEmbedding e he).injective

end Workspace

/-- Both coordinate normal forms of every coefficient, indexed by one small type. -/
def polynomialCoordinateForms (P : Polynomial Surcomplex.{u}) :
    ℕ ⊕ ℕ → SmallNormalForm.{u} :=
  Sum.elim (fun n => SmallNormalForm.normalForm (P.coeff n).re)
    (fun n => SmallNormalForm.normalForm (P.coeff n).im)

/-- One small divisible exponent group contains all coordinate coefficient supports. -/
abbrev polynomialWorkspaceExponents (P : Polynomial Surcomplex.{u}) :=
  SignSequence.workspaceExponents (⋃ i, SmallNormalForm.support (polynomialCoordinateForms P i))

/-- The actual complex embedding for the polynomial's common coefficient workspace. -/
def polynomialWorkspaceEmbedding (P : Polynomial Surcomplex.{u}) :
    _root_.HahnSeries (polynomialWorkspaceExponents P) ℂ →+* Surcomplex.{u} :=
  hahnEmbedding (polynomialWorkspaceExponents P).subtype.toAddMonoidHom (fun _ _ h => h)

/-- Every coefficient is in the range of the same algebraically closed Hahn workspace. -/
theorem coeff_mem_range_polynomialWorkspaceEmbedding (P : Polynomial Surcomplex.{u}) (n : ℕ) :
    P.coeff n ∈ Set.range (polynomialWorkspaceEmbedding P) := by
  let F := polynomialCoordinateForms P
  let r := SmallNormalForm.familyHahnPreimage F (Sum.inl n)
  let s := SmallNormalForm.familyHahnPreimage F (Sum.inr n)
  refine ⟨Surreal.HahnSeries.realComplexHahnEquiv ⟨r, s⟩, ?_⟩
  rw [polynomialWorkspaceEmbedding, hahnEmbedding_realComplexHahnEquiv]
  apply ext
  · change SmallNormalForm.cutEvaluation (SmallNormalForm.familyWorkspaceEmbedding F r) = _
    rw [SmallNormalForm.familyWorkspaceEmbedding_preimage]
    exact SmallNormalForm.cutEvaluation_normalForm _
  · change SmallNormalForm.cutEvaluation (SmallNormalForm.familyWorkspaceEmbedding F s) = _
    rw [SmallNormalForm.familyWorkspaceEmbedding_preimage]
    exact SmallNormalForm.cutEvaluation_normalForm _

/-- Every actual surcomplex polynomial descends to one algebraically closed Hahn field. -/
theorem exists_polynomial_hahn_preimage (P : Polynomial Surcomplex.{u}) :
    ∃ Q : Polynomial (_root_.HahnSeries (polynomialWorkspaceExponents P) ℂ),
      Q.map (polynomialWorkspaceEmbedding P) = P := by
  apply (Polynomial.mem_lifts P).mp
  apply (Polynomial.lifts_iff_coeff_lifts P).mpr
  exact coeff_mem_range_polynomialWorkspaceEmbedding P

/-- Every nonconstant polynomial has an actual surcomplex root. -/
theorem exists_isRoot_of_natDegree_pos (P : Polynomial Surcomplex.{u})
    (hP : 0 < P.natDegree) : ∃ z : Surcomplex.{u}, P.IsRoot z := by
  obtain ⟨Q, hQ⟩ := exists_polynomial_hahn_preimage P
  have hd : Q.natDegree = P.natDegree := by
    have h := natDegree_map_eq_of_injective (polynomialWorkspaceEmbedding P).injective Q
    rw [hQ] at h
    exact h.symm
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root Q
    (degree_ne_of_natDegree_ne (by rw [hd]; exact Nat.ne_of_gt hP))
  refine ⟨polynomialWorkspaceEmbedding P z, ?_⟩
  simpa only [hQ] using (hz.map (f := polynomialWorkspaceEmbedding P))

/-- The constructed actual surcomplex field is algebraically closed. -/
instance surcomplexIsAlgClosed : IsAlgClosed Surcomplex.{u} := by
  apply IsAlgClosed.of_exists_root
  intro P _ hP
  exact exists_isRoot_of_natDegree_pos P hP.natDegree_pos

/-- Every actual surcomplex polynomial splits into linear factors. -/
theorem polynomial_splits (P : Polynomial Surcomplex.{u}) : P.Splits := IsAlgClosed.splits P

/-- Linear factorization lists every actual root with its multiplicity, including constants. -/
theorem polynomial_factorization (P : Polynomial Surcomplex.{u}) :
    P = C P.leadingCoeff * (P.roots.map fun z => X - C z).prod :=
  FinitePolynomial.factorization P

/-- The total multiplicity of actual roots equals the degree. -/
theorem polynomial_roots_card (P : Polynomial Surcomplex.{u}) :
    P.roots.card = P.natDegree := FinitePolynomial.roots_card P

end

end Surreal.Surcomplex
