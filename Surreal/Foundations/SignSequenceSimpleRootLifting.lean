import Surreal.Foundations.SignSequenceWorkspace
import Surreal.Foundations.SignSequenceHahnValuation
import Surreal.Foundations.SignSequencePolynomialNormalization
import Surreal.HahnSeries.PronyLocalRoots
import Surreal.Algebra.PolynomialSimpleReduction

/-!
# Simple residue roots in the actual surreal field

The nonmonic Hahn lifting theorem is transferred through a common small
workspace for all polynomial coefficients. This proves actual-carrier
simple-root lifting for `trigonometry:lem:hensel` and the real univariate
clause of `prony:lem:hensel`. Uniqueness compares all actual finite roots,
not just roots in the workspace used for existence.
-/

universe u v

namespace Surreal.Foundations.SignSequence

open Polynomial

noncomputable section

section Workspace

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Small.{u} Γ]

/-- A small Hahn embedding restricts to the actual finite-element rings. -/
def finiteHahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e) :
    Surreal.HahnSeries.nonnegativeSubring Γ ℝ →+* FiniteElement.{u} where
  toFun x := ⟨hahnEmbedding e he x.1, (isFinite_hahnEmbedding_iff e he x.1).mpr x.2⟩
  map_zero' := by apply Subtype.ext; exact map_zero (hahnEmbedding e he)
  map_one' := by apply Subtype.ext; exact map_one (hahnEmbedding e he)
  map_add' x y := by apply Subtype.ext; exact map_add (hahnEmbedding e he) x.1 y.1
  map_mul' x y := by apply Subtype.ext; exact map_mul (hahnEmbedding e he) x.1 y.1

@[simp] theorem finiteHahnEmbedding_val (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : Surreal.HahnSeries.nonnegativeSubring Γ ℝ) :
    (finiteHahnEmbedding e he x).1 = hahnEmbedding e he x.1 := rfl

/-- The restricted embedding preserves the literal standard-part map. -/
@[simp] theorem standardPart_finiteHahnEmbedding (e : Γ →+ SignSequence.{u}) (he : StrictMono e)
    (x : Surreal.HahnSeries.nonnegativeSubring Γ ℝ) :
    standardPartHom (finiteHahnEmbedding e he x) = Surreal.HahnSeries.standardPart Γ ℝ x :=
  standardPart_hahnEmbedding e he x.1 x.2

end Workspace

/-- Every finite polynomial with a simple ordinary-real residue root has an actual finite root. -/
theorem exists_root_of_simple_residue (p : Polynomial FiniteElement.{u}) (c : ℝ)
    (hc : (p.map standardPartHom.toRingHom).IsRoot c)
    (hd : (p.map standardPartHom.toRingHom).derivative.eval c ≠ 0) :
    ∃ x : FiniteElement.{u}, p.IsRoot x ∧ standardPartHom x = c := by
  let P := p.map finiteElementInclusion
  let Γ := workspaceExponents
    (⋃ n, SmallNormalForm.support (SmallNormalForm.normalForm (P.coeff n)))
  let e : Γ →+ SignSequence.{u} := Γ.subtype.toAddMonoidHom
  have he : StrictMono e := fun _ _ h => h
  obtain ⟨Q, hQ⟩ := exists_polynomial_hahn_preimage P
  have hcoeff (n : ℕ) : hahnEmbedding e he (Q.coeff n) = (p.coeff n).1 := by
    have hh := congrArg (fun q => q.coeff n) hQ
    simp only [coeff_map] at hh
    change hahnEmbedding e he (Q.coeff n) = P.coeff n at hh
    simpa only [P, coeff_map, finiteElementInclusion_apply] using hh
  have hnonneg (n : ℕ) : 0 ≤ (Q.coeff n).orderTop := by
    apply (isFinite_hahnEmbedding_iff e he _).mp
    rw [hcoeff]
    exact (p.coeff n).2
  have hlift : Q ∈ lifts (Surreal.HahnSeries.nonnegativeSubring Γ ℝ).subtype := by
    apply (lifts_iff_coeff_lifts Q).mpr
    intro n
    exact ⟨⟨Q.coeff n, hnonneg n⟩, rfl⟩
  obtain ⟨H, hH⟩ := (mem_lifts Q).mp hlift
  have hHp : H.map (finiteHahnEmbedding e he) = p := by
    apply Polynomial.ext
    intro n
    apply Subtype.ext
    have hh := congrArg (fun q => q.coeff n) hH
    simp only [coeff_map, Subring.subtype_apply] at hh
    simpa only [coeff_map, finiteHahnEmbedding_val, hh] using hcoeff n
  have hres : H.map (Surreal.HahnSeries.standardPart Γ ℝ) = p.map standardPartHom.toRingHom := by
    rw [← hHp, map_map]
    congr 1
    ext x
    exact (standardPart_finiteHahnEmbedding e he x).symm
  obtain ⟨x, ⟨hx, hxc⟩, _⟩ := Surreal.PronyLocal.existsUnique_root_of_simple_residue H c
    (by rwa [hres]) (by rwa [hres])
  refine ⟨finiteHahnEmbedding e he x, ?_, ?_⟩
  · simpa only [hHp] using hx.map (f := finiteHahnEmbedding e he)
  · simpa only [standardPart_finiteHahnEmbedding] using hxc

/-- The lift is unique among all actual finite surreals with the given standard part. -/
theorem existsUnique_root_of_simple_residue (p : Polynomial FiniteElement.{u}) (c : ℝ)
    (hc : (p.map standardPartHom.toRingHom).IsRoot c)
    (hd : (p.map standardPartHom.toRingHom).derivative.eval c ≠ 0) :
    ∃! x : FiniteElement.{u}, p.IsRoot x ∧ standardPartHom x = c := by
  obtain ⟨x, hx, hxc⟩ := exists_root_of_simple_residue p c hc hd
  refine ⟨x, ⟨hx, hxc⟩, ?_⟩
  rintro y ⟨hy, hyc⟩
  exact FinitePolynomial.eq_of_isRoot_of_simple_reduction standardPartHom.toRingHom p x y
    hx hy (hyc.trans hxc.symm) (by
      change (p.map standardPartHom.toRingHom).derivative.eval (standardPartHom x) ≠ 0
      rwa [hxc])

/-- A lift of a simple residue root has a nonzero derivative in the finite ring. -/
theorem derivative_ne_zero_of_simple_residue (p : Polynomial FiniteElement.{u}) (c : ℝ)
    (hd : (p.map standardPartHom.toRingHom).derivative.eval c ≠ 0)
    (x : FiniteElement.{u}) (hxc : standardPartHom x = c) : p.derivative.eval x ≠ 0 := by
  apply FinitePolynomial.eval_derivative_ne_zero_of_simple_reduction standardPartHom.toRingHom
  change (p.map standardPartHom.toRingHom).derivative.eval (standardPartHom x) ≠ 0
  rwa [hxc]

/-- Actual-coefficient form of simple-root lifting, with no monicity hypothesis. -/
theorem existsUnique_finite_root_of_simple_reduction (P : Polynomial SignSequence.{u})
    (hP : ∀ n, IsFinite (P.coeff n)) (c : ℝ)
    (hc : (reducePolynomial P hP).IsRoot c)
    (hd : (reducePolynomial P hP).derivative.eval c ≠ 0) :
    ∃! x : SignSequence.{u}, IsFinite x ∧ P.IsRoot x ∧ standardPart x = c := by
  obtain ⟨x, ⟨hx, hxc⟩, hu⟩ := existsUnique_root_of_simple_residue (finitePolynomial P hP) c hc hd
  have hroot : P.IsRoot x.1 := by
    simpa only [map_finitePolynomial, finiteElementInclusion_apply] using
      hx.map (f := finiteElementInclusion)
  refine ⟨x.1, ⟨x.2, hroot, hxc⟩, ?_⟩
  rintro y ⟨hy, hyr, hyc⟩
  let y' : FiniteElement.{u} := ⟨y, hy⟩
  have hyr' : (finitePolynomial P hP).IsRoot y' := by
    apply Polynomial.IsRoot.of_map (f := finiteElementInclusion) _ finiteElementInclusion_injective
    simpa only [map_finitePolynomial, finiteElementInclusion_apply] using hyr
  exact congrArg Subtype.val (hu y' ⟨hyr', hyc⟩)

/-- Every actual root with a simple residue has native polynomial multiplicity one. -/
theorem rootMultiplicity_eq_one_of_simple_reduction (P : Polynomial SignSequence.{u})
    (hP : ∀ n, IsFinite (P.coeff n)) (c : ℝ)
    (hd : (reducePolynomial P hP).derivative.eval c ≠ 0)
    (x : SignSequence.{u}) (hx : IsFinite x) (hroot : P.IsRoot x)
    (hxc : standardPart x = c) : P.rootMultiplicity x = 1 := by
  let x' : FiniteElement.{u} := ⟨x, hx⟩
  have hd' := derivative_ne_zero_of_simple_residue (finitePolynomial P hP) c hd x' hxc
  have hdx : P.derivative.eval x ≠ 0 := by
    have hn := finiteElementInclusion_injective.ne hd'
    simpa only [map_zero, ← eval₂_at_apply, ← eval_map, ← derivative_map,
      map_finitePolynomial, finiteElementInclusion_apply] using hn
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact hdx (by simp)
  have hpos := (rootMultiplicity_pos hP0).mpr hroot
  have hle : ¬ 1 < P.rootMultiplicity x := fun h =>
    hdx ((one_lt_rootMultiplicity_iff_isRoot hP0).mp h).2.eq_zero
  omega

/-- The manuscript's simple-residue-root lemma: reduction `Y+b₀` has exactly
one finite root, with standard part `-b₀`, and that root is simple. -/
theorem exists_unique_simple_root_of_linear_reduction (P : Polynomial SignSequence.{u})
    (hP : ∀ n, IsFinite (P.coeff n)) (b : ℝ)
    (hred : reducePolynomial P hP = X + C b) :
    ∃ x : SignSequence.{u}, IsFinite x ∧ standardPart x = -b ∧ P.IsRoot x ∧
      P.rootMultiplicity x = 1 ∧
        ∀ y, IsFinite y → P.IsRoot y → standardPart y = -b → y = x := by
  have hc : (reducePolynomial P hP).IsRoot (-b) := by simp [hred, IsRoot.def]
  have hd : (reducePolynomial P hP).derivative.eval (-b) ≠ 0 := by simp [hred]
  obtain ⟨x, ⟨hx, hroot, hxc⟩, hu⟩ :=
    existsUnique_finite_root_of_simple_reduction P hP (-b) hc hd
  exact ⟨x, hx, hxc, hroot,
    rootMultiplicity_eq_one_of_simple_reduction P hP (-b) hd x hx hroot hxc,
    fun y hy hyr hyc => hu y ⟨hy, hyr, hyc⟩⟩

end
end Surreal.Foundations.SignSequence
