import Surreal.Surcomplex.HahnValuation
import Surreal.HahnSeries.PronyLocalRoots
import Surreal.Algebra.PolynomialSimpleReduction

/-!
# Simple residue roots in the actual surcomplex field

This transfers the univariate clause of `prony:lem:hensel` from a common
small complex Hahn workspace to actual surcomplex numbers. Polynomials
need not be monic. The comparison proof establishes uniqueness among all
actual finite roots with the prescribed residue, independently of the
workspace used for existence. Multivariate existence remains separate.
-/

universe u v

namespace Surreal.Surcomplex

open Polynomial

noncomputable section

section Workspace

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Small.{u} Γ]

/-- A small Hahn embedding restricts to the actual finite-element rings. -/
def finiteHahnEmbedding (e : Γ →+ Foundations.SignSequence.{u}) (he : StrictMono e) :
    Surreal.HahnSeries.nonnegativeSubring Γ ℂ →+* finiteSubring.{u} where
  toFun x := ⟨hahnEmbedding e he x.1, (isFinite_hahnEmbedding_iff e he x.1).mpr x.2⟩
  map_zero' := by apply Subtype.ext; exact map_zero (hahnEmbedding e he)
  map_one' := by apply Subtype.ext; exact map_one (hahnEmbedding e he)
  map_add' x y := by apply Subtype.ext; exact map_add (hahnEmbedding e he) x.1 y.1
  map_mul' x y := by apply Subtype.ext; exact map_mul (hahnEmbedding e he) x.1 y.1

@[simp] theorem finiteHahnEmbedding_val (e : Γ →+ Foundations.SignSequence.{u}) (he : StrictMono e)
    (x : Surreal.HahnSeries.nonnegativeSubring Γ ℂ) :
    (finiteHahnEmbedding e he x).1 = hahnEmbedding e he x.1 := rfl

/-- The restricted embedding preserves the literal standard-part map. -/
@[simp] theorem standardPart_finiteHahnEmbedding (e : Γ →+ Foundations.SignSequence.{u}) (he : StrictMono e)
    (x : Surreal.HahnSeries.nonnegativeSubring Γ ℂ) :
    standardPartHom (finiteHahnEmbedding e he x) = Surreal.HahnSeries.standardPart Γ ℂ x :=
  standardPart_hahnEmbedding e he x.1 x.2

end Workspace

/-- Every finite polynomial with a simple ordinary-complex residue root has an actual finite root. -/
theorem exists_root_of_simple_residue (p : Polynomial finiteSubring.{u}) (c : ℂ)
    (hc : (p.map standardPartHom).IsRoot c)
    (hd : (p.map standardPartHom).derivative.eval c ≠ 0) :
    ∃ x : finiteSubring.{u}, p.IsRoot x ∧ standardPartHom x = c := by
  let P := p.map finiteSubring.subtype
  let Γ := polynomialWorkspaceExponents P
  let e : Γ →+ Foundations.SignSequence.{u} := Γ.subtype.toAddMonoidHom
  have he : StrictMono e := fun _ _ h => h
  obtain ⟨Q, hQ⟩ := exists_polynomial_hahn_preimage P
  have hcoeff (n : ℕ) : hahnEmbedding e he (Q.coeff n) = (p.coeff n).1 := by
    have hh := congrArg (fun q => q.coeff n) hQ
    simp only [coeff_map] at hh
    change hahnEmbedding e he (Q.coeff n) = P.coeff n at hh
    simpa only [P, coeff_map, Subring.subtype_apply] using hh
  have hnonneg (n : ℕ) : 0 ≤ (Q.coeff n).orderTop := by
    apply (isFinite_hahnEmbedding_iff e he _).mp
    rw [hcoeff]
    exact (p.coeff n).2
  have hlift : Q ∈ lifts (Surreal.HahnSeries.nonnegativeSubring Γ ℂ).subtype := by
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
  have hres : H.map (Surreal.HahnSeries.standardPart Γ ℂ) = p.map standardPartHom := by
    rw [← hHp, map_map]
    congr 1
    ext x
    exact (standardPart_finiteHahnEmbedding e he x).symm
  obtain ⟨x, ⟨hx, hxc⟩, _⟩ := Surreal.PronyLocal.existsUnique_root_of_simple_residue H c
    (by rwa [hres]) (by rwa [hres])
  refine ⟨finiteHahnEmbedding e he x, ?_, ?_⟩
  · simpa only [hHp] using hx.map (f := finiteHahnEmbedding e he)
  · simpa only [standardPart_finiteHahnEmbedding] using hxc

/-- The lift is unique among all actual finite surcomplex numbers with the given standard part. -/
theorem existsUnique_root_of_simple_residue (p : Polynomial finiteSubring.{u}) (c : ℂ)
    (hc : (p.map standardPartHom).IsRoot c)
    (hd : (p.map standardPartHom).derivative.eval c ≠ 0) :
    ∃! x : finiteSubring.{u}, p.IsRoot x ∧ standardPartHom x = c := by
  obtain ⟨x, hx, hxc⟩ := exists_root_of_simple_residue p c hc hd
  refine ⟨x, ⟨hx, hxc⟩, ?_⟩
  rintro y ⟨hy, hyc⟩
  exact FinitePolynomial.eq_of_isRoot_of_simple_reduction standardPartHom p x y
    hx hy (hyc.trans hxc.symm) (by
      change (p.map standardPartHom).derivative.eval (standardPartHom x) ≠ 0
      rwa [hxc])

/-- A lift of a simple residue root has a nonzero derivative in the finite ring. -/
theorem derivative_ne_zero_of_simple_residue (p : Polynomial finiteSubring.{u}) (c : ℂ)
    (hd : (p.map standardPartHom).derivative.eval c ≠ 0)
    (x : finiteSubring.{u}) (hxc : standardPartHom x = c) : p.derivative.eval x ≠ 0 := by
  apply FinitePolynomial.eval_derivative_ne_zero_of_simple_reduction standardPartHom
  change (p.map standardPartHom).derivative.eval (standardPartHom x) ≠ 0
  rwa [hxc]

/-- The lift is an actual infinitesimal correction to the prescribed ordinary complex root. -/
theorem existsUnique_infinitesimal_root_correction (p : Polynomial finiteSubring.{u}) (c : ℂ)
    (hc : (p.map standardPartHom).IsRoot c)
    (hd : (p.map standardPartHom).derivative.eval c ≠ 0) :
    ∃! ε : Surcomplex.{u}, IsInfinitesimal ε ∧
      (p.map finiteSubring.subtype).IsRoot (ofComplex c + ε) := by
  obtain ⟨x, ⟨hx, hxc⟩, hu⟩ := existsUnique_root_of_simple_residue p c hc hd
  refine ⟨x.1 - ofComplex c, ⟨(infinitesimal_sub_ofComplex_iff x.2).mpr hxc, ?_⟩, ?_⟩
  · simpa only [add_sub_cancel, Subring.subtype_apply] using hx.map (f := finiteSubring.subtype)
  · rintro ε ⟨hε, hr⟩
    let y : finiteSubring.{u} := ⟨ofComplex c + ε,
      finiteSubring.add_mem (finite_ofComplex c) (finite_of_infinitesimal hε)⟩
    have hyr : p.IsRoot y := hr.of_map (f := finiteSubring.subtype) Subtype.val_injective
    have hyc : standardPartHom y = c := by
      apply (infinitesimal_sub_ofComplex_iff y.2).mp
      simpa only [y, add_sub_cancel_left] using hε
    have he := congrArg Subtype.val (hu y ⟨hyr, hyc⟩)
    change ofComplex c + ε = x.1 at he
    rw [← he, add_sub_cancel_left]

end
end Surreal.Surcomplex
