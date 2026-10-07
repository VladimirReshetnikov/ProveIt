import OAI.Combinatorics.Progressions.Lattices.ParametricFullResidueCoveredExtension

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped NNReal

noncomputable def coverCoordinatePolynomial {X D : Type*} [Fintype D]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (q : ℕ) (p : VectorPolynomial X ℝ W) :
    VectorPolynomial X ℝ (D → ℝ) :=
  map ((q : ℝ)⁻¹ • ((EuclideanSpace.equiv D ℝ).toLinearMap.comp W.subtype)) p

theorem coverCoordinatePolynomial_eval {X D : Type*} [Fintype D]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (q : ℕ) (p : VectorPolynomial X ℝ W) (t : X → ℝ) :
    eval t (coverCoordinatePolynomial W q p) = fun i => (eval t p).val i / q := by
  rw [coverCoordinatePolynomial, eval_map]
  funext i
  change (q : ℝ)⁻¹ * (eval t p).val i = (eval t p).val i / q
  ring

theorem coverCoordinatePolynomial_degree {X D : Type*} [Fintype D]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (q : ℕ) (p : VectorPolynomial X ℝ W)
    {w : X → ℕ} {d : ℕ} (hp : DegreeLE w d p) :
    DegreeLE w d (coverCoordinatePolynomial W q p) := hp.map _

noncomputable def coverPolynomialOrbit {X M : Type*} {D : M → Type*} [∀ j, Fintype (D j)]
    (W : ∀ j, Submodule ℝ (EuclideanSpace ℝ (D j))) (q : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (W j)) (t : X → ℝ) : (Σ j, D j) → UnitAddCircle :=
  fun a => (eval t (coverCoordinatePolynomial (W a.1) q (p a.1)) a.2 : UnitAddCircle)

theorem coverPolynomialOrbit_eq {X M : Type*} {D : M → Type*} [∀ j, Fintype (D j)]
    (W : ∀ j, Submodule ℝ (EuclideanSpace ℝ (D j))) (q : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (W j)) (t : X → ℝ) :
    coverPolynomialOrbit W q p t = fun a => (((eval t (p a.1)).val a.2 / q : ℝ) : UnitAddCircle) := by
  funext a
  rw [coverPolynomialOrbit, coverCoordinatePolynomial_eval]

variable {X M : Type*} [Fintype M] {D E : M → Type*}
variable [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [∀ j, Fintype (E j)]
variable {n : M → ℕ}
variable (W : ∀ j, Submodule ℝ (EuclideanSpace ℝ (D j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (D j)) (W j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (W j)ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (W j))
variable (q : ℕ) [NeZero q]

include bW in
theorem exists_layered_cover_polynomial_site_factor
    (f : (∀ j, Fin (n j) → ZMod q) → ((Σ j, D j) → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hbound : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : ((Σ j, D j) → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * q) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (p : ∀ j, VectorPolynomial X ℝ (W j)) (t : X → ℝ)
        (x : ∀ j, W j × (Fin (n j) → ℤ)),
        (∀ j, (QuotientAddGroup.mk (eval t (p j)) : W j ⧸
          (latticeSection (standardEuclideanLattice (D j)) (W j)).toAddSubgroup) =
            normalizedLatticeQuotient (W j) (b j) (hb j) (x j)) →
        (∀ j i, |normalizedLatticePoint (W j) (b j) (x j) i| ≤ 1 / 4) →
        g (coverPolynomialOrbit W q p t) =
          f (fun j i => ((x j).2 i : ZMod q))
            (fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2) := by
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_layered_cover_site_extension W bW b hb q f L B hf hbound
  refine ⟨g, hg, hgb, ?_⟩
  intro p t x hu hx
  rw [coverPolynomialOrbit_eq]
  exact hvalue (fun j => eval t (p j)) x hu hx

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped NNReal Classical

noncomputable def coveredSiteCoordinatePolynomial {X D : Type*} [Fintype D]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (q d : ℕ) (p : VectorPolynomial X ℝ W) :
    VectorPolynomial X ℝ (D → ℝ) :=
  coverCoordinatePolynomial W q (map ((d : ℝ) • LinearMap.id) p)

theorem coveredSiteCoordinatePolynomial_eval {X D : Type*} [Fintype D]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (q d : ℕ) (p : VectorPolynomial X ℝ W)
    (t : X → ℝ) :
    eval t (coveredSiteCoordinatePolynomial W q d p) =
      fun i => (d : ℝ) * (eval t p).val i / q := by
  rw [coveredSiteCoordinatePolynomial, coverCoordinatePolynomial_eval, eval_map]
  rfl

theorem coveredSiteCoordinatePolynomial_degree {X D : Type*} [Fintype D]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (q d : ℕ) (p : VectorPolynomial X ℝ W)
    {weight : X → ℕ} {degree : ℕ} (hp : DegreeLE weight degree p) :
    DegreeLE weight degree (coveredSiteCoordinatePolynomial W q d p) :=
  coverCoordinatePolynomial_degree W q _ (hp.map _)

theorem exists_layered_covered_polynomial_site_factor
    {X M : Type*} [Fintype M] {D E : M → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [∀ j, Fintype (E j)] {n : M → ℕ}
    (W : ∀ j, Submodule ℝ (EuclideanSpace ℝ (D j)))
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (D j)) (W j)))
    (b : ∀ j, Basis (Fin (n j)) ℝ (W j)ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (W j))
    (q d : ℕ) [NeZero q] [NeZero d]
    (f : (∀ j, Fin (n j) ⊕ E j → ZMod q) → ((Σ j, D j) → ℝ) → ℂ)
    (L B : ℝ≥0) (hf : ∀ a, LipschitzWith L (f a)) (hbound : ∀ a v, ‖f a v‖ ≤ B) :
    ∃ g : ((Σ j, D j) → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * q) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (p : ∀ j, VectorPolynomial X ℝ (W j)) (t : X → ℝ)
        (x : ∀ j, W j × (Fin (n j) → ℤ)) (r : ∀ j, E j → ZMod d),
        (∀ j, (QuotientAddGroup.mk (eval t (p j)) : W j ⧸
          (latticeSection (standardEuclideanLattice (D j)) (W j)).toAddSubgroup) =
            normalizedCoveredChart (W j) (b j) (hb j) (bW j) d (x j, r j)) →
        (∀ j i, |normalizedLatticePoint (W j) (b j) (x j) i| ≤ 1 / 4) →
        ∃ w : ∀ j, E j → ℤ,
          (∀ j, normalizedLatticeRepresentative (W j) (b j) (hb j) (x j) +
            ((bW j).equivFun.symm (w j)).val = (d : ℝ) • eval t (p j)) ∧
          (∀ j, integerResidueMap (E j) d (w j) = r j) ∧
          g (fun a => (eval t (coveredSiteCoordinatePolynomial (W a.1) q d (p a.1)) a.2 :
            UnitAddCircle)) =
          f (fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => (w j i : ZMod q)))
            (fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2) := by
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_layered_full_residue_extension W bW b hb q f L B hf hbound
  refine ⟨g, hg, hgb, ?_⟩
  intro p t x r hu hx
  choose w hw hr using (fun j =>
    exists_covered_representative_offset (W j) (bW j) (b j) (hb j) d (eval t (p j)) (x j) (r j) (hu j))
  refine ⟨w, hw, hr, ?_⟩
  have h := hvalue x w hx
  simpa only [hw, coveredSiteCoordinatePolynomial_eval, Submodule.coe_smul,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] using h

end Erdos3.VectorPolynomial

end

end OAI
