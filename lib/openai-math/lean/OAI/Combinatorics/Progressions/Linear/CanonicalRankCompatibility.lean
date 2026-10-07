import OAI.Combinatorics.Progressions.Nilpotent.DegreeRankBCH
import OAI.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem eq_of_layer_eq {F G : NilpotentLieFiltration L s} (h : F.layer = G.layer) : F = G := by
  cases F
  cases G
  cases h
  rfl

variable (F : NilpotentLieFiltration L s)

theorem canonicalDegreeRank_associatedDegree_eq : F.canonicalDegreeRank.associatedDegree = F :=
  eq_of_layer_eq (funext F.canonicalDegreeRank_associatedDegree_layer)

theorem canonicalDegreeRank_subgroup (d i : ℕ) :
    F.canonicalDegreeRank.subgroup d i = F.rankSubgroup d i := by
  ext x
  rfl

noncomputable def orbitEquivOfEq {G : NilpotentLieFiltration L s} (h : F = G)
    {σ : Type*} (w : σ → ℕ) : F.PolynomialOrbit w ≃* G.PolynomialOrbit w := by
  subst G
  exact MulEquiv.refl _

theorem orbitEquivOfEq_eval {G : NilpotentLieFiltration L s} (h : F = G)
    {σ : Type*} (w : σ → ℕ) (g : F.PolynomialOrbit w) (x : σ → ℤ) :
    G.polynomialOrbitEval w x (F.orbitEquivOfEq h w g) = F.polynomialOrbitEval w x g := by
  subst G
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
