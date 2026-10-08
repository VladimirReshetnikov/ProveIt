import GowersSzemeredi.Proofs16PolynomialStructuredPiece
import GowersSzemeredi.Proofs16CubicRelationDecomposition

/-! Decompose actual product relations using the polynomial recurrence.

Graph selection and greedy removal extend the new graph-piece cover to
arbitrary two-dimensional product relations. The existing mass and family
count are preserved. The constants C and p are independent of all density
parameters, the modulus, and the relation.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A large projection supplies a graph selection. Its product property
then gives an actual cubic-controlled subrelation of fixed positive mass. -/
theorem exists_polynomial_cubic_relation_piece :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (theta gamma : Real), 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        RelationProductProperty gamma Gamma →
        theta * (N : Real)^2 ≤ (relationProjection Gamma).card →
        ∃ D ⊆ Gamma, section16CubicPieceMass theta gamma * (N : Real)^2 ≤ D.card ∧
          MultiplyLinearWith
            (section16CubicTwoGraphBound (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma)
            (section16PolynomialCubicTwoExponent C p (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma) D := by
  obtain ⟨C, p, hC, hp, hpiece⟩ := exists_polynomial_cubic_product_graph_piece
  refine ⟨C, p, hC, hp, ?_⟩
  intro theta gamma ht ht1 hg hg1
  obtain ⟨N0, hN0⟩ := hpiece theta gamma ht ht1 hg hg1
  refine ⟨max 3 N0, ?_⟩
  intro N _ _ hN Gamma hprod hlarge
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have ho : Odd N := (Fact.out : N.Prime).odd_of_ne_two (by omega)
  obtain ⟨phi, hgraph⟩ := relationProjection_graph_selection Gamma
  obtain ⟨D, hD, hmass, hML⟩ := hN0 N ((le_max_right _ _).trans hN) ho
    (relationProjection Gamma) phi hlarge (hprod _ phi hgraph)
  refine ⟨D, ?_, hmass, hML⟩
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hD hz)
  exact hgraph x hx

/-- Every two-dimensional product relation of bounded size is covered over
a large base domain by a uniformly bounded family of cubic-controlled pieces. -/
theorem exists_polynomial_cubic_relation_decomposition :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (theta gamma : Real), 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real)^2 →
        RelationProductProperty gamma Gamma →
        ∃ q : Nat, ∃ G : Fin q → Finset (Point N 2 × ZMod N), ∃ J : Finset (Point N 2),
          (∀ i, G i ⊆ Gamma ∧ MultiplyLinearWith
            (section16CubicTwoGraphBound (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma)
            (section16PolynomialCubicTwoExponent C p (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma)
            (G i)) ∧
          (q : Real) ≤ gamma ^ (-(2 : Int)) / section16CubicPieceMass theta gamma ∧
          (1 - theta) * (N : Real)^2 ≤ J.card ∧
          restrictRelation Gamma J ⊆ section16FinsetUnion G := by
  obtain ⟨C, p, hC, hp, hpiece⟩ := exists_polynomial_cubic_relation_piece
  refine ⟨C, p, hC, hp, ?_⟩
  intro theta gamma ht ht1 hg hg1
  obtain ⟨N0, hN0⟩ := hpiece theta gamma ht ht1 hg hg1
  refine ⟨N0, ?_⟩
  intro N _ _ hN Gamma hcard hprod
  have hη := section16CubicPieceMass_pos ht hg
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hNpow : (0 : Real) < (N : Real)^2 := pow_pos hNpos _
  obtain ⟨q, G, J, hG, hq, hJ, hcover⟩ := section16_greedy_relation_decomposition
    (MultiplyLinearWith
      (section16CubicTwoGraphBound (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma)
      (section16PolynomialCubicTwoExponent C p (section16BaseFamilyBound gamma (theta / 4)) (theta / 2) gamma))
    theta (section16CubicPieceMass theta gamma * (N : Real)^2) (mul_pos hη hNpow) Gamma
    (fun Delta hDelta hlarge => hN0 N hN Delta (hprod.mono hDelta) hlarge)
  refine ⟨q, G, J, hG, ?_, hJ, hcover⟩
  apply (le_div_iff₀ hη).mpr
  apply (mul_le_mul_iff_left₀ hNpow).mp
  calc
    (q : Real) * section16CubicPieceMass theta gamma * (N : Real)^2 =
        q * (section16CubicPieceMass theta gamma * (N : Real)^2) := by ring
    _ ≤ (Gamma.card : Real) := hq
    _ ≤ gamma ^ (-(2 : Int)) * (N : Real)^2 := hcard

end LeanProofs.GowersSzemeredi
