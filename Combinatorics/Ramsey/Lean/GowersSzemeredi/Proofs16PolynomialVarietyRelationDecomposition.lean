import GowersSzemeredi.Proofs16PolynomialVarietyStructuredPiece
import GowersSzemeredi.Proofs16CubicRelationDecomposition

/-! Actual dimension-three product relations decompose into uniformly
controlled graph pieces, conditional on deep variety structure. The
positive mass and family count do not depend on the modulus or inner loss.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16VarietyPieceMass (theta gamma : Real) : Real :=
  section16ThetaTwo (section16ThetaOne (theta / 2) gamma 2)

theorem section16VarietyPieceMass_pos {theta gamma : Real} (ht : 0 < theta) (hg : 0 < gamma) :
    0 < section16VarietyPieceMass theta gamma := by
  unfold section16VarietyPieceMass section16ThetaTwo section16ThetaOne
  positivity

def section16VarietyThreeGraphBound (D : Nat) (theta gamma rho : Real) : Real :=
  max (section16VarietyLiftGraphBound (section16VarietyExtractionCount D gamma (theta / 4))
    (theta / 2) gamma rho) 27

def section16VarietyThreePieceExponent (C p Cv pv Cs ps D : Nat) (theta gamma rho : Real) : Real :=
  section16PolynomialVarietyThreeExponent C p Cv pv Cs ps D
    (section16VarietyExtractionCount D gamma (theta / 4))
    (section16VarietyExtractionDensity gamma (theta / 4)) (theta / 2) gamma rho

/-- The statement of `exists_polynomial_variety_relation_piece` at fixed constants. -/
def PolynomialVarietyRelationPieceAt (C p Cv pv Cs ps : Nat) : Prop :=
  ∀ D : Nat, MilicevicDeepVarietyStructure D →
  ∀ (theta gamma : Real), 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 3 × ZMod N),
        RelationProductProperty gamma Gamma →
        theta * (N : Real)^3 ≤ (relationProjection Gamma).card →
        ∃ Piece ⊆ Gamma, section16VarietyPieceMass theta gamma * (N : Real)^3 ≤ Piece.card ∧
          MultiplyLinearWith
            (section16VarietyThreeGraphBound D theta gamma)
            (section16VarietyThreePieceExponent C p Cv pv Cs ps D theta gamma) Piece

/-- `exists_polynomial_variety_relation_piece` at the constants of its input. -/
theorem polynomialVarietyRelationPieceAt_of {C p Cv pv Cs ps : Nat} (hC : 2 ≤ C) (hp : 0 < p) (hCv : 2 ≤ Cv) (hpv : 0 < pv) (hCs : 2 ≤ Cs) (hps : 0 < ps)
    (hpiece : PolynomialVarietyProductGraphPieceAt C p Cv pv Cs ps) : PolynomialVarietyRelationPieceAt C p Cv pv Cs ps := by
  unfold PolynomialVarietyRelationPieceAt
  intro D hD theta gamma ht ht1 hg hg1
  obtain ⟨N0, hN0⟩ := hpiece D hD theta gamma ht ht1 hg hg1
  refine ⟨max 3 N0, ?_⟩
  intro N _ _ hN Gamma hprod hlarge
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have ho : Odd N := (Fact.out : N.Prime).odd_of_ne_two (by omega)
  obtain ⟨phi, hgraph⟩ := relationProjection_graph_selection Gamma
  obtain ⟨Piece, hPiece, hmass, hML⟩ := hN0 N ((le_max_right _ _).trans hN) ho
    (relationProjection Gamma) phi hlarge (hprod _ phi hgraph)
  refine ⟨Piece, ?_, hmass, hML⟩
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hPiece hz)
  exact hgraph x hx

/-- A large projection supplies a graph selection. Its product property
then gives an actual polynomially controlled subrelation of fixed positive mass. -/
theorem exists_polynomial_variety_relation_piece :
  ∃ C p Cv pv Cs ps : Nat, 2 ≤ C ∧ 0 < p ∧ 2 ≤ Cv ∧ 0 < pv ∧ 2 ≤ Cs ∧ 0 < ps ∧
  ∀ D : Nat, MilicevicDeepVarietyStructure D →
  ∀ (theta gamma : Real), 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 3 × ZMod N),
        RelationProductProperty gamma Gamma →
        theta * (N : Real)^3 ≤ (relationProjection Gamma).card →
        ∃ Piece ⊆ Gamma, section16VarietyPieceMass theta gamma * (N : Real)^3 ≤ Piece.card ∧
          MultiplyLinearWith
            (section16VarietyThreeGraphBound D theta gamma)
            (section16VarietyThreePieceExponent C p Cv pv Cs ps D theta gamma) Piece := by
  obtain ⟨C, p, Cv, pv, Cs, ps, hC, hp, hCv, hpv, hCs, hps, hpiece⟩ := exists_polynomial_variety_product_graph_piece
  exact ⟨C, p, Cv, pv, Cs, ps, hC, hp, hCv, hpv, hCs, hps, polynomialVarietyRelationPieceAt_of hC hp hCv hpv hCs hps hpiece⟩

/-- The statement of `exists_polynomial_variety_relation_decomposition` at fixed constants. -/
def PolynomialVarietyRelationDecompositionAt (C p Cv pv Cs ps : Nat) : Prop :=
  ∀ D : Nat, MilicevicDeepVarietyStructure D →
  ∀ (theta gamma : Real), 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 3 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real)^3 →
        RelationProductProperty gamma Gamma →
        ∃ q : Nat, ∃ G : Fin q → Finset (Point N 3 × ZMod N), ∃ J : Finset (Point N 3),
          (∀ i, G i ⊆ Gamma ∧ MultiplyLinearWith
            (section16VarietyThreeGraphBound D theta gamma)
            (section16VarietyThreePieceExponent C p Cv pv Cs ps D theta gamma)
            (G i)) ∧
          (q : Real) ≤ gamma ^ (-(2 : Int)) / section16VarietyPieceMass theta gamma ∧
          (1 - theta) * (N : Real)^3 ≤ J.card ∧
          restrictRelation Gamma J ⊆ section16FinsetUnion G

/-- `exists_polynomial_variety_relation_decomposition` at the constants of its input. -/
theorem polynomialVarietyRelationDecompositionAt_of {C p Cv pv Cs ps : Nat} (hC : 2 ≤ C) (hp : 0 < p) (hCv : 2 ≤ Cv) (hpv : 0 < pv) (hCs : 2 ≤ Cs) (hps : 0 < ps)
    (hpiece : PolynomialVarietyRelationPieceAt C p Cv pv Cs ps) : PolynomialVarietyRelationDecompositionAt C p Cv pv Cs ps := by
  unfold PolynomialVarietyRelationDecompositionAt
  intro D hD theta gamma ht ht1 hg hg1
  obtain ⟨N0, hN0⟩ := hpiece D hD theta gamma ht ht1 hg hg1
  refine ⟨N0, ?_⟩
  intro N _ _ hN Gamma hcard hprod
  have hη := section16VarietyPieceMass_pos ht hg
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hNpow : (0 : Real) < (N : Real)^3 := pow_pos hNpos _
  obtain ⟨q, G, J, hG, hq, hJ, hcover⟩ := section16_greedy_relation_decomposition
    (MultiplyLinearWith
      (section16VarietyThreeGraphBound D theta gamma)
      (section16VarietyThreePieceExponent C p Cv pv Cs ps D theta gamma))
    theta (section16VarietyPieceMass theta gamma * (N : Real)^3) (mul_pos hη hNpow) Gamma
    (fun Delta hDelta hlarge => hN0 N hN Delta (hprod.mono hDelta) hlarge)
  refine ⟨q, G, J, hG, ?_, hJ, hcover⟩
  apply (le_div_iff₀ hη).mpr
  apply (mul_le_mul_iff_left₀ hNpow).mp
  calc
    (q : Real) * section16VarietyPieceMass theta gamma * (N : Real)^3 =
        q * (section16VarietyPieceMass theta gamma * (N : Real)^3) := by ring
    _ ≤ (Gamma.card : Real) := hq
    _ ≤ gamma ^ (-(2 : Int)) * (N : Real)^3 := hcard

/-- Every three-dimensional product relation of bounded size is covered over
a large base domain by a uniformly bounded family of polynomially controlled pieces. -/
theorem exists_polynomial_variety_relation_decomposition :
  ∃ C p Cv pv Cs ps : Nat, 2 ≤ C ∧ 0 < p ∧ 2 ≤ Cv ∧ 0 < pv ∧ 2 ≤ Cs ∧ 0 < ps ∧
  ∀ D : Nat, MilicevicDeepVarietyStructure D →
  ∀ (theta gamma : Real), 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 3 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real)^3 →
        RelationProductProperty gamma Gamma →
        ∃ q : Nat, ∃ G : Fin q → Finset (Point N 3 × ZMod N), ∃ J : Finset (Point N 3),
          (∀ i, G i ⊆ Gamma ∧ MultiplyLinearWith
            (section16VarietyThreeGraphBound D theta gamma)
            (section16VarietyThreePieceExponent C p Cv pv Cs ps D theta gamma)
            (G i)) ∧
          (q : Real) ≤ gamma ^ (-(2 : Int)) / section16VarietyPieceMass theta gamma ∧
          (1 - theta) * (N : Real)^3 ≤ J.card ∧
          restrictRelation Gamma J ⊆ section16FinsetUnion G := by
  obtain ⟨C, p, Cv, pv, Cs, ps, hC, hp, hCv, hpv, hCs, hps, hpiece⟩ := exists_polynomial_variety_relation_piece
  exact ⟨C, p, Cv, pv, Cs, ps, hC, hp, hCv, hpv, hCs, hps, polynomialVarietyRelationDecompositionAt_of hC hp hCv hpv hCs hps hpiece⟩

end LeanProofs.GowersSzemeredi
