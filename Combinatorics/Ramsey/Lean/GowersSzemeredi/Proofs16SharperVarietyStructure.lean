import GowersSzemeredi.Proofs16SharperLineExtractor

/-! Supply the variety structure side with the sharper line-density extraction.
The deep variety structure hypothesis remains explicit. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem structure_side_of_milicevic_sharper {D : Nat} (hM : MilicevicDeepVarietyStructure D)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 →
        RelationProductProperty gamma Gamma →
        ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
          ∃ (K : Nat) (G : Fin K → Finset (ZMod N × ZMod N))
            (f : Fin K → ZMod N × ZMod N → ZMod N),
            (K : Real) ≤
              bihomFamilySize (densePieceMassGen section16SharperLineMass) gamma (theta / 2) *
              Real.exp (milicevicBound D (theta / 2 /
                bihomFamilySize (densePieceMassGen section16SharperLineMass) gamma (theta / 2))) ∧
            (∀ k, IsVarietyPiece D (theta / 2 /
              bihomFamilySize (densePieceMassGen section16SharperLineMass) gamma (theta / 2))
              (f k) (G k)) ∧
            restrictRelation Gamma J ⊆ section16FinsetUnion
              (fun k => partialGraph ((G k).image pairPoint) (fun x => f k (x 0, x 1))) :=
  variety_structure_side hM (bihomExtraction_of_densePiece densePiece_sharper)
    gamma theta hg hg1 ht ht1


end LeanProofs.GowersSzemeredi
