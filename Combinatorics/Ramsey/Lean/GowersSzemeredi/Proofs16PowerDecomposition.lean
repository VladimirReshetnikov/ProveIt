import GowersSzemeredi.Proofs16LargePowerPiece
import GowersSzemeredi.Proofs16GreedyRelations
import GowersSzemeredi.Proofs16BaseCaseEndpoint

/-! Execute the full finite relation extraction with the proved contextual
power profiles. No unit-multiple-linearity or separate lifting hypothesis
is assumed. Combining the profiles with the source controls remains open. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- After discarding a small set of projected points, a product relation
is covered by a bounded number of subrelations with explicit power-cover
profiles. The only structural assumptions are in preceding dimensions. -/
theorem section16_power_decomposition_of_dimension_induction {k : Nat} (hk : 1 ≤ k)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l)
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N (k + 1) × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ (k + 1) →
        RelationProductProperty gamma Gamma →
        ∃ q : Nat, ∃ G : Fin q → Finset (Point N (k + 1) × ZMod N),
          ∃ J : Finset (Point N (k + 1)),
            (∀ i, G i ⊆ Gamma ∧ Section16PowerCoverProfile theta gamma k (G i)) ∧
            (q : Real) ≤ gamma ^ (-(2 : Int)) * multipleS theta gamma (k + 1) ∧
            (1 - theta) * (N : Real) ^ (k + 1) ≤ J.card ∧
            restrictRelation Gamma J ⊆ section16FinsetUnion G := by
  obtain ⟨N0, hN0⟩ := section16_large_power_piece_of_dimension_induction hk hth theta gamma ht ht1 hg hg1
  refine ⟨N0, fun N _ _ hN Gamma hcard hprod => ?_⟩
  have hS : 0 < multipleS theta gamma (k + 1) :=
    zero_lt_one.trans_le (one_le_multipleS (k + 1) ht ht1 hg hg1)
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let mass := (N : Real) ^ (k + 1) / multipleS theta gamma (k + 1)
  have hmass : 0 < mass := by dsimp [mass]; positivity
  obtain ⟨q, G, J, hG, hq, hJ, hc⟩ := section16_greedy_relation_decomposition
    (Section16PowerCoverProfile theta gamma k) theta mass hmass Gamma
    (fun Delta hDelta hlarge => hN0 N hN Delta (hprod.mono hDelta) hlarge)
  refine ⟨q, G, J, hG, ?_, hJ, hc⟩
  have hbudget : (q : Real) * mass ≤
      (gamma ^ (-(2 : Int)) * multipleS theta gamma (k + 1)) * mass := by
    calc
      _ ≤ (Gamma.card : Real) := hq
      _ ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ (k + 1) := hcard
      _ = _ := by dsimp [mass]; field_simp
  exact (mul_le_mul_iff_left₀ hmass).mp hbudget

/-- The two-dimensional relation decomposition is unconditional: its only
preceding structural dimension is the proved one-dimensional base. -/
theorem section16_bilinear_power_decomposition
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 →
        RelationProductProperty gamma Gamma →
        ∃ q : Nat, ∃ G : Fin q → Finset (Point N 2 × ZMod N), ∃ J : Finset (Point N 2),
          (∀ i, G i ⊆ Gamma ∧ Section16PowerCoverProfile theta gamma 1 (G i)) ∧
          (q : Real) ≤ gamma ^ (-(2 : Int)) * multipleS theta gamma 2 ∧
          (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
          restrictRelation Gamma J ⊆ section16FinsetUnion G := by
  apply section16_power_decomposition_of_dimension_induction (k := 1) le_rfl _ theta gamma ht ht1 hg hg1
  intro l hl hl1
  have heq : l = 1 := by omega
  subst l
  exact lemma_16_3_holds

end LeanProofs.GowersSzemeredi
