import GowersSzemeredi.Proofs16VarietyGreedyCover

/-! The structure side (S) of Part J in dimension two, from two inputs.

`StackableStructureAt 2 Q q` (`Proofs16PartJInterface`) asks two things.
After removing a `θ` fraction of base points, every product relation must be
covered by `Q` members of a class. That class must also be stackable. This
module derives the **covering** clause from two hypotheses, with variety
pieces as members.

* `BihomExtraction m` (research notes J.4, step 1; open). After removing
  `θ`, a product relation is covered by the graphs of `m γ θ` Freiman
  bihomomorphisms on their domains. This is the dimension-two analogue of
  `section16_extract_uniform_base_family`, in the form of a bilinear
  Balog–Szemerédi–Gowers step. It is stated with the quantifiers of
  `StackableStructureAt`.
* `MilicevicDeepVarietyStructure D` (research notes J.2).

`variety_structure_side`: under both, after removing `θ` of the base, the
relation is covered by at most `m·exp(B(θ/(2m)))` variety pieces
(`IsVarietyPiece`), each read as a partial function on `Point N 2`. Here
`m = m γ (θ/2)` and `B = milicevicBound D`. Both inputs remain hypotheses,
and stackability of the variety class is a separate question (J.4 step 3).
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- A pair as a point of `Z_N^2`. -/
def pairPoint {N : Nat} (q : ZMod N × ZMod N) : Point N 2 := ![q.1, q.2]

theorem pairPoint_coords {N : Nat} (x : Point N 2) : pairPoint (x 0, x 1) = x := by
  funext i
  fin_cases i <;> rfl

/-- **Extraction of Freiman bihomomorphisms from product relations**
(research notes J.4, step 1). A hypothesis; not asserted. -/
def BihomExtraction (m : Real → Real → Nat) : Prop :=
  ∀ gamma theta : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
    0 < m gamma theta ∧
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 →
        RelationProductProperty gamma Gamma →
        ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
          ∃ (φ : Fin (m gamma theta) → ZMod N × ZMod N → ZMod N)
            (A : Fin (m gamma theta) → Finset (ZMod N × ZMod N)),
            (∀ j, IsEBihomomorphism (A j) (φ j) {0}) ∧
            ∀ z ∈ restrictRelation Gamma J,
              ∃ j, (z.1 0, z.1 1) ∈ A j ∧ z.2 = φ j (z.1 0, z.1 1)

/-- **The covering clause of `StackableStructureAt 2`, by variety pieces.** -/
theorem variety_structure_side {D : Nat} (hM : MilicevicDeepVarietyStructure D)
    {m : Real → Real → Nat} (hX : BihomExtraction m)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 →
        RelationProductProperty gamma Gamma →
        ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
          ∃ (K : Nat) (G : Fin K → Finset (ZMod N × ZMod N))
            (f : Fin K → ZMod N × ZMod N → ZMod N),
            (K : Real) ≤ m gamma (theta / 2) *
              Real.exp (milicevicBound D (theta / 2 / m gamma (theta / 2))) ∧
            (∀ k, IsVarietyPiece D (theta / 2 / m gamma (theta / 2)) (f k) (G k)) ∧
            restrictRelation Gamma J ⊆ section16FinsetUnion
              (fun k => partialGraph ((G k).image pairPoint) (fun x => f k (x 0, x 1))) := by
  have ht2 : 0 < theta / 2 := by positivity
  obtain ⟨hmpos, N0, hN0⟩ := hX gamma (theta / 2) hg hg1 ht2 (by linarith)
  refine ⟨N0, fun N _ _ hN Gamma hcard hprod => ?_⟩
  obtain ⟨J₀, hJ₀, φ, A, hA, hcover⟩ := hN0 N hN Gamma hcard hprod
  obtain ⟨K, piece, owner, U, hK, hU, hpieces, hcov⟩ :=
    greedy_variety_cover_family hM ht2 hmpos φ A hA
  refine ⟨J₀ \ U.image pairPoint, ?_, K, piece, fun k => φ (owner k), hK,
    fun k => (hpieces k).2, ?_⟩
  · have h1 : J₀.card ≤ (J₀ \ U.image pairPoint).card + (U.image pairPoint).card :=
      Finset.card_le_card_sdiff_add_card
    have h2 : (U.image pairPoint).card ≤ U.card := Finset.card_image_le
    have h3 : (J₀.card : Real) ≤ (J₀ \ U.image pairPoint).card + U.card := by
      exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
    linarith
  · intro z hz
    obtain ⟨hzΓ, hzJ⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzJ₀, hzU⟩ := Finset.mem_sdiff.mp hzJ
    obtain ⟨j, hjA, hjφ⟩ := hcover z (Finset.mem_filter.mpr ⟨hzΓ, hzJ₀⟩)
    have hnotU : (z.1 0, z.1 1) ∉ U := by
      intro hU'
      apply hzU
      rw [← pairPoint_coords z.1]
      exact Finset.mem_image_of_mem _ hU'
    obtain ⟨k, hk, hkp⟩ := hcov j _ hjA hnotU
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image.mpr
      ⟨z.1, ?_, ?_⟩⟩
    · rw [← pairPoint_coords z.1]
      exact Finset.mem_image_of_mem _ hkp
    · show (z.1, φ (owner k) (z.1 0, z.1 1)) = z
      rw [hk, ← hjφ]

end LeanProofs.GowersSzemeredi
