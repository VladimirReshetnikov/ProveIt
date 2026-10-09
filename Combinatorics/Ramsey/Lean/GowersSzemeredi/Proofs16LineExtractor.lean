import GowersSzemeredi.Proofs16DenseBihomPiece
import GowersSzemeredi.Proofs16BaseCaseRestriction

/-! An unconditional, polynomial line extractor from Gowers's base case.

Gowers's product property is stronger than additive energy: it holds on every
sub-domain, for every weight, and simultaneously for `p` copies. The corpus's
dimension-one step `BaseCase.section16_product_restriction` (Lemma 16.3) turns
it into an order-eight Freiman restriction on `≥ α(γ,β)N` points, with the
polynomial `α = lemma163Alpha γ β = 2^(−2000)(γβ)^10000`.

* `relationProductProperty_of_line`: a line map with `LineProductProperty`
  has a graph relation (in `Point N 1`) with the one-dimensional product
  property. All `p` coordinate restrictions coincide with the map.
* `lineExtractor_polynomial`: `LineExtractor (fun γ β => lemma163Alpha γ β)`.
  Order-eight Freiman homomorphisms respect quadruples
  (`IsAddFreimanHom.mono`, `IsAddFreimanHom.add_eq_add`).
* `densePiece_polynomial`, `structure_side_of_milicevic`: the covering half of
  `StackableStructureAt 2` now rests on `MilicevicDeepVarietyStructure`
  **alone**. Theorem 2.26 is no longer needed, and the extraction mass is
  polynomial in `γθ`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical
open BaseCase

/-- The graph of a line map, as a one-dimensional relation. -/
def lineRelation {N : Nat} [NeZero N] (R : Finset (ZMod N)) (g : ZMod N → ZMod N) :
    Finset (Point N 1 × ZMod N) :=
  R.image fun a => ((pointOneEquiv N).symm a, g a)

theorem mem_lineRelation {N : Nat} [NeZero N] {R : Finset (ZMod N)} {g : ZMod N → ZMod N}
    {x : Point N 1} {v : ZMod N} :
    (x, v) ∈ lineRelation R g ↔ x 0 ∈ R ∧ v = g (x 0) := by
  unfold lineRelation
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨ha, rfl⟩
  · rintro ⟨hx, rfl⟩
    refine ⟨x 0, hx, ?_⟩
    simp only [Prod.mk.injEq, and_true]
    exact (pointOneEquiv N).left_inv x

/-- Energies only see the maps on the summation set. -/
theorem weightedSimultaneousAdditiveEnergy_congr {N p : Nat} [NeZero N] (E : Finset (ZMod N))
    (w : ZMod N → Real) (ψ ψ' : Fin p → ZMod N → ZMod N)
    (h : ∀ i, ∀ x ∈ E, ψ i x = ψ' i x) :
    weightedSimultaneousAdditiveEnergy E w ψ = weightedSimultaneousAdditiveEnergy E w ψ' := by
  unfold weightedSimultaneousAdditiveEnergy
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : ∀ t, q t ∈ E
  · have : ∀ i, (fun t => ψ i (q t)) = fun t => ψ' i (q t) := fun i => funext fun t => h i _ (hq t)
    simp only [this]
  · simp [hq]

/-- **The line graph has the one-dimensional product property.** -/
theorem relationProductProperty_of_line {N : Nat} [NeZero N] {γ : Real} {R : Finset (ZMod N)}
    {g : ZMod N → ZMod N} (h : LineProductProperty γ R g) :
    RelationProductProperty γ (lineRelation R g) := by
  intro B ψ hgraph p j y E w hw hE
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  -- points of `E` lie in `R`, where `ψ` is `g`
  have hpt : ∀ i, ∀ x ∈ E, x ∈ R ∧ coordinateRestriction ψ (y i) 0 x = g x := by
    intro i x hx
    have hB := hE i x hx
    have hg := mem_lineRelation.mp (hgraph _ hB)
    have hx0 : (replaceCoordinate (y i) 0 x) 0 = x := by
      simp [replaceCoordinate]
    rw [hx0] at hg
    exact ⟨hg.1, hg.2⟩
  have hER : 0 < p → E ⊆ R := fun hp x hx => (hpt ⟨0, hp⟩ x hx).1
  rw [weightedSimultaneousAdditiveEnergy_congr E w _ (fun _ : Fin p => g)
    fun i x hx => (hpt i x hx).2]
  exact h p E w hER hw

/-- **The polynomial line extractor**, from Gowers's Lemma 16.3 step. -/
theorem lineExtractor_polynomial :
    LineExtractor (fun γ β => lemma163Alpha γ β) := by
  refine ⟨fun γ β hg _ hb => lemma163Alpha_pos hg hb, ?_⟩
  intro N _ _ γ hg hg1 R g β hb hR hLP
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hβ1 : β ≤ 1 := by
    have hRN : (R.card : Real) ≤ N := by
      have : R.card ≤ N := by
        calc R.card ≤ (Finset.univ : Finset (ZMod N)).card := Finset.card_le_univ _
          _ = N := ZMod.card N
      exact_mod_cast this
    have : β * N ≤ 1 * N := by linarith
    exact le_of_mul_le_mul_right this hNR
  let B : Finset (Point N 1) := R.map (pointOneEquiv N).symm.toEmbedding
  have hBcard : (B.card : Real) = R.card := by simp [B]
  obtain ⟨C, hCsize, hCgraph, hCfreiman⟩ :=
    section16_product_restriction γ β hg hg1 hb hβ1 (Fact.out : N.Prime) (lineRelation R g)
      (relationProductProperty_of_line hLP) B (fun x => g (x 0)) (by rw [hBcard]; exact hR)
      (by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
        exact mem_lineRelation.mpr ⟨ha, rfl⟩)
  -- the Freiman piece, as a subset of the line
  have hmem : ∀ z ∈ pointOneDomain C.1, z ∈ R ∧ pointOneMap C.2 z = g z := by
    intro z hz
    have hz' := (mem_pointOneDomain C.1 z).mp hz
    have hg := mem_lineRelation.mp (hCgraph _ hz')
    exact ⟨hg.1, hg.2⟩
  refine ⟨pointOneDomain C.1, fun z hz => (hmem z hz).1, ?_, ?_⟩
  · rw [pointOneDomain_card]
    exact hCsize
  · intro z₁ z₂ z₃ z₄ h1 h2 h3 h4 hsum
    have h2F := (hCfreiman.mono (by norm_num : 2 ≤ 8)).add_eq_add
      (by exact_mod_cast h1) (by exact_mod_cast h2) (by exact_mod_cast h3) (by exact_mod_cast h4) hsum
    rw [(hmem z₁ h1).2, (hmem z₂ h2).2, (hmem z₃ h3).2, (hmem z₄ h4).2] at h2F
    exact h2F

/-- **The single extraction step, unconditionally**, with a polynomial mass. -/
theorem densePiece_polynomial :
    DenseBihomPiece (densePieceMassGen fun γ β => lemma163Alpha γ β) :=
  densePiece_of_lineExtractor lineExtractor_polynomial

/-- **The covering half of `StackableStructureAt 2` from Milićević's
structure theorem alone.** -/
theorem structure_side_of_milicevic {D : Nat} (hM : MilicevicDeepVarietyStructure D)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 2 × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 →
        RelationProductProperty gamma Gamma →
        ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
          ∃ (K : Nat) (G : Fin K → Finset (ZMod N × ZMod N))
            (f : Fin K → ZMod N × ZMod N → ZMod N),
            (K : Real) ≤
              bihomFamilySize (densePieceMassGen fun γ β => lemma163Alpha γ β) gamma (theta / 2) *
              Real.exp (milicevicBound D (theta / 2 /
                bihomFamilySize (densePieceMassGen fun γ β => lemma163Alpha γ β) gamma (theta / 2))) ∧
            (∀ k, IsVarietyPiece D (theta / 2 /
              bihomFamilySize (densePieceMassGen fun γ β => lemma163Alpha γ β) gamma (theta / 2))
              (f k) (G k)) ∧
            restrictRelation Gamma J ⊆ section16FinsetUnion
              (fun k => partialGraph ((G k).image pairPoint) (fun x => f k (x 0, x 1))) :=
  variety_structure_side hM (bihomExtraction_of_densePiece densePiece_polynomial)
    gamma theta hg hg1 ht ht1

end LeanProofs.GowersSzemeredi
