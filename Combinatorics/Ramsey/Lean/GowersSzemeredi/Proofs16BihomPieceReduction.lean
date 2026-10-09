import GowersSzemeredi.Proofs16VarietyStructureSide
import GowersSzemeredi.Proofs16GreedyRelations

/-! `BihomExtraction` from a single extraction step.

`BihomExtraction m` (research notes J.4, step 1) covers a whole product
relation by `m` Freiman-bihomomorphism graphs. By the corpus's peeling
argument (`section16_greedy_relation_decomposition`) and the monotonicity of
the product property (`RelationProductProperty.mono`), one step suffices.

`DenseBihomPiece mass` asks for one step: a sub-relation with the product
property and a projection of size `≥ θN²` contains the graph of a Freiman
bihomomorphism on a domain of size `≥ mass(γ,θ)·N²`. This is the content of
Milićević's §15 (arXiv:2601.01682), proof of Theorem 15.1, applied to a
single-valued selection of the relation. Such a selection inherits the
product property, hence large additive energy on every dense row and
column. Theorem 2.26 (Sanders's bounds) is applied row by row, giving a
dense horizontally Freiman piece. Repeating on columns keeps the horizontal
property, because domains only shrink. That step is not formalized here.

`bihomExtraction_of_densePiece`: `DenseBihomPiece mass` implies
`BihomExtraction m`, with `m γ θ = ⌈γ⁻² / mass γ θ⌉ + 1`. Shorter families
are padded with empty pieces. A quasi-polynomial `mass` gives a
quasi-polynomial `m`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- **One extraction step** (Milićević §15 applied to a selection). A
hypothesis; not asserted. -/
def DenseBihomPiece (mass : Real → Real → Real) : Prop :=
  ∀ gamma theta : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
    0 < mass gamma theta ∧
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Delta : Finset (Point N 2 × ZMod N),
        (Delta.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 →
        RelationProductProperty gamma Delta →
        theta * (N : Real) ^ 2 ≤ (relationProjection Delta).card →
        ∃ (φ : ZMod N × ZMod N → ZMod N) (A : Finset (ZMod N × ZMod N)),
          IsEBihomomorphism A φ {0} ∧ mass gamma theta * (N : Real) ^ 2 ≤ A.card ∧
          ∀ q ∈ A, (pairPoint q, φ q) ∈ Delta

/-- The family size produced from a one-step mass. -/
def bihomFamilySize (mass : Real → Real → Real) (gamma theta : Real) : Nat :=
  ⌈gamma ^ (-(2 : Int)) / mass gamma theta⌉₊ + 1

theorem pairPoint_injective {N : Nat} : Function.Injective (pairPoint (N := N)) := by
  intro p q h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [pairPoint, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact Prod.ext h0 h1

/-- The empty domain carries every map as a Freiman bihomomorphism. -/
theorem isEBihomomorphism_empty {N : Nat} (φ : ZMod N × ZMod N → ZMod N) (E : Set (ZMod N)) :
    IsEBihomomorphism ∅ φ E :=
  ⟨fun _ _ _ _ _ _ h => absurd h (Finset.notMem_empty _),
   fun _ _ _ _ _ _ h => absurd h (Finset.notMem_empty _)⟩

/-- **`BihomExtraction` from one extraction step.** -/
theorem bihomExtraction_of_densePiece {mass : Real → Real → Real} (h : DenseBihomPiece mass) :
    BihomExtraction (bihomFamilySize mass) := by
  intro gamma theta hg hg1 ht ht1
  obtain ⟨hmass, N0, hN0⟩ := h gamma theta hg hg1 ht ht1
  refine ⟨Nat.succ_pos _, N0, fun N _ _ hN Gamma hcard hprod => ?_⟩
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN2 : (0 : Real) < (N : Real) ^ 2 := by positivity
  -- the good pieces: graphs of Freiman bihomomorphisms
  let Good : Finset (Point N 2 × ZMod N) → Prop := fun D =>
    ∃ (φ : ZMod N × ZMod N → ZMod N) (A : Finset (ZMod N × ZMod N)),
      IsEBihomomorphism A φ {0} ∧ ∀ z ∈ D, (z.1 0, z.1 1) ∈ A ∧ z.2 = φ (z.1 0, z.1 1)
  have hextract : ∀ Delta ⊆ Gamma,
      theta * (N : Real) ^ 2 ≤ (relationProjection Delta).card →
      ∃ D ⊆ Delta, mass gamma theta * (N : Real) ^ 2 ≤ D.card ∧ Good D := by
    intro Delta hsub hproj
    have hDcard : (Delta.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 :=
      le_trans (by exact_mod_cast Finset.card_le_card hsub) hcard
    obtain ⟨φ, A, hA, hAmass, hAin⟩ :=
      hN0 N hN Delta hDcard (hprod.mono hsub) hproj
    refine ⟨A.image fun q => (pairPoint q, φ q), ?_, ?_, φ, A, hA, ?_⟩
    · intro z hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      exact hAin q hq
    · rw [Finset.card_image_of_injective]
      · exact hAmass
      · intro p q hpq
        exact pairPoint_injective (congrArg Prod.fst hpq)
    · intro z hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      have hq' : ((pairPoint q) 0, (pairPoint q) 1) = q := rfl
      simp only [hq']
      exact ⟨hq, trivial⟩
  obtain ⟨q, G, J, hG, hqmass, hJ, hcov⟩ :=
    section16_greedy_relation_decomposition Good theta (mass gamma theta * (N : Real) ^ 2)
      (mul_pos hmass hN2) Gamma hextract
  -- the number of pieces fits in the family size
  have hqm : q < bihomFamilySize mass gamma theta := by
    have hqR : (q : Real) ≤ gamma ^ (-(2 : Int)) / mass gamma theta := by
      rw [le_div_iff₀ hmass]
      have h1 : (q : Real) * (mass gamma theta * (N : Real) ^ 2) ≤
          gamma ^ (-(2 : Int)) * (N : Real) ^ 2 := hqmass.trans hcard
      have h2 : (q : Real) * mass gamma theta * (N : Real) ^ 2 ≤
          gamma ^ (-(2 : Int)) * (N : Real) ^ 2 := by linarith [h1, mul_assoc (q : Real) (mass gamma theta) ((N : Real) ^ 2)]
      exact le_of_mul_le_mul_right h2 hN2
    have := Nat.le_ceil (gamma ^ (-(2 : Int)) / mass gamma theta)
    have hq_le : q ≤ ⌈gamma ^ (-(2 : Int)) / mass gamma theta⌉₊ := by
      exact_mod_cast hqR.trans this
    unfold bihomFamilySize
    omega
  choose φs As hAs hcovs using fun i => (hG i).2
  refine ⟨J, hJ, fun j => if hj : j.val < q then φs ⟨j.val, hj⟩ else fun _ => 0,
    fun j => if hj : j.val < q then As ⟨j.val, hj⟩ else ∅, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < q
    · simp only [dif_pos hj]
      exact hAs _
    · simp only [dif_neg hj]
      exact isEBihomomorphism_empty _ _
  · intro z hz
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (hcov hz)
    refine ⟨⟨i.val, lt_trans i.isLt hqm⟩, ?_⟩
    have hi' : (⟨i.val, lt_trans i.isLt hqm⟩ : Fin (bihomFamilySize mass gamma theta)).val < q :=
      i.isLt
    simp only [dif_pos hi']
    exact hcovs i z hi

end LeanProofs.GowersSzemeredi
