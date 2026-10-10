import GowersSzemeredi.Proofs16AlternativeChoiceCounts
import GowersSzemeredi.Proofs16RepresentativeChoiceSelection
import GowersSzemeredi.Proofs16FourRepresentationUpperCounts

/-! Joint failure events for selected 16-tuples and for heavy alternative
representation failures in any of the four rows. Replacement counting
charges all events to the same original bad tuple family. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def sourceAlternativeBadRepresentations {N : Nat}
    (U : Finset (ZMod N)) (q : Fin 4 → ZMod N) (b : Fin 4 → FourRepresentationTuple N)
    (Bad : Finset (ColumnAnchorTuple N 15)) (i : Fin 4) : Finset (FourRepresentationTuple N) :=
  (fourDifferenceRepresentations U (q i)).filter fun p => flattenFourRepresentations (Function.update b i p) ∈ Bad

def jointBadRepresentationBlocks {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (q : Fin 4 → ZMod N) (Bad : Finset (ColumnAnchorTuple N 15))
    (kappa : Real) : Finset (Fin 4 → FourRepresentationTuple N) :=
  representedBadFourBlocks U q Bad ∪ Finset.univ.biUnion fun i : Fin 4 =>
    heavyAlternativeConfigurations (fun j => fourDifferenceRepresentations U (q j))
      (representedBadFourBlocks U q Bad) i (kappa*(N : Real)^3/2)

/-- For valid selected rows, the replacement event is exactly the original
bad-tuple event; replacing a row preserves its represented index. -/
theorem source_alternative_bad_eq_coordinate {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (q : Fin 4 → ZMod N) (b : Fin 4 → FourRepresentationTuple N)
    (Bad : Finset (ColumnAnchorTuple N 15)) (i : Fin 4)
    (hb : ∀ j, b j ∈ fourDifferenceRepresentations U (q j)) :
    sourceAlternativeBadRepresentations U q b Bad i =
      alternativeCoordinateChoices (fun j => fourDifferenceRepresentations U (q j))
        (representedBadFourBlocks U q Bad) i b := by
  classical
  ext p
  simp only [sourceAlternativeBadRepresentations,alternativeCoordinateChoices,representedBadFourBlocks,Finset.mem_filter]
  constructor
  · rintro ⟨hp,hflat⟩
    refine ⟨hp,Fintype.mem_piFinset.mpr ?_,hflat⟩
    intro j
    by_cases hj : j = i
    · subst j
      simpa using hp
    · simpa only [Function.update_of_ne hj] using hb j
  · rintro ⟨hp,hvalid,hflat⟩
    exact ⟨hp,hflat⟩

theorem joint_bad_representation_blocks_valid {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (q : Fin 4 → ZMod N) (Bad : Finset (ColumnAnchorTuple N 15))
    (kappa : Real) {b : Fin 4 → FourRepresentationTuple N} (hb : b ∈ jointBadRepresentationBlocks U q Bad kappa) :
    ∀ j, b j ∈ fourDifferenceRepresentations U (q j) := by
  rcases Finset.mem_union.mp hb with hb | hb
  · exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp hb).1
  · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hb
    exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp hi).1

/-- The four heavy replacement events cost at most `8/kappa` times the
original row-block failures. The unused old row has at most `N^3` choices. -/
theorem joint_bad_representation_blocks_card {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (q : Fin 4 → ZMod N) (Bad : Finset (ColumnAnchorTuple N 15))
    {kappa : Real} (hk : 0 < kappa) :
    ((jointBadRepresentationBlocks U q Bad kappa).card : Real) ≤
      (1+8/kappa)*((representedBadFourBlocks U q Bad).card : Real) := by
  classical
  let F := fun j => fourDifferenceRepresentations U (q j)
  let B := representedBadFourBlocks U q Bad
  let H := fun i : Fin 4 => heavyAlternativeConfigurations F B i (kappa*(N : Real)^3/2)
  have hB : ∀ b ∈ B, ∀ j, b j ∈ F j :=
    fun b hb => Fintype.mem_piFinset.mp (Finset.mem_filter.mp hb).1
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hH : ∀ i, ((H i).card : Real) ≤ (2/kappa)*(B.card : Real) := by
    intro i
    have hscaled := heavy_alternative_configurations_scaled F B i (kappa*(N : Real)^3/2) hB
    have hF : ((F i).card : Real) ≤ (N : Real)^3 := by exact_mod_cast four_difference_representations_card_le U (q i)
    have hupper := hscaled.trans (mul_le_mul_of_nonneg_right hF (Nat.cast_nonneg _))
    have hdiv : ((H i).card : Real) ≤ ((N : Real)^3*B.card)/(kappa*(N : Real)^3/2) := by
      apply (le_div_iff₀ (by positivity)).mpr
      simpa only [mul_comm] using hupper
    have heq : ((N : Real)^3*B.card)/(kappa*(N : Real)^3/2) = (2/kappa)*B.card := by field_simp
    simpa only [heq] using hdiv
  have hcount : ((jointBadRepresentationBlocks U q Bad kappa).card : Real) ≤
      (B.card : Real)+∑ i : Fin 4, ((H i).card : Real) := by
    have hnat := (Finset.card_union_le B (Finset.univ.biUnion H)).trans
      (Nat.add_le_add_left (Finset.card_biUnion_le) B.card)
    exact_mod_cast hnat
  calc ((jointBadRepresentationBlocks U q Bad kappa).card : Real) ≤ (B.card : Real)+∑ i : Fin 4, ((H i).card : Real) := hcount
    _ ≤ (B.card : Real)+∑ _i : Fin 4, (2/kappa)*(B.card : Real) :=
      add_le_add (le_refl _) (Finset.sum_le_sum fun i _ => hH i)
    _ = _ := by simp; ring

/-- Summing joint events still charges the original bad 16-tuple family. -/
theorem joint_bad_representation_blocks_total {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (Q : Finset (Fin 4 → ZMod N)) (Bad : Finset (ColumnAnchorTuple N 15))
    {kappa : Real} (hk : 0 < kappa) :
    (∑ q ∈ Q, ((jointBadRepresentationBlocks U q Bad kappa).card : Real)) ≤ (1+8/kappa)*(Bad.card : Real) := by
  have htotal : (∑ q ∈ Q, ((representedBadFourBlocks U q Bad).card : Real)) ≤ (Bad.card : Real) := by
    exact_mod_cast represented_bad_four_blocks_total_le U Q Bad
  calc (∑ q ∈ Q, ((jointBadRepresentationBlocks U q Bad kappa).card : Real)) ≤
      ∑ q ∈ Q, (1+8/kappa)*((representedBadFourBlocks U q Bad).card : Real) :=
        Finset.sum_le_sum fun q _ => joint_bad_representation_blocks_card U q Bad hk
    _ = (1+8/kappa)*(∑ q ∈ Q, ((representedBadFourBlocks U q Bad).card : Real)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal (by positivity)

/-- Outside the joint event, the selected tuple is good and at least half
the uniform representation mass survives each possible row replacement. -/
theorem good_joint_representation_block {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (q : Fin 4 → ZMod N) (b : Fin 4 → FourRepresentationTuple N)
    (Bad : Finset (ColumnAnchorTuple N 15)) {kappa : Real}
    (hb : ∀ j, b j ∈ fourDifferenceRepresentations U (q j))
    (hrep : ∀ i, kappa*(N : Real)^3 ≤ (fourDifferenceRepresentations U (q i)).card)
    (hgood : b ∉ jointBadRepresentationBlocks U q Bad kappa) :
    flattenFourRepresentations b ∉ Bad ∧
      ∀ i, kappa*(N : Real)^3/2 ≤ (((fourDifferenceRepresentations U (q i)).filter
        fun p => flattenFourRepresentations (Function.update b i p) ∉ Bad).card : Real) := by
  classical
  have hnotB : b ∉ representedBadFourBlocks U q Bad := fun h =>
    hgood (Finset.mem_union_left _ h)
  refine ⟨?_,?_⟩
  · intro hflat
    exact hnotB (Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hb,hflat⟩)
  · intro i
    have hbadle : ((sourceAlternativeBadRepresentations U q b Bad i).card : Real) ≤ kappa*(N : Real)^3/2 := by
      apply not_lt.mp
      intro hheavy
      apply hgood
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hb, ?_⟩⟩
      simpa only [source_alternative_bad_eq_coordinate U q b Bad i hb] using hheavy
    have hsplit : ((sourceAlternativeBadRepresentations U q b Bad i).card : Real)+
        (((fourDifferenceRepresentations U (q i)).filter fun p => flattenFourRepresentations (Function.update b i p) ∉ Bad).card : Real) =
          (fourDifferenceRepresentations U (q i)).card := by
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := fourDifferenceRepresentations U (q i))
        (fun p => flattenFourRepresentations (Function.update b i p) ∈ Bad)
    have hmass := hrep i
    linarith

end LeanProofs.GowersSzemeredi
