import GowersSzemeredi.Proofs16OriginalEightEncoding
import GowersSzemeredi.Proofs16DifferenceAnchorCounts

/-! Varying a valid anchor and two original four-term representation
families produces distinct original eight-tuples. The negative block
encodes its anchor, so joining introduces no multiplicity loss. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def sourceEightFamilies {N : Nat} (C : Finset (ZMod N))
    (A B : ZMod N → Finset (FourRepresentationTuple N)) (a : ZMod N) :
    Finset (Sigma fun _ : ZMod N => FourRepresentationTuple N × FourRepresentationTuple N) :=
  (progressionBridgeSet C a).sigma fun u => A (u+a) ×ˢ B u

def sourceJoinedEightTuples {N : Nat} (C : Finset (ZMod N))
    (A B : ZMod N → Finset (FourRepresentationTuple N)) (a : ZMod N) : Finset (ColumnAnchorTuple N 7) :=
  (sourceEightFamilies C A B a).image fun p => joinSourceRepresentations p.2.1 p.2.2

/-- The negative representation determines the varied anchor, so every
original joined eight-tuple is counted once. -/
theorem source_eight_joined_card {N : Nat} (U C : Finset (ZMod N))
    (A B : ZMod N → Finset (FourRepresentationTuple N)) (a : ZMod N)
    (hB : ∀ u ∈ C, ∀ p ∈ B u, p ∈ fourDifferenceRepresentations U u) :
    (sourceJoinedEightTuples C A B a).card = (sourceEightFamilies C A B a).card := by
  apply Finset.card_image_of_injOn
  intro p hp q hq he
  have hrows := joinSourceRepresentations_injective he
  obtain ⟨hpAnchor,hpRows⟩ := Finset.mem_sigma.mp hp
  obtain ⟨hqAnchor,hqRows⟩ := Finset.mem_sigma.mp hq
  have hpB := hB _ (Finset.mem_filter.mp hpAnchor).1 _ (Finset.mem_product.mp hpRows).2
  have hqB := hB _ (Finset.mem_filter.mp hqAnchor).1 _ (Finset.mem_product.mp hqRows).2
  have hpIndex : representationTupleEval id p.2.2 = p.1 := (Finset.mem_filter.mp hpB).2
  have hqIndex : representationTupleEval id q.2.2 = q.1 := (Finset.mem_filter.mp hqB).2
  have hu : p.1 = q.1 := hpIndex.symm.trans
    ((congrArg (fun r : FourRepresentationTuple N × FourRepresentationTuple N => representationTupleEval id r.2) hrows).trans hqIndex)
  cases p with | mk p1 p2 =>
    cases q with | mk q1 q2 =>
      dsimp only at hu hrows
      subst q1
      exact Sigma.ext rfl (heq_of_eq hrows)

theorem source_eight_joined_mem_fibre {N : Nat} [NeZero N] (U C : Finset (ZMod N))
    (A B : ZMod N → Finset (FourRepresentationTuple N)) (a : ZMod N)
    (hA : ∀ x ∈ C, ∀ p ∈ A x, p ∈ fourDifferenceRepresentations U x)
    (hB : ∀ x ∈ C, ∀ p ∈ B x, p ∈ fourDifferenceRepresentations U x) :
    sourceJoinedEightTuples C A B a ⊆ columnAnchorFibre U 7 a := by
  intro t ht
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hpAnchor,hpRows⟩ := Finset.mem_sigma.mp hp
  obtain ⟨hu,hua⟩ := Finset.mem_filter.mp hpAnchor
  obtain ⟨hpA,hpB⟩ := Finset.mem_product.mp hpRows
  exact join_source_representations_mem_fibre U (hA _ hua _ hpA) (hB _ hu _ hpB)

/-- Linear anchor mass and two cubic alternative masses give the full
`N^7` family of distinct original tuples, with its exact density factor. -/
theorem source_eight_joined_mass {N : Nat} [NeZero N] (U C : Finset (ZMod N))
    (A B : ZMod N → Finset (FourRepresentationTuple N)) (a : ZMod N)
    {lambda kappa : Real} (hk : 0 ≤ kappa)
    (hanchors : lambda*N ≤ ((progressionBridgeSet C a).card : Real))
    (hA : ∀ x ∈ C, kappa*(N : Real)^3/2 ≤ ((A x).card : Real))
    (hB : ∀ x ∈ C, kappa*(N : Real)^3/2 ≤ ((B x).card : Real))
    (hBrep : ∀ x ∈ C, ∀ p ∈ B x, p ∈ fourDifferenceRepresentations U x) :
    lambda*kappa^2/4*(N : Real)^7 ≤ (sourceJoinedEightTuples C A B a).card := by
  rw [source_eight_joined_card U C A B a hBrep]
  have hfamily : ((progressionBridgeSet C a).card : Real)*(kappa*(N : Real)^3/2)^2 ≤
      (sourceEightFamilies C A B a).card := by
    calc _ = ∑ _u ∈ progressionBridgeSet C a, (kappa*(N : Real)^3/2)^2 := by simp
      _ ≤ ∑ u ∈ progressionBridgeSet C a, ((A (u+a) ×ˢ B u).card : Real) := by
        apply Finset.sum_le_sum
        intro u hu
        obtain ⟨huC,huaC⟩ := Finset.mem_filter.mp hu
        have h := mul_le_mul (hA _ huaC) (hB _ huC) (by positivity) (Nat.cast_nonneg (A (u+a)).card)
        simpa only [Finset.card_product,Nat.cast_mul,pow_two] using h
      _ = _ := by exact_mod_cast (Finset.card_sigma (progressionBridgeSet C a) (fun u => A (u+a) ×ˢ B u)).symm
  have hscaled := (mul_le_mul_of_nonneg_right hanchors (sq_nonneg (kappa*(N : Real)^3/2))).trans hfamily
  have heq : lambda*N*(kappa*(N : Real)^3/2)^2 = lambda*kappa^2/4*(N : Real)^7 := by ring
  simpa only [heq] using hscaled

end LeanProofs.GowersSzemeredi
