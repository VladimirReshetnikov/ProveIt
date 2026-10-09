import GowersSzemeredi.Proofs16SelectionAveraging

/-! Selection averaging over indexed requirements. Keeping their indices
avoids any loss from identifying requirements with the same support. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A requirement prescribing at most `m` values is met with a loss of
at most `K^m`, counting repeated requirements separately. -/
theorem exists_good_indexed_selection {X Y : Type} {I : Type*} [Fintype X]
    (U : X → Finset Y) (hne : ∀ x, (U x).Nonempty) {K m : Nat}
    (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K)
    (T : Finset I) (req : I → Finset X × (X → Y))
    (hreq : ∀ i ∈ T, (req i).1.card ≤ m ∧ ∀ x ∈ (req i).1, (req i).2 x ∈ U x) :
    ∃ f ∈ Fintype.piFinset U,
      T.card ≤ K^m * (T.filter fun i => Meets f (req i)).card := by
  let F := Fintype.piFinset U
  have hFpos : 0 < F.card := by
    rw [Fintype.card_piFinset]
    exact Finset.prod_pos fun x _ => (hne x).card_pos
  have hlocal : ∀ i ∈ T, F.card ≤ K^m * (F.filter fun f => Meets f (req i)).card := by
    intro i hi
    exact (card_all_le_mul_meeting U hK (req i) (hreq i hi).2).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hK1 (hreq i hi).1))
  have hdouble : ∑ f ∈ F, (T.filter fun i => Meets f (req i)).card =
      ∑ i ∈ T, (F.filter fun f => Meets f (req i)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  by_contra hcon
  push Not at hcon
  have hlt : K^m * ∑ f ∈ F, (T.filter fun i => Meets f (req i)).card < F.card*T.card := by
    rw [Finset.mul_sum]
    calc ∑ f ∈ F, K^m * (T.filter fun i => Meets f (req i)).card
        < ∑ _f ∈ F, T.card := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hFpos)
          fun f hf => hcon f hf
      _ = _ := by rw [Finset.sum_const,smul_eq_mul]
  have hge : F.card*T.card ≤ K^m * ∑ i ∈ T, (F.filter fun f => Meets f (req i)).card := by
    rw [Finset.mul_sum]
    calc F.card*T.card = ∑ _i ∈ T, F.card := by rw [Finset.sum_const,smul_eq_mul,mul_comm]
      _ ≤ _ := Finset.sum_le_sum hlocal
  rw [hdouble] at hlt
  omega

/-- Independent colors allow repeated positions: each coordinate fixes
one value of its own function. No distinct-position hypothesis is needed. -/
theorem exists_good_colored_selection {X Y : Type} {I : Type*} [Fintype X] {m K : Nat}
    (U : X → Finset Y) (hne : ∀ x, (U x).Nonempty)
    (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K)
    (T : Finset I) (pos : I → Fin m → X) (val : I → Fin m → Y)
    (hval : ∀ t ∈ T, ∀ i, val t i ∈ U (pos t i)) :
    ∃ f : Fin m → X → Y, (∀ i x, f i x ∈ U x) ∧
      T.card ≤ K^m * (T.filter fun t => ∀ i, f i (pos t i) = val t i).card := by
  let req (t : I) : Finset (Fin m × X) × ((Fin m × X) → Y) :=
    (Finset.univ.image (fun i => (i,pos t i)),fun p => val t p.1)
  have hr : ∀ t ∈ T, (req t).1.card ≤ m ∧
      ∀ x ∈ (req t).1, (req t).2 x ∈ U x.2 := by
    intro t ht
    refine ⟨?_,?_⟩
    · exact Finset.card_image_le.trans (by simp)
    · intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact hval t ht i
  obtain ⟨f,hf,hcount⟩ := exists_good_indexed_selection (fun p : Fin m × X => U p.2)
    (fun p => hne p.2) hK1 (fun p => hK p.2) T req hr
  have hf' : ∀ p : Fin m × X, f p ∈ U p.2 := by
    simpa only [Fintype.mem_piFinset] using hf
  refine ⟨fun i x => f (i,x),fun i x => hf' (i,x),?_⟩
  have heq : (T.filter fun t => Meets f (req t)) =
      T.filter fun t => ∀ i, f (i,pos t i) = val t i := by
    ext t
    simp only [Finset.mem_filter,Meets,req,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨ht,h⟩
      exact ⟨ht,fun i => h (i,pos t i) ⟨i,rfl⟩⟩
    · rintro ⟨ht,h⟩
      exact ⟨ht,fun _ ⟨i,hi⟩ => hi ▸ h i⟩
  rwa [heq] at hcount

end LeanProofs.GowersSzemeredi
