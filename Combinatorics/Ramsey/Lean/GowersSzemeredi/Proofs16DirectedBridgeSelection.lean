import GowersSzemeredi.Proofs16DirectedExceptionCore

/-! Select a common bridge avoiding four directed pair exceptions. Each
shift is injective, so it costs only the original exceptional row degree. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exceptional_row_pullback_card_le {V : Type*} [DecidableEq V]
    (E : Finset (V × V)) (B : Finset V) (a : V) (f : V → V) (hf : Function.Injective f) :
    (B.filter fun y => (a,f y) ∈ E).card ≤ exceptionalPairOutDegree E a := by
  apply Finset.card_le_card_of_injOn (fun y => (a,f y))
  · intro y hy
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).2,rfl⟩
  · intro y _ z _ he
    exact hf (congrArg Prod.snd he)

theorem two_predicate_failure_card_le {V : Type*} [DecidableEq V]
    (B : Finset V) (P Q : V → Prop) [DecidablePred P] [DecidablePred Q] :
    (B.filter fun y => ¬(P y ∧ Q y)).card ≤
      (B.filter fun y => ¬P y).card+(B.filter fun y => ¬Q y).card := by
  apply (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_union] at hy ⊢
  tauto

/-- Four sparse rows leave a common candidate, including two translated
rows. The source and target sets may overlap arbitrarily. -/
theorem exists_directed_bridge_four_good_pairs {G : Type*} [AddCommGroup G] [DecidableEq G]
    (E : Finset (G × G)) (B : Finset G) (a b c e shift : G) {t : Nat}
    (ha : exceptionalPairOutDegree E a ≤ t) (hb : exceptionalPairOutDegree E b ≤ t)
    (hc : exceptionalPairOutDegree E c ≤ t) (he : exceptionalPairOutDegree E e ≤ t)
    (hB : 4*t < B.card) :
    ∃ y ∈ B, (a,y) ∉ E ∧ (b,y) ∉ E ∧ (c,y+shift) ∉ E ∧ (e,y+shift) ∉ E := by
  let P := fun y => (a,y) ∉ E ∧ (b,y) ∉ E
  let R := fun y => (c,y+shift) ∉ E ∧ (e,y+shift) ∉ E
  have hfirst : (B.filter fun y => ¬P y).card ≤ 2*t := by
    have h := two_predicate_failure_card_le B (fun y => (a,y) ∉ E) (fun y => (b,y) ∉ E)
    have ha' := (exceptional_row_pullback_card_le E B a id (fun _ _ h => h)).trans ha
    have hb' := (exceptional_row_pullback_card_le E B b id (fun _ _ h => h)).trans hb
    simp only [not_not, id_eq] at h ha' hb'
    dsimp only [P]
    omega
  have hsecond : (B.filter fun y => ¬R y).card ≤ 2*t := by
    have h := two_predicate_failure_card_le B (fun y => (c,y+shift) ∉ E) (fun y => (e,y+shift) ∉ E)
    have hc' := (exceptional_row_pullback_card_le E B c (fun y => y+shift) (fun _ _ h => add_right_cancel h)).trans hc
    have he' := (exceptional_row_pullback_card_le E B e (fun y => y+shift) (fun _ _ h => add_right_cancel h)).trans he
    simp only [not_not] at h
    dsimp only [R]
    omega
  obtain ⟨y, hy, hP, hR⟩ := exists_bridge_avoiding_two_failures B P R (by omega)
  exact ⟨y,hy,hP.1,hP.2,hR.1,hR.2⟩

end LeanProofs.GowersSzemeredi
