import GowersSzemeredi.Proofs16HigherAnchorAveraging

/-! Repeated shifts occupy four linear collision families. Each has at
most ten free parameters, so their total cost is at most `4*N^10`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem higher_fixed_first_card_le {N : Nat} [NeZero N]
    (S : Finset (HigherArrangementParameter N)) (f : (Fin 9 → ZMod N) → ZMod N)
    (hS : ∀ p ∈ S, p.1.1 = f p.1.2) : S.card ≤ N^10 := by
  have hc : S.card ≤ (Finset.univ : Finset ((Fin 9 → ZMod N) × ZMod N)).card := by
    apply Finset.card_le_card_of_injOn (fun p : HigherArrangementParameter N => (p.1.2,p.2))
      (fun _ _ => Finset.mem_univ _)
    intro p hp q hq he
    have he' : p.1.2 = q.1.2 ∧ p.2 = q.2 := Prod.mk.inj he
    refine Prod.ext (Prod.ext ?_ he'.1) he'.2
    rw [hS p hp,hS q hq,he'.1]
  simpa only [Finset.card_univ,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ZMod.card,
    show N^9*N = N^10 by ring] using hc

theorem higher_equal_inner_shifts_card_le {N : Nat} [NeZero N]
    (S : Finset (HigherArrangementParameter N)) (hS : ∀ p ∈ S, p.1.2 0 = p.1.2 1) :
    S.card ≤ N^10 := by
  have hc : S.card ≤ (Finset.univ : Finset (ZMod N × ((Fin 8 → ZMod N) × ZMod N))).card := by
    apply Finset.card_le_card_of_injOn (fun p : HigherArrangementParameter N => (p.1.1,(Fin.tail p.1.2,p.2)))
      (fun _ _ => Finset.mem_univ _)
    intro p hp q hq he
    have ha := congrArg (fun t : ZMod N × ((Fin 8 → ZMod N) × ZMod N) => t.1) he
    have ht := congrArg (fun t : ZMod N × ((Fin 8 → ZMod N) × ZMod N) => t.2.1) he
    have hu := congrArg (fun t : ZMod N × ((Fin 8 → ZMod N) × ZMod N) => t.2.2) he
    refine Prod.ext (Prod.ext ha ?_) hu
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact (hS p hp).trans ((congrFun ht 0).trans (hS q hq).symm)
    · exact congrFun ht k
  simpa only [Finset.card_univ,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ZMod.card,
    show N*(N^8*N) = N^10 by ring] using hc

theorem higher_shift_collision_cases {N : Nat} (p : HigherArrangementParameter N)
    (h : ¬ Function.Injective (higherArrangementShifts p)) :
    p.1.1 = p.1.2 0 ∨ p.1.1 = p.1.2 1 ∨ p.1.2 0 = p.1.2 1 ∨
      p.1.1 = p.1.2 1+p.1.2 1-p.1.2 0 := by
  by_contra hn
  have h1 : p.1.1 ≠ p.1.2 0 := fun he => hn (Or.inl he)
  have h2 : p.1.1 ≠ p.1.2 1 := fun he => hn (Or.inr (Or.inl he))
  have h3 : p.1.2 0 ≠ p.1.2 1 := fun he => hn (Or.inr (Or.inr (Or.inl he)))
  have h4 : p.1.1 ≠ p.1.2 1+p.1.2 1-p.1.2 0 := fun he => hn (Or.inr (Or.inr (Or.inr he)))
  apply h
  intro i j hij
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals dsimp [higherArrangementShifts] at hij
  all_goals exfalso
  all_goals first | exact h1 (by linear_combination hij) | exact h1 (by linear_combination -hij) |
    exact h2 (by linear_combination hij) | exact h2 (by linear_combination -hij) |
    exact h3 (by linear_combination hij) | exact h3 (by linear_combination -hij) |
    exact h4 (by linear_combination hij) | exact h4 (by linear_combination -hij)

theorem higher_repeated_shifts_card_le {N : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N)) :
    (H.filter fun p => ¬ Function.Injective (higherArrangementShifts p)).card ≤ 4*N^10 := by
  let A := H.filter fun p => p.1.1 = p.1.2 0
  let B := H.filter fun p => p.1.1 = p.1.2 1
  let C := H.filter fun p => p.1.2 0 = p.1.2 1
  let D := H.filter fun p => p.1.1 = p.1.2 1+p.1.2 1-p.1.2 0
  have hA := higher_fixed_first_card_le A (fun z => z 0) (fun p hp => (Finset.mem_filter.mp hp).2)
  have hB := higher_fixed_first_card_le B (fun z => z 1) (fun p hp => (Finset.mem_filter.mp hp).2)
  have hC := higher_equal_inner_shifts_card_le C (fun p hp => (Finset.mem_filter.mp hp).2)
  have hD := higher_fixed_first_card_le D (fun z => z 1+z 1-z 0) (fun p hp => (Finset.mem_filter.mp hp).2)
  have hsub : (H.filter fun p => ¬ Function.Injective (higherArrangementShifts p)) ⊆ A ∪ B ∪ C ∪ D := by
    intro p hp
    obtain ⟨hpH,hpbad⟩ := Finset.mem_filter.mp hp
    have he := higher_shift_collision_cases p hpbad
    simp only [Finset.mem_union,Finset.mem_filter,A,B,C,D]
    tauto
  have hAB := Finset.card_union_le A B
  have hABC := Finset.card_union_le (A ∪ B) C
  have hABCD := Finset.card_union_le (A ∪ B ∪ C) D
  exact (Finset.card_le_card hsub).trans (by omega)

end LeanProofs.GowersSzemeredi
