import GowersSzemeredi.Proofs16PopularAffineRowAgreement

/-! Repeated entries in an additive quadruple occupy four families,
each parametrized by two ambient elements. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem additive_quadruple_collision_cases {N : Nat} (a : Fin 4 → ZMod N)
    (ha : a 0+a 1 = a 2+a 3) (h : ¬ Function.Injective a) :
    a 0 = a 1 ∨ a 0 = a 2 ∨ a 1 = a 2 ∨ a 0 = a 2+a 2-a 1 := by
  by_contra hn
  have h1 : a 0 ≠ a 1 := fun he => hn (Or.inl he)
  have h2 : a 0 ≠ a 2 := fun he => hn (Or.inr (Or.inl he))
  have h3 : a 1 ≠ a 2 := fun he => hn (Or.inr (Or.inr (Or.inl he)))
  have h4 : a 0 ≠ a 2+a 2-a 1 := fun he => hn (Or.inr (Or.inr (Or.inr he)))
  apply h
  intro i j hij
  fin_cases i <;> fin_cases j <;> try rfl
  · change a 0 = a 1 at hij
    exfalso
    exact h1 hij
  · change a 0 = a 2 at hij
    exfalso
    exact h2 hij
  · change a 0 = a 3 at hij
    exfalso
    exact h3 (by linear_combination ha-hij)
  · change a 1 = a 0 at hij
    exfalso
    exact h1 hij.symm
  · change a 1 = a 2 at hij
    exfalso
    exact h3 hij
  · change a 1 = a 3 at hij
    exfalso
    exact h2 (by linear_combination ha-hij)
  · change a 2 = a 0 at hij
    exfalso
    exact h2 hij.symm
  · change a 2 = a 1 at hij
    exfalso
    exact h3 hij.symm
  · change a 2 = a 3 at hij
    exfalso
    exact h4 (by linear_combination ha-hij)
  · change a 3 = a 0 at hij
    exfalso
    exact h3 (by linear_combination ha+hij)
  · change a 3 = a 1 at hij
    exfalso
    exact h2 (by linear_combination ha+hij)
  · change a 3 = a 2 at hij
    exfalso
    exact h4 (by linear_combination ha+hij)

theorem additive_quadruples_fixed_first_card_le {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (f : ZMod N → ZMod N → ZMod N)
    (hadd : ∀ a ∈ Q, a 0+a 1 = a 2+a 3) (hf : ∀ a ∈ Q, a 0 = f (a 1) (a 2)) :
    Q.card ≤ N^2 := by
  have h : Q.card ≤ (Finset.univ : Finset (ZMod N × ZMod N)).card := by
    apply Finset.card_le_card_of_injOn (fun a : Fin 4 → ZMod N => (a 1,a 2))
      (fun _ _ => Finset.mem_univ _)
    intro a ha b hb he
    have h12 := Prod.mk.inj he
    have h0 : a 0 = b 0 := by rw [hf a ha,hf b hb,h12.1,h12.2]
    funext i
    fin_cases i
    · exact h0
    · exact h12.1
    · exact h12.2
    · change a 3 = b 3
      linear_combination -hadd a ha+hadd b hb+h0+h12.1-h12.2
  simpa only [Finset.card_univ,Fintype.card_prod,ZMod.card,pow_two] using h

theorem additive_quadruples_equal_middle_card_le {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (hadd : ∀ a ∈ Q, a 0+a 1 = a 2+a 3)
    (heq : ∀ a ∈ Q, a 1 = a 2) : Q.card ≤ N^2 := by
  have h : Q.card ≤ (Finset.univ : Finset (ZMod N × ZMod N)).card := by
    apply Finset.card_le_card_of_injOn (fun a : Fin 4 → ZMod N => (a 0,a 1))
      (fun _ _ => Finset.mem_univ _)
    intro a ha b hb he
    have h01 := Prod.mk.inj he
    have h2 : a 2 = b 2 := (heq a ha).symm.trans (h01.2.trans (heq b hb))
    funext i
    fin_cases i
    · exact h01.1
    · exact h01.2
    · exact h2
    · change a 3 = b 3
      linear_combination -hadd a ha+hadd b hb+h01.1+h01.2-h2
  simpa only [Finset.card_univ,Fintype.card_prod,ZMod.card,pow_two] using h

theorem additive_quadruples_repeated_card_le {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (hadd : ∀ a ∈ Q, a 0+a 1 = a 2+a 3) :
    (Q.filter fun a => ¬ Function.Injective a).card ≤ 4*N^2 := by
  let A := Q.filter fun a => a 0 = a 1
  let B := Q.filter fun a => a 0 = a 2
  let C := Q.filter fun a => a 1 = a 2
  let D := Q.filter fun a => a 0 = a 2+a 2-a 1
  have hA := additive_quadruples_fixed_first_card_le A (fun x _ => x)
    (fun a ha => hadd a (Finset.mem_filter.mp ha).1) (fun a ha => (Finset.mem_filter.mp ha).2)
  have hB := additive_quadruples_fixed_first_card_le B (fun _ y => y)
    (fun a ha => hadd a (Finset.mem_filter.mp ha).1) (fun a ha => (Finset.mem_filter.mp ha).2)
  have hC := additive_quadruples_equal_middle_card_le C
    (fun a ha => hadd a (Finset.mem_filter.mp ha).1) (fun a ha => (Finset.mem_filter.mp ha).2)
  have hD := additive_quadruples_fixed_first_card_le D (fun x y => y+y-x)
    (fun a ha => hadd a (Finset.mem_filter.mp ha).1) (fun a ha => (Finset.mem_filter.mp ha).2)
  have hsub : (Q.filter fun a => ¬ Function.Injective a) ⊆ A ∪ B ∪ C ∪ D := by
    intro a ha
    obtain ⟨haQ,hbad⟩ := Finset.mem_filter.mp ha
    have h := additive_quadruple_collision_cases a (hadd a haQ) hbad
    simp only [Finset.mem_union,Finset.mem_filter,A,B,C,D]
    tauto
  have hAB := Finset.card_union_le A B
  have hABC := Finset.card_union_le (A ∪ B) C
  have hABCD := Finset.card_union_le (A ∪ B ∪ C) D
  exact (Finset.card_le_card hsub).trans (by omega)

theorem additive_quadruples_distinct_mass {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (hadd : ∀ a ∈ Q, a 0+a 1 = a 2+a 3)
    {kappa : Real} (hmass : kappa*(N : Real)^3 ≤ Q.card) (hN : 8 ≤ kappa*(N : Real)) :
    (kappa/2)*(N : Real)^3 ≤ (Q.filter Function.Injective).card := by
  have hbad : ((Q.filter fun a => ¬ Function.Injective a).card : Real) ≤ 4*(N : Real)^2 := by
    exact_mod_cast additive_quadruples_repeated_card_le Q hadd
  have hsmall : 4*(N : Real)^2 ≤ (kappa/2)*(N : Real)^3 := by
    calc 4*(N : Real)^2 = (8/2)*(N : Real)^2 := by ring
      _ ≤ (kappa*(N : Real)/2)*(N : Real)^2 :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hN (by norm_num)) (by positivity)
      _ = _ := by ring
  have hpart : ((Q.filter Function.Injective).card : Real)+
      (Q.filter fun a => ¬ Function.Injective a).card = Q.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := Q) Function.Injective
  linarith

end LeanProofs.GowersSzemeredi
