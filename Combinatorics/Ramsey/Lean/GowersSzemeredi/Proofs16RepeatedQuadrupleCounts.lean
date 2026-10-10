import GowersSzemeredi.Definitions

/-! Repeated indices in additive quadruples are counted separately from
independent representation choices. Each repeated coordinate pair costs
at most `N^2`; there are six possible pairs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem repeated_additive_quad_coordinate_card_le {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N))
    (hQ : ∀ q ∈ Q, q 0-q 1+q 2-q 3 = 0) (i j : Fin 4) (hij : i < j) :
    (Q.filter fun q => q i = q j).card ≤ N^2 := by
  let proj : (Fin 4 → ZMod N) → ZMod N × ZMod N := fun q =>
    (q 0, if j = 1 ∨ i = 2 then q 2 else q 1)
  have hinj : Set.InjOn proj ↑(Q.filter fun q => q i = q j) := by
    intro q hq r hr he
    have haq := hQ q (Finset.mem_filter.mp hq).1
    have har := hQ r (Finset.mem_filter.mp hr).1
    have hqe := (Finset.mem_filter.mp hq).2
    have hre := (Finset.mem_filter.mp hr).2
    have h0 : q 0 = r 0 := congrArg Prod.fst he
    have hs := congrArg Prod.snd he
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals norm_num [proj] at hs
    · change q 0 = q 1 at hqe
      change r 0 = r 1 at hre
      change q 2 = r 2 at hs
      have h1 : q 1 = r 1 := by linear_combination h0-hqe+hre
      have h3 : q 3 = r 3 := by linear_combination -haq+har+hqe-hre+hs
      funext k; fin_cases k <;> assumption
    · change q 0 = q 2 at hqe
      change r 0 = r 2 at hre
      change q 1 = r 1 at hs
      have h2 : q 2 = r 2 := by linear_combination h0-hqe+hre
      have h3 : q 3 = r 3 := by linear_combination -haq+har+2*h0-hs-hqe+hre
      funext k; fin_cases k <;> assumption
    · change q 0 = q 3 at hqe
      change r 0 = r 3 at hre
      change q 1 = r 1 at hs
      have h2 : q 2 = r 2 := by linear_combination haq-har+hs-hqe+hre
      have h3 : q 3 = r 3 := by linear_combination h0-hqe+hre
      funext k; fin_cases k <;> assumption
    · change q 1 = q 2 at hqe
      change r 1 = r 2 at hre
      change q 1 = r 1 at hs
      have h2 : q 2 = r 2 := by linear_combination hs-hqe+hre
      have h3 : q 3 = r 3 := by linear_combination -haq+har+h0-hqe+hre
      funext k; fin_cases k <;> assumption
    · change q 1 = q 3 at hqe
      change r 1 = r 3 at hre
      change q 1 = r 1 at hs
      have h2 : q 2 = r 2 := by linear_combination haq-har-h0+2*hs-hqe+hre
      have h3 : q 3 = r 3 := by linear_combination hs-hqe+hre
      funext k; fin_cases k <;> assumption
    · change q 2 = q 3 at hqe
      change r 2 = r 3 at hre
      change q 2 = r 2 at hs
      have h1 : q 1 = r 1 := by linear_combination -haq+har+h0+hqe-hre
      have h3 : q 3 = r 3 := by linear_combination hs-hqe+hre
      funext k; fin_cases k <;> assumption
  have hc := Finset.card_le_card_of_injOn proj
    (s := Q.filter fun q => q i = q j) (t := (Finset.univ : Finset (ZMod N × ZMod N)))
    (by simp) hinj
  simpa [pow_two] using hc

/-- Noninjective additive queries contribute at most six quadratic error terms. -/
theorem repeated_additive_quadruples_card_le {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (hQ : ∀ q ∈ Q, q 0-q 1+q 2-q 3 = 0) :
    (Q.filter fun q => ¬ Function.Injective q).card ≤ 6*N^2 := by
  let P := (Finset.univ : Finset (Fin 4 × Fin 4)).filter fun p => p.1 < p.2
  have hP : P.card = 6 := by decide
  have hsub : (Q.filter fun q => ¬ Function.Injective q) ⊆
      P.biUnion (fun p => Q.filter fun q => q p.1 = q p.2) := by
    intro q hq
    obtain ⟨hqQ, hn⟩ := Finset.mem_filter.mp hq
    simp only [Function.Injective] at hn
    push Not at hn
    obtain ⟨i, j, he, hne⟩ := hn
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact Finset.mem_biUnion.mpr ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
        Finset.mem_filter.mpr ⟨hqQ, he⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨(j,i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩,
        Finset.mem_filter.mpr ⟨hqQ, he.symm⟩⟩
  calc
    _ ≤ ∑ p ∈ P, (Q.filter fun q => q p.1 = q p.2).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, N^2 := Finset.sum_le_sum fun p hp =>
      repeated_additive_quad_coordinate_card_le Q hQ p.1 p.2 (Finset.mem_filter.mp hp).2
    _ = _ := by simp [hP]

end LeanProofs.GowersSzemeredi
