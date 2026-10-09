import GowersSzemeredi.Proofs16JointAnchorRowIndices

/-! A dense family of additive quadruples has a dense projection at
every position: fixing one coordinate leaves only two free coordinates. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def anchorRowSupport {N : Nat} (R : Finset (Fin 4 → ZMod N)) (j : Fin 4) : Finset (ZMod N) :=
  R.image (fun a => a j)

theorem additive_quadruples_row_card_le {N : Nat} [NeZero N]
    (R : Finset (Fin 4 → ZMod N)) (hadd : ∀ a ∈ R, a 0+a 1 = a 2+a 3) (j : Fin 4) :
    R.card ≤ (anchorRowSupport R j).card*N^2 := by
  let f : (Fin 4 → ZMod N) → ZMod N × (ZMod N × ZMod N) :=
    fun a => (a j, if j = 0 then (a 1,a 2) else if j = 1 then (a 0,a 2) else (a 0,a 1))
  have hi : Set.InjOn f (R : Set (Fin 4 → ZMod N)) := by
    intro a ha b hb he
    have hfirst : a j = b j := congrArg Prod.fst he
    have hrest : (f a).2 = (f b).2 := congrArg Prod.snd he
    have hA := hadd a ha
    have hB := hadd b hb
    fin_cases j
    · change a 0 = b 0 at hfirst
      simp [f] at hrest
      obtain ⟨h0,h1⟩ := hrest
      funext i
      fin_cases i
      · exact hfirst
      · exact h0
      · exact h1
      · change a 3 = b 3
        linear_combination -hA+hB+hfirst+h0-h1
    · change a 1 = b 1 at hfirst
      simp [f] at hrest
      obtain ⟨h0,h1⟩ := hrest
      funext i
      fin_cases i
      · exact h0
      · exact hfirst
      · exact h1
      · change a 3 = b 3
        linear_combination -hA+hB+hfirst+h0-h1
    · change a 2 = b 2 at hfirst
      simp [f] at hrest
      obtain ⟨h0,h1⟩ := hrest
      funext i
      fin_cases i
      · exact h0
      · exact h1
      · exact hfirst
      · change a 3 = b 3
        linear_combination -hA+hB+h0+h1-hfirst
    · change a 3 = b 3 at hfirst
      simp [f] at hrest
      obtain ⟨h0,h1⟩ := hrest
      funext i
      fin_cases i
      · exact h0
      · exact h1
      · change a 2 = b 2
        linear_combination -hA+hB+h0+h1-hfirst
      · exact hfirst
  have hc : R.card ≤ ((anchorRowSupport R j) ×ˢ (Finset.univ : Finset (ZMod N × ZMod N))).card := by
    apply Finset.card_le_card_of_injOn f
    · intro a ha
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨a,ha,rfl⟩,Finset.mem_univ _⟩
    · exact hi
  simpa only [Finset.card_product,Finset.card_univ,Fintype.card_prod,ZMod.card,pow_two] using hc

theorem additive_quadruples_row_density {N : Nat} [NeZero N]
    (R : Finset (Fin 4 → ZMod N)) (hadd : ∀ a ∈ R, a 0+a 1 = a 2+a 3)
    {kappa : Real} (hR : kappa*(N : Real)^3 ≤ R.card) (j : Fin 4) :
    kappa*N ≤ ((anchorRowSupport R j).card : Real) := by
  have hc : (R.card : Real) ≤ (anchorRowSupport R j).card*(N : Real)^2 := by
    exact_mod_cast additive_quadruples_row_card_le R hadd j
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hn)).mp
  nlinarith only [hR,hc]

end LeanProofs.GowersSzemeredi
