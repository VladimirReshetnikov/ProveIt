import GowersSzemeredi.Proofs16RepresentedMap

/-! Four-tuple witnesses project to a dense set of represented points:
each point has at most `N^3` representing tuples. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The represented point and first three entries determine a four-tuple. -/
theorem fourSum_three_entries_injective {N : Nat} :
    Function.Injective (fun q : Fin 4 → ZMod N => (fourSum q, (q 0, q 1, q 2))) := by
  intro q r h
  have hs : fourSum q = fourSum r := congrArg Prod.fst h
  have he := congrArg Prod.snd h
  have h0 : q 0 = r 0 := congrArg Prod.fst he
  have h1 : q 1 = r 1 := congrArg (fun z => z.2.1) he
  have h2 : q 2 = r 2 := congrArg (fun z => z.2.2) he
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · change q 3 = r 3
    dsimp only [fourSum] at hs
    linear_combination -hs + h0 + h1 - h2

/-- A set of four-tuples has at most `N^3` times as many elements as its
set of represented points. -/
theorem fourSum_image_card_bound {N : Nat} [NeZero N] (W : Finset (Fin 4 → ZMod N)) :
    W.card ≤ (W.image fourSum).card * N^3 := by
  have h := Finset.card_le_card_of_injOn (s := W)
    (t := W.image fourSum ×ˢ (Finset.univ : Finset (ZMod N × ZMod N × ZMod N)))
    (fun q => (fourSum q, (q 0, q 1, q 2)))
    (fun q hq => Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hq, Finset.mem_univ _⟩)
    fourSum_three_entries_injective.injOn
  simpa only [Finset.card_product, Finset.card_univ, Fintype.card_prod, ZMod.card,
    show N * (N * N) = N^3 by ring] using h

/-- Ambient density of witnesses gives the same ambient density of
represented points. -/
theorem fourSum_image_density {N : Nat} [NeZero N] (W : Finset (Fin 4 → ZMod N))
    {theta : Real} (hW : theta * (N : Real)^4 ≤ W.card) :
    theta * N ≤ ((W.image fourSum).card : Real) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hbound : (W.card : Real) ≤ (W.image fourSum).card * (N : Real)^3 := by
    exact_mod_cast fourSum_image_card_bound W
  apply (mul_le_mul_iff_left₀ (pow_pos hN 3)).mp
  calc (theta * N) * (N : Real)^3 = theta * (N : Real)^4 := by ring
    _ ≤ _ := hW.trans hbound

end LeanProofs.GowersSzemeredi
