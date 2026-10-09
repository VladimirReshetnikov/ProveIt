import GowersSzemeredi.Proofs16HigherAnchorQuadrupleProjection

/-! Fixing the eight columns on either side fixes seven independent
parameters. The other side contributes only four free anchor bases. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherArrangementLeftColumns {N : Nat} (p : HigherArrangementParameter N) : Fin 8 → ZMod N :=
  fun i => higherArrangementEndpoints p (Fin.castAdd 8 i)
def higherArrangementRightColumns {N : Nat} (p : HigherArrangementParameter N) : Fin 8 → ZMod N :=
  fun i => higherArrangementEndpoints p (Fin.natAdd 8 i)
def higherArrangementRightBases {N : Nat} (p : HigherArrangementParameter N) : Fin 4 → ZMod N :=
  ![p.1.2 5,p.1.2 6,p.1.2 7,p.1.2 8]

theorem higherArrangementLeftEncoding_injective {N : Nat} :
    Function.Injective (fun p : HigherArrangementParameter N =>
      (higherArrangementLeftColumns p,higherArrangementRightBases p)) := by
  intro p q h
  have hL := congrArg Prod.fst h
  have hR := congrArg Prod.snd h
  have h0 := congrFun hL 0
  have h1 := congrFun hL 1
  have h2 := congrFun hL 2
  have h3 := congrFun hL 3
  have h4 := congrFun hL 4
  have h5 := congrFun hL 5
  have h7 := congrFun hL 7
  dsimp [higherArrangementLeftColumns,higherArrangementEndpoints] at h0 h1 h2 h3 h4 h5 h7
  refine Prod.ext (Prod.ext ?_ ?_) h1
  · linear_combination h0-h1
  · funext i
    fin_cases i
    · change p.1.2 0 = q.1.2 0
      linear_combination h2-h3
    · change p.1.2 1 = q.1.2 1
      linear_combination h4-h5
    · exact h3
    · exact h5
    · exact h7
    · exact congrFun hR 0
    · exact congrFun hR 1
    · exact congrFun hR 2
    · exact congrFun hR 3

theorem higherArrangementLeftColumns_sides {N : Nat} (p : HigherArrangementParameter N) :
    higherArrangementLeftColumns ((higherArrangementSides N).parameters p) =
      higherArrangementRightColumns p := by
  funext i
  fin_cases i <;> rfl

theorem higher_arrangements_left_columns_card_le {N : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N)) (E : Finset (Fin 8 → ZMod N))
    (hE : ∀ p ∈ H, higherArrangementLeftColumns p ∈ E) : H.card ≤ E.card*N^4 := by
  have hc : H.card ≤ (E ×ˢ (Finset.univ : Finset (Fin 4 → ZMod N))).card := by
    apply Finset.card_le_card_of_injOn (fun p => (higherArrangementLeftColumns p,higherArrangementRightBases p))
    · intro p hp
      exact Finset.mem_product.mpr ⟨hE p hp,Finset.mem_univ _⟩
    · exact fun p _ q _ he => higherArrangementLeftEncoding_injective he
  simpa only [Finset.card_product,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,ZMod.card] using hc

theorem higher_arrangements_right_columns_card_le {N : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N)) (E : Finset (Fin 8 → ZMod N))
    (hE : ∀ p ∈ H, higherArrangementRightColumns p ∈ E) : H.card ≤ E.card*N^4 := by
  let s := higherArrangementSides N
  have hc := higher_arrangements_left_columns_card_le (H.image s.parameters) E (by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [higherArrangementLeftColumns_sides]
    exact hE q hq)
  simpa only [Finset.card_image_of_injective _ s.parameters.injective] using hc

end LeanProofs.GowersSzemeredi
