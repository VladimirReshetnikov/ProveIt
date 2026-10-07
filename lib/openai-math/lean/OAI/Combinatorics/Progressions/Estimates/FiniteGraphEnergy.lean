import Mathlib

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def shiftedAdditiveQuadruples (A : Finset G) (d : G) : Finset ((G × G) × (G × G)) :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter
    (fun x => x.1.1 + x.1.2 = x.2.1 + x.2.2 + d)

theorem shiftedAdditiveQuadruples_card (A : Finset G) (d : G) :
    (shiftedAdditiveQuadruples A d).card =
      ∑ r : G, ((A ×ˢ A).filter (fun x => x.1 + x.2 = r)).card *
        ((A ×ˢ A).filter (fun x => x.1 + x.2 = r - d)).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun x : (G × G) × (G × G) => x.1.1 + x.1.2)
    (t := Finset.univ) (by intro x _; exact Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro r _
  have heq : (shiftedAdditiveQuadruples A d).filter
      (fun x => x.1.1 + x.1.2 = r) =
        ((A ×ˢ A).filter (fun x => x.1 + x.2 = r)) ×ˢ
          ((A ×ˢ A).filter (fun x => x.1 + x.2 = r - d)) := by
    ext x
    simp only [shiftedAdditiveQuadruples, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h₁, h₂⟩, hsum⟩, hr⟩
      exact ⟨⟨h₁, hr⟩, h₂, (eq_sub_iff_add_eq).mpr (hsum.symm.trans hr)⟩
    · rintro ⟨⟨h₁, hr⟩, h₂, hd⟩
      exact ⟨⟨⟨h₁, h₂⟩, hr.trans ((eq_sub_iff_add_eq).mp hd).symm⟩, hr⟩
  rw [heq, Finset.card_product]

theorem shiftedAdditiveQuadruples_card_le_energy (A : Finset G) (d : G) :
    (shiftedAdditiveQuadruples A d).card ≤ Finset.addEnergy A A := by
  rw [shiftedAdditiveQuadruples_card, Finset.addEnergy_eq_sum_sq]
  let f : G → ℕ := fun r => ((A ×ˢ A).filter (fun x => x.1 + x.2 = r)).card
  change (∑ r : G, f r * f (r - d)) ≤ ∑ r : G, f r ^ 2
  have hshift : (∑ r : G, f (r - d) ^ 2) = ∑ r : G, f r ^ 2 :=
    Fintype.sum_equiv (Equiv.subRight d) _ _ (fun _ => rfl)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f (fun r => f (r - d))
  rw [hshift] at hcs
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (by simpa only [pow_two] using hcs)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G K : Type*} [AddCommGroup G] [AddCommGroup K]
  [Fintype G] [Fintype K] [DecidableEq G] [DecidableEq K]

def additiveGraph (H : Finset G) (b : G → K) : Finset (G × K) :=
  H.image (fun h => (h, b h))

omit [AddCommGroup G] [AddCommGroup K] [Fintype G] [Fintype K] in
theorem additiveGraph_card (H : Finset G) (b : G → K) :
    (additiveGraph H b).card = H.card :=
  Finset.card_image_of_injective H (fun _ _ h => congrArg Prod.fst h)

def additiveGraphQuadruple (b : G → K) (t : G × G × G) :
    ((G × K) × (G × K)) × ((G × K) × (G × K)) :=
  (((t.2.1 - t.1, b (t.2.1 - t.1)), (t.2.2, b t.2.2)),
    ((t.2.1, b t.2.1), (t.2.2 - t.1, b (t.2.2 - t.1))))

omit [AddCommGroup K] [Fintype G] [Fintype K] [DecidableEq G] [DecidableEq K] in
theorem additiveGraphQuadruple_injective (b : G → K) :
    Function.Injective (additiveGraphQuadruple b) := by
  intro t u h
  have hh : t.2.1 = u.2.1 := congrArg (fun x => x.2.1.1) h
  have hk : t.2.2 = u.2.2 := congrArg (fun x => x.1.2.1) h
  have hs : t.2.1 - t.1 = u.2.1 - u.1 := congrArg (fun x => x.1.1.1) h
  rw [hh, sub_eq_add_neg, sub_eq_add_neg] at hs
  exact Prod.ext (neg_injective (add_left_cancel hs)) (Prod.ext hh hk)

theorem graph_energy_of_few_quadruple_differences
    (H : Finset G) (S : Finset (G × G × G)) (b : G → K) (D : Finset K)
    (hH : ∀ t ∈ S, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H)
    (hD : ∀ t ∈ S, b (t.2.1 - t.1) + b t.2.2 - b t.2.1 - b (t.2.2 - t.1) ∈ D) :
    S.card ≤ D.card * Finset.addEnergy (additiveGraph H b) (additiveGraph H b) := by
  let δ : G × G × G → K := fun t =>
    b (t.2.1 - t.1) + b t.2.2 - b t.2.1 - b (t.2.2 - t.1)
  have hcard (d : K) : (S.filter (fun t => δ t = d)).card ≤
      (shiftedAdditiveQuadruples (additiveGraph H b) (0, d)).card := by
    apply Finset.card_le_card_of_injOn (additiveGraphQuadruple b) _
      (fun _ _ _ _ h => additiveGraphQuadruple_injective b h)
    intro t ht
    obtain ⟨htS, hδ⟩ := Finset.mem_filter.mp ht
    obtain ⟨h₀, h₁, h₂, h₃⟩ := hH t htS
    have hmem (x : G) (hx : x ∈ H) : (x, b x) ∈ additiveGraph H b :=
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hmem _ h₁, hmem _ h₂⟩,
        Finset.mem_product.mpr ⟨hmem _ h₀, hmem _ h₃⟩⟩, ?_⟩
    apply Prod.ext
    · change (t.2.1 - t.1) + t.2.2 = (t.2.1 + (t.2.2 - t.1)) + 0
      abel
    · change b (t.2.1 - t.1) + b t.2.2 = (b t.2.1 + b (t.2.2 - t.1)) + d
      rw [← hδ]
      dsimp only [δ]
      abel
  calc
    S.card = ∑ d ∈ D, (S.filter (fun t => δ t = d)).card :=
      Finset.card_eq_sum_card_fiberwise hD
    _ ≤ ∑ d ∈ D, (shiftedAdditiveQuadruples (additiveGraph H b) (0, d)).card :=
      Finset.sum_le_sum (fun d _ => hcard d)
    _ ≤ ∑ _d ∈ D, Finset.addEnergy (additiveGraph H b) (additiveGraph H b) :=
      Finset.sum_le_sum (fun d _ => shiftedAdditiveQuadruples_card_le_energy _ (0, d))
    _ = _ := by simp

end Erdos3

end

end OAI
