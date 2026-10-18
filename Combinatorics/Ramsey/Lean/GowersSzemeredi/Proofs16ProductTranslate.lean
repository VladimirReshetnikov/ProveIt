import GowersSzemeredi.Proofs16CoordinateFaces
import GowersSzemeredi.Proofs16GreedyRelations

/-! The product property is invariant under translation.

The weighted simultaneous additive energy is a sum over all quadruples, so
shifting every coordinate by a constant permutes its terms
(`weightedSimultaneousAdditiveEnergy_translate`). Hence:
* `HasProductProperty.translate`: `(B, φ)` has the product property iff its
  translate `(B + t, φ(· − t))` has it;
* `RelationProductProperty.translate`: the same for relations translated in
  their base coordinates.

The three-dimensional pieces need this. Their spectrum relation enters the
original frame translated by the base point `x₀`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Shifting the support, the weights and the maps by a constant leaves the
energy unchanged. -/
theorem weightedSimultaneousAdditiveEnergy_translate {N p : Nat} [NeZero N]
    (E : Finset (ZMod N)) (theta : ZMod N → Real) (psi : Fin p → ZMod N → ZMod N) (c : ZMod N) :
    weightedSimultaneousAdditiveEnergy (E.image fun x => x - c) (fun x => theta (x + c))
      (fun i x => psi i (x + c)) = weightedSimultaneousAdditiveEnergy E theta psi := by
  unfold weightedSimultaneousAdditiveEnergy
  refine Fintype.sum_equiv (Equiv.addRight (fun _ : Fin 4 => c)) _ _ fun q => ?_
  have hmem : (∀ t, q t ∈ E.image fun x => x - c) ↔ ∀ t, q t + c ∈ E := by
    simp [sub_eq_iff_eq_add]
  have hq : IsAdditiveQuadruple q ↔ IsAdditiveQuadruple (fun t => q t + c) := by
    simp only [IsAdditiveQuadruple]
    constructor <;> intro h <;> linear_combination h
  simp only [Equiv.coe_addRight, Pi.add_apply]
  by_cases hc : (∀ t, q t ∈ E.image fun x => x - c) ∧ IsAdditiveQuadruple q ∧
      ∀ i, IsAdditiveQuadruple (fun t => psi i (q t + c))
  · rw [if_pos hc, if_pos ⟨hmem.mp hc.1, hq.mp hc.2.1, hc.2.2⟩]
  · rw [if_neg hc, if_neg]
    exact fun h' => hc ⟨hmem.mpr h'.1, hq.mpr h'.2.1, h'.2.2⟩

theorem replaceCoordinate_sub {N k : Nat} (y t : Point N k) (j : Fin k) (x : ZMod N) :
    replaceCoordinate (y - t) j (x - t j) = replaceCoordinate y j x - t := by
  funext i
  unfold replaceCoordinate
  by_cases h : i = j
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- **The product property is invariant under translation.** -/
theorem HasProductProperty.translate {N k : Nat} [NeZero N] {B : Finset (Point N k)}
    {phi : Point N k → ZMod N} {gamma : Real} (h : HasProductProperty B phi gamma)
    (t : Point N k) :
    HasProductProperty (B.image fun x => x + t) (fun x => phi (x - t)) gamma := by
  intro p j y E theta htheta hE
  have hh := h p j (fun i => y i - t) (E.image fun x => x - t j) (fun x => theta (x + t j))
    (fun x => htheta _) fun i x hx => by
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.mp (hE i x' hx')
      rwa [replaceCoordinate_sub, ← hbeq, add_sub_cancel_right]
  rw [Finset.sum_image fun a _ b _ hab => sub_left_injective hab] at hh
  simp only [sub_add_cancel] at hh
  have hfun : (fun i x => coordinateRestriction (fun x => phi (x - t)) (y i) j (x + t j)) =
      fun i => coordinateRestriction phi (y i - t) j := by
    funext i x
    simp only [coordinateRestriction]
    rw [← replaceCoordinate_sub (y i) t j (x + t j), add_sub_cancel_right]
  rwa [← weightedSimultaneousAdditiveEnergy_translate E theta _ (t j), hfun]

/-- **The relation product property is invariant under base translation.** -/
theorem RelationProductProperty.translate {N k : Nat} [NeZero N] {gamma : Real}
    {Gamma : Finset (Point N k × ZMod N)} (h : RelationProductProperty gamma Gamma)
    (t : Point N k) :
    RelationProductProperty gamma (Gamma.image fun z => (z.1 + t, z.2)) := by
  intro C phi hC
  have hC' : GraphContained (C.image fun x => x - t) (fun x => phi (x + t)) Gamma := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨a, b⟩, hz, hzeq⟩ := Finset.mem_image.mp (hC x' hx')
    simp only [Prod.mk.injEq] at hzeq
    obtain ⟨rfl, rfl⟩ := hzeq
    simpa using hz
  have hp := (h _ _ hC').translate t
  rw [show (C.image fun x => x - t).image (fun x => x + t) = C by
    simp [Finset.image_image, Function.comp_def]] at hp
  exact hp.congr_on fun x _ => by simp

end LeanProofs.GowersSzemeredi
