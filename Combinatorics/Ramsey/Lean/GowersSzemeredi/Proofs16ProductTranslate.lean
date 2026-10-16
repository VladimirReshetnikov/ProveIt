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
  refine Fintype.sum_equiv (Equiv.addRight (fun _ : Fin 4 => c)) _ _ ?_
  intro q
  have hmem : (∀ t, q t ∈ E.image fun x => x - c) ↔ ∀ t, q t + c ∈ E := by
    refine forall_congr' fun t => ?_
    constructor
    · intro h
      obtain ⟨x, hx, hxq⟩ := Finset.mem_image.mp h
      rw [← hxq, sub_add_cancel]
      exact hx
    · intro h
      exact Finset.mem_image.mpr ⟨q t + c, h, add_sub_cancel_right _ _⟩
  have hq : IsAdditiveQuadruple q ↔ IsAdditiveQuadruple (fun t => q t + c) := by
    unfold IsAdditiveQuadruple
    constructor
    · intro h; simp only; rw [show q 0 + c + (q 1 + c) = (q 0 + q 1) + c + c by ring, h]; ring
    · intro h
      have h' : q 0 + q 1 + c + c = q 2 + q 3 + c + c := by
        simp only at h; linear_combination h
      exact add_right_cancel (add_right_cancel h')
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
  have hE' : ∀ i x, x ∈ E.image (fun x => x - t j) →
      replaceCoordinate (y i - t) j x ∈ B := by
    intro i x hx
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    rw [replaceCoordinate_sub]
    obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.mp (hE i x' hx')
    rw [← hbeq, add_sub_cancel_right]
    exact hb
  have hh := h p j (fun i => y i - t) (E.image fun x => x - t j) (fun x => theta (x + t j))
    (fun x => htheta _) hE'
  have hsum : ∑ x ∈ E.image (fun x => x - t j), theta (x + t j) = ∑ x ∈ E, theta x := by
    rw [Finset.sum_image (fun a _ b _ hab => sub_left_injective hab)]
    simp
  rw [hsum] at hh
  have henergy := weightedSimultaneousAdditiveEnergy_translate E theta
    (fun i => coordinateRestriction (fun x => phi (x - t)) (y i) j) (t j)
  have hfun : (fun i x => coordinateRestriction (fun x => phi (x - t)) (y i) j (x + t j)) =
      fun i => coordinateRestriction phi (y i - t) j := by
    funext i x
    unfold coordinateRestriction
    show phi (replaceCoordinate (y i) j (x + t j) - t) = _
    rw [← replaceCoordinate_sub (y i) t j (x + t j), add_sub_cancel_right]
  rw [hfun] at henergy
  rw [← henergy]
  exact hh

/-- **The relation product property is invariant under base translation.** -/
theorem RelationProductProperty.translate {N k : Nat} [NeZero N] {gamma : Real}
    {Gamma : Finset (Point N k × ZMod N)} (h : RelationProductProperty gamma Gamma)
    (t : Point N k) :
    RelationProductProperty gamma (Gamma.image fun z => (z.1 + t, z.2)) := by
  intro C phi hC
  have hC' : GraphContained (C.image fun x => x - t) (fun x => phi (x + t)) Gamma := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp (hC x' hx')
    obtain ⟨h1, h2⟩ := Prod.mk.inj hzeq
    show (x' - t, phi (x' - t + t)) ∈ Gamma
    rw [sub_add_cancel, ← h2]
    have : (x' - t, z.2) = z := Prod.ext (by rw [← h1, add_sub_cancel_right]) rfl
    rw [this]
    exact hz
  have hp := (h _ _ hC').translate t
  have himg : (C.image fun x => x - t).image (fun x => x + t) = C := by
    rw [Finset.image_image]
    have hid : ((fun x : Point N k => x + t) ∘ fun x => x - t) = id := by
      funext x; simp
    rw [hid, Finset.image_id]
  rw [himg] at hp
  refine hp.congr_on ?_
  intro x _
  show phi (x - t + t) = phi x
  rw [sub_add_cancel]

end LeanProofs.GowersSzemeredi
