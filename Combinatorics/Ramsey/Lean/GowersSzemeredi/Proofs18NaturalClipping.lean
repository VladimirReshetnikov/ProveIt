import GowersSzemeredi.Proofs18NaturalReindex

/-! Clipping an ordinary arithmetic progression at interval boundaries
preserves its progression structure, including empty intersections. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- An intersection with an integer interval is an ordinary progression.
The endpoints are chosen from the first and last surviving indices. -/
theorem NatAP.exists_inter_Ico (P : NatAP) (hP : P.IsProper) (a b : Nat) :
    ∃ Q : NatAP, Q.IsProper ∧ Q.carrier = P.carrier ∩ Finset.Ico a b := by
  let I : Finset (Fin P.length) := Finset.univ.filter (fun i => a ≤ P.index i ∧ P.index i < b)
  have hI (i : Fin P.length) : i ∈ I ↔ a ≤ P.index i ∧ P.index i < b := by simp [I]
  by_cases hne : I.Nonempty
  · let u := I.min' hne
    let v := I.max' hne
    have hu := (hI u).mp (I.min'_mem hne)
    have hv := (hI v).mp (I.max'_mem hne)
    have hmono : Monotone P.index := fun i j hij =>
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _
    refine ⟨⟨P.index u, P.step, (v : Nat) + 1 - u⟩, NatAP.isProper_of_step_pos _ hP.1, ?_⟩
    ext x
    simp only [NatAP.carrier, Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_Ico]
    constructor
    · rintro ⟨j, rfl⟩
      have hj := j.isLt
      let i : Fin P.length := ⟨(u : Nat) + j, by have := v.isLt; omega⟩
      have hui : u ≤ i := show (u : Nat) ≤ (u : Nat) + j by omega
      have hiv : i ≤ v := show (u : Nat) + j ≤ v by omega
      have hx : P.index u + j * P.step = P.index i := by simp only [NatAP.index, i]; ring
      exact hx ▸ ⟨⟨i, rfl⟩, hu.1.trans (hmono hui), (hmono hiv).trans_lt hv.2⟩
    · rintro ⟨⟨i, rfl⟩, hi⟩
      have hui : u ≤ i := I.min'_le i ((hI i).mpr hi)
      have hiv : i ≤ v := I.le_max' i ((hI i).mpr hi)
      refine ⟨⟨(i : Nat) - u, by omega⟩, ?_⟩
      simp only [NatAP.index]
      rw [add_assoc, ← Nat.add_mul, Nat.add_sub_of_le hui]
  · refine ⟨⟨0, 1, 0⟩, NatAP.isProper_of_step_pos _ one_pos, ?_⟩
    ext x
    simp only [NatAP.carrier, Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_Ico, IsEmpty.exists_iff, false_iff, not_and]
    rintro ⟨i, rfl⟩ h1 h2
    exact hne ⟨i, (hI i).mpr ⟨h1, h2⟩⟩

/-- Translation followed by a justified subtraction preserves natural
progressions. The lower bound is required only on actual carrier points. -/
theorem NatAP.exists_image_add_sub (P : NatAP) (hP : P.IsProper) (a b : Nat)
    (hlo : ∀ x ∈ P.carrier, b ≤ a + x) :
    ∃ Q : NatAP, Q.IsProper ∧ Q.carrier = P.carrier.image (fun x => a + x - b) := by
  by_cases hlen : P.length = 0
  · refine ⟨⟨0, 1, 0⟩, NatAP.isProper_of_step_pos _ (by decide), ?_⟩
    have hempty : P.carrier = ∅ := Finset.card_eq_zero.mp (hP.2.trans hlen)
    rw [hempty]
    simp [NatAP.carrier]
  · have hstart : P.start ∈ P.carrier := by
      exact Finset.mem_image.mpr (⟨⟨0, by omega⟩, Finset.mem_univ _, by simp⟩)
    have hab : b ≤ a + P.start := hlo _ hstart
    let Q : NatAP := ⟨a + P.start - b, P.step, P.length⟩
    refine ⟨Q, Q.isProper_of_step_pos hP.1, ?_⟩
    unfold NatAP.carrier
    rw [Finset.image_image]
    apply Finset.image_congr
    intro i _
    change a + P.start - b + (i : Nat) * P.step = a + (P.start + (i : Nat) * P.step) - b
    omega

end LeanProofs.GowersSzemeredi
