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
  classical
  let I : Finset (Fin P.length) := Finset.univ.filter (fun i => a ≤ P.index i ∧ P.index i < b)
  by_cases hI : I.Nonempty
  · let u := I.min' hI
    let v := I.max' hI
    have hu : u ∈ I := Finset.min'_mem I hI
    have hv : v ∈ I := Finset.max'_mem I hI
    have huv : u ≤ v := Finset.min'_le I v hv
    have hmono : Monotone P.index := by
      intro i j hij
      exact Nat.add_le_add_left (Nat.mul_le_mul_right P.step hij) _
    have hmem (i : Fin P.length) : i ∈ I ↔ u ≤ i ∧ i ≤ v := by
      constructor
      · intro hi
        exact ⟨Finset.min'_le I i hi, Finset.le_max' I i hi⟩
      · rintro ⟨hui, hiv⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · exact (Finset.mem_filter.mp hu).2.1.trans (hmono hui)
        · exact (hmono hiv).trans_lt (Finset.mem_filter.mp hv).2.2
    let Q : NatAP := ⟨P.index u, P.step, (v : Nat) + 1 - u⟩
    refine ⟨Q, Q.isProper_of_step_pos hP.1, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      have hj : (j : Nat) < (v : Nat) + 1 - u := j.isLt
      let i : Fin P.length := ⟨(u : Nat) + j, by have := v.isLt; omega⟩
      have hi : i ∈ I := (hmem i).mpr ⟨by change (u : Nat) ≤ (u : Nat) + j; omega,
        by change (u : Nat) + j ≤ (v : Nat); omega⟩
      have heq : Q.start + (j : Nat) * Q.step = P.index i := by
        dsimp [Q, NatAP.index, i]
        ring
      rw [heq]
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
          Finset.mem_Ico.mpr (Finset.mem_filter.mp hi).2⟩
    · intro hx
      obtain ⟨hxP, hx⟩ := Finset.mem_inter.mp hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxP
      have hi : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_Ico.mp hx⟩
      obtain ⟨hui, hiv⟩ := (hmem i).mp hi
      let j : Fin Q.length := ⟨(i : Nat) - u, by dsimp [Q]; omega⟩
      refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
      have hji : (u : Nat) + j = i := by dsimp [j]; omega
      change P.index u + (j : Nat) * P.step = P.start + (i : Nat) * P.step
      rw [← hji]
      dsimp [NatAP.index]
      ring
  · refine ⟨⟨0, 1, 0⟩, NatAP.isProper_of_step_pos _ (by decide), ?_⟩
    have hempty : P.carrier ∩ Finset.Ico a b = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hxP, hx⟩ := Finset.mem_inter.mp hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxP
      exact hI ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_Ico.mp hx⟩⟩
    rw [hempty]
    simp [NatAP.carrier]

/-- Translation followed by a justified subtraction preserves natural
progressions. The lower bound is required only on actual carrier points. -/
theorem NatAP.exists_image_add_sub (P : NatAP) (hP : P.IsProper) (a b : Nat)
    (hlo : ∀ x ∈ P.carrier, b ≤ a + x) :
    ∃ Q : NatAP, Q.IsProper ∧ Q.carrier = P.carrier.image (fun x => a + x - b) := by
  classical
  by_cases hlen : P.length = 0
  · refine ⟨⟨0, 1, 0⟩, NatAP.isProper_of_step_pos _ (by decide), ?_⟩
    have hempty : P.carrier = ∅ := Finset.card_eq_zero.mp (hP.2.trans hlen)
    rw [hempty]
    simp [NatAP.carrier]
  · have hstart : P.start ∈ P.carrier := by
      apply Finset.mem_image.mpr
      exact ⟨⟨0, by omega⟩, Finset.mem_univ _, by simp⟩
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
