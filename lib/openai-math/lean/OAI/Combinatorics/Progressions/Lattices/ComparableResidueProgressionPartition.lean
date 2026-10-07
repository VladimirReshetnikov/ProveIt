import OAI.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition

namespace OAI

section

namespace Erdos3.FiniteProgressionPartition

noncomputable def residues (N q : ℕ) (hq : 0 < q) :
    FiniteProgressionPartition N := by
  let len : Fin q → ℕ := fun r => truncatedProgressionLength N r.val q N
  let f : (Σ r : Fin q, Fin (len r)) → Fin N := fun x =>
    ⟨x.1.val + q * x.2.val, ((lt_truncatedProgressionLength_iff hq).mp x.2.isLt).2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨r, j⟩ ⟨s, k⟩ heq
      have he : r.val + q * j.val = s.val + q * k.val := congrArg Fin.val heq
      have hrs : r = s := by
        apply Fin.ext
        have hm := congrArg (fun n => n % q) he
        simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt,
          Nat.mod_eq_of_lt s.isLt] using hm
      cases hrs
      have hjk : j = k := Fin.ext (mul_left_cancel₀ hq.ne' (Nat.add_left_cancel he))
      cases hjk
      rfl
    · intro n
      let r : Fin q := ⟨n.val % q, Nat.mod_lt _ hq⟩
      have hj : n.val / q < len r := by
        apply (lt_truncatedProgressionLength_iff hq).mpr
        exact ⟨lt_of_le_of_lt (Nat.div_le_self _ _) n.isLt,
          by simpa only [r, Nat.mod_add_div] using n.isLt⟩
      exact ⟨⟨r, ⟨n.val / q, hj⟩⟩, Fin.ext (Nat.mod_add_div _ _)⟩
  exact {
    Label := Fin q
    labelFintype := inferInstance
    start := fun r => r.val
    step := fun _ => q
    length := len
    step_pos := fun _ => hq
    equiv := Equiv.ofBijective f hf
    equiv_val := fun _ _ => rfl }

@[simp] theorem residues_start (N q : ℕ) (hq : 0 < q)
    (r : (residues N q hq).Label) : (residues N q hq).start r = r.val := rfl

@[simp] theorem residues_step (N q : ℕ) (hq : 0 < q)
    (r : (residues N q hq).Label) : (residues N q hq).step r = q := rfl

theorem residues_length_lower {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (r : (residues N q hq).Label) :
    H ≤ (residues N q hq).length r := by
  have hHN : H ≤ N := le_trans (Nat.le_mul_of_pos_left H hq) hfit
  have hpoint : r.val + q * (H - 1) < N := by
    have heq : q * (H - 1) + q = q * H := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    have hlt := Nat.add_lt_add_right r.isLt (q * (H - 1))
    omega
  have hj : H - 1 < (residues N q hq).length r :=
    (lt_truncatedProgressionLength_iff hq).mpr ⟨by omega, hpoint⟩
  omega

noncomputable def comparableResidueProgressions (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) : FiniteProgressionPartition N :=
  (residues N q hq).bind (fun r =>
    mergedIntervals ((residues N q hq).length r) H hH
      (residues_length_lower hq hH hfit r))

@[simp] theorem comparableResidueProgressions_step (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (comparableResidueProgressions N q H hq hH hfit).Label) :
    (comparableResidueProgressions N q H hq hH hfit).step i = q := by
  rcases i with ⟨r, j⟩
  simp [comparableResidueProgressions]

theorem comparableResidueProgressions_length_bounds (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (comparableResidueProgressions N q H hq hH hfit).Label) :
    H ≤ (comparableResidueProgressions N q H hq hH hfit).length i ∧
      (comparableResidueProgressions N q H hq hH hfit).length i < 2 * H :=
  mergedIntervals_length_bounds _ H hH (residues_length_lower hq hH hfit i.1) i.2

theorem exists_comparable_residue_partition (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) :
    ∃ P : FiniteProgressionPartition N,
      (∀ i, P.step i = q) ∧ (∀ i, H ≤ P.length i ∧ P.length i < 2 * H) :=
  ⟨comparableResidueProgressions N q H hq hH hfit,
    comparableResidueProgressions_step N q H hq hH hfit,
    comparableResidueProgressions_length_bounds N q H hq hH hfit⟩

end Erdos3.FiniteProgressionPartition

end

end OAI
