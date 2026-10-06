import GowersSzemeredi.Proofs16StepBounds

/-! # Prescribed signed steps for proper progression partitions

Reversing the parametrization leaves a progression's carrier and length
unchanged. This lets the natural residue-partition construction use either
orientation of a centered modular step.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The same finite progression enumerated in the opposite direction. -/
def ModAP.reverse {N : Nat} (P : ModAP N) : ModAP N where
  start := P.start + ((P.length - 1 : Nat) : ZMod N) * P.step
  step := -P.step
  length := P.length

theorem ModAP.reverse_index {N : Nat} (P : ModAP N) (i : Fin P.length) :
    P.reverse.start + (i : ZMod N) * P.reverse.step =
      P.start + ((i.rev : Fin P.length) : ZMod N) * P.step := by
  have h : P.length - 1 = (i.rev : Nat) + (i : Nat) := by
    simp only [Fin.val_rev]
    omega
  change P.start + ((P.length - 1 : Nat) : ZMod N) * P.step +
    (i : ZMod N) * (-P.step) = P.start + (i.rev : ZMod N) * P.step
  rw [h, Nat.cast_add]
  ring

@[simp] theorem ModAP.reverse_carrier {N : Nat} (P : ModAP N) :
    P.reverse.carrier = P.carrier := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨i.rev, Finset.mem_univ _, (P.reverse_index i).symm⟩
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨i.rev, Finset.mem_univ _, ?_⟩
    simpa only [Fin.rev_rev] using P.reverse_index i.rev

@[simp] theorem ModAP.reverse_isProper {N : Nat} (P : ModAP N) :
    P.reverse.IsProper ↔ P.IsProper := by
  unfold ModAP.IsProper
  rw [ModAP.reverse_carrier]
  rfl

/-- A proper progression can be refined at a positive natural multiple of
its step, with all output lengths equal to v-1 or v. -/
theorem ModAP.residue_partition {N : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (p v : Nat)
    (hp : 0 < p) (hv : 1 ≤ v) (hsize : p * v ^ 2 ≤ P.length) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j => (Q j).carrier) P.carrier ∧
      (∀ j, (Q j).IsProper ∧ 0 < (Q j).length ∧
        ((Q j).length = v - 1 ∨ (Q j).length = v)) ∧
      ∀ j, (Q j).step = (p : ZMod N) * P.step := by
  obtain ⟨M, R, _, hRpart, hRprop, hRstep⟩ :=
    section5_residue_target_partition P.length p v hp hv hsize
  refine ⟨M, fun j => section5Transport P (R j),
    section5Transport_partition P R hP hRpart, ?_, ?_⟩
  · intro j
    exact ⟨section5Transport_isProper P (R j) hP (hRprop j).1
      (IsPartition.cell_subset hRpart j), (hRprop j).2⟩
  · intro j
    change ((R j).step : ZMod N) * P.step = _
    rw [hRstep]

/-- The centered absolute step always represents either orientation. -/
theorem centeredAbs_cast_eq_or_neg {N : Nat} [NeZero N] (d : ZMod N) :
    (centeredAbs d : ZMod N) = d ∨ (centeredAbs d : ZMod N) = -d := by
  unfold centeredAbs
  rw [ZMod.natCast_natAbs_valMinAbs]
  split_ifs <;> simp

/-- Use a prescribed modular multiplier, reversing the output cells when
its centered representative is negative. -/
theorem ModAP.signed_residue_partition {N : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) (d : ZMod N) (v : Nat)
    (hd : 0 < centeredAbs d) (hv : 1 ≤ v)
    (hsize : centeredAbs d * v ^ 2 ≤ P.length) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j => (Q j).carrier) P.carrier ∧
      (∀ j, (Q j).IsProper ∧ 0 < (Q j).length ∧
        ((Q j).length = v - 1 ∨ (Q j).length = v)) ∧
      ∀ j, (Q j).step = d * P.step := by
  obtain ⟨M, Q, hpart, hprop, hstep⟩ := P.residue_partition hP (centeredAbs d) v hd hv hsize
  rcases centeredAbs_cast_eq_or_neg d with heq | heq
  · exact ⟨M, Q, hpart, hprop, fun j => by rw [hstep j, heq]⟩
  · refine ⟨M, fun j => (Q j).reverse, ?_, ?_, ?_⟩
    · simpa only [ModAP.reverse_carrier] using hpart
    · intro j
      exact ⟨(ModAP.reverse_isProper _).mpr (hprop j).1, (hprop j).2⟩
    · intro j
      change -(Q j).step = d * P.step
      rw [hstep j, heq]
      ring

/-- A proper progression of length at least two cannot have zero step. -/
theorem ModAP.centered_step_pos {N : Nat} [NeZero N] (P : ModAP N)
    (hP : P.IsProper) (hlen : 2 ≤ P.length) : 0 < centeredAbs P.step := by
  by_contra h
  have hzero : centeredAbs P.step = 0 := by omega
  have hs : P.step = 0 := by
    simpa only [centeredAbs, Int.natAbs_eq_zero, ZMod.valMinAbs_eq_zero] using hzero
  have heq : (0 : Nat) = 1 := section5IndexPoint_injective_on_range P hP
    (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by omega))
    (by simp [section5IndexPoint, hs])
  omega

/-- A contained proper progression supplies the full
partition budget on a second axis at least as long as the containing interval. -/
theorem ModAP.partition_at_short_interval_step {N n v : Nat} [NeZero N]
    (R P : ModAP N) (hR : R.IsProper) (hP : P.IsProper) (hn : 2 * n ≤ N)
    (hsub : R.carrier ⊆ (modInterval N 0 n).carrier)
    (hL : n ≤ P.length) (hv : 1 ≤ v)
    (hfit : v ^ 2 ≤ R.length - 1) :
    ∃ M : Nat, ∃ Q : Fin M → ModAP N,
      IsPartition (fun j => (Q j).carrier) P.carrier ∧
      (∀ j, (Q j).IsProper ∧ 0 < (Q j).length ∧
        ((Q j).length = v - 1 ∨ (Q j).length = v)) ∧
      ∀ j, (Q j).step = R.step * P.step := by
  have hv2 : 1 ≤ v ^ 2 := one_le_pow₀ hv
  have hlen : 2 ≤ R.length := by omega
  exact P.signed_residue_partition hP R.step v (R.centered_step_pos hR hlen) hv
    (R.step_target_budget hn hsub (by omega) hL hfit)

end LeanProofs.GowersSzemeredi
