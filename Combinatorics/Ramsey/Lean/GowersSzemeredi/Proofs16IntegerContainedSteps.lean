import GowersSzemeredi.Proofs16IntegerResiduePartition
import GowersSzemeredi.Proofs16ProductTiling

/-! Containment of ordinary progressions supplies an actual positive integer
step ratio. Retiling a parallel progression at that step preserves all points
and the uniform lengths `v-1` or `v`, without a modular orientation choice. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem NatAP.step_ratio_and_span_of_subset (R B : NatAP)
    (hR : R.IsProper) (hB : B.IsProper) (hlen : 2 ≤ R.length)
    (hsub : R.carrier ⊆ B.carrier) :
    ∃ p : Nat, 0 < p ∧ R.step = p * B.step ∧
      p * (R.length - 1) ≤ B.length - 1 := by
  classical
  have hmem (a : Nat) (ha : a < R.length) : R.start + a * R.step ∈ R.carrier :=
    Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hsub (hmem 0 (by omega)))
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hsub (hmem 1 (by omega)))
  have hi' : B.start + i.val * B.step = R.start := by simpa only [zero_mul, add_zero] using hi
  have hj' : B.start + j.val * B.step = R.start + R.step := by simpa only [one_mul] using hj
  have hij : i.val < j.val := by
    have hstep := hR.1
    nlinarith only [hi', hj', hstep]
  let p := j.val - i.val
  have hp : 0 < p := by dsimp [p]; omega
  have hjval : j.val = i.val + p := by dsimp [p]; omega
  have hratio : R.step = p * B.step := by
    rw [hjval, add_mul] at hj'
    nlinarith only [hi', hj']
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (hsub (hmem (R.length - 1) (by omega)))
  have heq : B.start + (i.val + (R.length - 1) * p) * B.step =
      B.start + a.val * B.step := by
    rw [add_mul, mul_assoc, ← add_assoc, hi', ← hratio]
    exact ha.symm
  have hind := Nat.mul_right_cancel hB.1 (Nat.add_left_cancel heq)
  refine ⟨p, hp, hratio, ?_⟩
  have haL := a.isLt
  rw [mul_comm p]
  omega

theorem NatAP.step_lt_of_two_le {N : Nat} (P : NatAP)
    (hPN : P.carrier ⊆ Finset.range N) (hlen : 2 ≤ P.length) : P.step < N := by
  have hmem : P.start + P.step ∈ P.carrier := by
    refine Finset.mem_image.mpr ⟨⟨1, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only [one_mul]
  have hbound := Finset.mem_range.mp (hPN hmem)
  omega

theorem NatAP.step_eq_of_mod_step_eq {N : Nat} [NeZero N] (P Q : NatAP)
    (hPN : P.carrier ⊆ Finset.range N) (hQN : Q.carrier ⊆ Finset.range N)
    (hP : 2 ≤ P.length) (hQ : 2 ≤ Q.length)
    (hstep : (P.toModAP N).step = (Q.toModAP N).step) : P.step = Q.step := by
  have hval := congrArg ZMod.val hstep
  change (P.step : ZMod N).val = (Q.step : ZMod N).val at hval
  simpa only [ZMod.val_natCast_of_lt (P.step_lt_of_two_le hPN hP),
    ZMod.val_natCast_of_lt (Q.step_lt_of_two_le hQN hQ)] using hval

theorem NatAP.partition_at_contained_step (R B I : NatAP)
    (hR : R.IsProper) (hB : B.IsProper) (hI : I.IsProper)
    (hsub : R.carrier ⊆ B.carrier) (hparallel : B.step = I.step)
    (hL : B.length ≤ I.length) {v : Nat} (hv : 1 ≤ v)
    (hfit : v ^ 2 ≤ R.length - 1) :
    ∃ M : Nat, ∃ J : Fin M → NatAP,
      IsNatAPPartition J I.carrier ∧
      (∀ j, (J j).IsProper ∧ 0 < (J j).length ∧
        ((J j).length = v - 1 ∨ (J j).length = v)) ∧
      (∀ j, (J j).step = R.step) := by
  classical
  have hv2 : 1 ≤ v ^ 2 := one_le_pow₀ hv
  obtain ⟨p, hp, hstep, hspan⟩ := R.step_ratio_and_span_of_subset B hR hB (by omega) hsub
  have hbudget : p * v ^ 2 ≤ I.length :=
    (Nat.mul_le_mul_left p hfit).trans (hspan.trans ((Nat.sub_le _ _).trans hL))
  obtain ⟨M, A, _, hpart, hprops, hAstep⟩ :=
    section5_residue_target_partition I.length p v hp hv hbudget
  refine ⟨M, fun j => section5NatTransport I (A j),
    section5NatTransport_partition I A hI hpart, ?_, ?_⟩
  · intro j
    exact ⟨section5NatTransport_isProper I (A j) hI (hprops j).1, (hprops j).2⟩
  · intro j
    change (A j).step * I.step = R.step
    rw [hAstep j, ← hparallel, ← hstep]

theorem NatAP.carrier_subset_of_mod_carrier_subset {N : Nat} [NeZero N]
    (R B : NatAP) (hRN : R.carrier ⊆ Finset.range N) (hBN : B.carrier ⊆ Finset.range N)
    (hsub : (R.toModAP N).carrier ⊆ (B.toModAP N).carrier) :
    R.carrier ⊆ B.carrier := by
  classical
  rw [NatAP.toModAP_carrier, NatAP.toModAP_carrier] at hsub
  intro x hx
  obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp (hsub (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  have hval := congrArg ZMod.val heq
  rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp (hBN hy)),
    ZMod.val_natCast_of_lt (Finset.mem_range.mp (hRN hx))] at hval
  simpa only [hval] using hy

end LeanProofs.GowersSzemeredi
