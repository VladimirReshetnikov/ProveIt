import GowersSzemeredi.Proofs16SingletonPartition

/-! # Step bounds for progressions contained in short index intervals

A progression inside an interval shorter than half the modulus cannot jump
between two different integer representatives of its step. Its natural
representatives form an integer arithmetic progression, possibly descending.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The indexed point of a modular progression belongs to its carrier. -/
theorem modAP_index_mem {N : Nat} (P : ModAP N) {i : Nat} (hi : i < P.length) :
    P.start + (i : ZMod N) * P.step ∈ P.carrier := by
  classical
  exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩

/-- Membership in a short initial modular interval bounds the ordinary
representative, with no primality assumption. -/
theorem val_lt_of_mem_modInterval_zero {N n : Nat} [NeZero N] (hn : n ≤ N)
    {x : ZMod N} (hx : x ∈ (modInterval N 0 n).carrier) : x.val < n := by
  rw [modInterval_zero_carrier] at hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have hi' := Finset.mem_range.mp hi
  rwa [ZMod.val_natCast_of_lt (hi'.trans_le hn)]

/-- Every consecutive difference in a short containing interval is the
same centered integer representative of the progression step. -/
theorem ModAP.val_step_of_short_interval {N n : Nat} [NeZero N]
    (P : ModAP N) (hn : 2 * n ≤ N)
    (hsub : P.carrier ⊆ (modInterval N 0 n).carrier)
    {i : Nat} (hi : i + 1 < P.length) :
    P.step.valMinAbs =
      ((P.start + ((i + 1 : Nat) : ZMod N) * P.step).val : Int) -
        ((P.start + (i : ZMod N) * P.step).val : Int) := by
  have hx := val_lt_of_mem_modInterval_zero (by omega : n ≤ N)
    (hsub (modAP_index_mem P hi))
  have hy := val_lt_of_mem_modInterval_zero (by omega : n ≤ N)
    (hsub (modAP_index_mem P (show i < P.length by omega)))
  apply (ZMod.valMinAbs_spec _ _).mpr
  constructor
  · push_cast
    simp only [ZMod.natCast_zmod_val]
    ring
  · constructor <;> omega

/-- In a short containing interval the entire modular progression lifts
to an integer progression with its centered step. -/
theorem ModAP.val_affine_of_short_interval {N n : Nat} [NeZero N]
    (P : ModAP N) (hn : 2 * n ≤ N)
    (hsub : P.carrier ⊆ (modInterval N 0 n).carrier)
    (i : Nat) (hi : i < P.length) :
    ((P.start + (i : ZMod N) * P.step).val : Int) =
      P.start.val + (i : Int) * P.step.valMinAbs := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hprev := ih (by omega)
    have hdiff := P.val_step_of_short_interval hn hsub hi
    push_cast at hdiff ⊢
    linarith

/-- A long progression in a short index interval has a small step. This
is the integer budget needed to refine another axis at that same step. -/
theorem ModAP.centered_step_length_le {N n : Nat} [NeZero N]
    (P : ModAP N) (hn : 2 * n ≤ N)
    (hsub : P.carrier ⊆ (modInterval N 0 n).carrier) (hP : 0 < P.length) :
    centeredAbs P.step * (P.length - 1) ≤ n - 1 := by
  have hi : P.length - 1 < P.length := by omega
  have hx := val_lt_of_mem_modInterval_zero (by omega : n ≤ N)
    (hsub (modAP_index_mem P hi))
  have hy := val_lt_of_mem_modInterval_zero (by omega : n ≤ N)
    (hsub (modAP_index_mem P (show 0 < P.length from hP)))
  simp only [Nat.cast_zero, zero_mul, add_zero] at hy
  have haff := P.val_affine_of_short_interval hn hsub (P.length - 1) hi
  have heq : ((P.start + ((P.length - 1 : Nat) : ZMod N) * P.step).val : Int) - P.start.val =
      ((P.length - 1 : Nat) : Int) * P.step.valMinAbs := by linarith
  have hbound : (((P.start + ((P.length - 1 : Nat) : ZMod N) * P.step).val : Int) - P.start.val).natAbs ≤ n - 1 := by
    omega
  rw [heq, Int.natAbs_mul] at hbound
  simpa only [Int.natAbs_natCast, centeredAbs, Nat.mul_comm] using hbound

/-- A square target fitting into the old length minus one also fits the
residue-partition budget on any interval at least as long as the parent. -/
theorem ModAP.step_target_budget {N n L v : Nat} [NeZero N]
    (P : ModAP N) (hn : 2 * n ≤ N)
    (hsub : P.carrier ⊆ (modInterval N 0 n).carrier) (hP : 0 < P.length)
    (hL : n ≤ L) (hv : v ^ 2 ≤ P.length - 1) :
    centeredAbs P.step * v ^ 2 ≤ L := by
  exact (Nat.mul_le_mul_left _ hv).trans
    ((P.centered_step_length_le hn hsub hP).trans (by omega))

end LeanProofs.GowersSzemeredi
