import GowersSzemeredi.Definitions

/-!
# From short modular progressions to integer progressions

Section 18 ultimately needs progressions in an integer interval.  A modular
progression whose representatives all lie in `[1,n]`, with `2*n < N`, lifts
to an ordinary progression.  Its integer common difference may be negative;
reversing the order gives the positive difference required by `HasNatAP`.
No primality assumption or quantitative density-increment input is needed.

`hasNatAP_of_hasModAP_image` is in `Proofs18IntervalTransferSide`, outside the
final route. -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- A sequence of integers with a fixed modular difference and representatives
in a short interval has a fixed ordinary difference, in one of the two
orientations. -/
theorem hasNatAP_of_short_modular_sequence {N n k : Nat}
    (A : Finset Nat) (f : Nat → Nat) (a d : ZMod N)
    (hd : d ≠ 0) (hsize : 2 * n < N)
    (hf : ∀ i, i < k → f i ∈ A ∧ f i ≤ n ∧
      (f i : ZMod N) = a + (i : ZMod N) * d) :
    HasNatAP A k := by
  by_cases hk : k ≤ 1
  · refine ⟨f 0, 1, one_pos, fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    simpa using (hf 0 hi).1
  have h0 := hf 0 (by omega)
  have h1 := hf 1 (by omega)
  have hne : f 0 ≠ f 1 := fun heq => hd (by
    simpa [h0.2.2, h1.2.2] using congrArg (Nat.cast : Nat → ZMod N) heq)
  have hstep (i : Nat) (hi : i + 1 < k) : f (i + 1) + f 0 = f i + f 1 := by
    have hi0 := hf i (by omega)
    have hi1 := hf (i + 1) hi
    refine ((ZMod.natCast_eq_natCast_iff _ _ N).mp ?_).eq_of_lt_of_lt (by omega) (by omega)
    push_cast
    rw [hi1.2.2, h0.2.2, hi0.2.2, h1.2.2]
    push_cast
    ring
  rcases lt_or_gt_of_ne hne with hinc | hdec
  · refine ⟨f 0, f 1 - f 0, by omega, fun i hi => ?_⟩
    suffices f i = f 0 + i * (f 1 - f 0) from this ▸ (hf i hi).1
    induction i with
    | zero => simp
    | succ i ih => have := hstep i hi; have := ih (by omega); rw [Nat.succ_mul]; omega
  · refine ⟨f (k - 1), f 0 - f 1, by omega, fun i hi => ?_⟩
    suffices f (k - 1 - i) = f (k - 1) + i * (f 0 - f 1) from this ▸ (hf _ (by omega)).1
    induction i with
    | zero => simp
    | succ i ih =>
      have := hstep (k - 1 - (i + 1)) (by omega)
      rw [show k - 1 - (i + 1) + 1 = k - 1 - i by omega] at this
      have := ih (by omega)
      rw [Nat.succ_mul]
      omega

end LeanProofs.GowersSzemeredi
