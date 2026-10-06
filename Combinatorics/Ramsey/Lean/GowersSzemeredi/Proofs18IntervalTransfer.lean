import GowersSzemeredi.Definitions

/-!
# From short modular progressions to integer progressions

Section 18 ultimately needs progressions in an integer interval.  A modular
progression whose representatives all lie in `[1,n]`, with `2*n < N`, lifts
to an ordinary progression.  Its integer common difference may be negative;
reversing the order gives the positive difference required by `HasNatAP`.
No primality assumption or quantitative density-increment input is needed.
-/

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
  · by_cases hk0 : k = 0
    · subst k
      exact ⟨0, 1, by omega, by omega⟩
    · have hk1 : k = 1 := by omega
      refine ⟨f 0, 1, by omega, ?_⟩
      intro i hi
      have hi0 : i = 0 := by omega
      simpa [hi0] using (hf 0 (by omega)).1
  have hk2 : 2 ≤ k := by omega
  have h0 := hf 0 (by omega)
  have h1 := hf 1 (by omega)
  have hne : f 0 ≠ f 1 := by
    intro heq
    have heq' := congrArg (fun x : Nat => (x : ZMod N)) heq
    rw [h0.2.2, h1.2.2] at heq'
    simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, add_zero] at heq'
    exact hd (add_left_cancel (heq'.symm.trans (add_zero a).symm))
  have hstep (i : Nat) (hi : i + 1 < k) :
      f (i + 1) + f 0 = f i + f 1 := by
    have hfi := hf i (by omega)
    have hfi1 := hf (i + 1) hi
    have heq : ((f (i + 1) + f 0 : Nat) : ZMod N) =
        ((f i + f 1 : Nat) : ZMod N) := by
      push_cast
      rw [hfi1.2.2, h0.2.2, hfi.2.2, h1.2.2]
      push_cast
      ring
    have hl : f (i + 1) + f 0 < N := by omega
    have hr : f i + f 1 < N := by omega
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ N).mp heq
    simpa only [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] using hmod
  rcases lt_or_gt_of_ne hne with hinc | hdec
  · have hformula (i : Nat) (hi : i < k) :
        f i = f 0 + i * (f 1 - f 0) := by
      induction i with
      | zero => simp
      | succ i ih =>
        have hrec := hstep i hi
        have hind := ih (by omega)
        rw [Nat.succ_mul]
        omega
    refine ⟨f 0, f 1 - f 0, by omega, ?_⟩
    intro i hi
    rw [← hformula i hi]
    exact (hf i hi).1
  · have hformula (i : Nat) (hi : i < k) :
        f (k - 1 - i) = f (k - 1) + i * (f 0 - f 1) := by
      induction i with
      | zero => simp
      | succ i ih =>
        have hindex : k - 1 - (i + 1) + 1 = k - 1 - i := by omega
        have hrec := hstep (k - 1 - (i + 1)) (by omega)
        rw [hindex] at hrec
        have hind := ih (by omega)
        rw [Nat.succ_mul]
        omega
    refine ⟨f (k - 1), f 0 - f 1, by omega, ?_⟩
    intro i hi
    rw [← hformula i hi]
    exact (hf (k - 1 - i) (by omega)).1

/-- The no-wrap transfer needed to turn the prime-cyclic conclusion of
Corollary 3.6 into a progression in the original integer set. -/
theorem hasNatAP_of_hasModAP_image {N n k : Nat} [NeZero N]
    (A : Finset Nat) (hA : A ⊆ Finset.Icc 1 n) (hsize : 2 * n < N)
    (hAP : HasModAP (A.image fun x : Nat => (x : ZMod N)) k) :
    HasNatAP A k := by
  classical
  obtain ⟨a, d, hd, hAP⟩ := hAP
  apply hasNatAP_of_short_modular_sequence A (fun i => (a + (i : ZMod N) * d).val)
    a d (bne_iff_ne.mp hd) hsize
  intro i hi
  obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp (hAP i hi)
  have hxn := (Finset.mem_Icc.mp (hA hx)).2
  have hxN : x < N := by omega
  have hval : (a + (i : ZMod N) * d).val = x := by
    rw [← hxeq, ZMod.val_natCast_of_lt hxN]
  rw [hval]
  exact ⟨hx, hxn, hxeq⟩

end LeanProofs.GowersSzemeredi
