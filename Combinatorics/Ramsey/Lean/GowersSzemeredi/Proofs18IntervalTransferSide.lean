import GowersSzemeredi.Proofs18IntervalTransfer

/-! Declarations of `Proofs18IntervalTransfer` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The no-wrap transfer needed to turn the prime-cyclic conclusion of
Corollary 3.6 into a progression in the original integer set. -/
theorem hasNatAP_of_hasModAP_image {N n k : Nat} [NeZero N]
    (A : Finset Nat) (hA : A ⊆ Finset.Icc 1 n) (hsize : 2 * n < N)
    (hAP : HasModAP (A.image fun x : Nat => (x : ZMod N)) k) :
    HasNatAP A k := by
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
