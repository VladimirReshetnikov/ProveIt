import GowersSzemeredi.Proofs18AffineTransfer

/-! Declarations of `Proofs18AffineTransfer` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem ModAP.image_pullback {N : Nat} (P : ModAP N) (A : Finset (ZMod N)) :
    (P.pullback A).image P.index = A ∩ P.carrier := by
  ext x
  simp only [Finset.mem_image, ModAP.mem_pullback, Finset.mem_inter]
  constructor
  · rintro ⟨i, ⟨hi, hA⟩, rfl⟩
    exact ⟨hA, Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩⟩
  · rintro ⟨hxA, hxP⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxP
    exact ⟨i, ⟨i.isLt, hxA⟩, rfl⟩

/-- Reindexing preserves the cardinality used in the density increment. -/
theorem ModAP.card_pullback {N : Nat} (P : ModAP N) (hP : P.IsProper)
    (A : Finset (ZMod N)) : (P.pullback A).card = (A ∩ P.carrier).card := by
  rw [← P.image_pullback A]
  symm
  exact Finset.card_image_iff.mpr ((P.index_injOn hP).mono (Finset.filter_subset _ _))

/-- Injecting the index set into a larger cyclic group preserves cardinality.
This concerns cardinality, not density relative to the new modulus. -/
theorem ModAP.card_cyclic_pullback {N M : Nat} [NeZero M]
    (P : ModAP N) (hP : P.IsProper) (A : Finset (ZMod N))
    (hsize : P.length ≤ M) :
    ((P.pullback A).image fun i : Nat => (i : ZMod M)).card =
      (A ∩ P.carrier).card := by
  rw [← P.card_pullback hP A]
  apply Finset.card_image_iff.mpr
  intro i hi j hj hij
  have hiM := lt_of_lt_of_le ((P.mem_pullback A i).mp hi).1 hsize
  have hjM := lt_of_lt_of_le ((P.mem_pullback A j).mp hj).1 hsize
  have h := congrArg ZMod.val hij
  simpa only [ZMod.val_natCast_of_lt hiM, ZMod.val_natCast_of_lt hjM] using h

/-- Ordinary progressions in the index set transport to nonconstant modular
progressions. Properness suffices to make the new common difference nonzero. -/
theorem ModAP.hasModAP_of_hasNatAP_pullback {N k : Nat}
    (P : ModAP N) (hP : P.IsProper) (A : Finset (ZMod N)) (hk : 2 ≤ k)
    (hAP : HasNatAP (P.pullback A) k) : HasModAP A k := by
  obtain ⟨a, d, hd, hAP⟩ := hAP
  have h0 := (P.mem_pullback A a).mp (by simpa using hAP 0 (by omega))
  have h1 := (P.mem_pullback A (a + d)).mp (by simpa using hAP 1 (by omega))
  have hdne : (d : ZMod N) * P.step ≠ 0 := by
    intro hzero
    have heq : P.index (a + d) = P.index a := by
      simp [ModAP.index, Nat.cast_add, add_mul, hzero]
    have ha := P.index_injOn hP
      (Finset.mem_range.mpr h1.1) (Finset.mem_range.mpr h0.1) heq
    omega
  refine ⟨P.index a, (d : ZMod N) * P.step, bne_iff_ne.mpr hdne, ?_⟩
  intro i hi
  have hmem := ((P.mem_pullback A (a + i * d)).mp (hAP i hi)).2
  convert hmem using 1
  simp only [ModAP.index, Nat.cast_add, Nat.cast_mul]
  ring

/-- A modular progression in a new cyclic model of the index set can be
returned to the original modulus, provided the new model is large enough to
exclude wrapping. This is the combinatorial transfer in Section 18. -/
theorem ModAP.hasModAP_of_cyclic_pullback {N M k : Nat} [NeZero M]
    (P : ModAP N) (hP : P.IsProper) (A : Finset (ZMod N)) (hk : 2 ≤ k)
    (hsize : 2 * P.length < M)
    (hAP : HasModAP ((P.pullback A).image fun i : Nat => (i : ZMod M)) k) :
    HasModAP A k := by
  obtain ⟨a, d, hd, hAP⟩ := hAP
  have hnat : HasNatAP (P.pullback A) k := by
    apply hasNatAP_of_short_modular_sequence (P.pullback A)
      (fun i => (a + (i : ZMod M) * d).val) a d (bne_iff_ne.mp hd) hsize
    intro i hi
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp (hAP i hi)
    have hxL := ((P.mem_pullback A x).mp hx).1
    have hxM : x < M := by omega
    have hval : (a + (i : ZMod M) * d).val = x := by
      rw [← hxeq, ZMod.val_natCast_of_lt hxM]
    rw [hval]
    exact ⟨hx, hxL.le, hxeq⟩
  exact P.hasModAP_of_hasNatAP_pullback hP A hk hnat

end LeanProofs.GowersSzemeredi
