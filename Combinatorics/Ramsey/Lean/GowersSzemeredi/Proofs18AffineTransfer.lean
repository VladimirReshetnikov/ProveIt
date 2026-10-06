import GowersSzemeredi.Proofs18IntervalTransfer

/-!
# Affine transport for the density-increment iteration

Index a proper modular progression by an ordinary integer interval.  Pulling
back a set preserves its relative cardinality, and a progression found in a
sufficiently large new cyclic model transports back to the original set.
The old modulus need not be prime: properness of the original progression
already prevents the transported common difference from vanishing.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Parametrization of a modular progression by natural indices. -/
def ModAP.index {N : Nat} (P : ModAP N) (i : Nat) : ZMod N :=
  P.start + (i : ZMod N) * P.step

/-- A proper modular progression has an injective index parametrization. -/
theorem ModAP.index_injOn {N : Nat} (P : ModAP N) (hP : P.IsProper) :
    Set.InjOn P.index (Finset.range P.length) := by
  classical
  have hcard : (Finset.univ.image
      (fun i : Fin P.length => P.start + (i : Nat) * P.step)).card =
      (Finset.univ : Finset (Fin P.length)).card := by
    simpa only [ModAP.IsProper, ModAP.carrier, Finset.card_univ, Fintype.card_fin] using hP
  have hinj := Finset.card_image_iff.mp hcard
  intro i hi j hj hij
  have h := hinj (Finset.mem_univ (⟨i, Finset.mem_range.mp hi⟩ : Fin P.length))
    (Finset.mem_univ (⟨j, Finset.mem_range.mp hj⟩ : Fin P.length)) hij
  exact congrArg Fin.val h

/-- The index set of `A` on `P`. -/
def ModAP.pullback {N : Nat} (P : ModAP N) (A : Finset (ZMod N)) : Finset Nat :=
  (Finset.range P.length).filter fun i => P.index i ∈ A

@[simp] theorem ModAP.mem_pullback {N : Nat} (P : ModAP N)
    (A : Finset (ZMod N)) (i : Nat) :
    i ∈ P.pullback A ↔ i < P.length ∧ P.index i ∈ A := by
  classical
  simp [ModAP.pullback]

theorem ModAP.image_pullback {N : Nat} (P : ModAP N) (A : Finset (ZMod N)) :
    (P.pullback A).image P.index = A ∩ P.carrier := by
  classical
  ext x
  simp only [Finset.mem_image, ModAP.mem_pullback, Finset.mem_inter]
  constructor
  · rintro ⟨i, ⟨hi, hA⟩, rfl⟩
    refine ⟨hA, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  · rintro ⟨hxA, hxP⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxP
    exact ⟨i, ⟨i.isLt, hxA⟩, rfl⟩

/-- Reindexing preserves the cardinality used in the density increment. -/
theorem ModAP.card_pullback {N : Nat} (P : ModAP N) (hP : P.IsProper)
    (A : Finset (ZMod N)) : (P.pullback A).card = (A ∩ P.carrier).card := by
  classical
  rw [← P.image_pullback A]
  symm
  apply Finset.card_image_iff.mpr
  exact (P.index_injOn hP).mono (Finset.filter_subset _ _)

/-- Injecting the index set into a larger cyclic group preserves cardinality.
This concerns cardinality, not density relative to the new modulus. -/
theorem ModAP.card_cyclic_pullback {N M : Nat} [NeZero M]
    (P : ModAP N) (hP : P.IsProper) (A : Finset (ZMod N))
    (hsize : P.length ≤ M) :
    ((P.pullback A).image fun i : Nat => (i : ZMod M)).card =
      (A ∩ P.carrier).card := by
  classical
  rw [← P.card_pullback hP A]
  apply Finset.card_image_iff.mpr
  intro i hi j hj hij
  have hiM := lt_of_lt_of_le ((P.mem_pullback A i).mp hi).1 hsize
  have hjM := lt_of_lt_of_le ((P.mem_pullback A j).mp hj).1 hsize
  have h := congrArg ZMod.val hij
  simpa only [ZMod.val_natCast_of_lt hiM, ZMod.val_natCast_of_lt hjM] using h

/-- The exact density in the new cyclic model. Reindexing preserves the
numerator, but changing the ambient modulus changes the denominator. -/
theorem ModAP.density_cyclic_pullback {N M : Nat} [NeZero M]
    (P : ModAP N) (hP : P.IsProper) (A : Finset (ZMod N))
    (hsize : P.length ≤ M) :
    density ((P.pullback A).image fun i : Nat => (i : ZMod M)) =
      (P.length : Real) / M * ((A ∩ P.carrier).card / (P.length : Real)) := by
  classical
  rw [density, P.card_cyclic_pullback hP A hsize]
  by_cases hL : P.length = 0
  · have hempty : P.pullback A = ∅ := by simp [ModAP.pullback, hL]
    have hcard : (A ∩ P.carrier).card = 0 := by
      rw [← P.card_pullback hP A, hempty, Finset.card_empty]
    simp [hL, hcard]
  · have hL' : (P.length : Real) ≠ 0 := by exact_mod_cast hL
    have hM : (M : Real) ≠ 0 := by exact_mod_cast NeZero.ne M
    field_simp

/-- Ordinary progressions in the index set transport to nonconstant modular
progressions. Properness suffices to make the new common difference nonzero. -/
theorem ModAP.hasModAP_of_hasNatAP_pullback {N k : Nat}
    (P : ModAP N) (hP : P.IsProper) (A : Finset (ZMod N)) (hk : 2 ≤ k)
    (hAP : HasNatAP (P.pullback A) k) : HasModAP A k := by
  classical
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
  classical
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
