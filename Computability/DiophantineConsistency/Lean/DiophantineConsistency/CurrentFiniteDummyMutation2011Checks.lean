import DiophantineConsistency.CurrentFiniteDummyMutation2011

namespace DiophantineConsistency.CurrentFiniteDummyMutation2011Checks

open CurrentMasks2011 CurrentWordConstruction2011 CurrentWordClause2011
  CurrentDummyMutation2011 CurrentFiniteDummyMutation2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local irreducible] CurrentKernel2011.K

-- Sets retain Boolean controls: inserting an enabled cell again has no effect.
example {N : ℕ} (S : Finset (ZMod N)) (j : ZMod N) :
    enabled (insert j (insert j S)) = enabled (insert j S) := by
  rw [Finset.insert_idem]
example {N : ℕ} (S : Finset (ZMod N)) (j : ZMod N) :
    powerSum (insert j (insert j S)) = powerSum (insert j S) := by
  rw [Finset.insert_idem]
example {N : ℕ} (j : ZMod N) : enabled ({j} : Finset (ZMod N)) j = 1 := by
  simp only [enabled,Finset.mem_singleton_self,if_true]
example {N : ℕ} (j : ZMod N) :
    totalIncrement ({j} : Finset (ZMod N)) = dummyIncrement j := by
  rw [show ({j} : Finset (ZMod N)) = insert j ∅ from rfl,
    totalIncrement_insert _ _ (Finset.notMem_empty j),totalIncrement_empty,Nat.zero_add]
example {N : ℕ} (S : Finset (ZMod N)) (m : ℕ) :
    (powerSum S : ZMod m) = ∑ j ∈ S, ((radix : ZMod m)^2011)^j.val :=
  powerSum_cast (ZMod m) S

-- Safety remains a condition on each actual canonical representative.
-- At N=1 it forces the support to be empty, rather than hiding an N>1 premise.
example (S : Finset (ZMod 1)) (s : ℕ)
    (hsafe : ∀ j ∈ S, j.val+1 < 1 ∧ j.val+s < 1) : S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have h := (hsafe j hj).1
  omega
example : ¬∀ j ∈ ({2} : Finset (ZMod 3)), j.val+1 < 3 ∧ j.val+1 < 3 := by
  intro h
  have hf := (h 2 (Finset.mem_singleton_self 2)).1
  exact (by decide : ¬(2 : ZMod 3).val+1 < 3) hf

-- The source identity needs no Boolean marker or safety hypotheses.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (marker : ZMod N → ℕ)
    (S : Finset (ZMod N)) :
    NativeCyclicConvolution.word radix (word a (enabled S) marker) =
      NativeCyclicConvolution.word radix (word a (fun _ => 0) marker)+totalIncrement S :=
  source_enabled_sum a marker S

-- A genuine two-position update: both old and new bounded normalizations
-- are constructed from arbitrary actual tile data. No F increment, high
-- mask, matching, marked origin or modular-target equation is assumed.
example (a : ZMod 3 → Fin 942) (marker : ZMod 3 → ℕ) (hm : ∀ j, marker j ≤ 1) :
    ∃ k f k' f' : ZMod (3*2011) → ℕ,
      CurrentCarryConstruction2011.Facts (word a (fun _ => 0) marker)
        (displacement 1) k f ∧
      CurrentCarryConstruction2011.Facts (word a (enabled {0,1}) marker)
        (displacement 1) k' f' ∧
      NativeCyclicConvolution.word radix (word a (enabled {0,1}) marker) =
        NativeCyclicConvolution.word radix (word a (fun _ => 0) marker)+
          totalIncrement ({0,1} : Finset (ZMod 3)) ∧
      NativeCyclicConvolution.word radix f' = NativeCyclicConvolution.word radix f+
        (CurrentKernel2011.K+2^(displacement 1))*totalIncrement ({0,1} : Finset (ZMod 3)) := by
  obtain ⟨k,f,hf⟩ := CurrentCarryConstruction2011.exists_assembled_normalization
    a (fun _ => 0) marker (by intro; decide) hm (displacement 1)
  have hs : ∀ j ∈ ({0,1} : Finset (ZMod 3)), j.val+1 < 3 ∧ j.val+1 < 3 := by
    intro j hj
    rcases Finset.mem_insert.mp hj with hj | hj
    · subst j
      decide
    · have h : j = 1 := Finset.mem_singleton.mp hj
      subst j
      decide
  obtain ⟨k',f',hf',hC,hF⟩ := exists_finite_normalized_increment
    a marker hm 1 {0,1} hs k f hf
  exact ⟨k,f,k',f',hf,hf',hC,hF⟩

-- First derive the empty-support specialization symbolically; this avoids
-- reducing closed large word lengths during proof conversion at N=1.
private theorem empty_normalized_eq {N : ℕ} [NeZero N]
    (a : ZMod N → Fin 942) (marker : ZMod N → ℕ) (hm : ∀ j, marker j ≤ 1)
    (s : ℕ) (k f k' f' : ZMod (N*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (word a (fun _ => 0) marker)
      (displacement s) k f)
    (hf' : CurrentCarryConstruction2011.Facts (word a (enabled ∅) marker)
      (displacement s) k' f') :
    NativeCyclicConvolution.word radix f' = NativeCyclicConvolution.word radix f := by
  simpa only [totalIncrement_empty,Nat.mul_zero,Nat.add_zero] using
    finite_normalized_increment a marker hm s ∅ (by simp) k f k' f' hf hf'

-- Empty support works at N=1 and arbitrary whole-cell displacement, even
-- when two independently supplied bounded normalizations are used.
example (a : ZMod 1 → Fin 942) (marker : ZMod 1 → ℕ) (hm : ∀ j, marker j ≤ 1)
    (s : ℕ) (k f k' f' : ZMod (1*2011) → ℕ)
    (hf : CurrentCarryConstruction2011.Facts (word a (fun _ => 0) marker)
      (displacement s) k f)
    (hf' : CurrentCarryConstruction2011.Facts (word a (enabled ∅) marker)
      (displacement s) k' f') :
    NativeCyclicConvolution.word radix f' = NativeCyclicConvolution.word radix f :=
  empty_normalized_eq a marker hm s k f k' f' hf hf'

#print axioms enabled_boolean
#print axioms enabled_empty
#print axioms enabled_not_mem
#print axioms enabled_insert
#print axioms powerSum_empty
#print axioms powerSum_insert
#print axioms totalIncrement_empty
#print axioms totalIncrement_insert
#print axioms powerSum_cast
#print axioms source_enabled_sum
#print axioms finite_normalized_increment
#print axioms exists_finite_normalized_increment
#print axioms finite_rank_decrement

end DiophantineConsistency.CurrentFiniteDummyMutation2011Checks
