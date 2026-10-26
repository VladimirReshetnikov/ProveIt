import DiophantineConsistency.ControllerOrbitTransport

namespace DiophantineConsistency.ControllerOrbitTransportChecks

open ControllerIntervalSums ControllerOrbitTransport
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

-- Wrapped coordinates require the C0 multiplier to define an additive map.
example : (4 : ZMod 5)+3 = 2 ∧ (4 : ZMod 15)+3 ≠ 2 := by decide
example : scaledCoordinate 3 5 ((4 : ZMod 5)+3) =
    scaledCoordinate 3 5 4+scaledCoordinate 3 5 3 := map_add _ _ _
example : scaledCoordinate 3 5 (2 : ZMod 5) = 6 := by
  rw [scaledCoordinate_val]
  decide

-- Both signs of integer representatives give the same scaled residue.
example : scaledCoordinate 3 5 (-1 : ZMod 5) = 12 := by
  rw [show (-1 : ZMod 5) = ((-1 : ℤ) : ZMod 5) from rfl,
    scaledCoordinate_intCast]
  decide

-- A genuine reindexing of the domain, rather than an assumed target subset.
private def reindex (z : ZMod 5) : ZMod 5 := z+1
private theorem reindex_injective : Function.Injective reindex := by
  intro x y h
  exact add_right_cancel h
private def liftedWeight (x : ZMod 5) : ℤ := 1+3*((x-1).val : ℤ)

private theorem liftedWeight_affine (z : ZMod 5) :
    (liftedWeight (reindex z) : ZMod (3*5)) = 1+3*(z.val : ZMod (3*5)) := by
  simp only [liftedWeight,reindex,add_sub_cancel_right,Int.cast_add,Int.cast_one,
    Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]

example : (targetSubset reindex 3 (by decide : Nat.Coprime 3 5) 2).card = 3 ∧
    (∑ x ∈ targetSubset reindex 3 (by decide : Nat.Coprime 3 5) 2, liftedWeight x)
      ≡ 9 [ZMOD 15] := by
  refine ⟨targetSubset_card reindex reindex_injective 3 (by decide) (by decide) 2,?_⟩
  have hs := targetSubset_integer_sum 3 reindex reindex_injective liftedWeight
    liftedWeight_affine 3 (by decide) (by decide) (2 : ZMod 5)
  rw [show (2 : ZMod 5).val = 2 by decide] at hs
  norm_num at hs
  exact hs

-- Integer weights may have arbitrary multiples of the entire modulus added.
example (z : ZMod 5) :
    (((1+3*(z.val : ℤ))+15*7 : ℤ) : ZMod 15) = 1+3*(z.val : ZMod 15) := by
  simp only [Int.cast_add,Int.cast_mul,Int.cast_one,Int.cast_ofNat,Int.cast_natCast]
  rw [show (15 : ZMod 15) = 0 by decide,zero_mul,add_zero]

-- C0=0 is retained: ZMod(C0*T)=ZMod0, and the coordinate map vanishes.
example (T : ℕ) (z : ZMod T) : scaledCoordinate 0 T z = 0 :=
  scaledCoordinate_zero T z

example {T : ℕ} [NeZero T] (a : ℕ) (h : Nat.Coprime a T)
    (ha : a ≤ T) (u : ZMod T) :
    (∑ _x ∈ targetSubset (id : ZMod T → ZMod T) a h u, (1 : ℤ)) ≡
      (a : ℤ) [ZMOD 0] := by
  simpa only [Nat.zero_mul,Nat.cast_zero,Int.cast_zero,zero_mul,add_zero] using
    targetSubset_integer_sum 0 id Function.injective_id (fun _ => (1 : ℤ))
      (by intro z; simp) a h ha u

-- Both possible lengths for T=1 retain their actual cardinality.
example (u : ZMod 1) :
    (targetSubset (id : ZMod 1 → ZMod 1) 0 (by decide) u).card = 0 ∧
    (targetSubset (id : ZMod 1 → ZMod 1) 1 (by decide) u).card = 1 :=
  ⟨targetSubset_card id Function.injective_id 0 (by decide) (by decide) u,
    targetSubset_card id Function.injective_id 1 (by decide) (by decide) u⟩

-- Dropping the injection would collapse the cardinality.
example : ((interval (4 : ZMod 5) 3).image (fun _ => (0 : ℕ))).card = 1 ∧
    (interval (4 : ZMod 5) 3).card = 3 := by decide

-- The full symbolic endpoint requests an affine coordinate injection,
-- but neither a target-subset witness nor a concrete power-orbit assumption.
example {T : ℕ} [NeZero T] {α : Type*} [DecidableEq α]
    (C0 : ℕ) (e : ZMod T → α) (he : Function.Injective e) (w : α → ℤ)
    (hw : ∀ z, (w (e z) : ZMod (C0*T)) =
      1+(C0 : ZMod (C0*T))*(z.val : ZMod (C0*T)))
    (a : ℕ) (h : Nat.Coprime a T) (ha : a ≤ T) (u : ZMod T) :
    ∃ s : Finset α, s.card = a ∧
      (∑ x ∈ s, w x) ≡ (a : ℤ)+(C0 : ℤ)*(u.val : ℤ) [ZMOD (C0*T : ℕ)] :=
  exists_subset_integer_sum C0 e he w hw a h ha u

#print axioms targetSubset_card
#print axioms targetSubset_sum
#print axioms exists_subset_affine_sum
#print axioms scaledCoordinate_intCast
#print axioms scaledCoordinate_val
#print axioms scaledCoordinate_zero
#print axioms targetSubset_modular_sum
#print axioms targetSubset_integer_sum
#print axioms exists_subset_integer_sum

end DiophantineConsistency.ControllerOrbitTransportChecks
