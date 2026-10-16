import GowersSzemeredi.Proofs18RelativeBalance
import GowersSzemeredi.Proofs18IntervalCubeEnergy

/-! An interval set and its relative balance in different ambient moduli.
The relative density is computed on Fin L and is unchanged by embedding. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Embed a set of indices from [0,L) into a cyclic group. -/
def finiteIntervalImage {L : Nat} (N : Nat) (B : Finset (Fin L)) : Finset (ZMod N) :=
  B.image (fun i : Fin L ↦ ((i : Nat) : ZMod N))

/-- Casting a short interval does not identify distinct indices. -/
theorem finiteInterval_cast_injective {N L : Nat} [NeZero N] (hL : L ≤ N) :
    Function.Injective (fun i : Fin L ↦ ((i : Nat) : ZMod N)) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg ZMod.val hij
  simpa only [ZMod.val_natCast_of_lt (i.isLt.trans_le hL),
    ZMod.val_natCast_of_lt (j.isLt.trans_le hL)] using hv

theorem finiteIntervalImage_card {N L : Nat} [NeZero N] (hL : L ≤ N) (B : Finset (Fin L)) :
    (finiteIntervalImage N B).card = B.card :=
  Finset.card_image_iff.mpr (finiteInterval_cast_injective hL).injOn

@[simp] theorem finiteIntervalImage_mem_natCast {N L : Nat} [NeZero N]
    (hL : L ≤ N) (B : Finset (Fin L)) (i : Fin L) :
    ((i : Nat) : ZMod N) ∈ finiteIntervalImage N B ↔ i ∈ B := by
  classical
  constructor
  · rintro hx
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hx
    exact (finiteInterval_cast_injective hL hji) ▸ hj
  · intro hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

theorem finiteIntervalImage_subset {N L : Nat} (B : Finset (Fin L)) :
    finiteIntervalImage N B ⊆ finiteIntervalImage (L := L) N Finset.univ :=
  Finset.image_subset_image (Finset.subset_univ _)

theorem finiteIntervalImage_val_lt {N L : Nat} [NeZero N]
    (hL : L ≤ N) (B : Finset (Fin L)) {x : ZMod N} (hx : x ∈ finiteIntervalImage N B) :
    x.val < L := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  simpa only [ZMod.val_natCast_of_lt (i.isLt.trans_le hL)] using i.isLt

/-- The finite relative-balanced function before choosing an ambient modulus. -/
def finiteIntervalBalance {L : Nat} (B : Finset (Fin L)) (delta : Real) : Fin L → Complex :=
  fun i ↦ (((if i ∈ B then 1 else 0) - delta : Real) : Complex)

/-- The cyclic relative balance is exactly extension by zero of the same
finite function, with no change in its density parameter. -/
theorem relativeBalanced_finiteIntervalImage {N L : Nat} [NeZero N]
    (hL : L ≤ N) (B : Finset (Fin L)) (delta : Real) :
    relativeBalanced (finiteIntervalImage N B) (finiteIntervalImage (L := L) N Finset.univ) delta =
      intervalExtension N (finiteIntervalBalance B delta) := by
  classical
  funext x
  by_cases hx : x.val < L
  · let i : Fin L := ⟨x.val, hx⟩
    have hi : ((i : Nat) : ZMod N) = x := ZMod.natCast_zmod_val x
    rw [← hi, intervalExtension_natCast hL]
    simp only [relativeBalanced, relativeBalancedReal, finiteIntervalImage_mem_natCast hL,
      Finset.mem_univ, if_true, mul_one, finiteIntervalBalance]
  · have hxA : x ∉ finiteIntervalImage N B := fun h ↦ hx (finiteIntervalImage_val_lt hL B h)
    have hxS : x ∉ finiteIntervalImage N (Finset.univ : Finset (Fin L)) :=
      fun h ↦ hx (finiteIntervalImage_val_lt hL Finset.univ h)
    simp [relativeBalanced, relativeBalancedReal, intervalExtension, hxA, hxS, hx]

end LeanProofs.GowersSzemeredi
