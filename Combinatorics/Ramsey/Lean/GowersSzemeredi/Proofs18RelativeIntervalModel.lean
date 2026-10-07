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

/-- The image of the whole index interval is the corresponding modular AP. -/
theorem finiteIntervalImage_univ {N L : Nat} :
    finiteIntervalImage N (Finset.univ : Finset (Fin L)) = (modInterval N 0 L).carrier := by
  classical
  unfold finiteIntervalImage ModAP.carrier
  apply Finset.image_congr
  intro i _
  simp [modInterval]

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

/-- The support-relative cardinality identity survives every injective
interval embedding, without an L/N density factor. -/
theorem finiteIntervalImage_relative_card {N L : Nat} [NeZero N]
    (hL : L ≤ N) (B : Finset (Fin L)) (delta : Real)
    (hcard : (B.card : Real) = delta * L) :
    ((finiteIntervalImage N B).card : Real) = delta * (finiteIntervalImage N (Finset.univ : Finset (Fin L))).card := by
  simpa only [finiteIntervalImage_card hL, Finset.card_univ, Fintype.card_fin] using hcard

/-- The exact uniformity transfer for relative-balanced interval sets.
Only the ambient normalization changes; the relative density does not. -/
theorem relative_interval_uniform_iff {N M L k : Nat} [NeZero N] [NeZero M]
    (hN : (k + 2) * L ≤ N) (hM : (k + 2) * L ≤ M)
    (B : Finset (Fin L)) (delta alpha : Real) :
    UniformOfDegree (relativeBalanced (finiteIntervalImage N B) (finiteIntervalImage (L := L) N Finset.univ) delta) alpha k ↔
      UniformOfDegree (relativeBalanced (finiteIntervalImage M B) (finiteIntervalImage (L := L) M Finset.univ) delta)
        (alpha * ((N : Real) / M) ^ (k + 2)) k := by
  have hLN : L ≤ N := (Nat.le_mul_of_pos_left L (by omega)).trans hN
  have hLM : L ≤ M := (Nat.le_mul_of_pos_left L (by omega)).trans hM
  rw [relativeBalanced_finiteIntervalImage hLN, relativeBalanced_finiteIntervalImage hLM]
  exact intervalExtension_uniform_iff hN hM _ alpha

end LeanProofs.GowersSzemeredi
