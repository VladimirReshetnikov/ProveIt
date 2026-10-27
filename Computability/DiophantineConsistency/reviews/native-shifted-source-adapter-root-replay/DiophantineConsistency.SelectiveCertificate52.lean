import DiophantineConsistency.SelectiveQuadraticCoding
import Mathlib.Data.Fin.VecNotation

/-!
# The package-52 interior-regular selective weight certificate

The dummy coordinate has weight 81; one actual input has weight zero.
All 71 used padded pairs are isolated against all 528 unordered pairs.
The certificate is uniform for all row coefficients on this support.
It does not assert the native compiler or the complete nine-variable theorem.
-/

namespace DiophantineConsistency.SelectiveCertificate52

open SidonPositions SelectiveQuadraticCoding

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

def weights : Fin 32 → ℕ := ![81, 51, 169, 164, 28, 174, 146, 0, 32, 20, 24, 154, 45, 143, 140, 33, 141, 44, 123, 135, 11, 119, 148, 145, 18, 166, 1, 158, 25, 163, 29, 5]

def activePair : Fin 71 → PairIndex 31 :=
  ![⟨(0, 0), by decide⟩,
    ⟨(0, 1), by decide⟩,
    ⟨(0, 2), by decide⟩,
    ⟨(0, 3), by decide⟩,
    ⟨(0, 4), by decide⟩,
    ⟨(0, 5), by decide⟩,
    ⟨(0, 6), by decide⟩,
    ⟨(0, 7), by decide⟩,
    ⟨(0, 8), by decide⟩,
    ⟨(0, 9), by decide⟩,
    ⟨(0, 10), by decide⟩,
    ⟨(0, 11), by decide⟩,
    ⟨(0, 12), by decide⟩,
    ⟨(0, 13), by decide⟩,
    ⟨(0, 14), by decide⟩,
    ⟨(0, 15), by decide⟩,
    ⟨(0, 16), by decide⟩,
    ⟨(0, 17), by decide⟩,
    ⟨(0, 18), by decide⟩,
    ⟨(0, 19), by decide⟩,
    ⟨(0, 20), by decide⟩,
    ⟨(0, 21), by decide⟩,
    ⟨(0, 22), by decide⟩,
    ⟨(0, 23), by decide⟩,
    ⟨(0, 24), by decide⟩,
    ⟨(0, 25), by decide⟩,
    ⟨(0, 26), by decide⟩,
    ⟨(0, 27), by decide⟩,
    ⟨(0, 28), by decide⟩,
    ⟨(0, 29), by decide⟩,
    ⟨(0, 30), by decide⟩,
    ⟨(0, 31), by decide⟩,
    ⟨(1, 1), by decide⟩,
    ⟨(1, 2), by decide⟩,
    ⟨(1, 4), by decide⟩,
    ⟨(1, 11), by decide⟩,
    ⟨(1, 17), by decide⟩,
    ⟨(1, 25), by decide⟩,
    ⟨(2, 11), by decide⟩,
    ⟨(2, 17), by decide⟩,
    ⟨(2, 25), by decide⟩,
    ⟨(3, 11), by decide⟩,
    ⟨(3, 25), by decide⟩,
    ⟨(5, 5), by decide⟩,
    ⟨(5, 8), by decide⟩,
    ⟨(6, 18), by decide⟩,
    ⟨(7, 24), by decide⟩,
    ⟨(9, 20), by decide⟩,
    ⟨(10, 17), by decide⟩,
    ⟨(12, 12), by decide⟩,
    ⟨(13, 18), by decide⟩,
    ⟨(13, 19), by decide⟩,
    ⟨(13, 21), by decide⟩,
    ⟨(14, 18), by decide⟩,
    ⟨(14, 19), by decide⟩,
    ⟨(14, 21), by decide⟩,
    ⟨(15, 15), by decide⟩,
    ⟨(16, 21), by decide⟩,
    ⟨(18, 20), by decide⟩,
    ⟨(18, 22), by decide⟩,
    ⟨(19, 19), by decide⟩,
    ⟨(20, 20), by decide⟩,
    ⟨(20, 21), by decide⟩,
    ⟨(21, 21), by decide⟩,
    ⟨(21, 22), by decide⟩,
    ⟨(23, 23), by decide⟩,
    ⟨(24, 31), by decide⟩,
    ⟨(26, 31), by decide⟩,
    ⟨(27, 27), by decide⟩,
    ⟨(28, 30), by decide⟩,
    ⟨(29, 29), by decide⟩]

theorem active_isolated : ∀ k, Isolated weights (activePair k) := by
  unfold Isolated
  decide

theorem maximum_weight : ∀ i, weights i ≤ 174 := by decide

theorem dummy_weight : weights 0 = 81 := rfl

theorem input_zero_weight : weights 7 = 0 := rfl

def activeSupport : Finset (PairIndex 31) := Finset.univ.image activePair

theorem support_isolated (p : PairIndex 31) (hp : p ∈ activeSupport) :
    Isolated weights p := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
  exact active_isolated k

/-- Every coefficient family on the checked support has exact simultaneous
extraction at the delivered regular targets. Native row identification and
carry bounds are separate obligations. -/
theorem coeff_rows {R : Type*} [CommRing R]
    (s : Fin 22 → Finset (PairIndex 31)) (a : Fin 22 → PairIndex 31 → R)
    (u : Fin 32 → R) (hs : ∀ k p, p ∈ s k → p ∈ activeSupport) (l : Fin 22) :
    (encoded weights u ^ 2 * combined weights s a (fun k => 349 * (k.val + 1))).coeff
      (349 * (l.val + 1)) = 2 * rowValue (s l) (a l) u := by
  exact coeff_square_mul_regular weights 174 maximum_weight s a u
    (fun k p hp => support_isolated p (hs k p hp)) l

theorem final_target : regularTarget 174 21 = 7678 := rfl

#print axioms active_isolated
#print axioms coeff_rows

end DiophantineConsistency.SelectiveCertificate52
