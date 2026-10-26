import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
A checked geometric core for WangTiles942HelicalMarker and HelicalQuotient.
This file does not assert integration with the production 942-tile development.
The signed address is exactly the production convention.
-/
namespace NewProofStructures.HelicalCoordinates

def address (w H : ℕ) (x t : ℤ) : ZMod (w * H) :=
  ((-x - (w : ℤ) * t : ℤ) : ZMod (w * H))

/-- On a band of width w, equal addresses mean equal spatial sites and equal
    time classes modulo H. No coprimality premise is needed. -/
theorem address_eq_iff (w H : ℕ) (hw : 0 < w) (L x y t u : ℤ)
    (hx : -L ≤ x ∧ x < (w : ℤ) - L)
    (hy : -L ≤ y ∧ y < (w : ℤ) - L) :
    address w H x t = address w H y u ↔
      x = y ∧ (t : ZMod H) = (u : ZMod H) := by
  have hwz : 0 < (w : ℤ) := by exact_mod_cast hw
  rw [address, address, ZMod.intCast_eq_intCast_iff_dvd_sub]
  constructor
  · rintro ⟨k, hk⟩
    push_cast at hk
    have hxy : x - y = (w : ℤ) * ((H : ℤ) * k - t + u) := by
      nlinarith only [hk]
    have hd0 : -1 < (H : ℤ) * k - t + u := by
      by_contra h
      have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt h) hwz.le
      nlinarith only [hxy, hmul, hx.1, hy.2]
    have hd1 : (H : ℤ) * k - t + u < 1 := by
      by_contra h
      have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt h) hwz.le
      nlinarith only [hxy, hmul, hx.2, hy.1]
    have hd : (H : ℤ) * k - t + u = 0 := by omega
    have he : x = y := by rw [hd, mul_zero] at hxy; omega
    refine ⟨he, ?_⟩
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨-k, ?_⟩
    nlinarith only [hd]
  · rintro ⟨rfl, htu⟩
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub t u H).mp htu
    refine ⟨-k, ?_⟩
    push_cast
    nlinarith only [hk]

/-- The two coordinates used by the existing extension. -/
def representative (w : ℕ) (L x : ℤ) : ℤ := (x + L) % (w : ℤ) - L

def quotient (w : ℕ) (L x : ℤ) : ℤ := (x + L) / (w : ℤ)

/-- Normalization preserves the signed address. Band membership additionally needs w > 0. -/
theorem normalize_address (w H : ℕ) (L x t : ℤ) :
    address w H (representative w L x) (t + quotient w L x) =
      address w H x t := by
  have hd := Int.emod_add_mul_ediv (x + L) (w : ℤ)
  unfold address representative quotient
  congr 1
  nlinarith only [hd]

/-- Marker uniqueness becomes a specialization of the coordinate theorem. -/
theorem address_eq_zero_iff (w H : ℕ) (hw : 0 < w) (L x t : ℤ)
    (hL : 0 ≤ L ∧ L < (w : ℤ))
    (hx : -L ≤ x ∧ x < (w : ℤ) - L) :
    address w H x t = 0 ↔ x = 0 ∧ (t : ZMod H) = 0 := by
  simpa [address] using address_eq_iff w H hw L x 0 t 0 hx (by omega)

#print axioms address_eq_iff
#print axioms normalize_address
#print axioms address_eq_zero_iff
end NewProofStructures.HelicalCoordinates
