import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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

/-- The spatial canonical band as a type. -/
def Band (w : ℕ) (L : ℤ) := {x : ℤ // -L ≤ x ∧ x < (w : ℤ) - L}

/-- Address a band site at a finite time. -/
def bandAddress (w H : ℕ) (L : ℤ) (p : Band w L × ZMod H) : ZMod (w * H) :=
  address w H p.1.val (p.2.val : ℤ)

theorem bandAddress_injective (w H : ℕ) (hw : 0 < w) (L : ℤ)
    [NeZero H] : Function.Injective (bandAddress w H L) := by
  intro p q h
  have he := (address_eq_iff w H hw L p.1.val q.1.val p.2.val q.2.val
    p.1.property q.1.property).mp h
  apply Prod.ext
  · exact Subtype.ext he.1
  · simpa only [Int.cast_natCast, ZMod.natCast_val] using he.2

theorem bandAddress_surjective (w H : ℕ) (hw : 0 < w) (hH : 0 < H) (L : ℤ) :
    Function.Surjective (bandAddress w H L) := by
  letI : NeZero H := ⟨Nat.ne_of_gt hH⟩
  letI : NeZero (w * H) := ⟨Nat.ne_of_gt (Nat.mul_pos hw hH)⟩
  intro z
  let x : ℤ := -(z.val : ℤ)
  have hwz : 0 < (w : ℤ) := by exact_mod_cast hw
  have hb : -L ≤ representative w L x ∧
      representative w L x < (w : ℤ) - L := by
    have h0 := Int.emod_nonneg (x + L) (ne_of_gt hwz)
    have h1 := Int.emod_lt_of_pos (x + L) hwz
    unfold representative
    omega
  refine ⟨(⟨representative w L x, hb⟩, (quotient w L x : ZMod H)), ?_⟩
  unfold bandAddress
  have ht := (address_eq_iff w H hw L (representative w L x)
    (representative w L x) ((quotient w L x : ZMod H).val : ℤ)
    (quotient w L x) hb hb).mpr
      ⟨rfl, by simp only [Int.cast_natCast, ZMod.natCast_val]⟩
  dsimp only
  rw [ht]
  have hn := normalize_address w H L x 0
  simp only [zero_add] at hn
  rw [hn]
  simp [address, x]

/-- A full coordinate equivalence, including surjectivity. Coprimality is absent. -/
noncomputable def bandEquiv (w H : ℕ) (hw : 0 < w) (hH : 0 < H) (L : ℤ) :
    Band w L × ZMod H ≃ ZMod (w * H) := by
  letI : NeZero H := ⟨Nat.ne_of_gt hH⟩
  exact Equiv.ofBijective (bandAddress w H L)
    ⟨bandAddress_injective w H hw L, bandAddress_surjective w H hw hH L⟩

#print axioms address_eq_iff
#print axioms normalize_address
#print axioms address_eq_zero_iff
#print axioms bandAddress_injective
#print axioms bandAddress_surjective
#print axioms bandEquiv
end NewProofStructures.HelicalCoordinates
