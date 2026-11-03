import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-! # Integer-like facts in a discretely ordered commutative ring

The carrier equations' zero arguments use three properties of `ℤ`: positive
elements are at least one, the only units are `±1`, and congruences modulo a
fixed `n` may be checked in `ZMod n`. Here they are proved for any linearly and
strictly ordered commutative ring that is discrete and admits division with
remainder by `n`, so the arguments also run in the ring of differences of a
nonstandard model of arithmetic. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.DiscreteOrderedRingFacts

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Discreteness: no element lies strictly between `0` and `1`. -/
def Discrete (R : Type*) [CommRing R] [LinearOrder R] : Prop := ∀ x : R, 0 < x → 1 ≤ x

theorem le_of_lt_add_one (hd : Discrete R) {x y : R} (h : x < y + 1) : x ≤ y := by
  by_contra hxy
  push_neg at hxy
  have := hd (x - y) (by linarith)
  linarith

theorem abs_ge_one (hd : Discrete R) {x : R} (hx : x ≠ 0) : 1 ≤ |x| :=
  hd _ (abs_pos.mpr hx)

/-- The only units are `±1`. -/
theorem eq_one_or_neg_one_of_mul_eq_one (hd : Discrete R) {x y : R} (h : x * y = 1) :
    x = 1 ∨ x = -1 := by
  have hx : x ≠ 0 := by rintro rfl; simp at h
  have hy : y ≠ 0 := by rintro rfl; simp at h
  have hxa := abs_ge_one hd hx
  have hya := abs_ge_one hd hy
  have hprod : |x| * |y| = 1 := by rw [← abs_mul, h, abs_one]
  have h1 : |x| = 1 := by nlinarith
  rcases abs_eq (zero_le_one : (0 : R) ≤ 1) |>.mp h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

section Residue
variable (n : ℕ) [NeZero n]

/-- Division with remainder by `n`. -/
def HasResidues (R : Type*) [CommRing R] : Prop :=
  ∀ x : R, ∃ q : R, ∃ r : ℕ, r < n ∧ x = n * q + r

variable {n}

theorem residue_unique (hd : Discrete R) {q q' : R} {r r' : ℕ} (hr : r < n) (hr' : r' < n)
    (h : (n : R) * q + r = n * q' + r') : r = r' := by
  have hn : (0 : R) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hrR : (r : R) < n := by exact_mod_cast hr
  have hr'R : (r' : R) < n := by exact_mod_cast hr'
  have hr0 : (0 : R) ≤ r := Nat.cast_nonneg r
  have hr'0 : (0 : R) ≤ r' := Nat.cast_nonneg r'
  have hq : q = q' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := mul_le_mul_of_nonneg_left (hd (q' - q) (by linarith)) hn.le
      linarith
    · have h1 := mul_le_mul_of_nonneg_left (hd (q - q') (by linarith)) hn.le
      linarith
  subst hq
  exact_mod_cast (add_left_cancel h)

variable (hd : Discrete R) (hres : HasResidues n R)
include hd hres

/-- The residue of `x` modulo `n`. -/
def residue (x : R) : ZMod n := ((hres x).choose_spec.choose : ℕ)

theorem residue_spec {x q : R} {r : ℕ} (hr : r < n) (hx : x = n * q + r) :
    residue hres x = r := by
  obtain ⟨hr0, hx0⟩ := (hres x).choose_spec.choose_spec
  have := residue_unique hd hr0 hr (hx0.symm.trans hx)
  unfold residue
  rw [this]

theorem residue_natCast_add (q : R) (m : ℕ) : residue hres ((n : R) * q + m) = m := by
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  have hm : ((m : ℕ) : R) = n * ((m / n : ℕ) : R) + ((m % n : ℕ) : R) := by
    have := Nat.div_add_mod m n
    exact_mod_cast this.symm
  rw [residue_spec hd hres (Nat.mod_lt m hn) (q := q + ((m / n : ℕ) : R))
    (by rw [hm]; ring)]
  exact ZMod.natCast_mod m n

/-- Reduction modulo `n` is a ring homomorphism. -/
def residueHom : R →+* ZMod n where
  toFun := residue hres
  map_one' := by
    have := residue_natCast_add hd hres 0 1
    simpa using this
  map_zero' := by
    have := residue_natCast_add hd hres 0 0
    simpa using this
  map_add' x y := by
    obtain ⟨q, r, hr, rfl⟩ := hres x
    obtain ⟨q', r', hr', rfl⟩ := hres y
    rw [residue_natCast_add hd hres, residue_natCast_add hd hres,
      show (n : R) * q + r + (n * q' + r') = n * (q + q') + ((r + r' : ℕ) : R) by push_cast; ring,
      residue_natCast_add hd hres]
    exact Nat.cast_add r r'
  map_mul' x y := by
    obtain ⟨q, r, hr, rfl⟩ := hres x
    obtain ⟨q', r', hr', rfl⟩ := hres y
    rw [residue_natCast_add hd hres, residue_natCast_add hd hres,
      show ((n : R) * q + r) * (n * q' + r') = n * (n * q * q' + q * r' + r * q') + ((r * r' : ℕ) : R) by
        push_cast; ring,
      residue_natCast_add hd hres]
    exact Nat.cast_mul r r'

end Residue

end DiophantineConsistency.DiscreteOrderedRingFacts
