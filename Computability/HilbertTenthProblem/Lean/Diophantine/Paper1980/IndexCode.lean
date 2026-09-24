import Mathlib.Tactic

/-!
# Jones 1980, the single-parameter index

The announcement indexes the r.e. sets by three parameters `z, u, y`, and
remarks that a single parameter `v` may be used instead by adjoining the
equation `v = ((zuy)² + u)² + y` and regarding `z, u, y` as unknowns.  The
corrected edition's editorial footnote states that this coding is injective on
positive-integer triples.  Here that footnote is proved: the code determines
the triple, so the one-parameter indexing is as effective as the three-parameter
one.  (The article gives the equation without comment.)
-/

namespace Jones1980

/-- The one-parameter index `v = ((zuy)² + u)² + y` of the 1980 announcement. -/
def indexCode (z u y : ℕ) : ℕ := ((z * u * y) ^ 2 + u) ^ 2 + y

/-- A square plus a remainder at most twice the root determines both. -/
theorem sq_add_eq_iff {A B y y' : ℕ} (hy : y ≤ 2 * A) (hy' : y' ≤ 2 * B)
    (h : A ^ 2 + y = B ^ 2 + y') : A = B ∧ y = y' := by
  have hAB : A = B := by
    rcases lt_trichotomy A B with hlt | heq | hgt
    · exfalso
      have : (A + 1) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hlt 2
      nlinarith
    · exact heq
    · exfalso
      have : (B + 1) ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left hgt 2
      nlinarith
  subst hAB
  exact ⟨rfl, by omega⟩

/-- The index code is injective on positive triples. -/
theorem indexCode_injective {z u y z' u' y' : ℕ}
    (hz : 0 < z) (hu : 0 < u) (hy : 0 < y) (hz' : 0 < z') (hu' : 0 < u') (hy' : 0 < y')
    (h : indexCode z u y = indexCode z' u' y') : z = z' ∧ u = u' ∧ y = y' := by
  unfold indexCode at h
  -- `y ≤ zuy ≤ (zuy)²`, so `y` is a remainder below the next square
  have hprod : y ≤ z * u * y := Nat.le_mul_of_pos_left y (Nat.mul_pos hz hu)
  have hprod' : y' ≤ z' * u' * y' := Nat.le_mul_of_pos_left y' (Nat.mul_pos hz' hu')
  have hsq : z * u * y ≤ (z * u * y) ^ 2 := by nlinarith
  have hsq' : z' * u' * y' ≤ (z' * u' * y') ^ 2 := by nlinarith
  obtain ⟨h1, hyy⟩ := sq_add_eq_iff (A := (z * u * y) ^ 2 + u) (B := (z' * u' * y') ^ 2 + u')
    (by omega) (by omega) h
  -- `u ≤ zuy ≤ (zuy)²` likewise
  have hu1 : u ≤ z * u * y := by
    calc u = 1 * u * 1 := by ring
      _ ≤ z * u * y := Nat.mul_le_mul (Nat.mul_le_mul hz le_rfl) hy
  have hu1' : u' ≤ z' * u' * y' := by
    calc u' = 1 * u' * 1 := by ring
      _ ≤ z' * u' * y' := Nat.mul_le_mul (Nat.mul_le_mul hz' le_rfl) hy'
  obtain ⟨h2, huu⟩ := sq_add_eq_iff (A := z * u * y) (B := z' * u' * y')
    (by omega) (by omega) h1
  subst hyy huu
  have hzz : z * (u * y) = z' * (u * y) := by simpa [mul_assoc] using h2
  exact ⟨Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hu hy) hzz, rfl, rfl⟩

end Jones1980
