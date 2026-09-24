import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-!
# The coefficient layout of the 93-operation certificate (Sections 1–2)

`Papers/1980/AFFINE_RADIX_95_PROOF.md`, Sections 1–2 (unchanged by the 94-
and 93-operation refinements).  A compiled circuit is presented as a list
of *rows*: quadratic polynomials in the input `x` and `m` physical
coordinates `z₀, …, z_{m−1}`, with square coefficients `±1`, cross
coefficients `±2`, coefficients `±2` for `x zᵢ` and `±1` for `x²`.  The
physical coordinate `zᵢ` gets the weight `vᵢ = 6·3ⁱ`; every quadratic
monomial has an even weight `≤ 2M`, `M = 6·3^(m−1)`, determined by its
unordered pair of factors.

Row `j` is tested at the position `t_j = (s+1) d₀ + 2M + j d₀`,
`d₀ = 4M + 6`, where `s` is the number of rows; the bands of different rows
are `d₀` apart.  The coefficient polynomial is

  `D = D_main + D_reset + D₅ + D₇`,

with `D_main = Σ_j Σ_{terms of row j} sign · X^(t_j − weight)`,
`D_reset = Σ_j X^(t_j − 3)`, and the two padding polynomials
`D₅ = X^(t₅ − 1) + Σ_{p ∈ P₅} X^(t₅ − 1 − v_p)`, `D₇` alike, attached to the
last two rows.  The exponents of the three kinds are `≡ 0, 3, 5 (mod 6)`.

This file defines the layout and proves the band-separation and
residue-class facts used for coefficient isolation.
-/

namespace Jones1980

namespace Layout

/-- The weight of the physical coordinate `i`. -/
def v (i : ℕ) : ℕ := 6 * 3 ^ i

theorem v_pos (i : ℕ) : 0 < v i := by unfold v; positivity

theorem six_dvd_v (i : ℕ) : 6 ∣ v i := ⟨3 ^ i, rfl⟩

theorem v_le (i m : ℕ) (hi : i < m) : v i ≤ 6 * 3 ^ (m - 1) := by
  unfold v; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem v_strictMono : StrictMono v := by
  intro i j hij
  unfold v
  exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by norm_num) hij) (by norm_num)

/-- A row: the target polynomial of one compiled equation, over `x` and the physical
coordinates.  `sq` lists `(i, s)` for `s zᵢ²`, `cross` lists `(i, k, s)` with `i < k` for
`2 s zᵢ z_k`, `xz` lists `(i, s)` for `2 s x zᵢ`, and `xx` is the coefficient `s` of `x²`. -/
structure Row (m : ℕ) where
  sq : List (Fin m × ℤ)
  cross : List (Fin m × Fin m × ℤ)
  xz : List (Fin m × ℤ)
  xx : ℤ

/-- The value of a row at `x` and the coordinates `z`. -/
def Row.val {m : ℕ} (R : Row m) (x : ℤ) (z : Fin m → ℤ) : ℤ :=
  (R.sq.map fun p => p.2 * z p.1 ^ 2).sum +
  (R.cross.map fun p => 2 * p.2.2 * z p.1 * z p.2.1).sum +
  (R.xz.map fun p => 2 * p.2 * x * z p.1).sum + R.xx * x ^ 2

/-- The weights of the monomials of a row, with their (divided) signs. -/
def Row.terms {m : ℕ} (R : Row m) : List (ℕ × ℤ) :=
  (R.sq.map fun p => (2 * v p.1, p.2)) ++
  (R.cross.map fun p => (v p.1 + v p.2.1, p.2.2)) ++
  (R.xz.map fun p => (v p.1, p.2)) ++ [(0, R.xx)]

/-- Every monomial weight of a row over `m` coordinates is a multiple of six and at most
`2 · 6 · 3^(m−1)`. -/
theorem Row.terms_weight {m : ℕ} (R : Row m) :
    ∀ p ∈ R.terms, 6 ∣ p.1 ∧ p.1 ≤ 2 * (6 * 3 ^ (m - 1)) := by
  intro p hp
  unfold Row.terms at hp
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hp
  rcases hp with ((⟨q, _, rfl⟩ | ⟨q, _, rfl⟩) | ⟨q, _, rfl⟩) | rfl
  · refine ⟨Dvd.dvd.mul_left (six_dvd_v _) 2, ?_⟩
    have := v_le q.1 m q.1.2; omega
  · refine ⟨dvd_add (six_dvd_v _) (six_dvd_v _), ?_⟩
    have := v_le q.1 m q.1.2; have := v_le q.2.1 m q.2.1.2; omega
  · refine ⟨six_dvd_v _, ?_⟩
    have := v_le q.1 m q.1.2; omega
  · exact ⟨dvd_zero 6, by omega⟩

/-- The layout: `M`, `d₀`, and the target positions. -/
def M (m : ℕ) : ℕ := 6 * 3 ^ (m - 1)

def d0 (m : ℕ) : ℕ := 4 * M m + 6

/-- The position of target `j` among `s` targets. -/
def t (m s j : ℕ) : ℕ := (s + 1) * d0 m + 2 * M m + j * d0 m

theorem six_dvd_M (m : ℕ) : 6 ∣ M m := ⟨3 ^ (m - 1), rfl⟩

theorem six_dvd_d0 (m : ℕ) : 6 ∣ d0 m := by
  unfold d0; exact dvd_add (Dvd.dvd.mul_left (six_dvd_M m) 4) (dvd_refl 6)

theorem six_dvd_t (m s j : ℕ) : 6 ∣ t m s j := by
  unfold t
  exact dvd_add (dvd_add (Dvd.dvd.mul_left (six_dvd_d0 m) _) (Dvd.dvd.mul_left (six_dvd_M m) 2))
    (Dvd.dvd.mul_left (six_dvd_d0 m) _)

theorem M_pos (m : ℕ) : 0 < M m := by unfold M; positivity

theorem d0_gt (m : ℕ) : 2 * M m + 4 < d0 m := by unfold d0; have := M_pos m; omega

/-- Targets are `d₀` apart. -/
theorem t_succ (m s j : ℕ) : t m s (j + 1) = t m s j + d0 m := by unfold t; ring

theorem t_add (m s j k : ℕ) : t m s (j + k) = t m s j + k * d0 m := by unfold t; ring

/-- The first target is far above `2M`: `t 0 ≥ 2M + 5 d₀ ≥ ...`; in particular `t 0 > 2M + 5`. -/
theorem t_zero_gt (m s : ℕ) : 2 * M m + d0 m ≤ t m s 0 := by
  unfold t; have := M_pos m; nlinarith [d0_gt m]

/-- Distinct targets differ by at least `d₀`. -/
theorem t_sub_ge {m s j k : ℕ} (hjk : j < k) : t m s j + d0 m ≤ t m s k := by
  obtain ⟨i, rfl⟩ : ∃ i, k = j + 1 + i := ⟨k - (j + 1), by omega⟩
  rw [t_add, t_succ]; omega

/-- A weight is at most `M`. -/
theorem v_le_M {m i : ℕ} (hi : i < m) : v i ≤ M m := v_le i m hi

/-- Band separation: an exponent `d` of band `j` satisfies `t_j ≤ d + 2M` and `d + 1 ≤ t_j`;
a position `p` with `t_j ≤ p + 5` and `p ≤ t_j + 2` that is within `2M` of an exponent
`d'` of band `k` (`d' ≤ p ≤ d' + 2M`) forces `k = j`. -/
theorem band_unique {m s j k p d' : ℕ}
    (hp1 : t m s j ≤ p + 5) (hp2 : p ≤ t m s j + 2)
    (hd1 : t m s k ≤ d' + 2 * M m) (hd2 : d' + 1 ≤ t m s k)
    (hpd : d' ≤ p ∧ p ≤ d' + 2 * M m) : k = j := by
  by_contra hne
  have hd0 := d0_gt m
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := t_sub_ge (m := m) (s := s) hlt
    omega
  · have := t_sub_ge (m := m) (s := s) hgt
    omega

/-- Dummy exclusion: a coordinate position `u ≥ t_0` and an exponent `d ≥ t_0 − 2M − 1`
sum to more than `t_{s-1} + 2`, the last tested position. -/
theorem dummy_exclusion {m s u d : ℕ} (hs : 1 ≤ s) (hu : t m s 0 ≤ u)
    (hd : t m s 0 ≤ d + 2 * M m + 1) : t m s (s - 1) + 2 < u + d := by
  have h1 : t m s (s - 1) = t m s 0 + (s - 1) * d0 m := by
    have := t_add m s 0 (s - 1); rwa [zero_add] at this
  have h2 : t m s 0 = (s + 1) * d0 m + 2 * M m := by unfold t; ring
  have hd0 := d0_gt m
  have : (s - 1) * d0 m + 2 * d0 m = (s + 1) * d0 m := by
    rw [show s + 1 = (s - 1) + 2 by omega, add_mul]
  nlinarith

end Layout

end Jones1980
