import Mathlib

/-!
Finite algebra used in the eventual content-normalized residual Smith profile.

All triangular costs are doubled, avoiding division by two.  The analytic and
interpolation input is deliberately absent: these are the exact integer
inequalities used by the Lagrange-term and Sylvester-matching arguments.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace ContentNormalizedProfileFinite

def tri2 (z : ℤ) : ℤ := z * (z - 1)

def phi2 (z : ℤ) : ℤ := z * (z + 1)

def psi2 (n a s : ℤ) : ℤ :=
  s * ((n + 1) * (s + 1) - 2 - 2 * a)

theorem psi2_sub_tri2_identity (n a s : ℤ) :
    psi2 n a s - tri2 s = s * (n * (s + 1) - 2 * a) := by
  simp only [psi2, tri2]
  ring

/-- The endpoint weight gap strictly dominates the loss of `s` shallow roots
as soon as the boundary degree is larger than the diagonal valuation depth. -/
theorem tri2_lt_psi2 {n a s : ℤ}
    (ha0 : 0 ≤ a) (han : a < n) (hs : 1 ≤ s) :
    tri2 s < psi2 n a s := by
  have hna : 1 ≤ n - a := by omega
  have hs0 : 0 ≤ s - 1 := by omega
  have hprod : 0 ≤ n * (s - 1) := mul_nonneg (by omega) hs0
  have hbracket : 2 ≤ n * (s + 1) - 2 * a := by
    nlinarith
  rw [← sub_pos]
  rw [psi2_sub_tri2_identity]
  exact mul_pos (by omega) (by omega)

/-- Exact gap decomposition for the divided-difference coefficient cost. -/
theorem qcost_gap_identity (n N s d : ℤ) :
    tri2 (N - d) + 2 * (n - s) * d + tri2 s - tri2 N =
      2 * d * (n - N) + (d - s) * (d - s + 1) := by
  simp only [tri2]
  ring

theorem consecutive_mul_nonneg (z : ℤ) : 0 ≤ z * (z + 1) := by
  by_cases hz : 0 ≤ z
  · exact mul_nonneg hz (by omega)
  · have hz1 : z + 1 ≤ 0 := by omega
    exact mul_nonneg_of_nonpos_of_nonpos (by omega) hz1

/-- A boundary divided difference can lose at most `choose(s,2)` from the
canonical coefficient cost. -/
theorem tri2_le_qcost_add_tri2 {n N s d : ℤ}
    (hd : 0 ≤ d) (hN : N ≤ n) :
    tri2 N ≤ tri2 (N - d) + 2 * (n - s) * d + tri2 s := by
  have hfirst : 0 ≤ 2 * d * (n - N) := by positivity
  have hsecond := consecutive_mul_nonneg (d - s)
  rw [← sub_nonneg]
  rw [qcost_gap_identity]
  positivity

/-- Exact decomposition behind the direct-residual coefficient floor. -/
theorem direct_gap_identity (n a s d : ℤ) :
    psi2 n a s + 2 * (n - s) * d - (2 * d * (n - 1) + 2) =
      (s - 1) * ((n + 1) * s + 2 - 2 * d) + 2 * s * (n - 1 - a) := by
  simp only [psi2]
  ring

/-- After content removal, every nonleading direct-residual coefficient has
strict depth `d(n-1)+1`; this is the threshold needed to make every Sylvester
wrap term secondary. -/
theorem direct_floor_doubled {n a s d : ℤ}
    (ha0 : 0 ≤ a) (han : a < n) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hd : 1 ≤ d) (hdn : d ≤ n) :
    2 * d * (n - 1) + 2 ≤ psi2 n a s + 2 * (n - s) * d := by
  by_cases hs1 : s = 1
  · subst s
    simp only [psi2]
    nlinarith
  · have hs2 : 2 ≤ s := by omega
    have hna : 0 ≤ n - 1 - a := by omega
    have hleft : 0 ≤ s - 1 := by omega
    have hright : 0 ≤ (n + 1) * s + 2 - 2 * d := by
      nlinarith
    have hprod1 : 0 ≤ (s - 1) * ((n + 1) * s + 2 - 2 * d) :=
      mul_nonneg hleft hright
    have hprod2 : 0 ≤ 2 * s * (n - 1 - a) := by positivity
    rw [← sub_nonneg]
    rw [direct_gap_identity]
    positivity

/-- A reduction path in the nonwrap triangle is strictly deeper than its
canonical Toeplitz entry. -/
theorem nonwrap_correction_doubled {n N u : ℤ}
    (hu : 0 ≤ u) (huN : u < N) (hNn : N ≤ n) :
    tri2 N + 2 ≤ tri2 u + 2 * (n - 1) * (N - u) + 2 := by
  have hdu : 0 ≤ N - u := by omega
  have hother : 0 ≤ 2 * n - 1 - N - u := by omega
  have hid :
      tri2 u + 2 * (n - 1) * (N - u) - tri2 N =
        (N - u) * (2 * n - 1 - N - u) := by
    simp only [tri2]
    ring
  rw [add_le_add_iff_right]
  rw [← sub_nonneg]
  rw [hid]
  positivity

/-- Among wrap reductions, the shallowest possible last boundary index is
the largest allowed one. -/
theorem wrap_path_lower_doubled {n x j u : ℤ}
    (hu : 0 ≤ u) (huj : u ≤ j) (hjn : j ≤ n - 1) :
    tri2 j + 2 * (n - 1) * (x + 1) + 2 ≤
      tri2 u + 2 * (n - 1) * (x + j + 1 - u) + 2 := by
  have hju : 0 ≤ j - u := by omega
  have hother : 0 ≤ 2 * n - 1 - j - u := by omega
  have hid :
      tri2 u + 2 * (n - 1) * (x + j + 1 - u) -
          (tri2 j + 2 * (n - 1) * (x + 1)) =
        (j - u) * (2 * n - 1 - j - u) := by
    simp only [tri2]
    ring
  rw [add_le_add_iff_right]
  rw [← sub_nonneg]
  rw [hid]
  positivity

def wrapCost2 (n x j : ℤ) : ℤ :=
  tri2 j + 2 * (n - 1) * (x + 1) + 2

/-- Exact algebraic comparison between a wrap cost and the fictitious convex
Toeplitz cost at the same row/column sum. -/
theorem phi2_sub_wrapCost2_identity (n x j : ℤ) :
    let z := x + j
    let t := z - n + 1
    phi2 z - wrapCost2 n x j =
      t * (t + 1) - (n - j) * (n - j - 1) - 2 := by
  dsimp only
  simp only [phi2, wrapCost2, tri2]
  ring

/-- On a compressed `m` by `m` matching (`m ≤ n`), the wrap deficit is no
larger than the positive convex-deviation term around mean `m-1`. -/
theorem wrap_deficit_le_deviation {n m x j : ℤ}
    (hmn : m ≤ n) (hx0 : 0 ≤ x) (hj0 : 0 ≤ j) (hjm : j < m)
    (hwrap : n ≤ x + j) :
    phi2 (x + j) - wrapCost2 n x j ≤
      (x + j - (m - 1)) * (x + j - (m - 1) + 1) := by
  let z := x + j
  let t := z - n + 1
  let y := z - (m - 1)
  have ht : 1 ≤ t := by dsimp [t, z]; omega
  have hty : t ≤ y := by dsimp [t, y, z]; omega
  have ht0 : 0 ≤ t := by omega
  have hy0 : 0 ≤ y := by omega
  have hmono : t * (t + 1) ≤ y * (y + 1) := by nlinarith
  have hnj : 1 ≤ n - j := by omega
  have hnjprod : 0 ≤ (n - j) * (n - j - 1) := by positivity
  rw [phi2_sub_wrapCost2_identity]
  dsimp only [z, t, y] at *
  nlinarith

/-- Convex-deviation identity used after row/column compression. -/
theorem phi2_deviation_identity (c y : ℤ) :
    phi2 (c + y) = phi2 c + 2 * c * y + y * (y + 1) := by
  simp only [phi2]
  ring

/-- Abstract finite assignment inequality.  `wrapped i` marks entries outside
the Toeplitz triangle.  The sum condition is exactly what a permutation of the
first `m` row and column ranks supplies. -/
theorem finite_assignment_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℤ) (z cost : ι → ℤ) (wrapped : ι → Bool)
    (hsum : ∑ i, (z i - c) = 0)
    (hlower : ∀ i,
      if wrapped i then
        phi2 (z i) - (z i - c) * (z i - c + 1) ≤ 2 * cost i
      else phi2 (z i) ≤ 2 * cost i) :
    Fintype.card ι * phi2 c ≤ 2 * ∑ i, cost i := by
  have hpoint : ∀ i,
      phi2 c + 2 * c * (z i - c) ≤ 2 * cost i := by
    intro i
    have hdev := consecutive_mul_nonneg (z i - c)
    have hid := phi2_deviation_identity c (z i - c)
    simp only [add_sub_cancel] at hid
    by_cases hwrap : wrapped i = true
    · have hi := hlower i
      simp only [hwrap, ↓reduceIte] at hi
      rw [hid] at hi
      linarith
    · have hi := hlower i
      simp [hwrap] at hi
      rw [hid] at hi
      linarith
  have hsumle := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) ↦ hpoint i
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.sum_mul, hsum, mul_zero, add_zero,
    ← Finset.mul_sum] at hsumle
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsumle

/-- Doubled-cost version of `finite_assignment_lower`, matching the integer
costs used in the profile matrix below. -/
theorem finite_assignment_lower_doubled
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℤ) (z cost2 : ι → ℤ) (wrapped : ι → Bool)
    (hsum : ∑ i, (z i - c) = 0)
    (hlower : ∀ i,
      if wrapped i then
        phi2 (z i) - (z i - c) * (z i - c + 1) ≤ cost2 i
      else phi2 (z i) ≤ cost2 i) :
    Fintype.card ι * phi2 c ≤ ∑ i, cost2 i := by
  have hpoint : ∀ i,
      phi2 c + 2 * c * (z i - c) ≤ cost2 i := by
    intro i
    have hdev := consecutive_mul_nonneg (z i - c)
    have hid := phi2_deviation_identity c (z i - c)
    simp only [add_sub_cancel] at hid
    by_cases hwrap : wrapped i = true
    · have hi := hlower i
      simp only [hwrap, ↓reduceIte] at hi
      rw [hid] at hi
      linarith
    · have hi := hlower i
      simp [hwrap] at hi
      rw [hid] at hi
      linarith
  have hsumle := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) ↦ hpoint i
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hsum, mul_zero, add_zero, ← Finset.mul_sum] at hsumle
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsumle

/-- Twice the sum of the ranks in `Fin m`. -/
theorem two_mul_sum_fin_val (m : ℕ) :
    2 * ∑ i : Fin m, (i.1 : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.coe_castSucc, Fin.val_last]
      push_cast
      nlinarith

/-- The row-plus-column deviations of a compressed permutation sum to zero. -/
theorem compressed_permutation_deviation_sum (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    ∑ i : Fin m,
      ((i.1 : ℤ) + ((σ i).1 : ℤ) - ((m : ℤ) - 1)) = 0 := by
  have hperm : (∑ i : Fin m, ((σ i).1 : ℤ)) = ∑ i : Fin m, (i.1 : ℤ) :=
    Equiv.sum_comp σ (fun i : Fin m ↦ (i.1 : ℤ))
  have htwo := two_mul_sum_fin_val m
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hperm]
  nlinarith

def profileCost2 (n x j : ℤ) : ℤ :=
  if x + j < n then phi2 (x + j) else wrapCost2 n x j

theorem profileCost2_mono_row {n x j : ℤ}
    (hn : 1 ≤ n) (hx : 0 ≤ x) (hj : 0 ≤ j) (hjn : j < n) :
    profileCost2 n x j ≤ profileCost2 n (x + 1) j := by
  by_cases hlow : x + j < n
  · by_cases hnext : x + 1 + j < n
    · simp only [profileCost2, hlow, hnext, ↓reduceIte]
      simp only [phi2]
      nlinarith
    · have hedge : x + j = n - 1 := by omega
      simp only [profileCost2, hlow, ↓reduceIte, hnext, wrapCost2, tri2, phi2]
      nlinarith [mul_nonneg (show 0 ≤ n - j - 1 by omega)
        (show 0 ≤ n + j by omega)]
  · have hwrap : ¬x + j < n := hlow
    have hwrap' : ¬x + 1 + j < n := by omega
    simp only [profileCost2, hwrap, hwrap', ↓reduceIte, wrapCost2]
    nlinarith

theorem profileCost2_mono_col {n x j : ℤ}
    (hn : 1 ≤ n) (hx : 0 ≤ x) (hj : 0 ≤ j) (hjn : j + 1 < n) :
    profileCost2 n x j ≤ profileCost2 n x (j + 1) := by
  by_cases hlow : x + j < n
  · by_cases hnext : x + (j + 1) < n
    · simp only [profileCost2, hlow, hnext, ↓reduceIte]
      simp only [phi2]
      nlinarith
    · have hedge : x + j = n - 1 := by omega
      simp only [profileCost2, hlow, ↓reduceIte, hnext, wrapCost2, tri2, phi2]
      nlinarith [mul_nonneg (show 0 ≤ n - j - 1 by omega)
        (show 0 ≤ n + j by omega)]
  · have hwrap : ¬x + j < n := hlow
    have hwrap' : ¬x + (j + 1) < n := by omega
    simp only [profileCost2, hwrap, hwrap', ↓reduceIte, wrapCost2, tri2]
    nlinarith

/-- Full compressed assignment inequality for the residual multiplication
matrix.  The anti-diagonal has exactly the displayed cost; this theorem proves
that no permutation, including one using wrap entries, can be cheaper. -/
theorem compressed_permutation_profileCost2_lower
    {m n : ℕ} (hmn : m ≤ n) (σ : Equiv.Perm (Fin m)) :
    (m : ℤ) * (m : ℤ) * ((m : ℤ) - 1) ≤
      ∑ i : Fin m, profileCost2 (n : ℤ) (i.1 : ℤ) ((σ i).1 : ℤ) := by
  let z : Fin m → ℤ := fun i ↦ (i.1 : ℤ) + ((σ i).1 : ℤ)
  let c : ℤ := (m : ℤ) - 1
  let wrapped : Fin m → Bool := fun i ↦ decide ((n : ℤ) ≤ z i)
  have hsum : ∑ i, (z i - c) = 0 := by
    simpa [z, c] using compressed_permutation_deviation_sum m σ
  have hlower : ∀ i,
      if wrapped i then
        phi2 (z i) - (z i - c) * (z i - c + 1) ≤
          profileCost2 (n : ℤ) (i.1 : ℤ) ((σ i).1 : ℤ)
      else
        phi2 (z i) ≤ profileCost2 (n : ℤ) (i.1 : ℤ) ((σ i).1 : ℤ) := by
    intro i
    by_cases hw : (n : ℤ) ≤ z i
    · have hdef := wrap_deficit_le_deviation
          (n := (n : ℤ)) (m := (m : ℤ)) (x := (i.1 : ℤ)) (j := ((σ i).1 : ℤ))
          (by exact_mod_cast hmn) (by positivity) (by positivity)
          (by exact_mod_cast (σ i).isLt) hw
      simp only [wrapped, hw, decide_true, ↓reduceIte]
      simpa [profileCost2, z, c, hw, not_lt.mpr hw, add_comm, add_left_comm,
        add_assoc] using hdef
    · have hlt : z i < (n : ℤ) := by omega
      simp only [wrapped, hw, decide_false, Bool.false_eq_true, ↓reduceIte]
      simp [profileCost2, z, hlt]
  have h := finite_assignment_lower_doubled c z
      (fun i ↦ profileCost2 (n : ℤ) (i.1 : ℤ) ((σ i).1 : ℤ)) wrapped hsum hlower
  simp only [Fintype.card_fin, c, phi2] at h
  nlinarith

end ContentNormalizedProfileFinite
end LeanProofs.TwoBaseIntegerExponent
