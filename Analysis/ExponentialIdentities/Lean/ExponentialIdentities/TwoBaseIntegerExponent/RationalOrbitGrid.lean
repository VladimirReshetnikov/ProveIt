import ExponentialIdentities.TwoBaseIntegerExponent.SparsePowerCurve

/-!
# Rational collisions on rectangular two-generator orbit grids

For a rational parameter `x = r / s` in lowest terms, equality of the orbit parameters

`i + j x = i' + j' x`

is equivalent to equality of the natural-number weights `s * i + r * j`.  This module
counts the distinct weights in an `M × N` rectangle exactly.  The result is the
combinatorial half of the report's sharp support spectrum:

`M * N - (M - r) * (N - s)`.

The analytic half for irrational parameters—injectivity of power-curve frequencies and the
`R + 1` sparse zero bound—is provided by `SparsePowerCurve`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

noncomputable section

/-- The integral weight representing `i + j * (r / s)`. -/
def rationalOrbitWeight (r s : ℕ) (ij : ℕ × ℕ) : ℕ :=
  s * ij.1 + r * ij.2

/-- The rectangular index set `{0, ..., M-1} × {0, ..., N-1}`. -/
def orbitRectangle (M N : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range M ×ˢ Finset.range N

/-- The distinct rational orbit weights represented in an `M × N` rectangle. -/
def rationalOrbitWeights (r s M N : ℕ) : Finset ℕ :=
  (orbitRectangle M N).image (rationalOrbitWeight r s)

/-- The weights in the newly adjoined row with first index `M`. -/
def rationalOrbitRow (r s M N : ℕ) : Finset ℕ :=
  (Finset.range N).image fun j ↦ s * M + r * j

/-- The finite set of real parameters `i + j*x` represented by a rectangular grid. -/
def orbitParameterSet (x : ℝ) (M N : ℕ) : Finset ℝ :=
  (orbitRectangle M N).image fun ij ↦ (ij.1 : ℝ) + (ij.2 : ℝ) * x

@[simp] theorem mem_orbitRectangle {M N i j : ℕ} :
    (i, j) ∈ orbitRectangle M N ↔ i < M ∧ j < N := by
  simp [orbitRectangle]

@[simp] theorem mem_rationalOrbitWeights {r s M N v : ℕ} :
    v ∈ rationalOrbitWeights r s M N ↔
      ∃ i < M, ∃ j < N, s * i + r * j = v := by
  simp only [rationalOrbitWeights, Finset.mem_image, rationalOrbitWeight]
  constructor
  · rintro ⟨⟨i, j⟩, hij, rfl⟩
    have hij' : i < M ∧ j < N := by simpa [orbitRectangle] using hij
    obtain ⟨hi, hj⟩ := hij'
    exact ⟨i, hi, j, hj, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨(i, j), by simp [orbitRectangle, hi, hj], rfl⟩

@[simp] theorem mem_rationalOrbitRow {r s M N v : ℕ} :
    v ∈ rationalOrbitRow r s M N ↔ ∃ j < N, s * M + r * j = v := by
  simp [rationalOrbitRow]

/-- Adjoining one first-coordinate row adjoins exactly `rationalOrbitRow`. -/
theorem rationalOrbitWeights_succ_first (r s M N : ℕ) :
    rationalOrbitWeights r s (M + 1) N =
      rationalOrbitWeights r s M N ∪ rationalOrbitRow r s M N := by
  ext v
  simp only [mem_rationalOrbitWeights, Finset.mem_union, mem_rationalOrbitRow]
  constructor
  · rintro ⟨i, hi, j, hj, hval⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by simpa using hi) with hiM | rfl
    · exact Or.inl ⟨i, hiM, j, hj, hval⟩
    · exact Or.inr ⟨j, hj, hval⟩
  · rintro (h | h)
    · obtain ⟨i, hi, j, hj, hval⟩ := h
      exact ⟨i, hi.trans (Nat.lt_succ_self M), j, hj, hval⟩
    · obtain ⟨j, hj, hval⟩ := h
      exact ⟨M, by omega, j, hj, hval⟩

/-- A positive step makes the parametrization of each newly adjoined row injective. -/
theorem rationalOrbitRow_card {r s M N : ℕ} (hr : 0 < r) :
    (rationalOrbitRow r s M N).card = N := by
  rw [rationalOrbitRow, Finset.card_image_iff.mpr]
  · exact Finset.card_range N
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hr (Nat.add_left_cancel hab)

/-- Exact criterion for a point in a new row to collide with an earlier row. -/
theorem newRowWeight_mem_previous_iff {r s M N j : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hcop : r.Coprime s) :
    s * M + r * j ∈ rationalOrbitWeights r s M N ↔
      r ≤ M ∧ j + s < N := by
  rw [mem_rationalOrbitWeights]
  constructor
  · rintro ⟨i, hi, j', hj', heq⟩
    have hji : j < j' := by
      by_contra hnot
      have hj'le : j' ≤ j := Nat.le_of_not_gt hnot
      have hsi : s * i < s * M := (Nat.mul_lt_mul_left hs).mpr hi
      have hrj : r * j' ≤ r * j := Nat.mul_le_mul_left r hj'le
      omega
    have hi_le : i ≤ M := Nat.le_of_lt hi
    have hj_le : j ≤ j' := Nat.le_of_lt hji
    have hdiff : s * (M - i) = r * (j' - j) := by
      nlinarith [Nat.sub_add_cancel hi_le, Nat.sub_add_cancel hj_le]
    have hr_dvd : r ∣ M - i := by
      apply (hcop.dvd_mul_right).mp
      rw [mul_comm, hdiff]
      exact dvd_mul_right r (j' - j)
    have hs_dvd : s ∣ j' - j := by
      apply (hcop.symm.dvd_mul_right).mp
      rw [mul_comm, ← hdiff]
      exact dvd_mul_right s (M - i)
    have hMi : 0 < M - i := Nat.sub_pos_of_lt hi
    have hjj' : 0 < j' - j := Nat.sub_pos_of_lt hji
    have hrle : r ≤ M - i := Nat.le_of_dvd hMi hr_dvd
    have hsle : s ≤ j' - j := Nat.le_of_dvd hjj' hs_dvd
    constructor <;> omega
  · rintro ⟨hrM, hjs⟩
    refine ⟨M - r, ?_, j + s, hjs, ?_⟩
    · have hrne : r ≠ 0 := Nat.ne_of_gt hr
      omega
    · have hsub : M - r + r = M := Nat.sub_add_cancel hrM
      nlinarith

/-- The intersection of a positive-step new row with the previous rectangle has the exact
size predicted by the primitive collision step. -/
theorem card_previous_inter_newRow {r s M N : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hcop : r.Coprime s) :
    (rationalOrbitWeights r s M N ∩ rationalOrbitRow r s M N).card =
      if r ≤ M then N - s else 0 := by
  let overlapIndices : Finset ℕ :=
    (Finset.range N).filter fun j ↦ r ≤ M ∧ j + s < N
  have hset : rationalOrbitWeights r s M N ∩ rationalOrbitRow r s M N =
      overlapIndices.image fun j ↦ s * M + r * j := by
    ext v
    simp only [Finset.mem_inter, mem_rationalOrbitRow, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range, overlapIndices]
    constructor
    · rintro ⟨hvold, j, hj, hval⟩
      refine ⟨j, ⟨hj, ?_⟩, hval⟩
      exact (newRowWeight_mem_previous_iff hr hs hcop).mp (hval ▸ hvold)
    · rintro ⟨j, ⟨hj, hover⟩, hval⟩
      refine ⟨?_, ⟨j, hj, hval⟩⟩
      exact hval ▸ (newRowWeight_mem_previous_iff hr hs hcop).mpr hover
  rw [hset, Finset.card_image_iff.mpr]
  · by_cases hrM : r ≤ M
    · simp only [overlapIndices, hrM, true_and, if_pos]
      have hfilter : (Finset.range N).filter (fun j ↦ j + s < N) =
          Finset.range (N - s) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [hfilter, Finset.card_range]
    · simp [overlapIndices, hrM]
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hr (Nat.add_left_cancel hab)

/-- Recurrence obtained by adjoining one row to the rectangle. -/
theorem card_rationalOrbitWeights_succ_first {r s M N : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hcop : r.Coprime s) :
    (rationalOrbitWeights r s (M + 1) N).card =
      (rationalOrbitWeights r s M N).card + N -
        (if r ≤ M then N - s else 0) := by
  rw [rationalOrbitWeights_succ_first]
  have hunion := Finset.card_union_add_card_inter
    (rationalOrbitWeights r s M N) (rationalOrbitRow r s M N)
  rw [rationalOrbitRow_card hr, card_previous_inter_newRow hr hs hcop] at hunion
  omega

/-- **Rectangular collision formula, positive numerator.**  In lowest terms with `r,s > 0`,
the number of distinct weights in an `M × N` rectangle is
`M*N - (M-r)*(N-s)`.  Natural subtraction supplies the positive-part convention. -/
theorem card_rationalOrbitWeights_of_pos {r s M N : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hcop : r.Coprime s) :
    (rationalOrbitWeights r s M N).card =
      M * N - (M - r) * (N - s) := by
  induction M with
  | zero => simp [rationalOrbitWeights, orbitRectangle]
  | succ M ih =>
      rw [show M + 1 = Nat.succ M by omega]
      rw [card_rationalOrbitWeights_succ_first hr hs hcop, ih]
      by_cases hrM : r ≤ M
      · rw [if_pos hrM]
        have hsub : M + 1 - r = (M - r) + 1 := by omega
        rw [hsub]
        have hbase : (M - r) * (N - s) ≤ M * N :=
          Nat.mul_le_mul (Nat.sub_le M r) (Nat.sub_le N s)
        have htotal : (M + 1) * N = M * N + N := by ring
        have hdefect : (M - r + 1) * (N - s) =
            (M - r) * (N - s) + (N - s) := by ring
        rw [htotal, hdefect]
        omega
      · rw [if_neg hrM]
        have hMr : M - r = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hrM)
        have hM1r : M + 1 - r = 0 := by omega
        simp [hMr, hM1r]
        ring

/-- When the rational parameter is zero, coprimality and positivity of the denominator force
`s = 1`, and a nonempty rectangle has exactly one value per first-coordinate row. -/
theorem card_rationalOrbitWeights_zero {s M N : ℕ}
    (hs : 0 < s) (hcop : Nat.Coprime 0 s) (hN : 0 < N) :
    (rationalOrbitWeights 0 s M N).card = M := by
  have hs1 : s = 1 := by simpa using hcop
  subst s
  let embedRow : ℕ → ℕ × ℕ := fun i ↦ (i, 0)
  have hweights : rationalOrbitWeights 0 1 M N = Finset.range M := by
    ext v
    simp only [mem_rationalOrbitWeights, Finset.mem_range, zero_mul, add_zero,
      one_mul]
    constructor
    · rintro ⟨i, hi, j, hj, rfl⟩
      exact hi
    · intro hv
      exact ⟨v, hv, 0, hN, rfl⟩
  rw [hweights, Finset.card_range]

/-- **Exact rectangular collision formula.**  For `r/s` in lowest nonnegative terms and a
nonempty second-coordinate range, the distinct orbit weights have cardinality

`M*N - (M-r)*(N-s)`.

The two subtractions are exactly the positive parts `(M-r)_+` and `(N-s)_+`. -/
theorem card_rationalOrbitWeights {r s M N : ℕ}
    (hs : 0 < s) (hcop : r.Coprime s) (hN : 0 < N) :
    (rationalOrbitWeights r s M N).card =
      M * N - (M - r) * (N - s) := by
  rcases r.eq_zero_or_pos with rfl | hr
  · rw [card_rationalOrbitWeights_zero hs hcop hN]
    have hs1 : s = 1 := by simpa using hcop
    subst s
    have htotal : M * N = M * (N - 1) + M := by
      calc
        M * N = M * ((N - 1) + 1) := by rw [Nat.sub_add_cancel hN]
        _ = M * (N - 1) + M := by ring
    simp only [Nat.sub_zero]
    rw [htotal]
    omega
  · exact card_rationalOrbitWeights_of_pos hr hs hcop

/-- Irrational grid parameters do not collide. -/
theorem irrational_gridParameter_injective {x : ℝ} (hx : Irrational x) :
    Function.Injective fun ij : ℕ × ℕ ↦ (ij.1 : ℝ) + (ij.2 : ℝ) * x :=
  IntegerExponent.Irrational.injective_nat_add_mul hx

/-- An irrational `M × N` orbit grid has all `M*N` parameters distinct. -/
theorem card_irrationalOrbitParameters {x : ℝ} (hx : Irrational x) (M N : ℕ) :
    (orbitParameterSet x M N).card = M * N := by
  rw [orbitParameterSet]
  rw [Finset.card_image_of_injective _ (irrational_gridParameter_injective hx)]
  simp [orbitRectangle]

/-- **Irrational square-grid sparse lower bound.**  A nonzero relation with `n+1`
distinct power-curve monomials that vanishes on every point of a `K × K` irrational
parameter grid must have at least `K^2 + 1` terms (equivalently, `K^2 ≤ n`). -/
theorem squareGrid_le_of_sparsePowerCurve_eq_zero {n K : ℕ} {x β : ℝ}
    (hx : Irrational x) (hβ : Irrational β)
    (rs : Fin (n + 1) → ℕ × ℕ) (hrs : Function.Injective rs)
    (c : Fin (n + 1) → ℝ) (hc : ∃ j, c j ≠ 0)
    (hzero : ∀ i < K, ∀ j < K,
      ∑ k, c k * Real.exp
        (powerCurveFrequency β (rs k) * ((i : ℝ) + (j : ℝ) * x)) = 0) :
    K ^ 2 ≤ n := by
  have hsetzero : ∀ z ∈ orbitParameterSet x K K,
      ∑ k, c k * Real.exp (powerCurveFrequency β (rs k) * z) = 0 := by
    intro z hz
    rw [orbitParameterSet, Finset.mem_image] at hz
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := hz
    have hij' : i < K ∧ j < K := by simpa [orbitRectangle] using hij
    exact hzero i hij'.1 j hij'.2
  have hcard := card_le_of_sparsePowerCurve_eq_zero hβ rs hrs c hc
    (orbitParameterSet x K K) hsetzero
  rw [card_irrationalOrbitParameters hx, ← pow_two] at hcard
  exact hcard

/-! ## Canonical rational-grid certificates -/

open Polynomial

/-- Increasing enumeration of the distinct positive nodes `exp(s*i+r*j)` in a rational
orbit rectangle.  Scaling the rational parameters by the positive denominator does not
change their collision pattern. -/
def rationalOrbitNodeFamily (r s M N : ℕ) :
    Fin (rationalOrbitWeights r s M N).card → ℝ :=
  fun k ↦ Real.exp ((rationalOrbitWeights r s M N).orderEmbOfFin rfl k : ℝ)

/-- The canonical one-variable polynomial through every distinct scaled rational-grid node. -/
def rationalOrbitNodePolynomial (r s M N : ℕ) : ℝ[X] :=
  positiveNodeInterpolant (rationalOrbitNodeFamily r s M N)

theorem rationalOrbitNodeFamily_pos (r s M N : ℕ)
    (k : Fin (rationalOrbitWeights r s M N).card) :
    0 < rationalOrbitNodeFamily r s M N k := by
  exact Real.exp_pos _

/-- Every coefficient of the canonical rational-grid node polynomial is nonzero, so its
support has exactly one more element than the set of distinct grid parameters. -/
theorem rationalOrbitNodePolynomial_support_card (r s M N : ℕ) :
    (rationalOrbitNodePolynomial r s M N).support.card =
      (rationalOrbitWeights r s M N).card + 1 := by
  exact positiveNodeInterpolant_support_card _ (rationalOrbitNodeFamily_pos r s M N)

/-- The canonical rational-grid certificate realizes the rectangular collision formula
exactly at the level of monomial support. -/
theorem rationalOrbitNodePolynomial_support_card_eq {r s M N : ℕ}
    (hs : 0 < s) (hcop : r.Coprime s) (hN : 0 < N) :
    (rationalOrbitNodePolynomial r s M N).support.card =
      M * N - (M - r) * (N - s) + 1 := by
  rw [rationalOrbitNodePolynomial_support_card,
    card_rationalOrbitWeights hs hcop hN]

/-- The canonical polynomial vanishes at every node represented by the rectangle. -/
theorem rationalOrbitNodePolynomial_eval_eq_zero {r s M N i j : ℕ}
    (hi : i < M) (hj : j < N) :
    (rationalOrbitNodePolynomial r s M N).eval
      (Real.exp (s * i + r * j : ℕ)) = 0 := by
  let W := rationalOrbitWeights r s M N
  have hw : s * i + r * j ∈ W := by
    rw [show W = rationalOrbitWeights r s M N by rfl, mem_rationalOrbitWeights]
    exact ⟨i, hi, j, hj, rfl⟩
  have hw' : s * i + r * j ∈
      Finset.image (W.orderEmbOfFin rfl) Finset.univ := by
    rwa [Finset.image_orderEmbOfFin_univ]
  obtain ⟨k, _hk, hk⟩ := Finset.mem_image.mp hw'
  have heval := positiveNodeInterpolant_eval (rationalOrbitNodeFamily r s M N) k
  rw [rationalOrbitNodePolynomial]
  rw [← hk]
  simpa [rationalOrbitNodeFamily, W] using heval

/-- **One-monomial rational certificate.**  If `K` exceeds the reduced numerator and
denominator of `r/s`, the canonical nonzero polynomial vanishing on the whole `K × K`
grid has at most `K^2` monomials. -/
theorem exists_rational_squareGrid_certificate {r s K : ℕ}
    (hs : 0 < s) (hcop : r.Coprime s) (hrK : r < K) (hsK : s < K) :
    ∃ P : ℝ[X], P ≠ 0 ∧ P.support.card ≤ K ^ 2 ∧
      ∀ i < K, ∀ j < K,
        P.eval (Real.exp (s * i + r * j : ℕ)) = 0 := by
  refine ⟨rationalOrbitNodePolynomial r s K K, ?_, ?_, ?_⟩
  · intro hzero
    have hcard := rationalOrbitNodePolynomial_support_card r s K K
    rw [hzero] at hcard
    simp at hcard
  · rw [rationalOrbitNodePolynomial_support_card]
    rw [card_rationalOrbitWeights hs hcop (hs.trans hsK)]
    have hprod : 0 < (K - r) * (K - s) :=
      Nat.mul_pos (Nat.sub_pos_of_lt hrK) (Nat.sub_pos_of_lt hsK)
    have hle : (K - r) * (K - s) ≤ K * K :=
      Nat.mul_le_mul (Nat.sub_le K r) (Nat.sub_le K s)
    simp only [← pow_two] at hle ⊢
    omega
  · intro i hi j hj
    exact rationalOrbitNodePolynomial_eval_eq_zero hi hj

/-- The exact rational collision defect in a square grid. -/
theorem card_rationalOrbitWeights_square {r s K : ℕ}
    (hs : 0 < s) (hcop : r.Coprime s) (hK : 0 < K) :
    (rationalOrbitWeights r s K K).card =
      K ^ 2 - (K - r) * (K - s) := by
  simpa [pow_two] using card_rationalOrbitWeights hs hcop hK (M := K) (N := K)

/-- Once a square exceeds both primitive steps, a rational grid has a strict collision and
therefore at most `K^2 - 1` distinct parameters.  Adding the universal one-variable node
polynomial gives an annihilator with at most `K^2` monomials. -/
theorem card_rationalOrbitWeights_lt_square {r s K : ℕ}
    (hs : 0 < s) (hcop : r.Coprime s) (hrK : r < K) (hsK : s < K) :
    (rationalOrbitWeights r s K K).card < K ^ 2 := by
  rw [card_rationalOrbitWeights_square hs hcop (hs.trans hsK)]
  have hprod : 0 < (K - r) * (K - s) :=
    Nat.mul_pos (Nat.sub_pos_of_lt hrK) (Nat.sub_pos_of_lt hsK)
  have hle : (K - r) * (K - s) ≤ K ^ 2 := by
    have hrle : K - r ≤ K := Nat.sub_le _ _
    have hsle : K - s ≤ K := Nat.sub_le _ _
    simpa [pow_two] using Nat.mul_le_mul hrle hsle
  omega

/-- The sharp cardinality dichotomy underlying the one-monomial certificate: irrational
square grids have `K^2` nodes, while every rational parameter has fewer than `K^2` nodes on
all squares larger than its reduced numerator and denominator. -/
theorem rational_irrational_squareGrid_cardinality_dichotomy
    {x : ℝ} {r s K : ℕ} (hx : x = (r : ℝ) / (s : ℝ))
    (hs : 0 < s) (hcop : r.Coprime s) (hrK : r < K) (hsK : s < K) :
    (rationalOrbitWeights r s K K).card < K ^ 2 ∧
      ¬ Irrational x := by
  constructor
  · exact card_rationalOrbitWeights_lt_square hs hcop hrK hsK
  · rw [hx]
    simp

end

end LeanProofs.TwoBaseIntegerExponent
