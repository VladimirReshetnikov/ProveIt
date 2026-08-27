import FabiusFunction.ThueMorseCatalanSeries

/-!
# The convolution identity for the substituted Catalan series

The heart of the algebraic equation for the integral lift: the
sequence `h(m)` (the substituted alternating Catalan series) satisfies
the quadratic convolution identity

`∑_{p+q=m} h(p)·h(q) = h(m) - h(m+1) - [m = 0]`,

the coefficient form of `H = 1 - u·H²` under `u = z/(1-z)`.

* `catalan_conv_interior` — the interior Catalan convolution
  `∑_{s=1}^{u-1} Cat(s)·Cat(u-s) = Cat(u+1) - 2·Cat(u)`.
* `catalanSeriesDelta_conv` — the convolution identity above.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **Interior Catalan convolution**: stripping the two boundary terms
from the Catalan recurrence,
`∑_{s=1}^{u-1} Cat(s)·Cat(u-s) = Cat(u+1) - 2·Cat(u)` for `u ≥ 1`. -/
theorem catalan_conv_interior (u : ℕ) (hu : 1 ≤ u) :
    ∑ s ∈ Icc 1 (u - 1), (catalan s : ℤ) * (catalan (u - s) : ℤ) =
      (catalan (u + 1) : ℤ) - 2 * (catalan u : ℤ) := by
  have hrec : catalan (u + 1) =
      ∑ i ∈ range (u + 1), catalan i * catalan (u - i) := by
    rw [catalan_succ,
      ← Fin.sum_univ_eq_sum_range (fun i => catalan i * catalan (u - i))
        (u + 1)]
  -- peel the two boundary terms `i = 0` and `i = u`
  have h0mem : (0 : ℕ) ∈ range (u + 1) := Finset.mem_range.mpr (by omega)
  have humem : u ∈ (range (u + 1)).erase 0 := by
    rw [Finset.mem_erase, Finset.mem_range]
    omega
  have herase2 : ((range (u + 1)).erase 0).erase u = Icc 1 (u - 1) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  have hpeel : ∑ i ∈ range (u + 1), catalan i * catalan (u - i) =
      catalan u + (catalan u +
        ∑ i ∈ Icc 1 (u - 1), catalan i * catalan (u - i)) := by
    rw [← Finset.add_sum_erase _ (fun i => catalan i * catalan (u - i))
      h0mem, catalan_zero, Nat.sub_zero, Nat.one_mul,
      ← Finset.add_sum_erase _ (fun i => catalan i * catalan (u - i))
      humem, Nat.sub_self, catalan_zero, Nat.mul_one, herase2]
  have hcast := congrArg (fun t : ℕ => (t : ℤ)) (hrec.trans hpeel)
  push_cast at hcast
  linarith [hcast]

private theorem delta_ext (M p : ℕ) (hp : 1 ≤ p) (hpM : p ≤ M) :
    catalanSeriesDelta p =
      ∑ s ∈ Icc 1 M, (-1) ^ s * (catalan s : ℤ) *
        (((p - 1).choose (s - 1) : ℕ) : ℤ) := by
  rw [catalanSeriesDelta, if_neg (by omega)]
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right hpM) ?_
  intro s hs hsnot
  have h1 := Finset.mem_Icc.mp hs
  have h2 : p < s := by
    by_contra hcon
    exact hsnot (Finset.mem_Icc.mpr ⟨h1.1, by omega⟩)
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  push_cast
  ring

private theorem vandermonde_collapse (m s t : ℕ) (hs : 1 ≤ s)
    (ht : 1 ≤ t) :
    ∑ p ∈ Icc 1 (m - 1),
        (((p - 1).choose (s - 1) : ℕ) : ℤ) *
          (((m - p - 1).choose (t - 1) : ℕ) : ℤ) =
      (((m - 1).choose (s + t - 1) : ℕ) : ℤ) := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · -- degenerate: the interval is empty and the binomial vanishes
    have hempty : Icc 1 (m - 1) = ∅ := by
      apply Finset.Icc_eq_empty
      omega
    rw [hempty, Finset.sum_empty]
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      norm_num
    · have hm2 : m = 1 := by omega
      subst hm2
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      norm_num
  · -- genuine case: reindex and apply the diagonal Vandermonde
    have hreindex : ∑ p ∈ Icc 1 (m - 1),
        (((p - 1).choose (s - 1) : ℕ) : ℤ) *
          (((m - p - 1).choose (t - 1) : ℕ) : ℤ) =
        ∑ i ∈ range (m - 1),
          ((i.choose (s - 1) : ℕ) : ℤ) *
            ((((m - 2) - i).choose (t - 1) : ℕ) : ℤ) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by congr 1) fun i hi => ?_
      have := Finset.mem_range.mp hi
      rw [show 1 + i - 1 = i by omega,
        show m - (1 + i) - 1 = (m - 2) - i by omega]
    rw [hreindex]
    have hV := sum_range_choose_mul_choose (t - 1) (m - 2) (s - 1)
    have hcast := congrArg (fun x : ℕ => (x : ℤ)) hV
    push_cast at hcast
    rw [show m - 2 + 1 = m - 1 by omega] at hcast
    rw [show (s - 1) + (t - 1) + 1 = s + t - 1 by omega] at hcast
    rw [← hcast]

/-- **The convolution identity for the substituted Catalan series**
(`H = 1 - u·H²` in coefficients):
`∑_{p+q=m} h(p)·h(q) = h(m) - h(m+1) - [m = 0]`. -/
theorem catalanSeriesDelta_conv (m : ℕ) :
    ∑ p ∈ range (m + 1), catalanSeriesDelta p * catalanSeriesDelta (m - p) =
      catalanSeriesDelta m - catalanSeriesDelta (m + 1) -
        (if m = 0 then 1 else 0) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [catalanSeriesDelta_one]
  rw [if_neg (by omega)]
  -- peel the boundary terms `p = 0` and `p = m`
  have h0mem : (0 : ℕ) ∈ range (m + 1) := Finset.mem_range.mpr (by omega)
  have hmmem : m ∈ (range (m + 1)).erase 0 := by
    rw [Finset.mem_erase, Finset.mem_range]
    omega
  have herase2 : ((range (m + 1)).erase 0).erase m = Icc 1 (m - 1) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  have hpeel : ∑ p ∈ range (m + 1),
      catalanSeriesDelta p * catalanSeriesDelta (m - p) =
      catalanSeriesDelta m + (catalanSeriesDelta m +
        ∑ p ∈ Icc 1 (m - 1),
          catalanSeriesDelta p * catalanSeriesDelta (m - p)) := by
    rw [← Finset.add_sum_erase _
      (fun p => catalanSeriesDelta p * catalanSeriesDelta (m - p)) h0mem,
      catalanSeriesDelta_zero, Nat.sub_zero, one_mul,
      ← Finset.add_sum_erase _
      (fun p => catalanSeriesDelta p * catalanSeriesDelta (m - p)) hmmem,
      Nat.sub_self, catalanSeriesDelta_zero, mul_one, herase2]
  rw [hpeel]
  -- the interior double sum, collapsed through the diagonal Vandermonde
  have hexpand : ∑ p ∈ Icc 1 (m - 1),
      catalanSeriesDelta p * catalanSeriesDelta (m - p) =
      ∑ s ∈ Icc 1 m, ∑ t ∈ Icc 1 m,
        ((-1) ^ s * (catalan s : ℤ)) * ((-1) ^ t * (catalan t : ℤ)) *
          (((m - 1).choose (s + t - 1) : ℕ) : ℤ) := by
    have hterm : ∀ p ∈ Icc 1 (m - 1),
        catalanSeriesDelta p * catalanSeriesDelta (m - p) =
        ∑ s ∈ Icc 1 m, ∑ t ∈ Icc 1 m,
          ((-1) ^ s * (catalan s : ℤ)) * ((-1) ^ t * (catalan t : ℤ)) *
            ((((p - 1).choose (s - 1) : ℕ) : ℤ) *
              (((m - p - 1).choose (t - 1) : ℕ) : ℤ)) := by
      intro p hp
      have h1 := Finset.mem_Icc.mp hp
      rw [delta_ext m p (by omega) (by omega),
        delta_ext m (m - p) (by omega) (by omega),
        Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl
        fun t _ => ?_
      rw [show m - p - 1 = (m - p) - 1 from rfl]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    -- now swap the `p`-sum inside and collapse it
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t ht => ?_
    have hs1 := (Finset.mem_Icc.mp hs).1
    have ht1 := (Finset.mem_Icc.mp ht).1
    rw [← Finset.mul_sum, vandermonde_collapse m s t hs1 ht1]
  rw [hexpand]
  -- restrict to the triangle `s + t ≤ m` (the binomial vanishes beyond)
  have htriangle : ∑ s ∈ Icc 1 m, ∑ t ∈ Icc 1 m,
      ((-1) ^ s * (catalan s : ℤ)) * ((-1) ^ t * (catalan t : ℤ)) *
        (((m - 1).choose (s + t - 1) : ℕ) : ℤ) =
      ∑ u ∈ Icc 2 m, (-1) ^ u * (((m - 1).choose (u - 1) : ℕ) : ℤ) *
        ((catalan (u + 1) : ℤ) - 2 * (catalan u : ℤ)) := by
    -- iterate to a sigma sum over the triangle and reindex by `u = s + t`
    rw [← Finset.sum_product']
    have hrestrict : ∑ st ∈ Icc 1 m ×ˢ Icc 1 m,
        ((-1) ^ st.1 * (catalan st.1 : ℤ)) *
          ((-1) ^ st.2 * (catalan st.2 : ℤ)) *
          (((m - 1).choose (st.1 + st.2 - 1) : ℕ) : ℤ) =
        ∑ st ∈ (Icc 1 m ×ˢ Icc 1 m).filter (fun st => st.1 + st.2 ≤ m),
          ((-1) ^ st.1 * (catalan st.1 : ℤ)) *
            ((-1) ^ st.2 * (catalan st.2 : ℤ)) *
            (((m - 1).choose (st.1 + st.2 - 1) : ℕ) : ℤ) := by
      symm
      refine Finset.sum_filter_of_ne fun st hst hne => ?_
      by_contra hcon
      have h1 := Finset.mem_product.mp hst
      have h2 := Finset.mem_Icc.mp h1.1
      have h3 := Finset.mem_Icc.mp h1.2
      have h4 : m - 1 < st.1 + st.2 - 1 := by omega
      rw [Nat.choose_eq_zero_of_lt h4] at hne
      push_cast at hne
      exact hne (by ring)
    rw [hrestrict]
    -- bijection: the triangle ↔ pairs `(u, s)` with `2 ≤ u ≤ m`,
    -- `1 ≤ s ≤ u - 1`
    have hbij : ∑ st ∈ (Icc 1 m ×ˢ Icc 1 m).filter
          (fun st => st.1 + st.2 ≤ m),
        ((-1) ^ st.1 * (catalan st.1 : ℤ)) *
          ((-1) ^ st.2 * (catalan st.2 : ℤ)) *
          (((m - 1).choose (st.1 + st.2 - 1) : ℕ) : ℤ) =
        ∑ u ∈ Icc 2 m, ∑ s ∈ Icc 1 (u - 1),
          ((-1) ^ s * (catalan s : ℤ)) *
            ((-1) ^ (u - s) * (catalan (u - s) : ℤ)) *
            (((m - 1).choose (u - 1) : ℕ) : ℤ) := by
      rw [Finset.sum_sigma']
      refine Finset.sum_nbij' (fun st => ⟨st.1 + st.2, st.1⟩)
        (fun us => (us.2, us.1 - us.2)) ?_ ?_ ?_ ?_ ?_
      · intro st hst
        have h1 := Finset.mem_filter.mp hst
        have h2 := Finset.mem_product.mp h1.1
        have h3 := Finset.mem_Icc.mp h2.1
        have h4 := Finset.mem_Icc.mp h2.2
        have h5 : st.1 + st.2 ≤ m := h1.2
        refine Finset.mem_sigma.mpr ⟨?_, ?_⟩ <;>
          refine Finset.mem_Icc.mpr ⟨?_, ?_⟩ <;> dsimp only <;> omega
      · intro us hus
        have h1 := Finset.mem_sigma.mp hus
        have h2 := Finset.mem_Icc.mp h1.1
        have h3 := Finset.mem_Icc.mp h1.2
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_product.mpr ⟨?_, ?_⟩ <;>
            refine Finset.mem_Icc.mpr ⟨?_, ?_⟩ <;> dsimp only <;> omega
        · dsimp only
          omega
      · intro st hst
        have h1 := Finset.mem_filter.mp hst
        have h2 := Finset.mem_product.mp h1.1
        have h3 := Finset.mem_Icc.mp h2.1
        refine Prod.ext ?_ ?_ <;> (dsimp only; omega)
      · intro us hus
        have h1 := Finset.mem_sigma.mp hus
        have h2 := Finset.mem_Icc.mp h1.1
        have h3 := Finset.mem_Icc.mp h1.2
        refine Sigma.ext ?_ ?_
        · dsimp only
          omega
        · exact HEq.rfl
      · intro st hst
        have h1 := Finset.mem_filter.mp hst
        have h2 := Finset.mem_product.mp h1.1
        have h3 := Finset.mem_Icc.mp h2.1
        have h4 := Finset.mem_Icc.mp h2.2
        simp only
        rw [show st.1 + st.2 - st.1 = st.2 by omega]
    rw [hbij]
    -- collapse each `u`-row through the interior Catalan convolution
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu2 := Finset.mem_Icc.mp hu
    have hrow : ∀ s ∈ Icc 1 (u - 1),
        ((-1) ^ s * (catalan s : ℤ)) *
          ((-1) ^ (u - s) * (catalan (u - s) : ℤ)) *
          (((m - 1).choose (u - 1) : ℕ) : ℤ) =
        (-1) ^ u * (((m - 1).choose (u - 1) : ℕ) : ℤ) *
          ((catalan s : ℤ) * (catalan (u - s) : ℤ)) := by
      intro s hs
      have hs1 := Finset.mem_Icc.mp hs
      have hsign : (-1 : ℤ) ^ s * (-1) ^ (u - s) = (-1) ^ u := by
        rw [← pow_add]
        congr 1
        omega
      calc ((-1) ^ s * (catalan s : ℤ)) *
            ((-1) ^ (u - s) * (catalan (u - s) : ℤ)) *
            (((m - 1).choose (u - 1) : ℕ) : ℤ)
          = ((-1 : ℤ) ^ s * (-1) ^ (u - s)) *
              (((m - 1).choose (u - 1) : ℕ) : ℤ) *
              ((catalan s : ℤ) * (catalan (u - s) : ℤ)) := by ring
        _ = (-1) ^ u * (((m - 1).choose (u - 1) : ℕ) : ℤ) *
              ((catalan s : ℤ) * (catalan (u - s) : ℤ)) := by
            rw [hsign]
    rw [Finset.sum_congr rfl hrow, ← Finset.mul_sum,
      catalan_conv_interior u (by omega)]
  rw [htriangle]
  -- boundary-peel comparisons: `S2 = h(m) + 1` and `S1 = h(m) - h(m+1) + 2`
  have hS2 : ∑ u ∈ Icc 2 m, (-1) ^ u *
      (((m - 1).choose (u - 1) : ℕ) : ℤ) * (catalan u : ℤ) =
      catalanSeriesDelta m + 1 := by
    rw [catalanSeriesDelta, if_neg (by omega)]
    have h1mem : (1 : ℕ) ∈ Icc 1 m := Finset.mem_Icc.mpr (by omega)
    have herase : (Icc 1 m).erase 1 = Icc 2 m := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_Icc]
      omega
    rw [← Finset.add_sum_erase _
      (fun t => (-1) ^ t * (catalan t : ℤ) * ((m - 1).choose (t - 1) : ℤ))
      h1mem, herase]
    have hone : (-1 : ℤ) ^ 1 * (catalan 1 : ℤ) *
        ((m - 1).choose (1 - 1) : ℤ) = -1 := by
      norm_num [catalan_one]
    rw [hone]
    have hcong : ∀ u ∈ Icc 2 m,
        (-1 : ℤ) ^ u * (catalan u : ℤ) * ((m - 1).choose (u - 1) : ℤ) =
        (-1) ^ u * (((m - 1).choose (u - 1) : ℕ) : ℤ) * (catalan u : ℤ) := by
      intro u _
      ring
    rw [Finset.sum_congr rfl hcong]
    ring
  have hS1 : ∑ u ∈ Icc 2 m, (-1) ^ u *
      (((m - 1).choose (u - 1) : ℕ) : ℤ) * (catalan (u + 1) : ℤ) =
      catalanSeriesDelta m - catalanSeriesDelta (m + 1) + 2 := by
    -- expand `h(m+1)`, peel `t = 1`, split by Pascal, and reassemble
    have hsucc : catalanSeriesDelta (m + 1) =
        ∑ t ∈ Icc 1 (m + 1), (-1) ^ t * (catalan t : ℤ) *
          ((m.choose (t - 1) : ℕ) : ℤ) := by
      rw [catalanSeriesDelta, if_neg (by omega)]
      rfl
    have h1mem : (1 : ℕ) ∈ Icc 1 (m + 1) := Finset.mem_Icc.mpr (by omega)
    have herase : (Icc 1 (m + 1)).erase 1 = Icc 2 (m + 1) := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_Icc]
      omega
    have hsplit : catalanSeriesDelta (m + 1) =
        -1 + ∑ t ∈ Icc 2 (m + 1), (-1) ^ t * (catalan t : ℤ) *
          ((((m - 1).choose (t - 1) : ℕ) : ℤ) +
            (((m - 1).choose (t - 2) : ℕ) : ℤ)) := by
      rw [hsucc, ← Finset.add_sum_erase _
        (fun t => (-1) ^ t * (catalan t : ℤ) * ((m.choose (t - 1) : ℕ) : ℤ))
        h1mem, herase]
      have hone : (-1 : ℤ) ^ 1 * (catalan 1 : ℤ) *
          ((m.choose (1 - 1) : ℕ) : ℤ) = -1 := by
        norm_num [catalan_one]
      rw [hone]
      congr 1
      refine Finset.sum_congr rfl fun t ht => ?_
      have ht2 := Finset.mem_Icc.mp ht
      have hPascal : m.choose (t - 1) =
          (m - 1).choose (t - 1) + (m - 1).choose (t - 2) := by
        have := Nat.choose_succ_succ (m - 1) (t - 2)
        simp only [Nat.succ_eq_add_one] at this
        rw [show m - 1 + 1 = m by omega,
          show t - 2 + 1 = t - 1 by omega] at this
        omega
      rw [hPascal]
      push_cast
      ring
    -- first Pascal half: `h(m)` with its top extension
    have hhalf1 : ∑ t ∈ Icc 2 (m + 1), (-1) ^ t * (catalan t : ℤ) *
        (((m - 1).choose (t - 1) : ℕ) : ℤ) =
        catalanSeriesDelta m + 1 := by
      have htop : ∑ t ∈ Icc 2 (m + 1), (-1) ^ t * (catalan t : ℤ) *
          (((m - 1).choose (t - 1) : ℕ) : ℤ) =
          ∑ t ∈ Icc 2 m, (-1) ^ t * (catalan t : ℤ) *
            (((m - 1).choose (t - 1) : ℕ) : ℤ) := by
        symm
        refine Finset.sum_subset (Finset.Icc_subset_Icc_right (by omega)) ?_
        intro t ht htnot
        have h1 := Finset.mem_Icc.mp ht
        have h2 : t = m + 1 := by
          by_contra hcon
          exact htnot (Finset.mem_Icc.mpr ⟨h1.1, by omega⟩)
        subst h2
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        push_cast
        ring
      rw [htop]
      rw [catalanSeriesDelta, if_neg (by omega)]
      have h1mem : (1 : ℕ) ∈ Icc 1 m := Finset.mem_Icc.mpr (by omega)
      have herase1 : (Icc 1 m).erase 1 = Icc 2 m := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_Icc]
        omega
      rw [← Finset.add_sum_erase _
        (fun t => (-1) ^ t * (catalan t : ℤ) * ((m - 1).choose (t - 1) : ℤ))
        h1mem, herase1]
      have hone : (-1 : ℤ) ^ 1 * (catalan 1 : ℤ) *
          ((m - 1).choose (1 - 1) : ℤ) = -1 := by
        norm_num [catalan_one]
      rw [hone]
      ring
    -- second Pascal half: peel `t = 2` and shift into `S1`
    have hhalf2 : ∑ t ∈ Icc 2 (m + 1), (-1) ^ t * (catalan t : ℤ) *
        (((m - 1).choose (t - 2) : ℕ) : ℤ) =
        2 - ∑ u ∈ Icc 2 m, (-1) ^ u *
          (((m - 1).choose (u - 1) : ℕ) : ℤ) * (catalan (u + 1) : ℤ) := by
      have h2mem : (2 : ℕ) ∈ Icc 2 (m + 1) := Finset.mem_Icc.mpr (by omega)
      have herase2 : (Icc 2 (m + 1)).erase 2 = Icc 3 (m + 1) := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_Icc]
        omega
      rw [← Finset.add_sum_erase _
        (fun t => (-1) ^ t * (catalan t : ℤ) *
          ((((m - 1).choose (t - 2) : ℕ) : ℤ)))
        h2mem, herase2]
      have htwo : (-1 : ℤ) ^ 2 * (catalan 2 : ℤ) *
          ((((m - 1).choose (2 - 2) : ℕ) : ℤ)) = 2 := by
        norm_num [catalan_two]
      rw [htwo]
      have hshift : ∑ t ∈ Icc 3 (m + 1), (-1) ^ t * (catalan t : ℤ) *
          ((((m - 1).choose (t - 2) : ℕ) : ℤ)) =
          -∑ u ∈ Icc 2 m, (-1) ^ u *
            (((m - 1).choose (u - 1) : ℕ) : ℤ) * (catalan (u + 1) : ℤ) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_nbij' (fun t => t - 1) (fun u => u + 1)
          ?_ ?_ ?_ ?_ ?_
        · intro t ht
          have := Finset.mem_Icc.mp ht
          exact Finset.mem_Icc.mpr (by omega)
        · intro u hu
          have := Finset.mem_Icc.mp hu
          exact Finset.mem_Icc.mpr (by omega)
        · intro t ht
          have := Finset.mem_Icc.mp ht
          omega
        · intro u hu
          omega
        · intro t ht
          have ht3 := Finset.mem_Icc.mp ht
          rw [show t - 1 + 1 = t by omega,
            show t - 1 - 1 = t - 2 by omega,
            show (-1 : ℤ) ^ (t - 1) = (-1) ^ t * (-1) from ?_]
          · ring
          · rw [show t = (t - 1) + 1 by omega, pow_succ]
            rw [show t - 1 + 1 - 1 = t - 1 by omega]
            ring
      rw [hshift]
      ring
    have := hsplit
    rw [Finset.sum_congr rfl (fun t ht =>
      by rw [mul_add] :
      ∀ t ∈ Icc 2 (m + 1),
        (-1 : ℤ) ^ t * (catalan t : ℤ) *
          ((((m - 1).choose (t - 1) : ℕ) : ℤ) +
            (((m - 1).choose (t - 2) : ℕ) : ℤ)) =
        (-1) ^ t * (catalan t : ℤ) * (((m - 1).choose (t - 1) : ℕ) : ℤ) +
          (-1) ^ t * (catalan t : ℤ) * (((m - 1).choose (t - 2) : ℕ) : ℤ)),
      Finset.sum_add_distrib, hhalf1, hhalf2] at this
    linarith [this]
  -- assemble
  have hfinal : ∑ u ∈ Icc 2 m, (-1) ^ u *
      (((m - 1).choose (u - 1) : ℕ) : ℤ) *
      ((catalan (u + 1) : ℤ) - 2 * (catalan u : ℤ)) =
      (∑ u ∈ Icc 2 m, (-1) ^ u *
        (((m - 1).choose (u - 1) : ℕ) : ℤ) * (catalan (u + 1) : ℤ)) -
      2 * ∑ u ∈ Icc 2 m, (-1) ^ u *
        (((m - 1).choose (u - 1) : ℕ) : ℤ) * (catalan u : ℤ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  rw [hfinal, hS1, hS2]
  ring

end Fabius
