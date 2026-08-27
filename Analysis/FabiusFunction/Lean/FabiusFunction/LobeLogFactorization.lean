import FabiusFunction.CentralLobeOnePeak

/-!
# The log-factorization of `|Φ|` on every lobe

The bridge that frees `thm:one-peak` from the central lobe: at every
real point `x` that is not a lattice zero,

`log ‖Φ(x)‖ = ∑'_{(h,r)} log (1 − x²/(2ʰ(r+1))²)`,

where finitely many factors are negative (those with zero `≤ |x|`) and
`Real.log`'s junk extension `log t = log |t|` absorbs their signs.

The finitely many exceptional pairs are collected in the Finset
`lobeExceptional |x|`; on its complement the factors are positive and
`Real.hasProd_of_hasSum_log` applies, and `Finset.hasProd_compl_iff`
re-attaches the exceptional block.

* `lobeExceptional`, `mem_lobeExceptional_iff` — the exceptional set.
* `abs_log_one_sub_le` — the reusable `|log(1−u)| ≤ u/c` bracket.
* `summable_log_lobe_factors` — unconditional summability.
* `log_norm_rvachevFourierProduct_eq_tsum` — **the identity**.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-! ## The exceptional set -/

/-- The finitely many lattice pairs whose zero `2^{p.1}·(p.2+1)` lies
at or below the threshold `c`. -/
noncomputable def lobeExceptional (c : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.range (⌊c⌋₊ + 1) ×ˢ Finset.range (⌊c⌋₊ + 1)).filter
    (fun p => 2 ^ p.1 * (p.2 + 1) ≤ ⌊c⌋₊)

/-- For `0 ≤ c`, a pair is exceptional exactly when its lattice value is at most `c`. -/
theorem mem_lobeExceptional_iff {c : ℝ} (hc : 0 ≤ c) (p : ℕ × ℕ) :
    p ∈ lobeExceptional c ↔ lobeZero p ≤ c := by
  unfold lobeExceptional
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_range]
  constructor
  · rintro ⟨-, hle⟩
    show ((2 ^ p.1 * (p.2 + 1) : ℕ) : ℝ) ≤ c
    exact (Nat.le_floor_iff hc).mp hle
  · intro hle
    have hle' : ((2 ^ p.1 * (p.2 + 1) : ℕ) : ℝ) ≤ c := hle
    have hnat : 2 ^ p.1 * (p.2 + 1) ≤ ⌊c⌋₊ := Nat.le_floor hle'
    have hb1 : 2 ^ p.1 ≤ 2 ^ p.1 * (p.2 + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have hb2 : p.2 + 1 ≤ 2 ^ p.1 * (p.2 + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    refine ⟨⟨?_, ?_⟩, hnat⟩
    · exact lt_trans
        (lt_of_lt_of_le Nat.lt_two_pow_self (le_trans hb1 hnat))
        (Nat.lt_succ_self _)
    · exact lt_trans (Nat.lt_of_succ_le (le_trans hb2 hnat))
        (Nat.lt_succ_self _)

/-- For `0 ≤ c`, every pair outside `lobeExceptional c` has lattice value above `c`. -/
theorem lt_lobeZero_of_not_mem {c : ℝ} (hc : 0 ≤ c) {p : ℕ × ℕ}
    (hp : p ∉ lobeExceptional c) : c < lobeZero p := by
  by_contra h
  exact hp ((mem_lobeExceptional_iff hc p).mpr (not_lt.mp h))

/-- Quantitative gap on the complement: the zeros jump past the next
integer above `c`. -/
theorem floor_succ_le_lobeZero_of_not_mem {c : ℝ} (hc : 0 ≤ c)
    {p : ℕ × ℕ} (hp : p ∉ lobeExceptional c) :
    ((⌊c⌋₊ + 1 : ℕ) : ℝ) ≤ lobeZero p := by
  have h := lt_lobeZero_of_not_mem hc hp
  have hfl : ((⌊c⌋₊ : ℕ) : ℝ) ≤ c := Nat.floor_le hc
  have hcast : ((⌊c⌋₊ : ℕ) : ℝ) < ((2 ^ p.1 * (p.2 + 1) : ℕ) : ℝ) :=
    lt_of_le_of_lt hfl (by simpa [lobeZero] using h)
  have hnat : ⌊c⌋₊ < 2 ^ p.1 * (p.2 + 1) := by exact_mod_cast hcast
  show ((⌊c⌋₊ + 1 : ℕ) : ℝ) ≤ lobeZero p
  simp only [lobeZero]
  exact_mod_cast hnat

/-! ## Factor signs -/

/-- Factors beyond the threshold are positive. -/
theorem factor_pos_of_abs_lt {x : ℝ} {p : ℕ × ℕ}
    (h : |x| < lobeZero p) : 0 < 1 - x ^ 2 / (lobeZero p) ^ 2 := by
  have ha := lobeZero_pos p
  have hsq : x ^ 2 < (lobeZero p) ^ 2 := by
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ < (lobeZero p) ^ 2 :=
        pow_lt_pow_left₀ h (abs_nonneg x) two_ne_zero
  have := (div_lt_one (by positivity :
    (0:ℝ) < (lobeZero p) ^ 2)).mpr hsq
  linarith

/-- Factors at or below the threshold are negative. -/
theorem factor_neg_of_lt_abs {x : ℝ} {p : ℕ × ℕ}
    (h : lobeZero p < |x|) : 1 - x ^ 2 / (lobeZero p) ^ 2 < 0 := by
  have ha := lobeZero_pos p
  have hsq : (lobeZero p) ^ 2 < x ^ 2 := by
    calc (lobeZero p) ^ 2 < |x| ^ 2 :=
        pow_lt_pow_left₀ h ha.le two_ne_zero
      _ = x ^ 2 := sq_abs x
  have := (one_lt_div (by positivity :
    (0:ℝ) < (lobeZero p) ^ 2)).mpr hsq
  linarith

/-! ## The elementary log bracket -/

/-- For `0 ≤ u` with `c ≤ 1 − u`, `|log(1−u)| ≤ u/c`. -/
theorem abs_log_one_sub_le {u c : ℝ} (hu : 0 ≤ u) (hc : 0 < c)
    (hcf : c ≤ 1 - u) : |Real.log (1 - u)| ≤ u / c := by
  have hf : (0:ℝ) < 1 - u := lt_of_lt_of_le hc hcf
  have hf1 : 1 - u ≤ 1 := by linarith
  rw [abs_of_nonpos (Real.log_nonpos hf.le hf1)]
  have hlb : 1 - 1 / (1 - u) ≤ Real.log (1 - u) := by
    have h := Real.log_le_sub_one_of_pos
      (show (0:ℝ) < (1 - u)⁻¹ by positivity)
    rw [Real.log_inv, ← one_div] at h
    linarith
  have hq : 1 / (1 - u) - 1 = u / (1 - u) := by
    rw [eq_div_iff hf.ne', sub_mul, one_div, inv_mul_cancel₀ hf.ne']
    ring
  have hmono : u / (1 - u) ≤ u / c :=
    div_le_div_of_nonneg_left hu hc hcf
  linarith

/-! ## Summability -/

/-- On the complement of the exceptional set the factor logs are
summable, with the uniform gap `1 − x²/(⌊|x|⌋+1)²` powering the
majorant. -/
theorem summable_log_compl (x : ℝ) :
    Summable (fun p : {p : ℕ × ℕ // p ∉ lobeExceptional |x|} =>
      Real.log (1 - x ^ 2 / (lobeZero p.val) ^ 2)) := by
  set A : ℝ := ((⌊|x|⌋₊ + 1 : ℕ) : ℝ) with hA
  have hA0 : 0 < A := by positivity
  have hxA : |x| < A := by
    have := Nat.lt_floor_add_one |x|
    simpa [hA] using this
  have hc0 : (0:ℝ) < 1 - x ^ 2 / A ^ 2 := by
    have hsq : x ^ 2 < A ^ 2 := by
      calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
        _ < A ^ 2 := pow_lt_pow_left₀ hxA (abs_nonneg x) two_ne_zero
    have := (div_lt_one (by positivity : (0:ℝ) < A ^ 2)).mpr hsq
    linarith
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun p => abs_nonneg _)
    (fun p => ?_)
    (((summable_inv_sq_lobeZero.mul_left
      (x ^ 2 / (1 - x ^ 2 / A ^ 2))).comp_injective
      Subtype.val_injective))
  have hgap : A ≤ lobeZero p.val :=
    floor_succ_le_lobeZero_of_not_mem (abs_nonneg x) p.property
  have ha0 := lobeZero_pos p.val
  have hdivle : x ^ 2 / (lobeZero p.val) ^ 2 ≤ x ^ 2 / A ^ 2 := by
    apply div_le_div_of_nonneg_left (sq_nonneg x)
      (by positivity)
    exact pow_le_pow_left₀ hA0.le hgap 2
  have hbound := abs_log_one_sub_le
    (u := x ^ 2 / (lobeZero p.val) ^ 2) (c := 1 - x ^ 2 / A ^ 2)
    (by positivity) hc0 (by linarith)
  calc |Real.log (1 - x ^ 2 / (lobeZero p.val) ^ 2)| ≤
      (x ^ 2 / (lobeZero p.val) ^ 2) / (1 - x ^ 2 / A ^ 2) :=
        hbound
    _ = x ^ 2 / (1 - x ^ 2 / A ^ 2) *
        (1 / (lobeZero p.val) ^ 2) := by
        field_simp
    _ = ((fun q : ℕ × ℕ => x ^ 2 / (1 - x ^ 2 / A ^ 2) *
        (1 / (lobeZero q) ^ 2)) ∘ Subtype.val) p := rfl

/-- The factor logs are summable at **every** real point (junk values
`log 0 = 0`, `log(negative) = log|·|` included). -/
theorem summable_log_lobe_factors (x : ℝ) :
    Summable (fun p : ℕ × ℕ =>
      Real.log (1 - x ^ 2 / (lobeZero p) ^ 2)) := by
  have h := (summable_log_compl x).hasSum
  exact ((Finset.hasSum_compl_iff
    (f := fun p : ℕ × ℕ => Real.log (1 - x ^ 2 / (lobeZero p) ^ 2))
    (lobeExceptional |x|)).mp h).summable

/-! ## The factor identity and the norm factorization -/

/-- The pair-product factor of `Φ` is the real lattice factor. -/
theorem one_add_sineTerm_eq (x : ℝ) (p : ℕ × ℕ) :
    (1 + sineTerm ((x : ℂ) / 2 ^ p.1) p.2) =
      ((1 - x ^ 2 / (lobeZero p) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨h, r⟩ := p
  have h2 : ((2:ℂ) ^ h) ≠ 0 := pow_ne_zero h two_ne_zero
  have hr : ((r:ℂ) + 1) ≠ 0 := by
    rw [show ((r:ℂ) + 1) = ((r + 1 : ℕ) : ℂ) by push_cast; ring]
    exact Nat.cast_ne_zero.mpr r.succ_ne_zero
  simp only [sineTerm, lobeZero]
  push_cast
  field_simp
  ring

/-- Off the zero lattice every factor is nonzero. -/
theorem factor_ne_zero_of_ne {x : ℝ} {p : ℕ × ℕ}
    (h : lobeZero p ≠ |x|) : 1 - x ^ 2 / (lobeZero p) ^ 2 ≠ 0 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact (factor_neg_of_lt_abs hlt).ne
  · exact (factor_pos_of_abs_lt hgt).ne'

/-- **The norm factorization**: off the zero lattice,
`‖Φ(x)‖ = exp (∑' log (1 − x²/(lobe zero)²))` — the junk extension
`Real.log = log|·|` absorbing the finitely many negative factors. -/
theorem norm_rvachevFourierProduct_eq_exp_tsum {x : ℝ}
    (hx : ∀ p : ℕ × ℕ, lobeZero p ≠ |x|) :
    ‖rvachevFourierProduct (x : ℂ)‖ =
      Real.exp (∑' p : ℕ × ℕ,
        Real.log (1 - x ^ 2 / (lobeZero p) ^ 2)) := by
  -- the complex product converges to `Φ(x)`
  have hmult : Multipliable fun p : ℕ × ℕ =>
      1 + sineTerm ((x : ℂ) / 2 ^ p.1) p.2 :=
    multipliable_one_add_of_summable
      (summable_norm_sineTerm_pair (x : ℂ))
  have hprodC : HasProd (fun p : ℕ × ℕ =>
      1 + sineTerm ((x : ℂ) / 2 ^ p.1) p.2)
      (rvachevFourierProduct (x : ℂ)) := by
    rw [rvachevFourierProduct_eq_tprod_pair]
    exact hmult.hasProd
  -- push through the multiplicative norm
  have hnormProd := hprodC.map
    ({ toFun := fun z : ℂ => ‖z‖, map_one' := norm_one,
       map_mul' := norm_mul } : ℂ →* ℝ) continuous_norm
  have hn1 : HasProd (fun p : ℕ × ℕ =>
      ‖1 + sineTerm ((x : ℂ) / 2 ^ p.1) p.2‖)
      ‖rvachevFourierProduct (x : ℂ)‖ := hnormProd
  have hfun : (fun p : ℕ × ℕ =>
      ‖1 + sineTerm ((x : ℂ) / 2 ^ p.1) p.2‖) =
      fun p : ℕ × ℕ => |1 - x ^ 2 / (lobeZero p) ^ 2| := by
    funext p
    rw [one_add_sineTerm_eq x p, Complex.norm_real,
      Real.norm_eq_abs]
  rw [hfun] at hn1
  -- the positive real product converges to the exponential
  have habs : HasProd
      (fun p : ℕ × ℕ => |1 - x ^ 2 / (lobeZero p) ^ 2|)
      (Real.exp (∑' p : ℕ × ℕ,
        Real.log (1 - x ^ 2 / (lobeZero p) ^ 2))) := by
    apply Real.hasProd_of_hasSum_log
    · intro p
      exact abs_pos.mpr (factor_ne_zero_of_ne (hx p))
    · have hcongr : (fun p : ℕ × ℕ =>
          Real.log |1 - x ^ 2 / (lobeZero p) ^ 2|) =
          fun p : ℕ × ℕ =>
            Real.log (1 - x ^ 2 / (lobeZero p) ^ 2) :=
        funext fun p => Real.log_abs _
      rw [hcongr]
      exact (summable_log_lobe_factors x).hasSum
  exact hn1.unique habs

/-- **The log-factorization identity** (`thm:one-peak`'s bridge): off
the zero lattice,
`log ‖Φ(x)‖ = ∑' log (1 − x²/(lobe zero)²)`. -/
theorem log_norm_rvachevFourierProduct_eq_tsum {x : ℝ}
    (hx : ∀ p : ℕ × ℕ, lobeZero p ≠ |x|) :
    Real.log ‖rvachevFourierProduct (x : ℂ)‖ =
      ∑' p : ℕ × ℕ, Real.log (1 - x ^ 2 / (lobeZero p) ^ 2) := by
  rw [norm_rvachevFourierProduct_eq_exp_tsum hx, Real.log_exp]

/-- Off the zero lattice the modulus is strictly positive. -/
theorem norm_rvachevFourierProduct_pos_of_ne {x : ℝ}
    (hx : ∀ p : ℕ × ℕ, lobeZero p ≠ |x|) :
    0 < ‖rvachevFourierProduct (x : ℂ)‖ := by
  rw [norm_rvachevFourierProduct_eq_exp_tsum hx]
  exact Real.exp_pos _

end Fabius
