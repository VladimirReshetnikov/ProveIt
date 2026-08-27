import FabiusFunction.ZeroOrderTail

/-!
# The zero order of `Φ` at the integer `m`

The audits' local zero structure (`prop:canonical`, quantitative
form): at the integer `m ≥ 1` the sinc product vanishes to order
**exactly** `μ = v₂(m) + 1`.  Precisely, along the punctured
neighborhood of `m`,

`log ‖Φ(x)‖ − μ·log |x−m|` converges to the finite constant

`L(m) = ∑_{a≤m, a≠m-fiber} log(1−m²/a²) + μ·(log 2m − log m²)
        + ∑'_{a≥m+1} log(1−m²/a²)`,

hence `‖Φ(x)‖ / |x−m|^μ → e^{L(m)} > 0`: each factor of the fiber
contributes one vanishing order, and the rest of the lattice
contributes a positive constant.

* `tendsto_log_norm_sub_zero_order` — the log form.
* `tendsto_norm_div_pow_zero_order` — **the zero order**.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-- **The log form of the zero order**: near `m ≥ 1`,
`log ‖Φ(x)‖ − (v₂(m)+1)·log |x−m|` has a finite limit. -/
theorem tendsto_log_norm_sub_zero_order (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun x : ℝ => Real.log ‖rvachevFourierProduct (x:ℂ)‖ -
      ((padicValNat 2 m + 1 : ℕ) : ℝ) * Real.log |x - (m:ℝ)|)
      (𝓝[≠] (m:ℝ))
      (𝓝 ((∑ p ∈ lobeExceptional (m:ℝ) \ lobeFiber m,
          Real.log (1 - (m:ℝ) ^ 2 / (lobeZero p) ^ 2) +
        ((padicValNat 2 m + 1 : ℕ) : ℝ) *
          (Real.log ((m:ℝ) + (m:ℝ)) - Real.log ((m:ℝ) ^ 2))) +
        ∑' p : {p : ℕ × ℕ // p ∉ lobeExceptional (m:ℝ)},
          Real.log (1 - (m:ℝ) ^ 2 / (lobeZero p.val) ^ 2))) := by
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  -- the three convergent pieces
  have hfin : Tendsto (fun x : ℝ =>
      ∑ p ∈ lobeExceptional (m:ℝ) \ lobeFiber m,
        Real.log (1 - x ^ 2 / (lobeZero p) ^ 2)) (𝓝 (m:ℝ))
      (𝓝 (∑ p ∈ lobeExceptional (m:ℝ) \ lobeFiber m,
        Real.log (1 - (m:ℝ) ^ 2 / (lobeZero p) ^ 2))) := by
    apply tendsto_finsetSum
    intro p hp
    exact (continuousAt_exceptional_factor hp).tendsto
  have hmid : Tendsto (fun x : ℝ =>
      ((padicValNat 2 m + 1 : ℕ) : ℝ) *
        (Real.log ((m:ℝ) + x) - Real.log ((m:ℝ) ^ 2))) (𝓝 (m:ℝ))
      (𝓝 (((padicValNat 2 m + 1 : ℕ) : ℝ) *
        (Real.log ((m:ℝ) + (m:ℝ)) - Real.log ((m:ℝ) ^ 2)))) := by
    apply Tendsto.const_mul
    apply Tendsto.sub_const
    have h2m : ((m:ℝ) + (m:ℝ)) ≠ 0 := by linarith
    exact ((continuous_const.add
      continuous_id).continuousAt.log h2m).tendsto
  have htail : Tendsto (fun x : ℝ =>
      ∑' p : {p : ℕ × ℕ // p ∉ lobeExceptional (m:ℝ)},
        Real.log (1 - x ^ 2 / (lobeZero p.val) ^ 2)) (𝓝 (m:ℝ))
      (𝓝 (∑' p : {p : ℕ × ℕ // p ∉ lobeExceptional (m:ℝ)},
        Real.log (1 - (m:ℝ) ^ 2 / (lobeZero p.val) ^ 2))) := by
    have h : ContinuousAt (fun x : ℝ =>
        ∑' p : {p : ℕ × ℕ // p ∉ lobeExceptional (m:ℝ)},
          Real.log (1 - x ^ 2 / (lobeZero p.val) ^ 2)) (m:ℝ) :=
      (continuousOn_zero_order_tail m).continuousAt
        (Ioo_mem_nhds (by linarith) (by linarith))
    exact h.tendsto
  have hsum := ((hfin.add hmid).add htail).mono_left
    (nhdsWithin_le_nhds (s := {(m:ℝ)}ᶜ))
  apply Filter.Tendsto.congr' ?_ hsum
  -- eventual equality on the punctured window
  have hwin : ∀ᶠ x : ℝ in 𝓝[≠] (m:ℝ),
      x ∈ Set.Ioo ((m:ℝ) - 1/2) ((m:ℝ) + 1/2) :=
    (Filter.eventually_of_mem
      (Ioo_mem_nhds (by linarith) (by linarith))
      (fun x hx => hx)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hwin, eventually_mem_nhdsWithin] with x hxIoo hxc
  have hxne : x ≠ (m:ℝ) := Set.mem_compl_singleton_iff.mp hxc
  obtain ⟨hx1, hx2⟩ := hxIoo
  -- pointwise identity
  have hlat := lobeZero_ne_abs_near hm ⟨hx1, hx2⟩ hxne
  have hlog := log_norm_rvachevFourierProduct_eq_tsum hlat
  have hsub : Summable
      (fun p : {p : ℕ × ℕ // p ∉ lobeExceptional (m:ℝ)} =>
        Real.log (1 - x ^ 2 / (lobeZero p.val) ^ 2)) :=
    (summable_log_lobe_factors x).comp_injective
      Subtype.val_injective
  have hsplit := ((Finset.hasSum_compl_iff
    (f := fun p : ℕ × ℕ => Real.log (1 - x ^ 2 / (lobeZero p) ^ 2))
    (lobeExceptional (m:ℝ))).mp hsub.hasSum).tsum_eq
  have hEsplit := Finset.sum_sdiff (f := fun p : ℕ × ℕ =>
    Real.log (1 - x ^ 2 / (lobeZero p) ^ 2))
    (lobeFiber_subset_exceptional m)
  -- the fiber contributes `μ` copies of the vanishing factor
  have hfib : ∑ p ∈ lobeFiber m,
      Real.log (1 - x ^ 2 / (lobeZero p) ^ 2) =
      ((padicValNat 2 m + 1 : ℕ) : ℝ) *
        Real.log (1 - x ^ 2 / (m:ℝ) ^ 2) := by
    have hconst : ∀ p ∈ lobeFiber m,
        Real.log (1 - x ^ 2 / (lobeZero p) ^ 2) =
        Real.log (1 - x ^ 2 / (m:ℝ) ^ 2) := by
      intro p hp
      rw [(mem_lobeFiber_iff_lobeZero p).mp hp]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const,
      card_lobeFiber m hm, nsmul_eq_mul]
  -- the vanishing factor splits off `log |x−m|`
  have hmx : (m:ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxne)
  have hpx : (0:ℝ) < (m:ℝ) + x := by linarith
  have hm2 : ((m:ℝ) ^ 2) ≠ 0 := by
    have : (0:ℝ) < (m:ℝ) ^ 2 := by nlinarith
    exact this.ne'
  have hfacsplit : Real.log (1 - x ^ 2 / (m:ℝ) ^ 2) =
      Real.log |x - (m:ℝ)| + Real.log ((m:ℝ) + x) -
        Real.log ((m:ℝ) ^ 2) := by
    have hfactor : 1 - x ^ 2 / (m:ℝ) ^ 2 =
        (((m:ℝ) - x) * ((m:ℝ) + x)) / (m:ℝ) ^ 2 := by
      field_simp
      ring
    rw [hfactor, Real.log_div (mul_ne_zero hmx hpx.ne') hm2,
      Real.log_mul hmx hpx.ne']
    have habs : Real.log ((m:ℝ) - x) = Real.log |x - (m:ℝ)| := by
      rw [← Real.log_abs ((m:ℝ) - x), abs_sub_comm]
    rw [habs]
  -- assemble
  show ∑ p ∈ lobeExceptional (m:ℝ) \ lobeFiber m,
      Real.log (1 - x ^ 2 / (lobeZero p) ^ 2) +
    ((padicValNat 2 m + 1 : ℕ) : ℝ) *
      (Real.log ((m:ℝ) + x) - Real.log ((m:ℝ) ^ 2)) +
    ∑' p : {p : ℕ × ℕ // p ∉ lobeExceptional (m:ℝ)},
      Real.log (1 - x ^ 2 / (lobeZero p.val) ^ 2) =
    Real.log ‖rvachevFourierProduct (x:ℂ)‖ -
      ((padicValNat 2 m + 1 : ℕ) : ℝ) * Real.log |x - (m:ℝ)|
  rw [hlog, hsplit, ← hEsplit, hfib, hfacsplit]
  ring

/-- **The zero order of `Φ` at `m`**: `‖Φ(x)‖/|x−m|^{v₂(m)+1}`
converges to a strictly positive constant — the vanishing order is
exactly `v₂(m) + 1`. -/
theorem tendsto_norm_div_pow_zero_order (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun x : ℝ => ‖rvachevFourierProduct (x:ℂ)‖ /
      |x - (m:ℝ)| ^ (padicValNat 2 m + 1))
      (𝓝[≠] (m:ℝ))
      (𝓝 (Real.exp ((∑ p ∈ lobeExceptional (m:ℝ) \ lobeFiber m,
          Real.log (1 - (m:ℝ) ^ 2 / (lobeZero p) ^ 2) +
        ((padicValNat 2 m + 1 : ℕ) : ℝ) *
          (Real.log ((m:ℝ) + (m:ℝ)) - Real.log ((m:ℝ) ^ 2))) +
        ∑' p : {p : ℕ × ℕ // p ∉ lobeExceptional (m:ℝ)},
          Real.log (1 - (m:ℝ) ^ 2 / (lobeZero p.val) ^ 2)))) := by
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have h := tendsto_log_norm_sub_zero_order m hm
  have hexp := (Real.continuous_exp.continuousAt.tendsto).comp h
  apply Filter.Tendsto.congr' ?_ hexp
  have hwin : ∀ᶠ x : ℝ in 𝓝[≠] (m:ℝ),
      x ∈ Set.Ioo ((m:ℝ) - 1/2) ((m:ℝ) + 1/2) :=
    (Filter.eventually_of_mem
      (Ioo_mem_nhds (by linarith) (by linarith))
      (fun x hx => hx)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hwin, eventually_mem_nhdsWithin] with x hxIoo hxc
  have hxne : x ≠ (m:ℝ) := Set.mem_compl_singleton_iff.mp hxc
  have hlat := lobeZero_ne_abs_near hm hxIoo hxne
  have hpos := norm_rvachevFourierProduct_pos_of_ne hlat
  have habs : (0:ℝ) < |x - (m:ℝ)| :=
    abs_pos.mpr (sub_ne_zero.mpr hxne)
  show Real.exp (Real.log ‖rvachevFourierProduct (x:ℂ)‖ -
      ((padicValNat 2 m + 1 : ℕ) : ℝ) * Real.log |x - (m:ℝ)|) =
    ‖rvachevFourierProduct (x:ℂ)‖ /
      |x - (m:ℝ)| ^ (padicValNat 2 m + 1)
  rw [Real.exp_sub, Real.exp_log hpos, Real.exp_nat_mul,
    Real.exp_log habs]

end Fabius
