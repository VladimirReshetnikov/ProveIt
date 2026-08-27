import FabiusFunction.BaselineDecay
import FabiusFunction.OnePeakPerLobe
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Continuity of `Φ` and the exact peak count

The pair product converges uniformly on compacts of the real axis
(`hasProdUniformlyOn_one_add` against the geometric×Basel majorant at
the endpoint radius), so `Φ` and `‖Φ‖` are continuous on `ℝ`.  With
strict log-concavity per lobe this pins the audits' `thm:one-peak`
quantitatively:

**every positive side lobe `(m, m+1)` and reflected negative side lobe
`(-(m+1), -m)`, `m ≥ 1`, contains exactly one peak of `|Φ|`**, and the
central-lobe peak is exactly `0`.

* `continuous_rvachevFourierProduct_real`, and the norm version.
* `norm_rvachevFourierProduct_lt_one_of_ne_zero` and
  `norm_rvachevFourierProduct_eq_one_iff` — the origin is the unique
  global point where `‖Φ‖ = 1`; at every nonzero real argument `‖Φ‖ < 1`.
* `isMaxOn_eq_of_strictConcaveOn_log_of_pos` — generic positive-log peak uniqueness;
  `isMaxOn_eq_of_strictConcaveOn_log` is its specialization to `‖Φ‖`.
* `existsUnique_isMaxOn_lobe` / `existsUnique_isMaxOn_neg_lobe` —
  **exactly one peak per positive or reflected negative side lobe**.
* `isMaxOn_central_eq_zero` — the central peak is the origin.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-! ## Continuity of the pair factors and of `Φ` -/

/-- Each indexed sine-product correction term is continuous along the real axis. -/
theorem continuous_sineTerm_real (p : ℕ × ℕ) :
    Continuous (fun x : ℝ => sineTerm ((x : ℂ) / 2 ^ p.1) p.2) := by
  have h : Continuous (fun x : ℝ =>
      -((x : ℂ) / 2 ^ p.1) ^ 2 / ((p.2 : ℂ) + 1) ^ 2) :=
    (((Complex.continuous_ofReal.div_const _).pow 2).neg).div_const _
  exact h

/-- Monotonicity of the factor norms in the radius. -/
theorem norm_sineTerm_le_of_abs_le {x R : ℝ} (hR : 0 ≤ R)
    (hxR : |x| ≤ R) (p : ℕ × ℕ) :
    ‖sineTerm ((x : ℂ) / 2 ^ p.1) p.2‖ ≤
      ‖sineTerm ((R : ℂ) / 2 ^ p.1) p.2‖ := by
  simp only [sineTerm, norm_div, norm_neg, norm_pow]
  have hx : ‖(x : ℂ)‖ ≤ ‖(R : ℂ)‖ := by
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hR]
    exact hxR
  gcongr

/-- **`Φ` is continuous along the real axis.** -/
theorem continuous_rvachevFourierProduct_real :
    Continuous (fun x : ℝ => rvachevFourierProduct (x : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hR0 : (0:ℝ) ≤ |x₀| + 1 := by positivity
  have hprod := Summable.hasProdUniformlyOn_one_add
    (K := Set.Icc (-(|x₀| + 1)) (|x₀| + 1))
    (isCompact_Icc)
    (summable_norm_sineTerm_pair ((|x₀| + 1 : ℝ) : ℂ))
    (Filter.Eventually.of_forall (fun p x hx => by
      have hxR : |x| ≤ |x₀| + 1 := abs_le.mpr hx
      exact norm_sineTerm_le_of_abs_le hR0 hxR p))
    (fun p => (continuous_sineTerm_real p).continuousOn)
  have htend := hprod.tendstoUniformlyOn
  have hconts : ContinuousOn (fun x : ℝ => ∏' p : ℕ × ℕ,
      (1 + sineTerm ((x : ℂ) / 2 ^ p.1) p.2))
      (Set.Icc (-(|x₀| + 1)) (|x₀| + 1)) := by
    apply htend.continuousOn
    exact (Filter.Eventually.of_forall (fun s =>
      continuousOn_finsetProd s (fun p _ =>
        (continuous_const.add
          (continuous_sineTerm_real p)).continuousOn))).frequently
  have hΦ : ContinuousOn (fun x : ℝ => rvachevFourierProduct (x : ℂ))
      (Set.Icc (-(|x₀| + 1)) (|x₀| + 1)) := by
    apply hconts.congr
    intro x _
    exact rvachevFourierProduct_eq_tprod_pair _
  exact hΦ.continuousAt (Icc_mem_nhds
    (by linarith [neg_abs_le x₀]) (by linarith [le_abs_self x₀]))

/-- **`|Φ|` is continuous along the real axis.** -/
theorem continuous_norm_rvachevFourierProduct :
    Continuous (fun x : ℝ => ‖rvachevFourierProduct (x : ℂ)‖) :=
  continuous_norm.comp continuous_rvachevFourierProduct_real

/-! ## The unique global peak -/

/-- **Global strict peak at the origin**: for every nonzero real `x`,
`‖Φ(x)‖ < 1`.  Inside the central lobe this is strict concavity;
outside it follows from the baseline bound `‖Φ(x)‖ ≤ 1 / (π|x|)`. -/
theorem norm_rvachevFourierProduct_lt_one_of_ne_zero {x : ℝ}
    (hx : x ≠ 0) :
    ‖rvachevFourierProduct (x : ℂ)‖ < 1 := by
  by_cases hcentral : |x| < 1
  · exact norm_rvachevFourierProduct_lt_one
      (Set.mem_Ioo.mpr (abs_lt.mp hcentral)) hx
  · have habs : 1 ≤ |x| := le_of_not_gt hcentral
    have hden : 0 < π * |x| :=
      mul_pos Real.pi_pos (abs_pos.mpr hx)
    have hpi_le : π ≤ π * |x| := by
      simpa using mul_le_mul_of_nonneg_left habs Real.pi_pos.le
    have hone : (1 : ℝ) < π * |x| :=
      (show (1 : ℝ) < π by linarith [Real.pi_gt_three]).trans_le hpi_le
    calc
      ‖rvachevFourierProduct (x : ℂ)‖ ≤ 1 / (π * |x|) :=
        norm_rvachevFourierProduct_le_inv hx
      _ < 1 := (div_lt_one hden).mpr hone

/-- The Rvachev Fourier product has unit norm on the real axis exactly
at the origin: `‖Φ(x)‖ = 1 ↔ x = 0`. -/
theorem norm_rvachevFourierProduct_eq_one_iff (x : ℝ) :
    ‖rvachevFourierProduct (x : ℂ)‖ = 1 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (ne_of_lt (norm_rvachevFourierProduct_lt_one_of_ne_zero hx)) h
  · rintro rfl
    simp

/-! ## Peak uniqueness from strict log-concavity -/

/-- A positive real-valued function has at most one maximizer on any set where its
logarithm is strictly concave. -/
theorem isMaxOn_eq_of_strictConcaveOn_log_of_pos
    {f : ℝ → ℝ} {s : Set ℝ} {c₁ c₂ : ℝ}
    (h : StrictConcaveOn ℝ s (fun x => Real.log (f x)))
    (hpos : ∀ x ∈ s, 0 < f x)
    (h₁ : c₁ ∈ s) (h₂ : c₂ ∈ s)
    (hmax₁ : IsMaxOn f s c₁) (hmax₂ : IsMaxOn f s c₂) :
    c₁ = c₂ := by
  apply h.eq_of_isMaxOn
  · rw [isMaxOn_iff]
    intro x hx
    exact Real.strictMonoOn_log.monotoneOn
      (hpos x hx) (hpos c₁ h₁) ((isMaxOn_iff.mp hmax₁) x hx)
  · rw [isMaxOn_iff]
    intro x hx
    exact Real.strictMonoOn_log.monotoneOn
      (hpos x hx) (hpos c₂ h₂) ((isMaxOn_iff.mp hmax₂) x hx)
  · exact h₁
  · exact h₂

/-- **Abstract peak uniqueness**: on any set where `log ‖Φ‖` is
strictly concave and `‖Φ‖` is positive, maximizers of `‖Φ‖` are
unique. -/
theorem isMaxOn_eq_of_strictConcaveOn_log {s : Set ℝ} {c₁ c₂ : ℝ}
    (h : StrictConcaveOn ℝ s
      (fun x => Real.log ‖rvachevFourierProduct (x : ℂ)‖))
    (hpos : ∀ x ∈ s, 0 < ‖rvachevFourierProduct (x : ℂ)‖)
    (h₁ : c₁ ∈ s) (h₂ : c₂ ∈ s)
    (hmax₁ : IsMaxOn (fun x : ℝ => ‖rvachevFourierProduct (x : ℂ)‖)
      s c₁)
    (hmax₂ : IsMaxOn (fun x : ℝ => ‖rvachevFourierProduct (x : ℂ)‖)
      s c₂) :
    c₁ = c₂ := by
  exact isMaxOn_eq_of_strictConcaveOn_log_of_pos
    h hpos h₁ h₂ hmax₁ hmax₂

/-! ## Exactly one peak per side lobe -/

/-- **Existence of the side-lobe peak**: for `m ≥ 1` the maximum of
`|Φ|` over `[m, m+1]` is attained in the open lobe. -/
theorem exists_isMaxOn_lobe (m : ℕ) (hm : 1 ≤ m) :
    ∃ c ∈ Set.Ioo (m:ℝ) ((m:ℝ) + 1),
      IsMaxOn (fun x : ℝ => ‖rvachevFourierProduct (x : ℂ)‖)
        (Set.Ioo (m:ℝ) ((m:ℝ) + 1)) c := by
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by linarith))
    (continuous_norm_rvachevFourierProduct.continuousOn
      (s := Set.Icc (m:ℝ) ((m:ℝ) + 1)))
  -- the endpoints are lattice zeros
  have hml : ((m:ℝ) : ℂ) = ((m : ℤ) : ℂ) := by push_cast; ring
  have hmr : (((m:ℝ) + 1 : ℝ) : ℂ) = (((m:ℤ) + 1 : ℤ) : ℂ) := by
    push_cast; ring
  have hzero_l : ‖rvachevFourierProduct (((m:ℝ) : ℝ) : ℂ)‖ = 0 := by
    rw [show (((m:ℝ) : ℝ) : ℂ) = ((m : ℤ) : ℂ) from hml,
      rvachevFourierProduct_int_eq_zero m
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hm), norm_zero]
  have hzero_r : ‖rvachevFourierProduct
      (((m:ℝ) + 1 : ℝ) : ℂ)‖ = 0 := by
    rw [hmr, rvachevFourierProduct_int_eq_zero ((m:ℤ) + 1)
      (by positivity), norm_zero]
  -- the midpoint has positive value
  have hmid_mem : (m:ℝ) + 1/2 ∈ Set.Ioo (m:ℝ) ((m:ℝ) + 1) :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have hmidpos : 0 < ‖rvachevFourierProduct
      (((m:ℝ) + 1/2 : ℝ) : ℂ)‖ :=
    norm_rvachevFourierProduct_pos_of_ne
      (lobeZero_ne_abs_of_mem_lobe hmid_mem)
  have hmid_le := (isMaxOn_iff.mp hmax) ((m:ℝ) + 1/2)
    (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
  have hcpos : 0 < ‖rvachevFourierProduct (c : ℂ)‖ :=
    lt_of_lt_of_le hmidpos hmid_le
  obtain ⟨hc1, hc2⟩ := Set.mem_Icc.mp hc
  have hcl : (m:ℝ) < c := by
    rcases lt_or_eq_of_le hc1 with h | h
    · exact h
    · exfalso
      rw [← h] at hcpos
      rw [hzero_l] at hcpos
      exact lt_irrefl 0 hcpos
  have hcr : c < (m:ℝ) + 1 := by
    rcases lt_or_eq_of_le hc2 with h | h
    · exact h
    · exfalso
      rw [h] at hcpos
      rw [hzero_r] at hcpos
      exact lt_irrefl 0 hcpos
  exact ⟨c, Set.mem_Ioo.mpr ⟨hcl, hcr⟩,
    hmax.on_subset Set.Ioo_subset_Icc_self⟩

/-- **Exactly one peak per side lobe** (`thm:one-peak`,
quantitative): for `m ≥ 1`, `|Φ|` has a unique maximizer in
`(m, m+1)`. -/
theorem existsUnique_isMaxOn_lobe (m : ℕ) (hm : 1 ≤ m) :
    ∃! c, c ∈ Set.Ioo (m:ℝ) ((m:ℝ) + 1) ∧
      IsMaxOn (fun x : ℝ => ‖rvachevFourierProduct (x : ℂ)‖)
        (Set.Ioo (m:ℝ) ((m:ℝ) + 1)) c := by
  obtain ⟨c, hc, hmax⟩ := exists_isMaxOn_lobe m hm
  refine ⟨c, ⟨hc, hmax⟩, ?_⟩
  rintro y ⟨hy, hymax⟩
  exact isMaxOn_eq_of_strictConcaveOn_log
    (strictConcaveOn_log_norm_on_lobe m)
    (fun x hx => norm_rvachevFourierProduct_pos_of_ne
      (lobeZero_ne_abs_of_mem_lobe hx))
    hy hc hymax hmax

/-- **Exactly one peak per negative side lobe** (`thm:one-peak`,
quantitative): for `m ≥ 1`, `|Φ|` has a unique maximizer in
`(-(m+1), -m)`, obtained by reflecting the positive-lobe maximizer. -/
theorem existsUnique_isMaxOn_neg_lobe (m : ℕ) (hm : 1 ≤ m) :
    ∃! c, c ∈ Set.Ioo (-((m : ℝ) + 1)) (-(m : ℝ)) ∧
      IsMaxOn (fun x : ℝ => ‖rvachevFourierProduct (x : ℂ)‖)
        (Set.Ioo (-((m : ℝ) + 1)) (-(m : ℝ))) c := by
  obtain ⟨c, ⟨hc, hmax⟩, huniq⟩ := existsUnique_isMaxOn_lobe m hm
  have hcneg : -c ∈ Set.Ioo (-((m : ℝ) + 1)) (-(m : ℝ)) := by
    obtain ⟨hc1, hc2⟩ := hc
    exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have hmaxneg :
      IsMaxOn (fun x : ℝ => ‖rvachevFourierProduct (x : ℂ)‖)
        (Set.Ioo (-((m : ℝ) + 1)) (-(m : ℝ))) (-c) := by
    rw [isMaxOn_iff]
    intro x hx
    have hxpos : -x ∈ Set.Ioo (m : ℝ) ((m : ℝ) + 1) := by
      obtain ⟨hx1, hx2⟩ := hx
      exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    have hle := (isMaxOn_iff.mp hmax) (-x) hxpos
    calc
      ‖rvachevFourierProduct (x : ℂ)‖ =
          ‖rvachevFourierProduct ((-x : ℝ) : ℂ)‖ :=
        (norm_rvachevFourierProduct_neg x).symm
      _ ≤ ‖rvachevFourierProduct (c : ℂ)‖ := hle
      _ = ‖rvachevFourierProduct ((-c : ℝ) : ℂ)‖ :=
        (norm_rvachevFourierProduct_neg c).symm
  refine ⟨-c, ⟨hcneg, hmaxneg⟩, ?_⟩
  rintro y ⟨hy, hymax⟩
  have hypos : -y ∈ Set.Ioo (m : ℝ) ((m : ℝ) + 1) := by
    obtain ⟨hy1, hy2⟩ := hy
    exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have hymaxpos :
      IsMaxOn (fun x : ℝ => ‖rvachevFourierProduct (x : ℂ)‖)
        (Set.Ioo (m : ℝ) ((m : ℝ) + 1)) (-y) := by
    rw [isMaxOn_iff]
    intro x hx
    have hxneg : -x ∈ Set.Ioo (-((m : ℝ) + 1)) (-(m : ℝ)) := by
      obtain ⟨hx1, hx2⟩ := hx
      exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    have hle := (isMaxOn_iff.mp hymax) (-x) hxneg
    calc
      ‖rvachevFourierProduct (x : ℂ)‖ =
          ‖rvachevFourierProduct ((-x : ℝ) : ℂ)‖ :=
        (norm_rvachevFourierProduct_neg x).symm
      _ ≤ ‖rvachevFourierProduct (y : ℂ)‖ := hle
      _ = ‖rvachevFourierProduct ((-y : ℝ) : ℂ)‖ :=
        (norm_rvachevFourierProduct_neg y).symm
  have h := huniq (-y) ⟨hypos, hymaxpos⟩
  linarith

/-- **The central peak is exactly the origin**: any maximizer of
`|Φ|` over `(−1,1)` equals `0`. -/
theorem isMaxOn_central_eq_zero {c : ℝ}
    (hc : c ∈ Set.Ioo (-1:ℝ) 1)
    (hmax : IsMaxOn (fun x : ℝ => ‖rvachevFourierProduct (x : ℂ)‖)
      (Set.Ioo (-1:ℝ) 1) c) :
    c = 0 :=
  isMaxOn_eq_of_strictConcaveOn_log
    strictConcaveOn_log_norm_rvachevFourierProduct
    (fun x hx => norm_rvachevFourierProduct_pos
      (abs_lt.mpr (Set.mem_Ioo.mp hx)))
    hc (Set.mem_Ioo.mpr (by norm_num)) hmax
    isMaxOn_norm_rvachevFourierProduct

end Fabius
