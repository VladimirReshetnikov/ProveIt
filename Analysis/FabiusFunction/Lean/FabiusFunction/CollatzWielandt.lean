import FabiusFunction.PerronEigenvalueUnique

/-!
# The Collatz–Wielandt bracket

`PerronEigenvalueUnique` pins the growth rate of `𝓛ⁿ𝟙` when an exact
positive eigenfunction is available.  Eigenfunctions are hard — their
existence needs Birkhoff–Hopf or Schauder, absent from Mathlib — but
the *inequality* form costs nothing and is what a numerical search can
actually supply: any continuous positive **test** function `h` with

`m·h ≤ 𝓛h ≤ M·h`  on `[0,1]`

brackets the growth rate, `m ≤ ρ ≤ M`.

Nothing in that argument is about `𝓛`, about `[0,1]`, or about sine
and cosine.  It uses exactly two properties of the operator —
monotonicity on the set and positive homogeneity — and exactly two of
the growth sequence — that `cₙ` is an upper bound for the orbit `Tⁿ𝟙`
on the set, and the least one.  So it is proved once, abstractly, and
the transfer operator is an instantiation.

* `iterate_mono_of_mono`, `iterate_hom` — monotonicity and
  homogeneity iterate.
* `iterate_bracket` — `mⁿ·h ≤ Tⁿh ≤ Mⁿ·h`.
* `collatzWielandt_bracket` — **the abstract bracket**.
* `perron_root_mem_of_two_sided` — its instance for `𝓛`.

The eigenfunction case is `m = M = ρ`, so
`tendsto_transferSup_rpow_of_eigenfunction` is the degenerate case of
this sandwich.
-/

set_option autoImplicit false

open Real Set Filter Topology

namespace Fabius

section Abstract

variable {T : (ℝ → ℝ) → (ℝ → ℝ)} {s : Set ℝ}

/-- Monotonicity iterates. -/
theorem iterate_mono_of_mono
    (hmono : ∀ {f g : ℝ → ℝ}, (∀ y ∈ s, f y ≤ g y) →
      ∀ x ∈ s, T f x ≤ T g x)
    {f g : ℝ → ℝ} (hfg : ∀ y ∈ s, f y ≤ g y) (n : ℕ) :
    ∀ x ∈ s, (T^[n] f) x ≤ (T^[n] g) x := by
  induction n with
  | zero => exact hfg
  | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hmono ih x hx

/-- Positive homogeneity iterates. -/
theorem iterate_hom
    (hhom : ∀ (k : ℝ) (f : ℝ → ℝ) (x : ℝ),
      T (fun y => k * f y) x = k * T f x)
    (k : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    T^[n] (fun y => k * f y) = fun x => k * (T^[n] f) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih]
      funext x
      exact hhom k (T^[n] f) x

/-- **Iterating a two-sided test inequality**: for a monotone,
positively homogeneous operator, `m·h ≤ Th ≤ M·h` on `s` iterates to
`mⁿ·h ≤ Tⁿh ≤ Mⁿ·h`. -/
theorem iterate_bracket {h : ℝ → ℝ} {m M : ℝ} (hm : 0 ≤ m) (hM : 0 ≤ M)
    (hmono : ∀ {f g : ℝ → ℝ}, (∀ y ∈ s, f y ≤ g y) →
      ∀ x ∈ s, T f x ≤ T g x)
    (hhom : ∀ (k : ℝ) (f : ℝ → ℝ) (x : ℝ),
      T (fun y => k * f y) x = k * T f x)
    (hlow : ∀ x ∈ s, m * h x ≤ T h x)
    (hhigh : ∀ x ∈ s, T h x ≤ M * h x) (n : ℕ) :
    ∀ x ∈ s, m ^ n * h x ≤ (T^[n] h) x ∧
      (T^[n] h) x ≤ M ^ n * h x := by
  induction n with
  | zero =>
      intro x _
      constructor <;> simp
  | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      refine ⟨?_, ?_⟩
      · have h1 := hmono (fun y hy => (ih y hy).1) x hx
        rw [hhom] at h1
        calc m ^ (n + 1) * h x = m ^ n * (m * h x) := by ring
          _ ≤ m ^ n * T h x :=
              mul_le_mul_of_nonneg_left (hlow x hx) (by positivity)
          _ ≤ T (T^[n] h) x := h1
      · have h1 := hmono (fun y hy => (ih y hy).2) x hx
        rw [hhom] at h1
        calc T (T^[n] h) x ≤ M ^ n * T h x := h1
          _ ≤ M ^ n * (M * h x) :=
              mul_le_mul_of_nonneg_left (hhigh x hx) (by positivity)
          _ = M ^ (n + 1) * h x := by ring

/-- **The Collatz–Wielandt bracket**.  For a monotone, positively
homogeneous `T`, with `cₙ` the least upper bound of the orbit `Tⁿ𝟙`
on `s` and `cₙ^{1/n} → ρ`, a positive test function obeying
`m·h ≤ Th ≤ M·h` forces `m ≤ ρ ≤ M`. -/
theorem collatzWielandt_bracket {h : ℝ → ℝ} {m M ρ a b x₀ : ℝ}
    {c : ℕ → ℝ}
    (hmono : ∀ {f g : ℝ → ℝ}, (∀ y ∈ s, f y ≤ g y) →
      ∀ x ∈ s, T f x ≤ T g x)
    (hhom : ∀ (k : ℝ) (f : ℝ → ℝ) (x : ℝ),
      T (fun y => k * f y) x = k * T f x)
    (hub : ∀ n : ℕ, ∀ x ∈ s, (T^[n] (fun _ => 1)) x ≤ c n)
    (hlub : ∀ (n : ℕ) (u : ℝ),
      (∀ x ∈ s, (T^[n] (fun _ => 1)) x ≤ u) → c n ≤ u)
    (hcpos : ∀ n : ℕ, 0 < c n)
    (ha0 : 0 < a) (hx₀ : x₀ ∈ s)
    (hale : ∀ x ∈ s, a ≤ h x) (hble : ∀ x ∈ s, h x ≤ b)
    (hm : 0 < m) (hM : 0 < M)
    (hlow : ∀ x ∈ s, m * h x ≤ T h x)
    (hhigh : ∀ x ∈ s, T h x ≤ M * h x)
    (hlim : Tendsto (fun n : ℕ => (c n) ^ ((1:ℝ)/n)) atTop (𝓝 ρ)) :
    m ≤ ρ ∧ ρ ≤ M := by
  have hb0 : 0 < b :=
    lt_of_lt_of_le ha0 (le_trans (hale x₀ hx₀) (hble x₀ hx₀))
  have hbr := iterate_bracket (T := T) (h := h) hm.le hM.le hmono hhom
    hlow hhigh
  constructor
  · -- lower: dominate `h` by `b·𝟙`, then test at the single point `x₀`
    have hlowbd : ∀ n : ℕ, m ^ n * (a / b) ≤ c n := by
      intro n
      have hdom : ∀ z ∈ s, h z ≤ (fun y => b * (1:ℝ)) z :=
        fun z hz => by rw [mul_one]; exact hble z hz
      have hchain : m ^ n * h x₀ ≤ b * (T^[n] (fun _ => 1)) x₀ := by
        calc m ^ n * h x₀ ≤ (T^[n] h) x₀ := (hbr n x₀ hx₀).1
          _ ≤ (T^[n] (fun y => b * (fun _ : ℝ => (1:ℝ)) y)) x₀ :=
              iterate_mono_of_mono hmono hdom n x₀ hx₀
          _ = b * (T^[n] (fun _ => 1)) x₀ := by
              rw [iterate_hom hhom b (fun _ => 1) n]
      have hfin : m ^ n * (a / b) ≤ (T^[n] (fun _ => 1)) x₀ := by
        rw [show m ^ n * (a / b) = m ^ n * a / b by ring,
          div_le_iff₀ hb0]
        nlinarith [hchain, pow_pos hm n, hale x₀ hx₀]
      exact le_trans hfin (hub n x₀ hx₀)
    refine le_of_tendsto_of_tendsto
      (tendsto_pow_mul_const_rpow hm
        (show (0:ℝ) < a / b by positivity)) hlim ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine Real.rpow_le_rpow ?_ (hlowbd n) ?_ <;> positivity
  · -- upper: dominate `𝟙` by `a⁻¹·h`, then use leastness of `cₙ`
    have hupbd : ∀ n : ℕ, c n ≤ M ^ n * (b / a) := by
      intro n
      refine hlub n _ (fun x hx => ?_)
      have hdom : ∀ z ∈ s, (fun _ : ℝ => (1:ℝ)) z ≤
          (fun y => a⁻¹ * h y) z := by
        intro z hz
        show (1:ℝ) ≤ a⁻¹ * h z
        calc (1:ℝ) = a⁻¹ * a := by rw [inv_mul_cancel₀ ha0.ne']
          _ ≤ a⁻¹ * h z :=
              mul_le_mul_of_nonneg_left (hale z hz) (by positivity)
      calc (T^[n] (fun _ => 1)) x ≤ (T^[n] (fun y => a⁻¹ * h y)) x :=
            iterate_mono_of_mono hmono hdom n x hx
        _ = a⁻¹ * (T^[n] h) x := by
            rw [iterate_hom hhom a⁻¹ h n]
        _ ≤ a⁻¹ * (M ^ n * h x) :=
            mul_le_mul_of_nonneg_left (hbr n x hx).2 (by positivity)
        _ ≤ a⁻¹ * (M ^ n * b) := by
            apply mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left (hble x hx) (by positivity)
        _ = M ^ n * (b / a) := by field_simp
    refine le_of_tendsto_of_tendsto hlim
      (tendsto_pow_mul_const_rpow hM
        (show (0:ℝ) < b / a by positivity)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine Real.rpow_le_rpow (hcpos n).le (hupbd n) ?_
    positivity

end Abstract

/-- **The bracket for the audits' transfer operator**: a continuous
test function, positive on `[0,1]`, with `m·h ≤ 𝓛h ≤ M·h` brackets the
Perron root, `m ≤ ρ ≤ M` — no eigenfunction required. -/
theorem perron_root_mem_of_two_sided {h : ℝ → ℝ} {m M ρ : ℝ}
    (hcont : Continuous h) (hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < h x)
    (hm : 0 < m) (hM : 0 < M)
    (hlow : ∀ x ∈ Set.Icc (0:ℝ) 1, m * h x ≤ rpfTransfer h x)
    (hhigh : ∀ x ∈ Set.Icc (0:ℝ) 1, rpfTransfer h x ≤ M * h x)
    (hlim : Tendsto (fun n : ℕ => (transferSup n) ^ ((1:ℝ)/n))
      atTop (𝓝 ρ)) :
    m ≤ ρ ∧ ρ ≤ M := by
  obtain ⟨xm, hxm, hminOn⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr zero_le_one) hcont.continuousOn
  obtain ⟨xM, hxM, hmaxOn⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) hcont.continuousOn
  refine collatzWielandt_bracket
    (T := rpfTransfer) (s := Set.Icc (0:ℝ) 1) (h := h)
    (a := h xm) (b := h xM) (x₀ := 0) (c := transferSup)
    (fun hfg x hx => rpfTransfer_mono hfg hx)
    rpfTransfer_const_mul
    (fun n x hx => apply_le_transferSup n hx)
    (fun n u hu => csSup_le (transferSup_image_nonempty n)
      (by rintro y ⟨x, hx, rfl⟩; exact hu x hx))
    transferSup_pos (hpos _ hxm) (by norm_num)
    (fun x hx => hminOn hx) (fun x hx => hmaxOn hx)
    hm hM hlow hhigh hlim

end Fabius
