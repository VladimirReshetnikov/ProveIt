import New.Spanning.Frames.Gains

/-!
# The sum over the shells

The positions are cut into shells by their height. On one shell the bound for one frame loses a
power of the height. Below a threshold this loss is affordable. Above it every position has a deep
vector, whose gain pays for the loss. The argument is the same at a real place and at the finite
places; the shells that are summed have the powers of 2 as heights.

Notions from other files:
* A `PlaceData` `F` at the place is its data: a unit `F.levelUnit`, the positions, a compact box and
  measures.
* A gauge `Γ` is a notion of size at the place, with a scale `Γ.loss ≥ 2` that bounds volumes.
* `F.formMajorant` is the integral of the moduli of the two correlations of `W` at a position, and
  `Γ.weightedSquareProduct` is the product of their second moments, with a constant.
* `F.FloorMassLe j V 1` says that the mass of floor `j` near the next floor is at most `V`.

Contents of this file:
* `New.Floors.Gauge.IsShell`: a set of positions with a finite height at least 1. It is covered by
  few position balls (`New.Floors.Gauge.positionsOfSize`, each for its own gauge).
* `New.Floors.Gauge.IsShell.setLIntegral_le`: one shell.
* `New.Floors.Gauge.IsShell.setLIntegral_formMajorant_le`: the gain on a remote shell.
* `New.Floors.Gauge.IsShell.setLIntegral_le_inv_height`: a few factors of the gain pay for the
  growth in the height.
* `New.Floors.Gauge.lintegral_le_of_shells`: the sum over the shells. The integral over a shell is
  at most a common bound times the inverse of the height, and `∑ 2⁻¹ ^ i = 2`.
-/

noncomputable section

namespace New.Floors

open MeasureTheory ENNReal Fintype PlaceData Finset Place

variable {A : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} {𝔰 : Shape} {T : 𝔰.Form A}
  [IsHermitianUnit T.splitGram] {F : PlaceData ι T m} {I : Type} [Fintype I]

/-- The unit in which integrals over positions are measured: the product of the moduli
`F.floorModulus l` of the level `F.levelUnit` on the Heisenberg groups (at finite places the volume
of the congruence subgroup of the unipotent group), times a power of the constant `P.kernelBound` of
Plancherel's formula, times the squared `L²` norm `F.pairingNormSq W` of the correlation of `W`. -/
def PlaceData.shellNormalization (F : PlaceData ι T m) (W : T.G → EuclideanSpace ℂ I) : ℝ≥0∞ :=
  (∏ l ∈ range 𝔰.ϱ, F.floorModulus l) * P.kernelBound ^ (card F.FreeIndex * 𝔰.ϱ) * F.pairingNormSq W

/-- For a gauge `Γ`, heads `p`, `q` of length `j` and the function `W`, a set `S` is a shell of the
given finite height at least 1 if it is covered by few position balls, and if a large height forces
a deep vector at each of its points. -/
structure Gauge.IsShell (Γ : Gauge F) (j : ℕ) (p q : ℕ → Aˣ) (W : T.G → EuclideanSpace ℂ I)
    (S : Set T.G) (height : ℝ≥0∞) : Prop where
  /-- The height is at least 1. -/
  one_le_height : 1 ≤ height
  /-- The height is finite. -/
  height_ne_top : height ≠ ∞
  /-- `S` is covered by few position balls: for `x` in `S` the matrix `(x - 1) / F.levelUnit` has
  size 1 in the sense of one of at most `2 height ^ (9 n)` gauges `Γ'`, that is, `x` is in
  `Γ'.positionsOfSize`, and the scales `Γ'.loss` are at most `Γ.loss height²`. -/
  exists_cover : ∃ 𝒢 : Finset (Gauge F), (#𝒢 : ℝ≥0∞) ≤ 2 * height ^ (9 * 𝔰.n) ∧
    S ⊆ ⋃ Γ' ∈ 𝒢, Γ'.positionsOfSize ∧ ∀ Γ' ∈ 𝒢, Γ'.loss ≤ Γ.loss * height ^ 2
  /-- Far means deep: if `σ < 1` and `Γ.loss ^ (1200 n²) ≤ σ^(400 n²) height`, every active point
  has a vector of depth at least `σ⁻²` after the head. -/
  hasDeepVector : ∀ x ∈ S, ∀ σ : ℝ≥0∞, σ < 1 → Γ.loss ^ (1200 * 𝔰.n ^ 2) ≤ σ ^ (400 * 𝔰.n ^ 2) *
    height →
    F.HasDeepVector j p q W x (σ ^ 2)⁻¹

/-- A shell lies in the set `F.positions` of positions of the level. -/
lemma Gauge.IsShell.subset_positions {Γ : Gauge F} {j : ℕ} {p q : ℕ → Aˣ}
    {W : T.G → EuclideanSpace ℂ I} {S : Set T.G} {height : ℝ≥0∞}
    (hS : Γ.IsShell j p q W S height) : S ⊆ F.positions := by
  obtain ⟨𝒢, -, h_subset, -⟩ := hS.exists_cover
  intro x hx
  obtain ⟨Γ', -, h_close⟩ := Set.mem_iUnion₂.1 (h_subset hx)
  simp only [Gauge.positionsOfSize] at h_close
  exact h_close.1

/-- The height of a shell is finite and not zero, so it cancels against its inverse. -/
lemma Gauge.IsShell.inv_height_mul_height {Γ : Gauge F} {j : ℕ} {p q : ℕ → Aˣ}
    {W : T.G → EuclideanSpace ℂ I} {S : Set T.G} {height : ℝ≥0∞}
    (hS : Γ.IsShell j p q W S height) : height⁻¹ * height = 1 :=
  ENNReal.inv_mul_cancel (one_pos.trans_le hS.one_le_height).ne' hS.height_ne_top

variable [F.groupMeasure.IsHaarMeasure] {Γ : Gauge F} {j r : ℕ} {p q : ℕ → Aˣ}
  {W : T.G → EuclideanSpace ℂ I} {f : T.G → ℝ≥0∞} {e V : ℝ≥0∞}

/-- Let `S ⊆ T.G` be a shell of height `height` for the gauge `Γ` and the sequences of units `p`,
`q`. Let `j ≤ 𝔰.ϱ`, and let `W` be a cut Bessel function (`F.IsCut W`). Only `q` is assumed to be a
head of length `j` for `Γ`. Suppose `f` has the gain `e` at each `x ∈ S`, that is, `f x ^ 2 ≤ e ^
2 * Γ.weightedSquareProduct j p q W x`. Then `F.headDensity j p q` times the integral of `f` over
`S` is at most `e * Γ.loss ^ (2 * 10 ^ 6 * 𝔰.n ^ 3) * height ^ (10 ^ 5 * 𝔰.n ^ 2) *
F.shellNormalization W`. -/
theorem Gauge.IsShell.setLIntegral_le {S : Set T.G} {height : ℝ≥0∞}
    (hS : Γ.IsShell j p q W S height) (hW : F.IsCut W) (hj : j ≤ 𝔰.ϱ) (hq : Γ.IsHead j q)
    (h_gain : ∀ x ∈ S, f x ^ 2 ≤ e ^ 2 * Γ.weightedSquareProduct j p q W x) :
    F.headDensity j p q * ∫⁻ x in S, f x ∂F.groupMeasure ≤
      e * Γ.loss ^ (2 * 10 ^ 6 * 𝔰.n ^ 3) * height ^ (10 ^ 5 * 𝔰.n ^ 2) * F.shellNormalization
        W := by
  obtain ⟨𝒢, h_card, h_subset, h_lambda⟩ : ∃ 𝒢 : Finset (Gauge F),
      (#𝒢 : ℝ≥0∞) ≤ 2 * height ^ (9 * 𝔰.n) ∧ S ⊆ ⋃ Γ' ∈ 𝒢, Γ'.positionsOfSize ∧
        ∀ Γ' ∈ 𝒢, Γ'.loss ≤ Γ.loss * height ^ 2 := hS.exists_cover
  let B : ℝ≥0∞ := e * (Γ.loss ^ (1500000 * 𝔰.n ^ 3) * Γ.loss ^ (25000 * 𝔰.n ^ 2) * Γ.loss) *
    height ^ (50000 * 𝔰.n ^ 2) * F.shellNormalization W
  -- Cauchy–Schwarz and the bound for one frame cost powers of `Γ.loss` and `Γ'.loss`.
  have h_piece (Γ' : 𝒢) :
      F.headDensity j p q * ∫⁻ x in S ∩ Γ'.val.positionsOfSize, f x ∂F.groupMeasure ≤ B := by
    have h_gain_piece : ∀ x ∈ S ∩ Γ'.val.positionsOfSize,
        f x ^ 2 ≤ e ^ 2 * Γ.weightedSquareProduct j p q W x := fun x hx ↦ h_gain x hx.1
    grw [Γ.headDensity_mul_lintegral_le_mul_pairingNormSq Γ' hW hj hq Set.inter_subset_right
      h_gain_piece,
      h_lambda Γ' Γ'.prop]
    simp only [B, shellNormalization]
    exact le_of_eq (by ring)
  have h_cover : S ⊆ ⋃ Γ' : 𝒢, S ∩ Γ'.val.positionsOfSize := fun x hx ↦ by
    obtain ⟨Γ', hΓ', h_close⟩ := Set.mem_iUnion₂.1 (h_subset hx)
    exact Set.mem_iUnion.2 ⟨⟨Γ', hΓ'⟩, hx, h_close⟩
  have h_scale : Γ.loss ^ (1500000 * 𝔰.n ^ 3) * Γ.loss ^ (25000 * 𝔰.n ^ 2) * Γ.loss * Γ.loss ≤
      Γ.loss ^ (2 * 10 ^ 6 * 𝔰.n ^ 3) := by
    rw [← pow_add, ← pow_succ, ← pow_succ]
    exact pow_le_pow_right₀ Γ.one_le_loss (by lia)
  have h_height : height ^ (50000 * 𝔰.n ^ 2) * height ^ (9 * 𝔰.n) ≤
      height ^ (10 ^ 5 * 𝔰.n ^ 2) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hS.one_le_height (by lia)
  calc F.headDensity j p q * ∫⁻ x in S, f x ∂F.groupMeasure
      ≤ ∑' Γ' : 𝒢, F.headDensity j p q *
          ∫⁻ x in S ∩ Γ'.val.positionsOfSize, f x ∂F.groupMeasure := by
        grw [lintegral_mono_set h_cover, lintegral_iUnion_le, ENNReal.tsum_mul_left]
    _ ≤ #𝒢 * B := by
        grw [ENNReal.tsum_le_tsum h_piece]
        simp
    _ ≤ e * Γ.loss ^ (2 * 10 ^ 6 * 𝔰.n ^ 3) * height ^ (10 ^ 5 * 𝔰.n ^ 2) * F.shellNormalization
      W := by
        grw [h_card, Γ.two_le_loss, ← h_scale, ← h_height]
        simp only [B]
        exact le_of_eq (by ring)

/-- Let `S` be a shell of height `height` for the gauge `Γ` and `p`, `q`. Let `j ≤ 𝔰.ϱ`, and let
`p`, `q` be heads of length `j` (`Γ.IsHead`). Let `W` be a cut Bessel function (`F.IsCut W`), and
let `V ≥ 1` with `F.FloorMassLe j V 1`. Let `height > Γ.loss ^ (2400 * 𝔰.n ^ 2)`, and let
`τ ^ (800 * 𝔰.n ^ 2) = height⁻¹`. Then `F.headDensity j p q` times the integral of
`F.formMajorant j p q W` over `S` is at most `V * τ ^ F.volumeExponent * Γ.loss ^ (2 * 10 ^ 6 * 𝔰.n
^ 3) * height ^ (10 ^ 5 * 𝔰.n ^ 2) * F.shellNormalization W`. -/
theorem Gauge.IsShell.setLIntegral_formMajorant_le {S : Set T.G} {height τ : ℝ≥0∞}
    (hS : Γ.IsShell j p q W S height) (hW : F.IsCut W) (hj : j ≤ 𝔰.ϱ) (hp : Γ.IsHead j p)
    (hq : Γ.IsHead j q) (h_mass : F.FloorMassLe j V 1) (hV : 1 ≤ V)
    (h_remote : Γ.loss ^ (2400 * 𝔰.n ^ 2) < height) (hτ : τ ^ (800 * 𝔰.n ^ 2) = height⁻¹) :
    F.headDensity j p q * ∫⁻ x in S, F.formMajorant j p q W x ∂F.groupMeasure ≤
      V * τ ^ F.volumeExponent * Γ.loss ^ (2 * 10 ^ 6 * 𝔰.n ^ 3) * height ^ (10 ^ 5 * 𝔰.n ^ 2) *
        F.shellNormalization W := by
  have τ_lt : τ < 1 := lt_of_pow_lt_pow_left' (800 * 𝔰.n ^ 2) <| by
    rw [hτ, one_pow, ENNReal.inv_lt_one]
    exact (one_le_pow₀ Γ.one_le_loss).trans_lt h_remote
  -- This inequality gives every active point a vector of depth at least `τ⁻²` after the head.
  have h_root : Γ.loss ^ (1200 * 𝔰.n ^ 2) ≤ τ ^ (400 * 𝔰.n ^ 2) * height := by
    rw [← ENNReal.pow_le_pow_left_iff two_ne_zero]
    calc (Γ.loss ^ (1200 * 𝔰.n ^ 2)) ^ 2
        = Γ.loss ^ (2400 * 𝔰.n ^ 2) := by ring
      _ ≤ τ ^ (800 * 𝔰.n ^ 2) * height * height := by
          rw [hτ, hS.inv_height_mul_height, one_mul]
          exact h_remote.le
      _ = (τ ^ (400 * 𝔰.n ^ 2) * height) ^ 2 := by ring
  refine hS.setLIntegral_le hW hj hq fun x hx ↦ ?_
  have h_deep : F.HasDeepVector j p q W x (τ ^ 2)⁻¹ := hS.hasDeepVector x hx τ τ_lt h_root
  grw [Γ.formMajorant_sq_le_of_hasDeepVector hW hj hp (hS.subset_positions hx) h_mass hV h_deep]
  exact le_of_eq (by ring)

/-- Let `S` be a shell of height `height` for `Γ` and `p`, `q`. Let `j ≤ 𝔰.ϱ`, and let `p`, `q` be
heads of length `j` (`Γ.IsHead`). Let `W` be a cut Bessel function (`F.IsCut W`), and let `V ≥ 1`
with `F.FloorMassLe j V 1`. Suppose `f x ≤ F.formMajorant j p q W x` for all `x`, and `f x ^
2 ≤ (V * e ^ F.volumeExponent) ^ 2 * Γ.weightedSquareProduct j p q W x` on `S`. Suppose also `e ≤ 1`
and `9 * 10 ^ 7 * 𝔰.n ^ 4 + r ≤ F.volumeExponent`. Then `F.headDensity j p q` times the integral of
`f` over `S` is at most `height⁻¹ * (V * e ^ r * Γ.loss ^ (3 * 10 ^ 8 * 𝔰.n ^ 4) *
F.shellNormalization W)`. -/
theorem Gauge.IsShell.setLIntegral_le_inv_height {S : Set T.G} {height : ℝ≥0∞}
    (hS : Γ.IsShell j p q W S height) (hW : F.IsCut W) (hj : j ≤ 𝔰.ϱ) (hp : Γ.IsHead j p)
    (hq : Γ.IsHead j q) (h_mass : F.FloorMassLe j V 1) (hV : 1 ≤ V) (he : e ≤ 1)
    (hf : ∀ x : T.G, f x ≤ F.formMajorant j p q W x)
    (h_gain : ∀ x ∈ S,
      f x ^ 2 ≤ (V * e ^ F.volumeExponent) ^ 2 * Γ.weightedSquareProduct j p q W x)
    (hr : 9 * 10 ^ 7 * 𝔰.n ^ 4 + r ≤ F.volumeExponent) :
    F.headDensity j p q * ∫⁻ x in S, f x ∂F.groupMeasure ≤
      height⁻¹ * (V * e ^ r * Γ.loss ^ (3 * 10 ^ 8 * 𝔰.n ^ 4) * F.shellNormalization W) := by
  have h_cancel : height⁻¹ * height = 1 := hS.inv_height_mul_height
  -- It suffices to find `g ≤ e` such that the integral has the bound with the gain
  -- `V * g ^ F.volumeExponent` and `g ^ (9 · 10⁷ n⁴) height ^ (1 + 10⁵ n²) ≤ Γ.loss ^ (29 · 10⁷
  -- n⁴)`.
  suffices h_split : ∃ g : ℝ≥0∞, g ≤ e ∧
      g ^ (9 * 10 ^ 7 * 𝔰.n ^ 4) * height ^ (1 + 10 ^ 5 * 𝔰.n ^ 2) ≤
        Γ.loss ^ (29 * 10 ^ 7 * 𝔰.n ^ 4) ∧
      F.headDensity j p q * ∫⁻ x in S, f x ∂F.groupMeasure ≤
        V * g ^ F.volumeExponent * Γ.loss ^ (2 * 10 ^ 6 * 𝔰.n ^ 3) * height ^ (10 ^ 5 * 𝔰.n ^ 2) *
          F.shellNormalization W by
    obtain ⟨g, hg, h_pay, h_bound⟩ := h_split
    have h_exp : g ^ F.volumeExponent ≤ g ^ (9 * 10 ^ 7 * 𝔰.n ^ 4) * e ^ r := by
      grw [pow_le_pow_right_of_le_one' (hg.trans he) hr, pow_add, ← hg]
    have h_scale : Γ.loss ^ (29 * 10 ^ 7 * 𝔰.n ^ 4) * Γ.loss ^ (2 * 10 ^ 6 * 𝔰.n ^ 3) ≤
        Γ.loss ^ (3 * 10 ^ 8 * 𝔰.n ^ 4) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ Γ.one_le_loss (by lia)
    calc F.headDensity j p q * ∫⁻ x in S, f x ∂F.groupMeasure
        = height⁻¹ * height * (F.headDensity j p q * ∫⁻ x in S, f x ∂F.groupMeasure) := by
          rw [h_cancel, one_mul]
      _ ≤ height⁻¹ * (V * e ^ r *
            (g ^ (9 * 10 ^ 7 * 𝔰.n ^ 4) * height ^ (1 + 10 ^ 5 * 𝔰.n ^ 2) *
              Γ.loss ^ (2 * 10 ^ 6 * 𝔰.n ^ 3)) * F.shellNormalization W) := by
          grw [h_bound, h_exp]
          exact le_of_eq (by ring)
      _ ≤ height⁻¹ * (V * e ^ r * Γ.loss ^ (3 * 10 ^ 8 * 𝔰.n ^ 4) * F.shellNormalization W) := by
          grw [h_pay, h_scale]
  obtain h_close | h_remote := le_or_gt height (Γ.loss ^ (2400 * 𝔰.n ^ 2))
  · -- Up to the height `Γ.loss ^ (2400 n²)` take `g = e`.
    refine ⟨e, le_rfl, ?_, hS.setLIntegral_le hW hj hq h_gain⟩
    grw [he, one_pow, one_mul, h_close, ← pow_mul]
    exact pow_le_pow_right₀ Γ.one_le_loss (by lia)
  -- Beyond it take the smaller of `e` and `τ = height ^ (-1 / (800 n²))`.
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ≥0∞, τ ^ (800 * 𝔰.n ^ 2) = height⁻¹ :=
    ⟨height⁻¹ ^ ((800 * 𝔰.n ^ 2 : ℕ) : ℝ)⁻¹, rpow_inv_natCast_pow (by positivity) _⟩
  refine ⟨min e τ, min_le_left e τ, ?_, ?_⟩
  · have h_exp : 800 * 𝔰.n ^ 2 * (112500 * 𝔰.n ^ 2) = 9 * 10 ^ 7 * 𝔰.n ^ 4 := by ring
    calc min e τ ^ (9 * 10 ^ 7 * 𝔰.n ^ 4) * height ^ (1 + 10 ^ 5 * 𝔰.n ^ 2)
        ≤ (τ ^ (800 * 𝔰.n ^ 2)) ^ (112500 * 𝔰.n ^ 2) * height ^ (112500 * 𝔰.n ^ 2) := by
          rw [← pow_mul, h_exp]
          gcongr
          · exact min_le_right e τ
          · exact hS.one_le_height
          · lia
      _ = 1 := by rw [hτ, ← mul_pow, h_cancel, one_pow]
      _ ≤ Γ.loss ^ (29 * 10 ^ 7 * 𝔰.n ^ 4) := one_le_pow₀ Γ.one_le_loss
  · obtain h_le | h_le := le_total e τ
    · rw [min_eq_left h_le]
      exact hS.setLIntegral_le hW hj hq h_gain
    · grw [min_eq_right h_le, lintegral_mono hf]
      exact hS.setLIntegral_formMajorant_le hW hj hp hq h_mass hV h_remote hτ

/-- **The sum over the shells.** Let each `S i` be a shell of height `2 ^ i` for the gauge `Γ` and
`p`, `q`. Let the `S i` cover the support of `f`. Let `j ≤ 𝔰.ϱ`, and let `p`, `q` be heads of length
`j` (`Γ.IsHead`). Let `W` be a cut Bessel function (`F.IsCut W`), and let `V ≥ 1` with
`F.FloorMassLe j V 1`. Suppose `f x ≤ F.formMajorant j p q W x` for all `x`. Suppose also that if
`e < 1`, then `f x ^ 2 ≤ (V * e ^ F.volumeExponent) ^ 2 * Γ.weightedSquareProduct j p q W x` for
`x ∈ F.positions`. Let `9 * 10 ^ 7 * 𝔰.n ^ 4 + r ≤ F.volumeExponent`. Then `F.headDensity j p q`
times the integral of `f` over `T.G` is at most `V * min 1 e ^ r * Γ.loss ^ (4 * 10 ^ 8 * 𝔰.n ^ 4) *
F.shellNormalization W`. -/
theorem Gauge.lintegral_le_of_shells {S : ℕ → Set T.G}
    (hS : ∀ i : ℕ, Γ.IsShell j p q W (S i) (2 ^ i)) (h_cover : f.support ⊆ ⋃ i : ℕ, S i)
    (hW : F.IsCut W) (hj : j ≤ 𝔰.ϱ) (hp : Γ.IsHead j p)
    (hq : Γ.IsHead j q) (h_mass : F.FloorMassLe j V 1) (hV : 1 ≤ V)
    (hf : ∀ x : T.G, f x ≤ F.formMajorant j p q W x)
    (h_gain : e < 1 → ∀ x ∈ F.positions,
      f x ^ 2 ≤ (V * e ^ F.volumeExponent) ^ 2 * Γ.weightedSquareProduct j p q W x)
    (hr : 9 * 10 ^ 7 * 𝔰.n ^ 4 + r ≤ F.volumeExponent) :
    F.headDensity j p q * ∫⁻ x : T.G, f x ∂F.groupMeasure ≤
      V * min 1 e ^ r * Γ.loss ^ (4 * 10 ^ 8 * 𝔰.n ^ 4) * F.shellNormalization W := by
  have h_sum : ∑' i : ℕ, ((2 : ℝ≥0∞) ^ i)⁻¹ ≤ 2 := by
    simp [ENNReal.inv_pow, ENNReal.tsum_geometric]
  set B : ℝ≥0∞ := V * min 1 e ^ r * Γ.loss ^ (3 * 10 ^ 8 * 𝔰.n ^ 4) * F.shellNormalization W with hB
  have h_shell (i : ℕ) :
      F.headDensity j p q * ∫⁻ x in S i, f x ∂F.groupMeasure ≤ (2 ^ i)⁻¹ * B := by
    have h_gain_min : ∀ x ∈ S i,
        f x ^ 2 ≤ (V * min 1 e ^ F.volumeExponent) ^ 2 * Γ.weightedSquareProduct j p q W x := by
      intro x hx
      obtain he_lt | he_ge := lt_or_ge e 1
      · rw [min_eq_right he_lt.le]
        exact h_gain he_lt x ((hS i).subset_positions hx)
      · grw [min_eq_left he_ge, one_pow, mul_one, hf]
        exact Γ.formMajorant_sq_le_of_floorMassLe hW hj hp ((hS i).subset_positions hx) h_mass
    exact (hS i).setLIntegral_le_inv_height hW hj hp hq h_mass hV (min_le_left 1 e) hf h_gain_min hr
  calc F.headDensity j p q * ∫⁻ x : T.G, f x ∂F.groupMeasure
      = F.headDensity j p q * ∫⁻ x in ⋃ i, S i, f x ∂F.groupMeasure := by
        rw [setLIntegral_eq_of_support_subset h_cover]
    _ ≤ ∑' i : ℕ, F.headDensity j p q * ∫⁻ x in S i, f x ∂F.groupMeasure := by
        grw [lintegral_iUnion_le, ENNReal.tsum_mul_left]
    _ ≤ ∑' i : ℕ, (2 ^ i)⁻¹ * B := ENNReal.tsum_le_tsum h_shell
    _ ≤ Γ.loss ^ (10 ^ 8 * 𝔰.n ^ 4) * B := by
        have h_two : (2 : ℝ≥0∞) ≤ Γ.loss ^ (10 ^ 8 * 𝔰.n ^ 4) :=
          Γ.two_le_loss.trans (le_self_pow₀ Γ.one_le_loss (by positivity))
        grw [ENNReal.tsum_mul_right, h_sum, h_two]
    _ = V * min 1 e ^ r * Γ.loss ^ (4 * 10 ^ 8 * 𝔰.n ^ 4) * F.shellNormalization W := by
        rw [hB]
        ring

end New.Floors

end
