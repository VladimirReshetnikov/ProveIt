import Lib.Adelic.AutomorphicForms.Cuspidality
import Lib.Adelic.TraceFormula.IsotropicStabiliser
import Lib.Adelic.TraceFormula.KernelBound

/-!
# Convergence of the geometric side

Let `k` be a function on the real points that decays against a high power of the norm, and let `φ`
be a test function on the finite points. The sums of `(k ⊗ φ)(x⁻¹ γ x)` over rational points `γ`
converge absolutely, with a bound by a power of the height of `x`. High in a cusp, short lattice
vectors span an isotropic subspace `A`, and the bound improves: for the `γ` that move `A`, the
points `x⁻¹ γ x` are large at infinity, and, if `k` is a cusp kernel, the terms of the `γ` that keep
`A` cancel along the unipotent radical. So the sum over the `γ` whose characteristic polynomial lies
in a given set is bounded uniformly in `x` and in the set, and the sum over the `γ` with irreducible
polynomial is bounded absolutely. These are known arguments for convergence in a simple trace
formula (cf. Flicker and Kazhdan).

Notions from other files:
* `New.Space E n s`: a hermitian form `J` over `E` with an adelic point. `G E s` is the unitary
  group `GInf E s × Gf E n`, and `V.ratEmbed` embeds the rational unitary group `U V.J` in it.
* `New.Space.height`: `V.height x` is the inverse of the first minimum, cut off at `1`, of the space
  `V.move x` whose point is moved by `x`.
* `New.IsCuspKernel B k`: `k` is a minimal idempotent kernel on the real points with decay of order
  `B`, an integrable moment and a compactly supported function that reproduces it.

## Main definitions and results

* `New.Space.exists_tsum_enorm_kernelTerm_le_height`: the bound by a power of the height.
* `New.Space.exists_norm_tsum_polyTerm_le`: the uniform bound for a set of polynomials.
* `New.Space.exists_tsum_enorm_irreducibleTerm_le`: the absolute bound for irreducible polynomials.
-/

open NumberField MeasureTheory Matrix Polynomial Fintype Norms.L2Operator

noncomputable section

namespace New

/-- If the sum of the moduli of the terms of a complex family is at most `T ≥ 0`, then so is the
modulus of the sum. -/
lemma norm_tsum_le_of_tsum_enorm_le {I : Type*} {f : I → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (h : ∑' i : I, ‖f i‖ₑ ≤ ENNReal.ofReal T) : ‖∑' i : I, f i‖ ≤ T :=
  ENNReal.toReal_le_of_le_ofReal hT (enorm_tsum_le_tsum_enorm.trans h)

/-- An order of decay of `13 n³` leaves `4 n³` to spare over the order `8 n² + 1` that the bound for
the kernel needs. -/
lemma add_le_of_thirteen_mul_cube_le {n B : ℕ} (hn : 0 < n) (hB : 13 * n ^ 3 ≤ B) :
    8 * n ^ 2 + 1 + 4 * n ^ 3 ≤ B := by
  nlinarith

lemma eight_mul_sq_lt_of_thirteen_mul_cube_le {n B : ℕ} (hn : 0 < n) (hB : 13 * n ^ 3 ≤ B) :
    8 * n ^ 2 < B :=
  Nat.le_of_add_right_le (add_le_of_thirteen_mul_cube_le hn hB)

namespace Space

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] [Nonempty n]
  {s : n → ℤˣ} (V : Space E n s)

/-- The term of the rational point `γ`, with the weight `a γ`, in the kernel of `k ⊗ φ` at the
pair of points `g, x`: the weight times the value of `k ⊗ φ` at `g⁻¹ γ x`. -/
def kernelTerm (k : GInf E s → ℂ) (φ : Gf E n → ℂ) (a : U V.J → ℂ) (g : G E s) (γ : U V.J)
    (x : G E s) : ℂ :=
  a γ * (k (g⁻¹ * V.ratEmbed γ * x).1 * φ (g⁻¹ * V.ratEmbed γ * x).2)

/-- The value of `k ⊗ φ` at `x⁻¹ γ x` if the characteristic polynomial of `γ` lies in `S`, and
`0` otherwise. -/
abbrev polyTerm (k : GInf E s → ℂ) (φ : Gf E n → ℂ) (S : Set E[X]) (γ : U V.J) (x : G E s) : ℂ :=
  V.kernelTerm k φ (fun γ : U V.J ↦ S.indicator 1 ((γ : GL n E) : Matrix n n E).charpoly) x γ x

/-- The value of `k ⊗ φ` at `x⁻¹ γ x` if the characteristic polynomial of `γ` is irreducible, and
`0` otherwise. -/
abbrev irreducibleTerm (k : GInf E s → ℂ) (φ : Gf E n → ℂ) (γ : U V.J) (x : G E s) : ℂ :=
  V.polyTerm k φ {P : E[X] | Irreducible P} γ x

section

omit [Nonempty n]
/-- The term of a set `S` of polynomials is the term of the kernel whose weight is the indicator
of the rational points with characteristic polynomial in `S`. -/
lemma polyTerm_eq_kernelTerm_indicator (k : GInf E s → ℂ) (φ : Gf E n → ℂ) (S : Set E[X])
    (γ : U V.J) (x : G E s) :
    V.polyTerm k φ S γ x = V.kernelTerm k φ
      ({γ : U V.J | ((γ : GL n E) : Matrix n n E).charpoly ∈ S}.indicator 1) x γ x :=
  rfl

/-- The part of the kernel of `k ⊗ φ` at `g, x` that comes from the rational points in `Z`. -/
def partialKernel (k : GInf E s → ℂ) (φ : Gf E n → ℂ) (Z : Set (U V.J)) (g x : G E s) : ℂ :=
  ∑' γ : U V.J, V.kernelTerm k φ (Z.indicator 1) g γ x

/-- For measurable `k` and a test function `φ`, each term of the kernel is measurable in the pair
of points. -/
@[fun_prop] lemma measurable_kernelTerm {k : GInf E s → ℂ} (φ : TestFunction (Gf E n))
    (a : U V.J → ℂ) (γ : U V.J) (hk : Measurable k) :
    Measurable fun ((g, x) : G E s × G E s) ↦ V.kernelTerm k φ a g γ x := by
  have h_cont : Continuous (φ : Gf E n → ℂ) := φ.property.1.continuous
  fun_prop [kernelTerm]

/-- The partial kernel of the rational points in `Z` is left invariant in `g` under every rational
point `ν` with `ν Z = Z`. -/
lemma partialKernel_ratEmbed_mul {k : GInf E s → ℂ} (φ : Gf E n → ℂ) {Z : Set (U V.J)} {ν : U V.J}
    (hν : ∀ γ : U V.J, ν * γ ∈ Z ↔ γ ∈ Z) (g x : G E s) :
    V.partialKernel k φ Z (V.ratEmbed ν * g) x = V.partialKernel k φ Z g x := by
  classical
  have h_point (γ : U V.J) :
      (V.ratEmbed ν * g)⁻¹ * V.ratEmbed (ν * γ) * x = g⁻¹ * V.ratEmbed γ * x := by simp [mul_assoc]
  calc V.partialKernel k φ Z (V.ratEmbed ν * g) x
      = ∑' γ : U V.J, V.kernelTerm k φ (Z.indicator 1) (V.ratEmbed ν * g) (ν * γ) x :=
        ((Equiv.mulLeft ν).tsum_eq _).symm
    _ = V.partialKernel k φ Z g x :=
        tsum_congr fun γ ↦ by simp [kernelTerm, Set.indicator, hν]

/-- For a hermitian space `V` with a point, the partial kernel `V.partialKernel k φ Z g x` is the
part of the kernel of `k ⊗ φ` at `g, x` coming from the rational points in `Z ⊆ U V.J`; in each of
its terms, `g` enters only through left multiplication by `g⁻¹`. If `φ` on `Gf E n` satisfies
`φ (u⁻¹ * y) = φ y` for all `u ∈ J`, then as a function of `g` the partial kernel has level `J`,
i.e. it is right invariant under `J ⊆ G_f`. -/
lemma hasLevel_partialKernel {k : GInf E s → ℂ} {φ : Gf E n → ℂ} {J : Subgroup (Gf E n)}
    (h_level : ∀ u ∈ J, ∀ y : Gf E n, φ (u⁻¹ * y) = φ y) (Z : Set (U V.J)) (x : G E s) :
    HasLevel (fun g : G E s ↦ V.partialKernel k φ Z g x) J := by
  intro u hu g
  refine tsum_congr fun γ ↦ ?_
  have h_point : (g * (1, u))⁻¹ * V.ratEmbed γ * x = (1, u⁻¹) * (g⁻¹ * V.ratEmbed γ * x) := by
    simp [mul_assoc]
  rw [kernelTerm, h_point, Prod.fst_mul, Prod.snd_mul, one_mul, h_level u hu, kernelTerm]

/-- A minimal idempotent kernel `k` on the real points satisfies `k * k = k`, so each term of the
kernel of `k ⊗ φ`, as a function of `g`, is fixed by right convolution with `k`. -/
lemma integral_mul_kernelTerm {k : GInf E s → ℂ} (φ : Gf E n → ℂ) (he : IsIdempotentKernel k)
    (a : U V.J → ℂ) (g : G E s) (γ : U V.J) (x : G E s) :
    ∫ h : GInf E s, k h * V.kernelTerm k φ a (g * (h, 1)) γ x = V.kernelTerm k φ a g γ x := by
  set y : G E s := g⁻¹ * V.ratEmbed γ * x with hy
  have h_point (h : GInf E s) : (g * (h, 1))⁻¹ * V.ratEmbed γ * x = (h⁻¹, 1) * y := by
    simp [hy, mul_assoc]
  calc ∫ h : GInf E s, k h * V.kernelTerm k φ a (g * (h, 1)) γ x
      = ∫ h : GInf E s, a γ * φ y.2 * (k h * k (h⁻¹ * y.1)) := by
        congr 1 with h
        rw [kernelTerm, h_point, Prod.fst_mul, Prod.snd_mul, one_mul]
        ring
    _ = a γ * φ y.2 * k y.1 := by rw [integral_const_mul, he.convolution_self]
    _ = V.kernelTerm k φ a g γ x := by rw [kernelTerm]; ring

/-- Let `k` be a minimal idempotent kernel on the real points (in particular continuous and
integrable, with `k * k = k`). If the sums of the moduli of the terms in a partial kernel (the sum
of the terms of the rational points in `Z`) are bounded in `g`, then the partial kernel, as a
function of `g`, is fixed by right convolution with `k`. -/
lemma realConv_partialKernel {k : GInf E s → ℂ} (φ : TestFunction (Gf E n))
    (he : IsIdempotentKernel k) {Z : Set (U V.J)} {x : G E s} {T : ℝ}
    (hT : ∀ g : G E s,
      ∑' γ : U V.J, ‖V.kernelTerm k φ (Z.indicator 1) g γ x‖ₑ ≤ ENNReal.ofReal T) :
    realConv k (fun g : G E s ↦ V.partialKernel k φ Z g x) =
      fun g : G E s ↦ V.partialKernel k φ Z g x := by
  ext g
  have hk : Measurable k := he.continuous.measurable
  let term (γ : U V.J) (h : GInf E s) : ℂ :=
    k h * V.kernelTerm k φ (Z.indicator 1) (g * (h, 1)) γ x
  have h_finite : ∫⁻ h : GInf E s, ∑' γ : U V.J, ‖term γ h‖ₑ < ⊤ :=
    calc _ ≤ ∫⁻ h : GInf E s, ‖k h‖ₑ * ENNReal.ofReal T := by
          simp only [term, enorm_mul, ENNReal.tsum_mul_left]
          exact lintegral_mono fun h ↦ mul_le_mul_right (hT _) _
      _ < ⊤ := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top he.integrable.hasFiniteIntegral ENNReal.ofReal_lt_top
  simp only [realConv, partialKernel, ← tsum_mul_left]
  -- Exchange sum and integral, which `h_finite` allows.
  rw [← (hasSum_integral_of_lintegral_tsum_lt_top h_finite (by fun_prop)).tsum_eq]
  exact tsum_congr fun γ ↦ V.integral_mul_kernelTerm φ he (Z.indicator 1) g γ x

/-- The matrices `A.isotropicCols` and `A.perpCols` of a cusp frame `A` of size `δ` for `V.move x`
(their columns are lattice vectors whose length bounds have product at most `δ`) span an isotropic
subspace and its orthogonal for the hermitian form `V.J`, which is the condition
`New.IsIsotropicFrame`. -/
lemma CuspFrame.isIsotropicFrame {V : Space E n s} {x : G E s} {δ : ℝ}
    (A : (V.move x).CuspFrame δ) : IsIsotropicFrame V.J A.isotropicCols A.perpCols :=
  ⟨V.isHermitian_J, V.isUnit_J, A.isotropic, A.orthogonal, A.spans⟩

/-- The height is positive, so multiplying it by `δ ^ card n` with `1 ≤ δ` does not decrease it. -/
lemma height_le_pow_mul_height {δ : ℝ} (hδ : 1 ≤ δ) (x : G E s) :
    V.height x ≤ δ ^ card n * V.height x :=
  le_mul_of_one_le_left (V.height_pos x).le (one_le_pow₀ hδ)
end

/-- If `k` has decay of order `B`, that is, `‖k g‖ ‖g‖ ^ B ≤ C` for the product `‖g‖` of the
operator norms at the infinite places, then `|k ⊗ φ|` is at most `C` times the majorant
`|φ(y_f)| / ‖y_∞‖ ^ B` of exponent `B`. -/
lemma norm_mul_le_majorant {B : ℕ} {k : GInf E s → ℂ} {C : ℝ}
    (hC : ∀ g : GInf E s,
      ‖k g‖ * (∏ w : InfinitePlace E, ‖((g w : GL n ℂ) : Matrix n n ℂ)‖) ^ B ≤ C)
    (φ : Gf E n → ℂ) (y : G E s) : ‖k y.1 * φ y.2‖ ≤ C * majorant φ B y := by
  set N : ℝ := ∏ w : InfinitePlace E, ‖((y.1 w : GL n ℂ) : Matrix n n ℂ)‖
  have hN : 1 ≤ N := (le_prod_opNorm y.1).1
  have h_decay : ‖k y.1‖ ≤ C * (N ^ B)⁻¹ := (le_mul_inv_iff₀ (by positivity)).2 (hC y.1)
  calc ‖k y.1 * φ y.2‖ ≤ C * (N ^ B)⁻¹ * ‖φ y.2‖ := by rw [norm_mul]; gcongr
    _ = C * majorant φ B y := by rw [majorant]; ring

/-- Let `‖y_∞‖` be the product of the operator norms of `y` at the infinite places. If
`A + j ≤ B` and `1 ≤ r ‖y_∞‖` unless `φ(y_f) = 0`, then the majorant
`|φ(y_f)| / ‖y_∞‖ ^ B` of exponent `B` is at most `r ^ j` times that of exponent `A`. -/
lemma majorant_le_pow_mul {B : ℕ} {φ : Gf E n → ℂ} {A j : ℕ} (hB : A + j ≤ B) {r : ℝ} {y : G E s}
    (hr : φ y.2 ≠ 0 → 1 ≤ r * ∏ w : InfinitePlace E, ‖((y.1 w : GL n ℂ) : Matrix n n ℂ)‖) :
    majorant φ B y ≤ r ^ j * majorant φ A y := by
  by_cases hφ : φ y.2 = 0
  · simp [majorant, hφ]
  set N : ℝ := ∏ w : InfinitePlace E, ‖((y.1 w : GL n ℂ) : Matrix n n ℂ)‖
  have hN : 1 ≤ N := (le_prod_opNorm y.1).1
  have h_gain : (N ^ B)⁻¹ ≤ r ^ j * (N ^ A)⁻¹ :=
    calc (N ^ B)⁻¹ ≤ (r * N) ^ j * (N ^ (A + j))⁻¹ :=
          (inv_anti₀ (by positivity) (pow_le_pow_right₀ hN hB)).trans
            (le_mul_of_one_le_left (by positivity) (one_le_pow₀ (hr hφ)))
      _ = r ^ j * (N ^ A)⁻¹ := by field_simp; ring
  simpa [majorant, mul_left_comm] using mul_le_mul_of_nonneg_left h_gain (norm_nonneg (φ y.2))


/-- The bound for the kernel, with the gain from rational points that are large at infinity. Let
`k` have decay of order `B ≥ 8 n² + 1 + j` against the product of the operator norms at the
infinite places (here `n` is short for `card n`), and let `r` times this product be at least `1`
at the points `g⁻¹ γ x` with `γ ∈ Z` at whose finite component `φ` does not vanish. Then the sum of
the moduli of the terms of `Z` in the kernel is at most a constant times `r ^ j` times a power of
the height of `x` (the inverse of the first minimum of the moved space, cut off at `1`). -/
theorem exists_tsum_enorm_kernelTerm_le {B : ℕ} {k : GInf E s → ℂ} {j : ℕ}
    (hB : 8 * card n ^ 2 + 1 + j ≤ B) (φ : TestFunction (Gf E n))
    (hk : ∃ C : ℝ, ∀ g : GInf E s,
      ‖k g‖ * (∏ w : InfinitePlace E, ‖((g w : GL n ℂ) : Matrix n n ℂ)‖) ^ B ≤ C) :
    ∃ C ≥ (0 : ℝ), ∀ (Z : Set (U V.J)) (g x : G E s), ∀ r ≥ (0 : ℝ),
      (∀ γ ∈ Z, (φ : Gf E n → ℂ) (g⁻¹ * V.ratEmbed γ * x).2 ≠ 0 →
        1 ≤ r * ∏ w : InfinitePlace E,
          ‖(((g⁻¹ * V.ratEmbed γ * x).1 w : GL n ℂ) : Matrix n n ℂ)‖) →
      ∑' γ : U V.J, ‖V.kernelTerm k φ (Z.indicator 1) g γ x‖ₑ ≤
        ENNReal.ofReal (C * r ^ j * V.height x ^ (4 * Core.numInfPlaces E * card n ^ 2)) := by
  obtain ⟨C, hC⟩ := hk
  obtain ⟨D, hD, h_crude⟩ := V.exists_tsum_majorant_le φ
  have hC_nonneg : 0 ≤ C := le_trans (by positivity) (hC 1)
  set d : ℕ := 4 * Core.numInfPlaces E * card n ^ 2
  refine ⟨C * D, mul_nonneg hC_nonneg hD, fun Z g x r hr h_large ↦ ?_⟩
  have h_term (γ : U V.J) : ‖V.kernelTerm k φ (Z.indicator 1) g γ x‖ ≤
      C * r ^ j * majorant φ (8 * card n ^ 2 + 1) (g⁻¹ * V.ratEmbed γ * x) := by
    by_cases hγ : γ ∈ Z
    · have h_gain : majorant φ B (g⁻¹ * V.ratEmbed γ * x) ≤
          r ^ j * majorant φ (8 * card n ^ 2 + 1) (g⁻¹ * V.ratEmbed γ * x) :=
        majorant_le_pow_mul hB (h_large γ hγ)
      rw [kernelTerm, Set.indicator_of_mem hγ, Pi.one_apply, one_mul, mul_assoc C]
      exact (norm_mul_le_majorant hC φ _).trans (mul_le_mul_of_nonneg_left h_gain hC_nonneg)
    · simp only [kernelTerm, Set.indicator_of_notMem hγ, zero_mul, norm_zero, majorant]
      positivity
  calc ∑' γ : U V.J, ‖V.kernelTerm k φ (Z.indicator 1) g γ x‖ₑ
      ≤ ∑' γ : U V.J, .ofReal (C * r ^ j) *
          ENNReal.ofReal (majorant φ (8 * card n ^ 2 + 1) (g⁻¹ * V.ratEmbed γ * x)) := by
        simp only [← ofReal_norm, ← ENNReal.ofReal_mul (show 0 ≤ C * r ^ j by positivity)]
        exact ENNReal.tsum_le_tsum fun γ ↦ ENNReal.ofReal_le_ofReal (h_term γ)
    _ ≤ .ofReal (C * r ^ j) * .ofReal (D * V.height x ^ d) :=
        ENNReal.tsum_mul_left.trans_le (mul_le_mul_right (h_crude g x) _)
    _ = .ofReal (C * D * r ^ j * V.height x ^ d) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        ring_nf

/-- If `k` has decay of order `B > 8 (card n)²`, then the sum of the moduli of the terms of any
set `Z` of rational points in the kernel of `k ⊗ φ` at `g, x` is bounded by a power of the height of
`x`, uniformly in `Z` and `g`. In particular the kernel converges absolutely. -/
theorem exists_tsum_enorm_kernelTerm_le_height {B : ℕ} {k : GInf E s → ℂ}
    (hB : 8 * card n ^ 2 < B) (φ : TestFunction (Gf E n))
    (hk : ∃ C : ℝ, ∀ g : GInf E s,
      ‖k g‖ * (∏ w : InfinitePlace E, ‖((g w : GL n ℂ) : Matrix n n ℂ)‖) ^ B ≤ C) :
    ∃ C ≥ (0 : ℝ), ∀ (Z : Set (U V.J)) (g x : G E s),
      ∑' γ : U V.J, ‖V.kernelTerm k φ (Z.indicator 1) g γ x‖ₑ ≤
        ENNReal.ofReal (C * V.height x ^ (4 * Core.numInfPlaces E * card n ^ 2)) := by
  obtain ⟨C, hC, h_bound⟩ := V.exists_tsum_enorm_kernelTerm_le (j := 0) hB φ hk
  refine ⟨C, hC, fun Z g x ↦ ?_⟩
  -- Apply the bound with `r = 1`, since the product of the operator norms is at least `1`.
  simpa only [pow_zero, mul_one] using
    h_bound Z g x 1 zero_le_one fun γ _ _ ↦ (le_prod_opNorm _).1.trans_eq (one_mul _).symm

/-- If `k` has decay of order at least `13 (card n)³`, then the terms of the rational points in
`Z` in the kernel of `k ⊗ φ` are summable. -/
theorem summable_kernelTerm {B : ℕ} {k : GInf E s → ℂ} (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n))
    (hk : ∃ C : ℝ, ∀ g : GInf E s,
      ‖k g‖ * (∏ w : InfinitePlace E, ‖((g w : GL n ℂ) : Matrix n n ℂ)‖) ^ B ≤ C)
    (Z : Set (U V.J)) (g x : G E s) :
    Summable fun γ : U V.J ↦ V.kernelTerm k φ (Z.indicator 1) g γ x := by
  obtain ⟨C, -, h_bound⟩ := V.exists_tsum_enorm_kernelTerm_le_height
    (eight_mul_sq_lt_of_thirteen_mul_cube_le card_pos hB) φ hk
  exact Summable.of_enorm ((h_bound Z g x).trans_lt ENNReal.ofReal_lt_top).ne

/-- If `k` has decay of order at least `13 (card n)³`, then the values of `k ⊗ φ` at `x⁻¹ γ x`,
for the rational points `γ` with characteristic polynomial in `S`, are summable. -/
theorem summable_polyTerm {B : ℕ} {k : GInf E s → ℂ} (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n))
    (hk : ∃ C : ℝ, ∀ g : GInf E s,
      ‖k g‖ * (∏ w : InfinitePlace E, ‖((g w : GL n ℂ) : Matrix n n ℂ)‖) ^ B ≤ C)
    (S : Set E[X]) (x : G E s) :
    Summable fun γ : U V.J ↦ V.polyTerm k φ S γ x := by
  simpa only [polyTerm_eq_kernelTerm_indicator] using V.summable_kernelTerm hB φ hk _ x x

/-- Let `‖k(g)‖ ‖g‖^B` be bounded with `B ≥ 13 (card n)³`, where `‖g‖` is the product of the
operator norms. Let `A` be a cusp frame of size `δ` for `V.move x`, the space with its point moved
by `x`. This is a nonzero rational isotropic subspace such that it and its orthogonal are spanned by
lattice vectors whose length bounds have product at most `δ`. If no `γ ∈ Z` stabilises this
subspace, then `∑_{γ ∈ Z} ‖(k ⊗ φ)(x⁻¹ γ x)‖` is at most `C (δ ^ card n * height x) ^ (4 *
numInfPlaces * card n ^ 2)`. Here `C` does not depend on `x`, `δ`, `A` or `Z`, and `height x` is
`1 / min(1, first minimum of V.move x)`. -/
theorem exists_tsum_enorm_kernelTerm_le_of_notMem {B : ℕ} {k : GInf E s → ℂ}
    (hB : 13 * card n ^ 3 ≤ B) (φ : TestFunction (Gf E n))
    (hk : ∃ C : ℝ, ∀ g : GInf E s,
      ‖k g‖ * (∏ w : InfinitePlace E, ‖((g w : GL n ℂ) : Matrix n n ℂ)‖) ^ B ≤ C) :
    ∃ C ≥ (0 : ℝ), ∀ (x : G E s), ∀ δ ≥ (0 : ℝ), ∀ (A : (V.move x).CuspFrame δ) (Z : Set (U V.J)),
      (∀ γ ∈ Z, γ ∉ spanStabilizer V.J A.isotropicCols) →
      ∑' γ : U V.J, ‖V.kernelTerm k φ (Z.indicator 1) x γ x‖ₑ ≤
        ENNReal.ofReal
          (C * (δ ^ card n * V.height x) ^ (4 * Core.numInfPlaces E * card n ^ 2)) := by
  set f : ℕ := Core.numInfPlaces E
  set d : ℕ := 4 * f * card n ^ 2
  obtain ⟨C, hC, h_bound⟩ :=
    V.exists_tsum_enorm_kernelTerm_le (add_le_of_thirteen_mul_cube_le card_pos hB) φ hk
  obtain ⟨-, h_compact, -⟩ := φ.property
  -- If `⟨y', γ y⟩ ≠ 0` for short lattice vectors, then `x⁻¹ γ x` is large at infinity, provided
  -- that its finite component lies in the support of `φ`.
  obtain ⟨c, hc, h_large⟩ := V.exists_one_le_pow_mul_prod_norm h_compact.isCompact
  refine ⟨C * (c ^ card n) ^ d, by positivity, fun x δ hδ A Z hZ ↦ ?_⟩
  have h_norm (γ : U V.J) (hγ : γ ∈ Z) (hφ : (φ : Gf E n → ℂ) (x⁻¹ * V.ratEmbed γ * x).2 ≠ 0) :
      1 ≤ (c * δ) ^ f * ∏ w : InfinitePlace E,
        ‖(((x⁻¹ * V.ratEmbed γ * x).1 w : GL n ℂ) : Matrix n n ℂ)‖ := by
    -- As `γ A ⊄ A = (A^⊥)^⊥`, some `⟨y', γ y⟩` is not zero, for a column `y` of `A.isotropicCols`
    -- and a column `y'` of `A.perpCols`.
    obtain ⟨i, j, hij⟩ : ∃ i j : n,
        star (A.perpCols.col i) ⬝ᵥ V.J *ᵥ (((γ : GL n E) : Matrix n n E) *ᵥ A.isotropicCols.col j) ≠
          0 := by
      by_contra! h_zero
      have h_prod : A.perpColsᴴ * (V.J * (((γ : GL n E) : Matrix n n E) * A.isotropicCols)) = 0 :=
        Matrix.ext h_zero
      exact hZ γ hγ (A.isIsotropicFrame.mem_spanStabilizer_iff.2 h_prod)
    obtain ⟨hX_mem, hX_short⟩ := A.col_isotropicCols_mem j
    obtain ⟨hY_mem, hY_short⟩ := A.col_perpCols_mem i
    have h_short : ‖(V.move x).archCoords (A.isotropicCols.col j)‖ * ‖(V.move x).archCoords
      (A.perpCols.col i)‖ ≤ δ :=
      (mul_le_mul hX_short hY_short (norm_nonneg _) ((norm_nonneg _).trans hX_short)).trans
        A.length_mul_le
    exact h_large x γ _ _ δ hX_mem hY_mem h_short (subset_tsupport _ hφ) hij
  calc ∑' γ : U V.J, ‖V.kernelTerm k φ (Z.indicator 1) x γ x‖ₑ
      ≤ ENNReal.ofReal (C * ((c * δ) ^ f) ^ (4 * card n ^ 3) * V.height x ^ d) :=
        h_bound Z x x ((c * δ) ^ f) (by positivity) h_norm
    _ = ENNReal.ofReal (C * (c ^ card n) ^ d * (δ ^ card n * V.height x) ^ d) := by ring_nf!

/-- If `k` has decay of order at least `13 (card n)³`, then the sum of the moduli of the values of
`k ⊗ φ` at `x⁻¹ γ x`, over the rational points `γ` with irreducible characteristic polynomial, is
bounded in `x`. -/
theorem exists_tsum_enorm_irreducibleTerm_le {B : ℕ} {k : GInf E s → ℂ}
    (hB : 13 * card n ^ 3 ≤ B) (φ : TestFunction (Gf E n))
    (hk : ∃ C : ℝ, ∀ g : GInf E s,
      ‖k g‖ * (∏ w : InfinitePlace E, ‖((g w : GL n ℂ) : Matrix n n ℂ)‖) ^ B ≤ C) :
    ∃ C : ℝ, ∀ x : G E s, ∑' γ : U V.J, ‖V.irreducibleTerm k φ γ x‖ₑ ≤ ENNReal.ofReal C := by
  -- Either the height of `x` is bounded, or `x` is high in a cusp with an isotropic subspace,
  -- which no rational point with irreducible polynomial keeps.
  set d : ℕ := 4 * Core.numInfPlaces E * card n ^ 2
  obtain ⟨κ, -, h_cusp⟩ := exists_cuspFrame_of_height (s := s) (⊤ : OpenSubgroup (Gf E n))
  obtain ⟨C₀, hC₀, h_low⟩ := V.exists_tsum_enorm_kernelTerm_le_height
    (eight_mul_sq_lt_of_thirteen_mul_cube_le card_pos hB) φ hk
  obtain ⟨C₁, -, h_moves⟩ := V.exists_tsum_enorm_kernelTerm_le_of_notMem hB φ hk
  refine ⟨max (C₀ * κ ^ d) (C₁ * κ ^ d), fun x ↦ ?_⟩
  have h_height : 0 < V.height x := V.height_pos x
  -- The equation `δ ^ card n * V.height x = κ` eliminates `κ`.
  obtain ⟨δ, hδ, rfl, h_frame⟩ := h_cusp V x
  simp only [irreducibleTerm, polyTerm_eq_kernelTerm_indicator]
  obtain h_one | h_one := le_total 1 δ
  · -- The height is bounded, so the bound by a power of the height suffices.
    refine (h_low _ x x).trans (ENNReal.ofReal_le_ofReal (le_max_of_le_left ?_))
    gcongr
    exact V.height_le_pow_mul_height h_one x
  -- High in a cusp, a point with irreducible polynomial moves the isotropic subspace.
  obtain ⟨A, -⟩ := h_frame h_one
  exact (h_moves x δ hδ.le A _ fun γ hγ h_keeps ↦
    A.isIsotropicFrame.not_irreducible_charpoly A.ne_zero h_keeps hγ).trans
      (ENNReal.ofReal_le_ofReal (le_max_right _ _))

/-- Let `k` be a cusp kernel of order `B ≥ 13 (card n)³`: a minimal idempotent with `α ∗ k = k` for
some continuous compactly supported `α`, and with `‖g‖^(B+1) k` integrable and `‖g‖^B k` bounded,
where `‖g‖` is the product of the operator norms. Let `φ` be left invariant under the level `J`, an
open subgroup of `Gf E n`. Let `A` be a cusp frame of size `δ` for `V.move x`, the space with its
point moved by `x`. This is a nonzero rational isotropic subspace such that it and its orthogonal
are spanned by lattice vectors whose length bounds have product at most `δ`. Assume its radical is
covered: `N_A x ⊆ (Γ ∩ N_A) x Z_δ J`, with `Z_δ` the real `δ`-ball about `1`. Then the norm of the
sum of `(k ⊗ φ)(x⁻¹ γ x)` over the rational isometries `γ` that keep the subspace and have
characteristic polynomial in `S` is at most `C (δ ^ card n * height x) ^ (4 * numInfPlaces * card n
^ 2)`. Here `C` does not depend on `x`, `δ`, `A` or `S`, and `height x` is
`1 / min(1, first minimum of V.move x)`. -/
theorem exists_norm_partialKernel_spanStabilizer_le {B : ℕ} {k : GInf E s → ℂ}
    (hB : 13 * card n ^ 3 ≤ B) (φ : TestFunction (Gf E n)) (he : IsCuspKernel B k)
    {J : Subgroup (Gf E n)} [hJ : IsLevel J]
    (h_level : ∀ u ∈ J, ∀ y : Gf E n, (φ : Gf E n → ℂ) (u⁻¹ * y) = (φ : Gf E n → ℂ) y) :
    ∃ C : ℝ, ∀ (x : G E s), ∀ δ ≥ (0 : ℝ), ∀ A : (V.move x).CuspFrame δ,
      (V.move x).RadicalCovered A.isotropicCols δ J → ∀ S : Set E[X],
      ‖V.partialKernel k φ {γ : U V.J | γ ∈ spanStabilizer V.J A.isotropicCols ∧
          ((γ : GL n E) : Matrix n n E).charpoly ∈ S} x x‖ ≤
        C * (δ ^ card n * V.height x) ^ (4 * Core.numInfPlaces E * card n ^ 2) := by
  set d : ℕ := 4 * Core.numInfPlaces E * card n ^ 2
  obtain ⟨C, hC, h_bound⟩ := V.exists_tsum_enorm_kernelTerm_le_height
    (eight_mul_sq_lt_of_thirteen_mul_cube_le card_pos hB) φ he.decay
  -- In a cusp of size `δ`, a bounded continuous function of level `J` that is fixed by `k` and
  -- invariant under the rational radical is at most `(δ / δ₀) ^ (card n * d)` times its bound.
  obtain ⟨δ₀, hδ₀, h_decay⟩ := exists_norm_le_of_radicalCovered (s := s) he (card n * d)
  refine ⟨C / δ₀ ^ (card n * d), fun x δ hδ A h_cover S ↦ ?_⟩
  set Z : Set (U V.J) :=
    {γ | γ ∈ spanStabilizer V.J A.isotropicCols ∧ ((γ : GL n E) : Matrix n n E).charpoly ∈ S}
  have hk : Measurable k := he.continuous.measurable
  have h_height : 0 < V.height x := V.height_pos x
  -- The rational radical keeps `Z`, since `ν γ` and `γ` have the same polynomial.
  have h_keeps (ν : U V.J) (hν : (ν, 1) ∈ dilationGroup A.isotropicCols) (γ : U V.J) :
    ν * γ ∈ Z ↔ γ ∈ Z := by
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      mul_mem_cancel_left (mem_spanStabilizer_of_mem_dilationGroup hν)]
    exact and_congr_right fun hγ ↦ by rw [A.isIsotropicFrame.charpoly_radical_mul hν hγ]
  -- As a function of `g`, the partial kernel is bounded, of level `J` and fixed by `k`, hence
  -- continuous.
  let F (g : G E s) : ℂ := V.partialKernel k φ Z g x
  have hF_bound (g : G E s) : ‖F g‖ ≤ C * V.height x ^ d :=
    norm_tsum_le_of_tsum_enorm_le (by positivity) (h_bound Z g x)
  have hF_level : HasLevel F J := V.hasLevel_partialKernel h_level Z x
  -- Convolution with `k` fixes `F`, since the sums of moduli are bounded.
  have hF_fix : realConv k F = F :=
    V.realConv_partialKernel φ he.toIsIdempotentKernel fun g ↦ h_bound Z g x
  have hF_meas : Measurable F := by fun_prop [partialKernel]
  have hF_cont : Continuous F := by
    rw [← hF_fix]
    exact continuous_realConv ⟨J, hJ.isOpen⟩ ⟨hF_meas.stronglyMeasurable, _, hF_bound⟩ hF_level
      he.integrable
  calc ‖F x‖ ≤ (δ / δ₀) ^ (card n * d) * (C * V.height x ^ d) :=
        h_decay J V x δ A.isotropicCols hδ A.ne_zero A.isotropic h_cover F _ hF_cont hF_bound hF_fix
          hF_level
          fun ν hν g ↦ V.partialKernel_ratEmbed_mul φ (h_keeps ν hν) g x
    _ = C / δ₀ ^ (card n * d) * (δ ^ card n * V.height x) ^ d := by ring

/-- If `k` is a cusp kernel (a minimal idempotent kernel with decay, an integrable moment and a
reproducing function of compact support) of order at least `13 (card n)³`, then the sums of
`k ⊗ φ` at `x⁻¹ γ x` over the rational points `γ` with characteristic polynomial in `S` are
bounded uniformly in the point `x` and in the set `S` of polynomials. -/
theorem exists_norm_tsum_polyTerm_le {B : ℕ} {k : GInf E s → ℂ} (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n)) (he : IsCuspKernel B k) :
    ∃ D : ℝ, ∀ (x : G E s) (S : Set E[X]), ‖∑' γ : U V.J, V.polyTerm k φ S γ x‖ ≤ D := by
  -- Bound the sum by the height where this is bounded. High in a cusp, split it into the points
  -- that move the isotropic subspace and those that keep it.
  classical
  obtain ⟨J, hJ, h_level, -⟩ := TestFunction.exists_isLevel_invariant φ
  obtain ⟨κ, -, h_cusp⟩ :=
    exists_cuspFrame_of_height (s := s) (⟨J, hJ.isOpen⟩ : OpenSubgroup (Gf E n))
  set d : ℕ := 4 * Core.numInfPlaces E * card n ^ 2
  obtain ⟨C₀, hC₀, h_low⟩ := V.exists_tsum_enorm_kernelTerm_le_height
    (eight_mul_sq_lt_of_thirteen_mul_cube_le card_pos hB) φ he.decay
  obtain ⟨C₁, hC₁, h_moves⟩ := V.exists_tsum_enorm_kernelTerm_le_of_notMem hB φ he.decay
  obtain ⟨C₂, h_keeps⟩ := V.exists_norm_partialKernel_spanStabilizer_le hB φ he h_level
  refine ⟨max (C₀ * κ ^ d) (C₂ * κ ^ d + C₁ * κ ^ d), fun x S ↦ ?_⟩
  have h_height : 0 < V.height x := V.height_pos x
  -- The equation `δ ^ card n * V.height x = κ` eliminates `κ`.
  obtain ⟨δ, hδ, rfl, h_frame⟩ := h_cusp V x
  let inS : Set (U V.J) := {γ | ((γ : GL n E) : Matrix n n E).charpoly ∈ S}
  have h_sum : ∑' γ : U V.J, V.polyTerm k φ S γ x = V.partialKernel k φ inS x x :=
    tsum_congr fun γ ↦ V.polyTerm_eq_kernelTerm_indicator k φ S γ x
  rw [h_sum]
  obtain h_one | h_one := le_total 1 δ
  · -- The height is bounded, so the bound by a power of the height suffices.
    have h_norm : ‖V.partialKernel k φ inS x x‖ ≤ C₀ * V.height x ^ d :=
      norm_tsum_le_of_tsum_enorm_le (by positivity) (h_low inS x x)
    refine le_max_of_le_left (h_norm.trans ?_)
    gcongr
    exact V.height_le_pow_mul_height h_one x
  -- High in a cusp, split the sum according to whether `γ` keeps the isotropic subspace.
  obtain ⟨A, h_cover⟩ := h_frame h_one
  let stab : Set (U V.J) := spanStabilizer V.J A.isotropicCols
  have h_split : V.partialKernel k φ inS x x =
      V.partialKernel k φ (stab ∩ inS) x x + V.partialKernel k φ (inS \ stab) x x := by
    simp only [partialKernel, ← (V.summable_kernelTerm hB φ he.decay _ x x).tsum_add
      (V.summable_kernelTerm hB φ he.decay _ x x)]
    refine tsum_congr fun γ ↦ ?_
    by_cases hγ : γ ∈ stab <;> simp [kernelTerm, Set.indicator, hγ]
  have h_move : ‖V.partialKernel k φ (inS \ stab) x x‖ ≤ C₁ * (δ ^ card n * V.height x) ^ d :=
    norm_tsum_le_of_tsum_enorm_le (by positivity) (h_moves x δ hδ.le A _ fun γ hγ ↦ hγ.2)
  rw [h_split]
  exact le_max_of_le_right (norm_add_le_of_le (h_keeps x δ hδ.le A h_cover S) h_move)

end Space

end New

end
