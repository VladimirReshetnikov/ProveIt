import Lib.Shimura.ComplexTheta.DimensionFormula

/-!
# Sizes of theta functions at torsion points: products, bounds and shift bounds

Theta functions (`New.RealComplexForm.thetaSpace`) on a complex torus `V / L`, measured at the
torsion points by a valuation `v` on `ℂ`. The degree is a form `B` (a `LatticeForm L`: it has
complex values B x y, and degrees are added and scaled by reals) with Appell–Humbert data
`New.IsAppellHumbert` and Riemann form `New.RealComplexForm.riemannForm`;
`New.RealComplexForm.thetaShift` is translation with the exponential factor that keeps the degree.
The size `New.ThetaTori.LatticeForm.sizeAt` of `f` at a torsion point `x` is
`v (exp (-B x x / 2) * f x)`, and `New.ThetaTori.LatticeForm.sizes` is the set of all sizes of
degree `B`, over all multipliers χ of finite order with `New.ThetaTori.IsAmpleType`. Roots of unity
have valuation `1`, so sizes are periodic and do not see these multipliers.

* `New.ThetaTori.mul_shift_mem_sizes`: products of sizes with torsion translates of sizes are sizes.
* `New.ThetaTori.bddAbove_of_mem_sizes`, `New.ThetaTori.IsAmpleType.thetaNorm_pos`: sizes are
  bounded, and the sup norm of `f ≠ 0` is positive.
* `New.ThetaTori.eq_zero_of_torsionPoints`: a holomorphic function that vanishes at all torsion
  points is zero.
* `New.ThetaTori.LatticeForm.HasShiftBound`: the bound `φ ^ 2 ≤ C * ⨆ x, φ x * φ (x + w)`. It passes
  from `B` to `B'` when the Riemann form of `B - B'` is positive
  (`New.ThetaTori.LatticeForm.HasShiftBound.of_isPosRiemann_sub`), and with `C = 1` it compares
  products of translates (`New.ThetaTori.mul_le_iSup_of_hasShiftBound`).

Notions from other files:
* `New.IsPosRiemann`: The Riemann form E of B is positive: E(u, iu) > 0 for every u ≠ 0.
* `New.RealComplexForm.dualLattice`: The dual of L for the Riemann form E of B: the v in V with E(v,
  l) an integer for all l in L.

## Relation to the literature

Known; see `Lib.Shimura.GoodReduction.MultiplicativeNorm` for sources.
-/

noncomputable section

namespace New.ThetaTori

open Function Complex NNReal Module Filter Submodule Set Quotient ZSpan thetaSpace

variable {V : Type} [FinComplexSpace V] {L : Submodule ℤ V}

/-! ### Definitions -/

/-- The ℤ-submodule of the vectors a of V with na in L for some n ≠ 0: the preimage in V of the
torsion subgroup of V/L. -/
def torsionPoints (L : Submodule ℤ V) : Submodule ℤ V :=
  ((torsion' ℤ (V ⧸ L) (nonZeroDivisors ℕ)).comap L.mkQ).copy {a : V | ∃ n ≠ (0 : ℕ), n • a ∈ L}
    (by simp [← mk_smul])

variable (v : Valuation ℂ ℝ≥0) (B B' : LatticeForm L)

/-- (L, B, χ) is an Appell–Humbert datum (the Riemann form E of B is integral on L, and χ is a
nonvanishing multiplier on L) with positive Riemann form, and χ has finite order on L: χⁿ = 1 there
for some n ≠ 0. -/
structure IsAmpleType (χ : V → ℂ) extends isAppellHumbert : IsAppellHumbert B χ,
  isPosRiemann : IsPosRiemann B where
  /-- The multiplier `χ` has finite order on `L`. -/
  finite_order : ∃ n ≠ (0 : ℕ), ∀ l ∈ L, χ l ^ n = 1

/-- The size of f at a vector x of V of finite order modulo L: the value
v(exp(−B(x, x)/2)·f(x)). -/
def LatticeForm.sizeAt (f : V → ℂ) (x : torsionPoints L) : ℝ≥0 := v (B.thetaShift x f 0)

/-- The sup norm of f in degree B: the supremum of its sizes `New.ThetaTori.LatticeForm.sizeAt` over
all torsion points of V/L. -/
abbrev LatticeForm.thetaNorm (v : Valuation ℂ ℝ≥0) (f : V → ℂ) : ℝ≥0 := iSup (B.sizeAt v f)

/-- The sizes of degree B: the functions `New.ThetaTori.LatticeForm.sizeAt` of f on the torsion
points of V/L, for f a theta function of type (B, χ) (f is holomorphic, and for l in L, f(z + l) is
χ(l) times an exponential factor fixed by B, times f(z)), with any χ such that
`New.ThetaTori.IsAmpleType` holds for B and χ (a twisted theta function of degree B). -/
inductive LatticeForm.sizes : Set (torsionPoints L → ℝ≥0)
  /-- For `f` in `B.thetaSpace χ` with `IsAmpleType B χ`, the function `B.sizeAt v f` belongs to
  `LatticeForm.sizes`. -/
  | of_mem_thetaSpace {χ f : V → ℂ} : IsAmpleType B χ → f ∈ B.thetaSpace χ → sizes (B.sizeAt v f)

/-- The analytic form of good reduction of V/L at v: for all degrees B, C and all sizes φ, ψ of
these degrees (sizes of twisted theta functions f, g), the sup norm of the product φψ, the size of
fg, is the product of the sup norms. -/
def HasMultiplicativeNorm (L : Submodule ℤ V) : Prop :=
  ∀ ⦃B C : LatticeForm L⦄ ⦃φ ψ : ↥(torsionPoints L) → ℝ≥0⦄, φ ∈ B.sizes v →
    ψ ∈ C.sizes v →
    iSup (φ * ψ) = iSup φ * iSup ψ

/-- The conditions of `New.ThetaTori.IsAmpleType`, plus three more. Some natural N with v(N) = 1
maps the dual lattice of L into L. The level r > 1 has v(r) = 1. The sup norm is multiplicative
(`New.ThetaTori.HasMultiplicativeNorm`). -/
structure HasGoodReduction (χ : V → ℂ) (v : Valuation ℂ ℝ≥0) (r : ℕ) extends IsAmpleType B χ where
  /-- Some natural number of valuation `1` multiplies the dual lattice of `L` into `L`. -/
  dual_torsion : ∃ N : ℕ, v N = 1 ∧ ∀ a ∈ B.dualLattice, N • a ∈ L
  /-- The level `r` has valuation `1`. -/
  val_eq_one : v r = 1
  /-- The level `r` is at least `2`. -/
  one_lt : 1 < r
  /-- The sup norm of theta functions on the torsion points is multiplicative. -/
  hasMultiplicativeNorm : HasMultiplicativeNorm v L

/-- For the size function φ of every twisted theta function of degree B, (sup φ)² ≤ C · sup_x
φ(x) φ(x + w), x over the torsion points. -/
def LatticeForm.HasShiftBound (w : ↥(torsionPoints L)) (C : ℝ≥0) : Prop :=
  ∀ φ ∈ B.sizes v, ∀ y : ↥(torsionPoints L),
    φ y ^ 2 ≤ C * ⨆ x : ↥(torsionPoints L), φ x * φ (x + w)

open LatticeForm

variable {v : Valuation ℂ ℝ≥0} {B B' : LatticeForm L} {χ g : V → ℂ}
  {φ ψ : ↥(torsionPoints L) → ℝ≥0} {C : ℝ≥0} {n : ℕ} {f : V → ℂ} {x y w : torsionPoints L}

/-! ### Products, translates and periodicity of sizes -/

@[simp]
lemma sizeAt_mul : (B + B').sizeAt v (f * g) = B.sizeAt v f * B'.sizeAt v g := by
  ext
  simp [sizeAt]

lemma sizeAt_pow : (n • B).sizeAt v (f ^ n) = B.sizeAt v f ^ n := by
  ext
  simp [sizeAt]

lemma valuation_eq_one_of_pow_eq_one {ζ : ℂ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) : v ζ = 1 := by
  simpa [hn] using congrArg v hζ

/-- Let `B` carry an Appell–Humbert datum (`New.IsAppellHumbert`), with Riemann form `E`. At torsion
points `a`, `b` the number `exp (π i E(a, b))` is a root of unity, so it has valuation `1`. -/
lemma _root_.New.IsAppellHumbert.valuation_exp_riemannForm (hB : IsAppellHumbert B χ)
    (a b : torsionPoints L) :
    v (exp (Real.pi * I * B.riemannForm a b)) = 1 := by
  obtain ⟨a, n, hn, ha⟩ := a
  obtain ⟨b, m, hm, hb⟩ := b
  -- `n • a` and `m • b` lie in `L`, so the exponential is a root of unity
  exact valuation_eq_one_of_pow_eq_one (n := 2 * n * m) (by simp [hn, hm])
    (hB.exp_riemannForm_pow_eq_one ha hb)

/-- The size at `x` of the translate `B.thetaShift w f` is the size of `f` at `x + w`, for torsion
points `w`, `x`. -/
lemma _root_.New.IsAppellHumbert.sizeAt_thetaShift (hB : IsAppellHumbert B χ)
    (w x : torsionPoints L) :
    B.sizeAt v (B.thetaShift w f) x = B.sizeAt v f (x + w) := by
  simp [sizeAt, hB.thetaShift_thetaShift, hB.valuation_exp_riemannForm]

/-- Sizes are periodic modulo `L`: a size `φ` of degree `B` takes the same value at two torsion
points with the same class in `V ⧸ L`. -/
lemma factorsThrough_mkQ_of_mem_sizes (hφ : φ ∈ B.sizes v) :
    FactorsThrough φ fun x : ↥(torsionPoints L) ↦ L.mkQ x := by
  obtain @⟨χ, f, ⟨hAH, -, n, hn, hχ⟩, hf⟩ := hφ
  intro x y h_mkQ
  have hxy : (x - y : V) ∈ L := SModEq.sub_mem.mp h_mkQ
  -- Translation by `x - y ∈ L` multiplies `f` by the root of unity `χ (x - y)`, of valuation 1.
  calc
    B.sizeAt v f x = B.sizeAt v (B.thetaShift (x - y : torsionPoints L) f) y := by
      rw [hAH.sizeAt_thetaShift, add_sub_cancel]
    _ = B.sizeAt v f y := by
      simp [thetaShift_of_mem hf hxy, valuation_eq_one_of_pow_eq_one hn (hχ _ hxy), sizeAt]

/-- Let `φ` and `ψ` be sizes of degrees `B` and `B'`. For every torsion point `w` the function
`x ↦ φ x * ψ (x + w)` is a size of degree `B + B'`. -/
lemma mul_shift_mem_sizes (hφ : φ ∈ B.sizes v) (hψ : ψ ∈ B'.sizes v) (w : ↥(torsionPoints L)) :
    (fun x : ↥(torsionPoints L) ↦ φ x * ψ (x + w)) ∈ (B + B').sizes v := by
  obtain @⟨χ, f, ⟨hB, hB_pos, n, hn, hχ⟩, hf⟩ := hφ
  obtain @⟨χ', g, ⟨hB', hB'_pos, m, hm, hχ'⟩, hg⟩ := hψ
  obtain ⟨w, r, hr, hrw⟩ := w
  -- The product is the size of `f` times the translate of `g` by `w`. Translation twists the
  -- multiplier of `g` by `B'.riemannPhase l w`, a root of unity because a multiple `r • w` lies in
  -- `L`.
  have h_pos : IsPosRiemann (B + B') := by simp_all [pr_iff, add_pos]
  have h_order : ∀ l ∈ L, (χ * fun l ↦ χ' l * B'.riemannPhase l w) l ^ (n * m * r) = 1 := by
    intro l hl
    simpa [mul_pow, pow_mul, pow_right_comm _ n, ← exp_nsmul, hχ l hl, hχ' l hl, mul_assoc] using
      hB'.exp_riemannForm_pow_eq_one (nsmul_mem hl (n * m)) hrw
  have h_ample : IsAmpleType (B + B') (χ * fun l ↦ χ' l * B'.riemannPhase l w) :=
    ⟨hB.add (.mul_riemannPhase w), h_pos, n * m * r, mul_ne_zero (mul_ne_zero hn hm) hr, h_order⟩
  have h_eq : (B + B').sizeAt v (f * B'.thetaShift w g) =
      fun x : ↥(torsionPoints L) ↦ B.sizeAt v f x * B'.sizeAt v g (x + ⟨w, r, hr, hrw⟩) := by
    funext x
    rw [sizeAt_mul, Pi.mul_apply, hB'.sizeAt_thetaShift ⟨w, r, hr, hrw⟩ x]
  exact h_eq.subst (sizes.of_mem_thetaSpace h_ample (mul hf (hB'.thetaShift_mem hg w)))

variable [IsFullRankLattice L]

/-! ### Finiteness and density of torsion points -/

/-- A function on the torsion points that depends only on the class modulo `L` takes finitely many
values on the points `x` with `n • x ∈ L`, for `n ≠ 0`. -/
lemma finite_range_nsmul_torsion {α : Type*} {p : torsionPoints L → α} (hn : n ≠ 0)
    (hp : p.FactorsThrough fun x : ↥(torsionPoints L) ↦ L.mkQ x) :
    (range fun x : L.comap (n • (torsionPoints L).subtype) ↦ p x).Finite := by
  -- The points killed by `n` modulo `L` lie in the image `M` of `n⁻¹ L` in `V ⧸ L`, a finitely
  -- generated torsion group, hence finite; and `p` factors through `V ⧸ L`.
  let M : Submodule ℤ (V ⧸ L) := L.map (L.mkQ ∘ₗ ((n⁻¹ : ℂ) • 1))
  have hM : (M : Set (V ⧸ L)).Finite := finite_of_fg_torsion M fun ⟨_, l, hl, rfl⟩ ↦
    ⟨⟨n, by simpa⟩, by simpa [← mk_smul, ← smul_assoc, hn]⟩
  -- `extend _ p (p ∘ 0)` is `p` pushed down to `V ⧸ L` (with the value `p 0` off the image)
  refine (hM.image (extend _ p (p ∘ 0))).subset
    (range_subset_iff.mpr fun x ↦ ⟨L.mkQ x, ⟨_, x.property, ?_⟩, hp.extend_apply ..⟩)
  simp [← Nat.cast_smul_eq_nsmul ℂ, hn]

/-- A full-rank lattice `L` in `V` is cocompact: some compact set meets every coset of `L`. -/
lemma isCocompact_of_isFullRankLattice : L.toAddSubgroup.IsCocompact := by
  -- The fractional parts for a basis `b` of `L` lie in the ball of radius `∑ i, ‖b i‖`.
  let b := (finBasis ℤ L).ofZLatticeBasis ℝ
  refine ⟨_, isCompact_closedBall 0 (∑ i, ‖b i‖), fun x ↦ ⟨-floor b x, ?_, ?_⟩⟩
  · exact ((finBasis ℤ L).ofZLatticeBasis_span ℝ).le (-floor b x).2
  · -- the fractional part `x - floor b x` has norm at most `∑ i, ‖b i‖`
    simpa [neg_add_eq_sub, ZSpan.fract_apply] using norm_fract_le b x

/-- A continuous function that vanishes on lattices of arbitrarily small mesh is zero: suppose that
for linear maps `d` arbitrarily close to `0` there is a left inverse `c` of `d` such that `f`
vanishes on the preimage of `L` under `c`. Then `f = 0`. -/
lemma eq_zero_of_small_mesh (hf : Continuous f)
    (h_small : ∃ᶠ d : V →L[ℂ] V in nhds 0, ∃ c : V →L[ℂ] V,
      (∀ y : V, c (d y) = y) ∧ ∀ y : V, c y ∈ L → f y = 0) :
    f = 0 := by
  obtain ⟨K, hK, h_cover⟩ := isCocompact_of_isFullRankLattice (L := L)
  funext z
  by_contra hz
  -- If `f z ≠ 0`, then for `d` near 0 the function `f` has no zero on `z - d K`.
  have h_ne : ∀ᶠ d : V →L[ℂ] V in nhds 0, ∀ u ∈ K, f (z - d u) ∈ ({0}ᶜ : Set ℂ) :=
    hK.eventually_forall_mem (fun (d : V →L[ℂ] V) u ↦ f (z - d u)) {0}ᶜ (by aesop)
  refine h_small (h_ne.mono fun d hd ⟨c, hcd, h_zero⟩ ↦ ?_)
  -- But `u = l + c z ∈ K` for some `l ∈ L`, and then `c (z - d u) = -l` lies in `L`.
  obtain ⟨l, hl, hu⟩ := h_cover (c z)
  exact hd _ hu (h_zero _ (by simpa [hcd] using hl))

/-- A holomorphic function `f` on `V` that vanishes at all torsion points of `V / L` is zero. -/
lemma eq_zero_of_torsionPoints (hf : Differentiable ℂ f) (h_zero : ∀ x : torsionPoints L, f x = 0) :
    f = 0 := by
  -- The zero set of `f` contains `n⁻¹ L` for all `n ≠ 0`, lattices of mesh tending to 0.
  have h_mesh : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (1 : V →L[ℂ] V)) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat.zero_smul_const 1
  -- for `d = n⁻¹ • 1` take `c = n • 1`: it inverts `d`, and `f` vanishes where `c y ∈ L`
  have h_small : ∃ᶠ d : V →L[ℂ] V in nhds 0, ∃ c : V →L[ℂ] V,
      (∀ y : V, c (d y) = y) ∧ ∀ y : V, c y ∈ L → f y = 0 := by
    refine h_mesh.frequently ((eventually_ne_atTop 0).frequently.mono fun n hn ↦ ?_)
    refine ⟨n, fun y ↦ ?_, fun y hy ↦ h_zero ⟨y, n, hn, hy⟩⟩
    simp [← smul_assoc, hn]
  exact eq_zero_of_small_mesh (L := L) hf.continuous h_small

omit [IsFullRankLattice L] in
/-- A fixed point argument for the constant in `New.ThetaTori.LatticeForm.HasShiftBound`, for a
family of degrees `B i` with translations `w i`. Suppose that some constant `D₀` serves every
`B i` with `w i`, and that whenever a constant `D` serves every `B i` with `w i`, the constant
`D * C` serves every `B i + B i` with `w i`. Then `C` serves every `B i` with `w i`. -/
lemma LatticeForm.HasShiftBound.of_doubling {ι : Sort*} (B : ι → LatticeForm L)
    (w : ι → torsionPoints L) (h_nonempty : ∃ D₀ : ℝ≥0, ∀ i : ι, (B i).HasShiftBound v (w i) D₀)
    (h_double : ∀ D : ℝ≥0, (∀ i : ι, (B i).HasShiftBound v (w i) D) →
      ∀ i : ι, (B i + B i).HasShiftBound v (w i) (D * C)) :
    ∀ i : ι, (B i).HasShiftBound v (w i) C := by
  -- `P D`: the constant `D` serves every degree `B i` with its translation `w i`; such a `D`
  -- is called admissible.
  let P (D : ℝ≥0) : Prop := ∀ i : ι, (B i).HasShiftBound v (w i) D
  have h_ne : Nonempty (Subtype P) := nonempty_subtype.mpr h_nonempty
  -- The infimum `D` of all admissible constants is admissible.
  set D : ℝ≥0 := ⨅ D' : Subtype P, D'.val
  have hD : P D := fun i φ hφ y ↦ le_iInf_mul fun D' : Subtype P ↦ D'.property i φ hφ y
  -- Apply `h_double` to the square `φ ^ 2` and take square roots: `√(D * C)` is admissible too.
  have hsqrt : P (sqrt (D * C)) := by
    intro i φ hφ
    have h_sq_mem : (fun x ↦ φ x * φ (x + 0)) ∈ (B i + B i).sizes v := mul_shift_mem_sizes hφ hφ 0
    simpa [← sq, ← le_sqrt_iff_sq_le, sqrt_mul] using h_double D hD i _ h_sq_mem
  -- Hence `D ^ 2 ≤ D * C`, that is `D ≤ C`.
  have hsq : D ^ 2 ≤ D * C :=
    le_sqrt_iff_sq_le.mp (ciInf_le' Subtype.val (⟨_, hsqrt⟩ : Subtype P))
  have hDC : D ≤ C := by nlinarith
  intro i φ hφ y
  calc φ y ^ 2 ≤ D * ⨆ x, φ x * φ (x + w i) := hD i φ hφ y
    _ ≤ C * ⨆ x, φ x * φ (x + w i) := by gcongr

/-- Let `L` be a full lattice in a finite-dimensional complex space `V`, and let `v` be an
ℝ≥0-valued valuation on ℂ. A size φ of degree `B` is the function `sizeAt` of `f` on the torsion
points of `V/L`, where `f` is a theta function of type (`B`, χ) for some χ with `IsAmpleType B χ`.
Every such φ is bounded above. -/
lemma bddAbove_of_mem_sizes (hφ : φ ∈ B.sizes v) : BddAbove (range φ) := by
  -- Let `φ` be the size of `g`, with multiplier of order dividing `n`. Then `g ^ (4 * n)` and
  -- `g₂ = g (2 ·) ^ n` have the same type, so the first is a combination of translates of `g₂`,
  -- with coefficients `c i`. Write `|c i|` for `v (c i)`.
  -- The maximum `M` of `φ` on a group `H`, finite modulo `L`, holding the translations and a given
  -- point then has `M ^ (4 * n) ≤ M ^ n * max |c i|`, so `M ≤ max 1 (max |c i|)`.
  obtain @⟨χ, g, h_ample, hg⟩ := hφ
  obtain ⟨n, hn, hχn⟩ := h_ample.finite_order
  have hB : IsAppellHumbert ((4 * n) • B) (χ ^ (4 * n)) := h_ample.isAppellHumbert.nsmul _
  have h_pos : IsPosRiemann ((4 * n) • B) := h_ample.isPosRiemann.nsmul (by lia)
  obtain ⟨N, hN, hNL⟩ := hB.exists_nsmul_mem_of_mem_dualLattice
  let g₂ : V → ℂ := (g ∘ fun z ↦ (2 : ℂ) • z) ^ n
  have h_span : g ^ (4 * n) ∈
      span ℂ ((fun a ↦ ((4 * n) • B).thetaShift a g₂) '' ((4 * n) • B).dualLattice) := by
    obtain rfl | hg0 := eq_or_ne g 0
    · simp [hn]
    have hg₂ : g₂ ∈ ((4 * n) • B).thetaSpace (χ ^ (4 * n)) := by
      obtain ⟨h_diff, h_per⟩ := hg
      refine ⟨by fun_prop, ?_⟩
      -- both multipliers `χ (2 l) ^ n` and `χ l ^ (4 * n)` are `1`; the exponents agree
      simp_all [g₂, mul_pow, pow_mul', ofNat_smul_eq_nsmul, nsmul_mem, ← exp_nsmul]
      -- what is left is the equality of the two exponents
      intro l hl z
      left
      congr 1
      ring
    have hg₂0 : g₂ ≠ 0 :=
      pow_ne_zero n ((MulAction.surjective₀ (two_ne_zero' ℂ)).injective_comp_right.ne hg0)
    -- irreducibility: the translates of one nonzero theta function by the dual lattice span all
    -- theta functions of its type, in particular `g ^ (4 * n)`
    exact hB.thetaSpace_le_of_thetaShift_mem hg₂ hg₂0 _ (image_subset_iff.mp subset_span) (pow hg _)
  obtain ⟨t, ht, c, hc⟩ := (mem_span_image_iff_exists_fun ℂ).mp h_span
  refine ⟨1 ⊔ iSup (v ∘ c), forall_mem_range.mpr fun ⟨x, m, hm, hx⟩ ↦ ?_⟩
  -- `H`: the points killed by `N * m` modulo `L`; `φ` is periodic, so takes finitely many values
  let H : Submodule ℤ (torsionPoints L) := L.comap ((N * m) • (torsionPoints L).subtype)
  have h_fin : (range fun z : H ↦ B.sizeAt v g z).Finite :=
    finite_range_nsmul_torsion (mul_ne_zero hN hm) (factorsThrough_mkQ_of_mem_sizes ⟨h_ample, hg⟩)
  set M : ℝ≥0 := ⨆ z : H, B.sizeAt v g z
  have h_le (z : torsionPoints L) (hz : z ∈ H) : B.sizeAt v g z ≤ M :=
    le_ciSup h_fin.bddAbove ⟨z, hz⟩
  -- the normalising factor of degree `4 n B` at `y` is the `n`-th power of that of `B` at `2 y`
  have h_double (a : ℂ) (y : torsionPoints L) :
      ((4 * n) • B).sizeAt v (a • g₂) y = B.sizeAt v g (2 • y) ^ n * v a := by
    simp [g₂, sizeAt, thetaShift, ofNat_smul_eq_nsmul, mul_pow, ← map_pow, ← exp_nsmul]
    ring_nf
  -- ultrametric inequality: it suffices to bound each term of the combination
  have h_size_pow_le (z : H) : ((4 * n) • B).sizeAt v (g ^ (4 * n)) z ≤ M ^ n * iSup (v ∘ c) := by
    rw [← hc, sizeAt, map_sum, Finset.sum_apply]
    refine v.map_sum_le fun i _ ↦ ?_
    let a : torsionPoints L := ⟨i, N, hN, hNL _ (ht i.property)⟩
    have ha : a ∈ H := by simp [a, H, mul_nsmul, nsmul_mem (hNL _ (ht i.property))]
    rw [← map_smul]
    calc _ = ((4 * n) • B).sizeAt v (c i • g₂) (z + a) := hB.sizeAt_thetaShift a z
      _ = B.sizeAt v g (2 • (z + a)) ^ n * v (c i) := h_double (c i) (z + a)
      _ ≤ M ^ n * iSup (v ∘ c) := by
        gcongr
        exacts [h_le _ (nsmul_mem (add_mem z.property ha) 2), Finite.le_ciSup (v ∘ c) i]
  have h_pow : M ^ (4 * n) ≤ M ^ n * iSup (v ∘ c) := by
    rw [iSup_pow]
    exact ciSup_le' fun z ↦ (sizeAt_pow.ge (z : torsionPoints L)).trans (h_size_pow_le z)
  have hx_H : (⟨x, m, hm, hx⟩ : torsionPoints L) ∈ H := by simp [H, mul_smul, nsmul_mem, hx]
  refine (h_le _ hx_H).trans ?_
  obtain hM | hM := le_or_gt M 1
  · exact le_sup_of_le_left hM
  · refine le_sup_of_le_right (le_of_mul_le_mul_left ?_ (pow_pos hM.pos n))
    calc M ^ n * M = M ^ (n + 1) := (pow_succ M n).symm
      _ ≤ M ^ (4 * n) := pow_le_pow_right₀ hM.le (by lia)
      _ ≤ M ^ n * iSup (v ∘ c) := h_pow

lemma le_iSup_of_mem_sizes (hφ : φ ∈ B.sizes v) (x : ↥(torsionPoints L)) : φ x ≤ iSup φ :=
  le_ciSup (bddAbove_of_mem_sizes hφ) x

/-- Let `L` be a full-rank lattice in `V`, `v` a valuation on ℂ, `x`, `y`, `w` torsion points, and
φ, ψ sizes of degrees `B`, `B'` (`sizes`: functions x ↦ v(exp(−B(x, x)/2)·f(x)) on the torsion
points, for f a twisted theta function of degree B). Suppose every size ρ of degree B + B' satisfies
(sup ρ)² ≤ sup_z ρ(z)·ρ(z + (y − x − w)), which is `HasShiftBound` for y − x − w with C = 1. Then
φ(x)ψ(y) ≤ sup_z φ(z)ψ(z + w). -/
lemma mul_le_iSup_of_hasShiftBound (hφ : φ ∈ B.sizes v) (hψ : ψ ∈ B'.sizes v)
    (h_shift : (B + B').HasShiftBound v (y - x - w) 1) :
    φ x * ψ y ≤ ⨆ z : ↥(torsionPoints L), φ z * ψ (z + w) := by
  -- With `d = y - x - w`, let `ρ k` be the sup of `φ · ψ (· + w + k d)`. Then `ρ n = ρ 0` for
  -- some `n ≠ 0`, and `ρ (k + 1) ^ 2 ≤ ρ k * ρ (k + 2)`. If the claim failed then `ρ 0 < ρ 1`, and
  -- by log-convexity `ρ` would be strictly increasing, against `ρ n = ρ 0`.
  set d : torsionPoints L := y - x - w with hd
  let ρ (k : ℕ) : ℝ≥0 := ⨆ z, φ z * ψ (z + (w + k • d))
  have h_le (k : ℕ) (z : torsionPoints L) : φ z * ψ (z + (w + k • d)) ≤ ρ k :=
    le_iSup_of_mem_sizes (mul_shift_mem_sizes hφ hψ _) z
  obtain ⟨n, hn, hnd⟩ := d.property
  -- `n • d` lies in the lattice, and sizes are periodic
  have h_per : ρ 0 = ρ n :=
    iSup_congr fun z ↦
      congrArg _ (factorsThrough_mkQ_of_mem_sizes hψ (by simpa [← mk_smul] using hnd))
  -- log-convexity: the hypothesis for the size `F = φ · ψ (· + w + (k + 1) d)`, with the four
  -- factors of `F z * F (z + d)` regrouped
  have h_convex (k : ℕ) : ρ (k + 1) * ρ (k + 1) ≤ ρ k * ρ (k + 1 + 1) := by
    let F (z : torsionPoints L) : ℝ≥0 := φ z * ψ (z + (w + (k + 1) • d))
    calc ρ (k + 1) * ρ (k + 1) = ⨆ z, F z ^ 2 := by rw [← sq, iSup_pow]
      _ ≤ 1 * ⨆ z, F z * F (z + d) := ciSup_le' (h_shift _ (mul_shift_mem_sizes hφ hψ _))
      _ = ⨆ z, φ (z + d) * ψ (z + d + (w + k • d)) * (φ z * ψ (z + (w + (k + 1 + 1) • d))) := by
        grind [succ_nsmul]
      _ ≤ ρ k * ρ (k + 1 + 1) := ciSup_le' fun z ↦ mul_le_mul' (h_le k (z + d)) (h_le _ z)
  by_contra! h_lt
  have h_step (k : ℕ) : ρ k < ρ (k + 1) := by
    induction k with
    | zero =>
      exact lt_of_lt_of_le (by simpa [ρ, hd] using h_lt) (h_le _ x)
    -- `ρ k * ρ (k + 1) < ρ (k + 1) ^ 2 ≤ ρ k * ρ (k + 2)`
    | succ k ih => nlinarith [h_convex k, (zero_le : 0 ≤ ρ k)]
  exact (strictMono_nat_of_lt_succ h_step hn.pos).ne h_per

omit [IsFullRankLattice L] in
lemma IsAmpleType.nsmul (h_ample : IsAmpleType B χ) (hn : n ≠ 0) : IsAmpleType (n • B) (χ ^ n) := by
  obtain ⟨m, hm, hχm⟩ := h_ample.finite_order
  exact ⟨h_ample.isAppellHumbert.nsmul n, h_ample.isPosRiemann.nsmul hn, m, hm,
    fun l hl ↦ by rw [Pi.pow_apply, pow_right_comm, hχm l hl, one_pow]⟩

/-- The sup norm `B.thetaNorm v f` of a nonzero theta function `f` of type `(B, χ)` is positive. -/
lemma IsAmpleType.thetaNorm_pos (h_ample : IsAmpleType B χ) (hf : f ∈ B.thetaSpace χ)
    (h_ne : f ≠ 0) : 0 < B.thetaNorm v f := by
  -- `f` is nonzero at some torsion point, and there its size is positive.
  have h_not_zero : ¬∀ x : torsionPoints L, f x = 0 := mt (eq_zero_of_torsionPoints hf.1) h_ne
  simpa [sizeAt, thetaShift, lt_ciSup_iff (bddAbove_of_mem_sizes ⟨h_ample, hf⟩), v.pos_iff]
    using h_not_zero

/-- Let L be a lattice of full rank in the finite-dimensional complex space V, let (L, B, χ) satisfy
`New.ThetaTori.IsAmpleType`, and let the Riemann form of B − B' be positive. If the bound of
`New.ThetaTori.LatticeForm.HasShiftBound` for w with constant C holds for the sizes of all theta
functions of type (B, χ), then it holds in degree B'. -/
lemma LatticeForm.HasShiftBound.of_isPosRiemann_sub (h_ample : IsAmpleType B χ)
    (h_pos : IsPosRiemann (B + -B'))
    (h_shift : ∀ f ∈ B.thetaSpace χ, ∀ y : ↥(torsionPoints L),
      B.sizeAt v f y ^ 2 ≤
        C * ⨆ x : ↥(torsionPoints L), B.sizeAt v f x * B.sizeAt v f (x + w)) :
    B'.HasShiftBound v w C := by
  -- Let `φ` be the size of `f`, of degree `B'` and multiplier `ζ`, and `σ` the size of a nonzero
  -- `g` of degree `B - B'` and multiplier `χ / ζ`. Apply the hypothesis to a product of translates
  -- of `f` and `g` with multiplier `χ`, bound the two factors `σ` on the right by `iSup σ`, take
  -- the sup over `s` on the left, and cancel `iSup σ ^ 2 > 0`.
  intro φ₀ hφ₀ x
  obtain @⟨ζ, f, ⟨hζ, hB', m, hm, hζm⟩, hf⟩ := hφ₀
  have hφ : B'.sizeAt v f ∈ B'.sizes v := sizes.of_mem_thetaSpace ⟨hζ, hB', m, hm, hζm⟩ hf
  have h_ample' : IsAmpleType (B + -B') (χ * ζ⁻¹) := by
    refine ⟨h_ample.add hζ.neg, h_pos, h_ample.finite_order.imp' (fun n ↦ n * m) ?_⟩
    simp_all [mul_pow, pow_mul, pow_right_comm]
  obtain ⟨g, hg, hg0⟩ := h_ample'.exists_mem_thetaSpace_ne_zero
  obtain ⟨N, hN, hNL⟩ := h_ample.exists_nsmul_mem_of_mem_dualLattice (hp := h_ample.isPosRiemann)
  have hσ : (B + -B').sizeAt v g ∈ (B + -B').sizes v := ⟨h_ample', hg⟩
  have hσ_pos : 0 < iSup ((B + -B').sizeAt v g) := h_ample'.thetaNorm_pos hg hg0
  set φ : torsionPoints L → ℝ≥0 := B'.sizeAt v f
  set σ : torsionPoints L → ℝ≥0 := (B + -B').sizeAt v g
  set S : ℝ≥0 := ⨆ z, φ z * φ (z + w)
  have h_sq_le (s : torsionPoints L) : φ x ^ 2 * σ s ^ 2 ≤ C * (S * iSup σ ^ 2) := by
    -- With `E`, `E'` the Riemann forms of `B`, `B'`, solve `E(u, ·) = E'(t, ·)`. If `r • t ∈ L`,
    -- then `r • u` lies in the dual lattice of `B`, so `u` is torsion.
    let t : torsionPoints L := s - x
    let u₀ : V := (B.riemannForm.toDual h_ample.nondegenerate).symm (B'.riemannForm t)
    have hu₀ (y : V) : B.riemannForm u₀ y = B'.riemannForm t y := by simp [u₀]
    obtain ⟨r, hr, hrt⟩ := t.property
    have h_dual : r • u₀ ∈ B.dualLattice := fun l hl ↦ by
      simpa [hu₀] using hζ.le_dualLattice hrt l hl
    let u : torsionPoints L := ⟨u₀, N * r, mul_ne_zero hN hr,
      by simpa [mul_smul] using hNL _ h_dual⟩
    -- the exponents `E'(l, u - t)` and `E(l, u) - E'(l, u)` that twist the multipliers cancel
    have h_mem :
        B'.thetaShift (u - t) f * (B + -B').thetaShift u g ∈ (B' + (B + -B')).thetaSpace χ := by
      refine (mul (hζ.thetaShift_mem hf (u - t)) (h_ample'.thetaShift_mem hg u)).imp_right
        fun h_per l hl ↦ ?_
      have hζ_ne : ζ l ≠ 0 := hζ.ne_zero hl
      simp [h_per, u, hu₀, riemannForm_swap _ l, hl, exp_sub, exp_add, exp_neg, mul_sub, mul_add,
        field]
    have h_size (y : torsionPoints L) :
        (B' + (B + -B')).sizeAt v (B'.thetaShift (u - t) f * (B + -B').thetaShift u g) y =
          φ (y + (u - t)) * σ (y + u) := by
      rw [sizeAt_mul, Pi.mul_apply]
      exact congrArg₂ (· * ·) (hζ.sizeAt_thetaShift (u - t) y) (h_ample'.sizeAt_thetaShift u y)
    calc
      φ x ^ 2 * σ s ^ 2 = (φ (s - u + (u - t)) * σ (s - u + u)) ^ 2 := by simp [t, mul_pow]
      _ ≤ C * ⨆ z, φ (z + (u - t)) * σ (z + u) * (φ (z + w + (u - t)) * σ (z + w + u)) := by
        simp only [← h_size]
        rw [show B' + (B + -B') = B by simp] at h_mem ⊢
        exact h_shift _ h_mem _
      _ ≤ C * (S * iSup σ ^ 2) := by
        gcongr
        refine ciSup_le' fun z ↦ ?_
        rw [mul_mul_mul_comm, add_right_comm z w, sq]
        gcongr
        exacts [le_iSup_of_mem_sizes (mul_shift_mem_sizes hφ hφ w) _, le_iSup_of_mem_sizes hσ _,
          le_iSup_of_mem_sizes hσ _]
  refine le_of_mul_le_mul_right ?_ (pow_pos hσ_pos 2)
  calc φ x ^ 2 * iSup σ ^ 2 = φ x ^ 2 * ⨆ s, σ s ^ 2 := by rw [iSup_pow]
    _ ≤ C * (S * iSup σ ^ 2) := mul_iSup_le h_sq_le
    _ = C * S * iSup σ ^ 2 := (mul_assoc C S _).symm

omit [IsFullRankLattice L] in
/-- Let (L, B, χ) satisfy `New.ThetaTori.IsAmpleType`. For every form A and all large enough m,
m ≠ 0 and the Riemann form of m • B − A is positive. -/
lemma IsAmpleType.eventually_isPosRiemann_smul_sub (h_ample : IsAmpleType B χ) (A : LatticeForm L) :
    ∀ᶠ m : ℕ in atTop, m ≠ 0 ∧ IsPosRiemann (m • B + -A) := by
  -- For large `m` the form `B - m⁻¹ A` is positive; multiply it by `m`.
  have h_pos : ∀ᶠ m : ℕ in atTop, IsPosRiemann (B + -((m : ℝ)⁻¹ • A)) :=
    tendsto_inv_atTop_nhds_zero_nat.zero_smul_const A h_ample.isPosRiemann.eventually_add_neg
  filter_upwards [h_pos, eventually_ne_atTop 0] with m hm hm0
  exact ⟨hm0, by simpa [← smul_assoc, hm0] using hm.nsmul hm0⟩

end New.ThetaTori

end
