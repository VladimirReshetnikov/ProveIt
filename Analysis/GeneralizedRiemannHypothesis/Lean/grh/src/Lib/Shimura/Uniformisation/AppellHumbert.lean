import Lib.General.Analysis.HolomorphicIntegrals
import Lib.Shimura.AbelianScheme.Pairings
import Lib.Shimura.Uniformisation.HolomorphicFamilies

/-!
# Existence in Appell–Humbert: projective embeddings are given by theta functions

The existence half of the Appell–Humbert theorem, for a projective embedding N of a uniformised
group A(ℂ) = V/L whose class satisfies the parallelogram law.

* `New.Uniformisation.appell_humbert`: the coordinates of N are theta functions for some
  Appell–Humbert data (L, B, χ) with positive Riemann form.
* `New.exists_analyticAt_double_eq`, `New.exists_extension_double`, `New.induction_on_double`: the
  doubling equation near 0, and its continuation to the whole space by halving.

Idea: the parallelogram law gives a frame on A × A, and its values define a function c. After
multiplying c by exp q(z, z) for a suitable quadratic form q, the doubling equation
σ(2z) = σ(z)⁴c(z) is solved near 0 and continued to V by halving. Then σ trivialises the pullback of
N.

`New.Uniformisation` A V is a surjective homomorphism e = `u.expMap` : V → A(ℂ), holomorphic and
immersive, with kernel the lattice L = `u.lattice`. `New.HasThetaCoords` says that θ(z) gives
homogeneous coordinates of e(z), each θ_i a theta function of type (B, χ): entire, with
θ_i(z + l) = χ(l)·exp(B l z + B l l / 2)·θ_i(z) for l in L.

Notions from other files:
* `New.atGeneric`: For a family s of sections of A over Spec O, O a valuation ring of ℂ, the complex
  point of A given by s(z) at the generic point.
* `New.LineBundle.IsHomogeneousCoords`: v is a vector of homogeneous coordinates of the point t for
  L: t lands in U_j exactly when v_j is a unit, and then g_jk(t) = v_k/v_j.
* `New.IsAppellHumbert`: Re B is symmetric, and on L one has |χ| = 1 and χ(l + m) = χ(l)χ(m)·exp(πi
  E(m, l)), E the Riemann form of B.
* `New.IsPosRiemann`: The Riemann form E of B is positive: E(u, iu) > 0 for every u ≠ 0.
* `New.Pic.ParallelogramLaw`: The parallelogram law for a class c in Pic A:
  (x+y)^*c + (x−y)^*c + 2·0^*c = 2(x^*c + y^*c) in Pic T for all T-points x, y of A and all
  S-schemes T.

## Relation to the literature

Known result: Appell–Humbert theorem, a step in the complex uniformisation of PEL abelian varieties.
For a given uniformisation, this file proves the existence half, for a very ample class obeying the
parallelogram law. Source: J. S. Milne, Introduction to Shimura Varieties (2005/2017), Theorem 8.17
and Lemma 5.12; R. Kottwitz, Points on some Shimura varieties over finite fields, J. AMS 5 (1992)
§8; G. Shimura, On analytic families of polarized abelian varieties and automorphic functions, Ann.
Math. 78 (1963); A. Borel, Some finiteness properties of adele groups over number fields, Publ. IHES
16 (1963); D. Mumford, Abelian Varieties §§1–2; L. Breen, Fonctions thêta et théorème du cube, LNM
980 (1983).
-/

open CategoryTheory CartesianMonoidalCategory Complex Over New LineBundle PointFn NormedAddGroup

/-- For `f` analytic at `0`, the equation `g (2z) = 4 g z + f z` has a solution analytic at `0`, up
to a quadratic form. -/
lemma New.exists_analyticAt_double_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : V → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ (g : V → ℂ) (q : V →L[ℂ] V →L[ℂ] ℂ),
      AnalyticAt ℂ g 0 ∧ ∀ᶠ z : V in nhds 0, g (z + z) = 4 * g z + f z + q z z := by
  obtain ⟨P, hP⟩ : ∃ P : FormalMultilinearSeries ℂ V ℂ, HasFPowerSeriesAt f P 0 := hf
  -- In degree `n` the equation reads `(2 ^ n - 4) G n = P n`. For `n = 2` the factor vanishes, so
  -- `G 2 = 0` and `q` cancels `P 2`.
  let G : FormalMultilinearSeries ℂ V ℂ := fun n ↦ (2 ^ n - 4 : ℝ)⁻¹ • P n
  -- The inverse of an integer has absolute value at most `1`, so `G` converges where `P` does.
  have h_norm (n : ℕ) : ‖G n‖ ≤ ‖P n‖ := by
    simpa [G, norm_smul] using
      mul_le_of_le_one_left (norm_nonneg _) (2 ^ n - 4 : ℤ).natAbs.cast_inv_le_one
  have h_ball : ∀ᶠ z : V in nhds 0, z ∈ Metric.eball 0 G.radius :=
    Metric.eball_mem_nhds _ (hP.radius_pos.trans_le (G.radius_le_of_le h_norm))
  have h_ball₂ : ∀ᶠ z : V in nhds 0, z + z ∈ Metric.eball 0 G.radius :=
    ((continuous_id.add continuous_id).tendsto' 0 0 (add_zero 0)).eventually h_ball
  refine ⟨G.sum, -continuousMultilinearCurryFin1 ℂ V _ (P 2).curryRight,
    G.analyticOnNhd _ h_ball.self_of_nhds, ?_⟩
  filter_upwards [h_ball, h_ball₂, hP.eventually_hasSum] with z hz hz₂ hfz
  have h_term (n : ℕ) (hn : n ≠ 2) :
      (G n fun _ ↦ z + z) - (4 * (G n fun _ ↦ z) + P n fun _ ↦ z) = 0 := by
    -- The factor `2 ^ n - 4` is not zero, so it cancels against its inverse in `G n`.
    have h_ne : (2 : ℂ) ^ n ≠ 4 := mod_cast (Nat.pow_right_injective le_rfl).ne hn
    simp [← two_smul ℂ, (P _).map_smul_univ, G, fieldEq]
  -- Summing over `n`, only the term of degree `2` is left.
  have h_sum : G.sum (z + z) - (4 * G.sum z + f (0 + z)) =
      (G 2 fun _ ↦ z + z) - (4 * (G 2 fun _ ↦ z) + P 2 fun _ ↦ z) :=
    ((G.hasSum hz₂).sub (((G.hasSum hz).mul_left 4).add hfz)).unique (hasSum_single 2 h_term)
  -- The two-variable tuple `(z, z)` built by `Fin.snoc` is the constant tuple.
  have h_snoc : (Fin.snoc (Fin.snoc 0 z) z : Fin 2 → V) = fun _ ↦ z := by
    simp [funext_iff, Fin.forall_fin_two]
  rw [eq_add_of_sub_eq h_sum]
  norm_num [G, h_snoc, add_comm]

/-- For `r > 0` and `‖z‖ ≥ r`, halving `z` lowers `⌊‖z‖ / r⌋₊`. -/
lemma New.floor_norm_half_div_lt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {r : ℝ}
    (hr : 0 < r) {z : V} (hz : ¬‖z‖ < r) :
    ⌊‖(2⁻¹ : ℂ) • z‖ / r⌋₊ < ⌊‖z‖ / r⌋₊ := by
  -- Halving divides `‖z‖ / r ≥ 1` by two, which lowers its floor.
  grw [Nat.floor_lt, ← Nat.div_two_lt_floor]
  · simp [field, norm_smul]
  · simp [field, not_lt.mp hz]
  · positivity

/-- Induction by doubling: a property that holds on the ball of radius `r > 0` around `0` and
passes from `z` to `z + z` holds on the whole space. -/
lemma New.induction_on_double {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {r : ℝ}
    (hr : 0 < r) {p : V → Prop} (h_small : ∀ z : V, ‖z‖ < r → p z)
    (h_double : ∀ z : V, p z → p (z + z)) (z : V) :
    p z := by
  induction z using (measure fun z : V ↦ ⌊‖z‖ / r⌋₊).wf.induction with
  | h z ih =>
    by_cases hz : ‖z‖ < r
    · exact h_small z hz
    · simpa [← two_smul ℂ, smul_smul] using h_double _ (ih _ (floor_norm_half_div_lt hr hz))

/-- A solution of `σ (2z) = σ z ^ 4 * c z` on a ball around `0` extends to the whole space. -/
lemma New.exists_extension_double {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {r : ℝ}
    (hr : 0 < r) {σ₀ c : V → ℂ}
    (h₀ : ∀ z : V, ‖z‖ < r → ‖z + z‖ < r → σ₀ (z + z) = σ₀ z ^ 4 * c z) :
    ∃ σ : V → ℂ, (∀ z : V, ‖z‖ < r → σ z = σ₀ z) ∧ ∀ z : V, σ (z + z) = σ z ^ 4 * c z := by
  -- Outside the ball put `σ z = σ (z / 2) ^ 4 * c (z / 2)`, a recursion on `⌊‖z‖ / r⌋₊`.
  obtain ⟨σ, hσ⟩ : ∃ σ : V → ℂ, ∀ z : V,
      σ z = if ‖z‖ < r then σ₀ z else σ ((2⁻¹ : ℂ) • z) ^ 4 * c ((2⁻¹ : ℂ) • z) :=
    ⟨_, (measure fun z : V ↦ ⌊‖z‖ / r⌋₊).wf.fix_eq fun z F ↦ if hz : ‖z‖ < r then σ₀ z else
      F _ (floor_norm_half_div_lt hr hz) ^ 4 * c ((2⁻¹ : ℂ) • z)⟩
  refine ⟨σ, fun z hz ↦ by rw [hσ, ite_eq_left hz], fun z ↦ ?_⟩
  by_cases hz : ‖z + z‖ < r
  · have hz' : ‖z‖ < r := by bound [(SameRay.refl z).norm_add]
    rw [hσ (z + z), hσ z, ite_eq_left hz, ite_eq_left hz', h₀ z hz' hz]
  · rw [hσ (z + z), ite_eq_right hz]
    simp [← two_smul ℂ, smul_smul]

/-- Let `Φ z` have no zero near `z`, with `Φ 0 / Φ z` analytic at `z` and `Φ 0 0 = 1`. Let `c`
have no zero, with `c 0 = 1` and `x ↦ c x * Φ (2a) (2x) / Φ a x ^ 4` analytic at `a`.
Then the doubling equation `σ (2z) = σ z ^ 4 * exp (q z z) * c z` holds for some bilinear form `q`
and some `σ` without zero such that `σ * Φ z` is analytic at `z`. -/
private lemma New.exists_analyticAt_mul_double_eq {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] {Φ : V → V → ℂ} {c : V → ℂ} (Φ_zero : Φ 0 0 = 1)
    (Φ_ne : ∀ z : V, ∀ᶠ w : V in nhds z, Φ z w ≠ 0)
    (Φ_an : ∀ z : V, AnalyticAt ℂ (fun w : V ↦ Φ 0 w / Φ z w) z)
    (c_zero : c 0 = 1) (c_ne : ∀ z : V, c z ≠ 0)
    (c_an : ∀ a : V, AnalyticAt ℂ (fun x : V ↦ c x * Φ (a + a) (x + x) / Φ a x ^ 4) a) :
    ∃ (σ : V → ℂ) (q : V →L[ℂ] V →L[ℂ] ℂ),
      (∀ z : V, σ z ≠ 0) ∧
      (∀ z : V, AnalyticAt ℂ (σ * Φ z) z) ∧
      ∀ z : V, σ (z + z) = σ z ^ 4 * (exp (q z z) * c z) := by
  -- Near `0`, `σ` is `exp g / Φ 0`, with `g` solving the logarithm of the doubling equation.
  let f (z : V) : ℂ := log (c z * Φ 0 (z + z) / Φ 0 z ^ 4)
  have hf : AnalyticAt ℂ f 0 := by
    have h_an : AnalyticAt ℂ (fun z : V ↦ c z * Φ 0 (z + z) / Φ 0 z ^ 4) 0 := by
      simpa only [add_zero] using c_an 0
    exact h_an.clog (by simp [c_zero, Φ_zero])
  obtain ⟨g, q, hg, hg_double⟩ := exists_analyticAt_double_eq hf
  obtain ⟨r, hr, h_small⟩ : ∃ r > 0, ∀ ⦃z : V⦄, ‖z‖ < r →
      Φ 0 z ≠ 0 ∧ AnalyticAt ℂ g z ∧ g (z + z) = 4 * g z + f z + q z z :=
    nhds_zero_basis_norm_lt.eventually_iff.1 ((Φ_ne 0).and (hg.eventually_analyticAt.and hg_double))
  -- The doubling equation holds there, so `σ` extends to `V`.
  obtain ⟨σ, hσ, σ_double⟩ : ∃ σ : V → ℂ, (∀ z : V, ‖z‖ < r → σ z = exp (g z) / Φ 0 z) ∧
      ∀ z : V, σ (z + z) = σ z ^ 4 * (exp (q z z) * c z) := by
    refine exists_extension_double hr fun z hz hz₂ ↦ ?_
    obtain ⟨h_ne, -, h_double⟩ := h_small hz
    obtain ⟨h_ne₂, -⟩ := h_small hz₂
    rw [h_double]
    simp [f, exp_log, h_ne, h_ne₂, c_ne, exp_add, ← exp_nat_mul, fieldEq]
  suffices σ_spec : ∀ z : V, σ z ≠ 0 ∧ AnalyticAt ℂ (σ * Φ z) z from
    ⟨σ, q, fun z ↦ (σ_spec z).1, fun z ↦ (σ_spec z).2, σ_double⟩
  refine induction_on_double hr (fun z hz ↦ ?_) fun x ⟨h_ne, h_an⟩ ↦ ?_
  · -- Inside the ball `σ * Φ z` is `exp g` divided by the analytic function `Φ 0 / Φ z`.
    obtain ⟨h_ne, hg_an, -⟩ := h_small hz
    have h_an : AnalyticAt ℂ (fun y : V ↦ exp (g y) / (Φ 0 y / Φ z y)) z :=
      hg_an.cexp.div (Φ_an z) (div_ne_zero h_ne (Φ_ne z).self_of_nhds)
    refine ⟨by simp [hσ z hz, h_ne], h_an.congr ?_⟩
    filter_upwards [tendsto_norm (gt_mem_nhds hz)] with y (hy : ‖y‖ < r)
    rw [Pi.mul_apply, hσ y hy, div_div_eq_mul_div, div_mul_eq_mul_div]
  · -- By the doubling equation, `y ↦ (σ * Φ (2x)) (2y)` is a product of functions analytic at `x`.
    have q_an : AnalyticAt ℂ (fun y : V ↦ q y y) x :=
      (q.analyticAt_bilinear (x, x)).comp₂ analyticAt_id analyticAt_id
    have h_double : AnalyticAt ℂ (fun y : V ↦ (σ * Φ (x + x)) (y + y)) x := by
      refine (((h_an.pow 4).mul (c_an x)).mul q_an.cexp).congr ?_
      filter_upwards [Φ_ne x] with y hy
      simp [σ_double, fieldEq]
    -- Compose with the halving map.
    have h_half : AnalyticAt ℂ (fun y : V ↦ (2⁻¹ : ℂ) • y) (x + x) := by fun_prop
    refine ⟨by simp [σ_double, h_ne, c_ne], ?_⟩
    simpa [Function.comp_def, Pi.mul_def, ← two_smul ℂ, smul_smul] using
      h_double.comp_of_eq h_half (by simp [← two_smul ℂ, smul_smul])

/-- Let `W` be entire on `V × V` without zero, and let `y ↦ W (2x, 2y) / W (x, y) ^ 4` be periodic
for the lattice `L`. Then the logarithmic derivative of `W` in the second variable is linear. -/
private lemma New.exists_linear_logDeriv_of_periodic {V : Type} [FinComplexSpace V]
    {L : Submodule ℤ V} [IsFullRankLattice L] {W : V × V → ℂ} (W_ne : ∀ u : V × V, W u ≠ 0)
    (W_an : ∀ u : V × V, AnalyticAt ℂ W u)
    (h_per : ∀ x y : V, ∀ l ∈ L,
      W (x + x, y + l + (y + l)) / W (x, y + l) ^ 4 = W (x + x, y + y) / W (x, y) ^ 4) :
    ∃ T : V × V →L[ℂ] V →L[ℂ] ℂ,
      ∀ x y : V, HasFDerivAt (fun z : V ↦ W (x, z)) (W (x, y) • T (x, y)) y := by
  let P (u : V × V) : V →L[ℂ] ℂ := (W u)⁻¹ • fderiv ℂ W u ∘L .inr ℂ V V
  have hP (x y : V) : HasFDerivAt (fun z : V ↦ W (x, z)) (W (x, y) • P (x, y)) y := by
    rw [smul_inv_smul₀ (W_ne _)]
    exact (W_an _).differentiableAt.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
  have P_double : ∀ u : V × V, P (u + u) = P u + P u := by
    rintro ⟨x, y⟩
    -- `R` is a theta function for `B = 0` and `χ = 1` without zero, hence constant.
    let R (z : V) : ℂ := W (x + x, z + z) / W (x, z) ^ 4
    have W_diff : Differentiable ℂ W := fun u ↦ (W_an u).differentiableAt
    have R_diff : Differentiable ℂ R := by
      simp only [R, div_eq_mul_inv]
      fun_prop (disch := simp [W_ne])
    have R_mem : R ∈ RealComplexForm.thetaSpace (L := L) 1 0 :=
      ⟨R_diff, fun l hl z ↦ by simpa using h_per x z l hl⟩
    have h_data : IsAppellHumbert (L := L) 0 1 := by simp [isAppellHumbert_iff]
    obtain ⟨-, -, R_eq⟩ := h_data.eq_exp_of_ne_zero R_mem (by simp [R, W_ne])
    have h_const (z : V) : W (x + x, z + z) = R 0 * W (x, z) ^ 4 :=
      (div_eq_iff (pow_ne_zero 4 (W_ne _))).1 (by simpa using R_eq z)
    -- Differentiate both sides of `h_const` at `y`.
    have h_left : HasFDerivAt (fun z : V ↦ W (x + x, z + z))
        ((2 * W (x + x, y + y)) • P (x + x, y + y)) y := by
      have h_add : HasFDerivAt (fun z : V ↦ z + z) (.id ℂ V + .id ℂ V : V →L[ℂ] V) y :=
        (hasFDerivAt_id y).add (hasFDerivAt_id y)
      refine ((hP (x + x) (y + y)).comp y (f := fun z : V ↦ z + z) h_add).congr_fderiv ?_
      ext v
      simp [two_mul, add_mul]
    have h_right : HasFDerivAt (fun z : V ↦ W (x + x, z + z))
        ((2 * W (x + x, y + y)) • (P (x, y) + P (x, y))) y := by
      simp only [h_const]
      refine (((hP x y).pow 4).const_mul (R 0)).congr_fderiv ?_
      ext v
      simp
      ring
    exact smul_right_injective _ (mul_ne_zero two_ne_zero (W_ne _)) (h_left.unique h_right)
  -- A map that is differentiable at `0` and commutes with doubling is linear.
  have P_lin : ∀ u : V × V, P u = fderiv ℂ P 0 u :=
    eq_fderiv_of_double P (by fun_prop (disch := simp [W_ne])) P_double
  exact ⟨fderiv ℂ P 0, fun x y ↦ by simpa only [← P_lin] using hP x y⟩

/-- Let `W` have no zero and a linear logarithmic derivative `T` in the second variable. A function
`g` without zero, differentiable at `0`, with
`g (x + y) * g (x - y) * W (l + x, y) = g x ^ 2 * W (x, y)` has constant logarithmic derivative. -/
private lemma New.exists_const_logDeriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {W : V × V → ℂ} {T : V × V →L[ℂ] V →L[ℂ] ℂ} {g : V → ℂ} {l : V} (W_ne : ∀ u : V × V, W u ≠ 0)
    (hT : ∀ x y : V, HasFDerivAt (fun z : V ↦ W (x, z)) (W (x, y) • T (x, y)) y)
    (g_ne : ∀ z : V, g z ≠ 0) (g_diff : DifferentiableAt ℂ g 0)
    (h_eq : ∀ x y : V, g (x + y) * g (x - y) * W (l + x, y) = g x ^ 2 * W (x, y)) :
    ∃ a : V →L[ℂ] ℂ, ∀ z : V, HasFDerivAt g (g z • a) z := by
  refine ⟨(g 0)⁻¹ • fderiv ℂ g 0 - T (l, 0), fun z ↦ ?_⟩
  -- Write `z = x + x` and differentiate `y ↦ g (x + y)` at `y = x`: the logarithmic derivative is
  -- `T (x, x) - T (l + x, x) + g' 0 / g 0`.
  obtain ⟨x, rfl⟩ : ∃ x : V, z = x + x := ⟨(2⁻¹ : ℂ) • z, by simp [← two_smul ℂ, smul_smul]⟩
  refine (hasFDerivAt_comp_add_left x).1 ?_
  have g_add (y : V) : g (x + y) = g x ^ 2 * (W (x, y) * (W (l + x, y) * g (x - y))⁻¹) := by
    field_simp [W_ne, g_ne]
    linear_combination h_eq x y
  have g_sub : HasFDerivAt (fun y : V ↦ g (x - y)) (-fderiv ℂ g 0) x := by
    have g_zero : HasFDerivAt g (fderiv ℂ g 0) (x - x) := by
      simpa only [sub_self] using g_diff.hasFDerivAt
    simpa [Function.comp_def] using g_zero.comp x ((hasFDerivAt_id x).const_sub x)
  have T_add : T (l + x, x) = T (l, 0) + T (x, x) := by simp [← map_add]
  have h_inv := (hasDerivAt_inv (mul_ne_zero (W_ne _) (g_ne _))).comp_hasFDerivAt x
    ((hT (l + x) x).mul g_sub)
  simp only [g_add]
  refine (((hT x x).mul h_inv).const_mul (g x ^ 2)).congr_fderiv ?_
  ext v
  simp [T_add]
  field [W_ne, g_ne]

/-- Let `σ` have no zero, satisfy `σ (2l) = σ l ^ 4 * exp (q l l)` on `L` for a bilinear form `q`,
and have the factor of automorphy `exp (B l z) * σ l / σ 0`, with `Re B` symmetric. Then `B` and
`l ↦ σ l / σ 0 / exp (B l l / 2)` are Appell–Humbert data. -/
private lemma New.isAppellHumbert_of_double_eq {V : Type*} [FinComplexSpace V] {L : Submodule ℤ V}
    {σ : V → ℂ} {q : V →L[ℂ] V →L[ℂ] ℂ} {B : RealComplexForm V} (σ_ne : ∀ z : V, σ z ≠ 0)
    (σ_double : ∀ l ∈ L, σ (l + l) = σ l ^ 4 * exp (q l l))
    (σ_add : ∀ l ∈ L, ∀ z : V, σ (z + l) = σ z * exp (B l z) * σ l / σ 0)
    (hB_symm : ∀ u v : V, (B u v).re = (B v u).re) :
    IsAppellHumbert (L := L) B fun l : V ↦ σ l / σ 0 / exp (B l l / 2) := by
  have exp_half (z : ℂ) : exp z = exp (z / 2) ^ 2 := by rw [sq, ← exp_add, add_halves]
  refine ⟨hB_symm, fun l hl ↦ ?_, fun l _ m hm ↦ ?_⟩
  · -- Compare the two formulas for `σ (2m)` at `m = 0`, `2l` and `l`, and eliminate `exp (q l l)`.
    have h_sq (m : V) (hm : m ∈ L) : σ m ^ 2 * σ 0 * exp (q m m) = exp (B m m) := by
      have h_two : σ m ^ 4 * exp (q m m) = σ m * exp (B m m) * σ m / σ 0 :=
        (σ_double m hm).symm.trans (σ_add m hm m)
      field_simp [σ_ne] at h_two
      linear_combination h_two
    have h_zero : σ 0 ^ 3 = 1 := by simpa [pow_succ] using h_sq 0 L.zero_mem
    have h_double : σ l ^ 8 * σ 0 * exp (q l l) ^ 6 = exp (B l l) ^ 4 := by
      have h_sq_double := h_sq (l + l) (L.add_mem hl hl)
      simp only [σ_double l hl, map_add, _root_.add_apply, exp_add] at h_sq_double
      linear_combination h_sq_double
    have h_four : σ l ^ 4 = exp (B l l) ^ 2 * σ 0 ^ 4 := by
      refine mul_right_cancel₀ (pow_ne_zero 4 (exp_ne_zero (B l l))) ?_
      calc σ l ^ 4 * exp (B l l) ^ 4
          = σ l ^ 4 * (σ l ^ 8 * σ 0 * exp (q l l) ^ 6) * (σ 0 ^ 3) ^ 3 := by
            rw [h_double, h_zero, one_pow, mul_one]
        _ = (σ l ^ 2 * σ 0 * exp (q l l)) ^ 6 * σ 0 ^ 4 := by ring
        _ = exp (B l l) ^ 2 * σ 0 ^ 4 * exp (B l l) ^ 4 := by
            rw [h_sq l hl]
            ring
    refine norm_eq_one_of_pow_eq_one ?_ four_ne_zero
    rw [div_pow, div_pow, h_four, exp_half (B l l)]
    field_simp [σ_ne]
  · have h_form : Real.pi * I * B.riemannForm m l = (B m l - B l m) / 2 := by
      apply Complex.ext
      · simp [hB_symm m l]
      · simp [riemannForm_def, -ofReal_div, fieldEq]
    rw [h_form, σ_add m hm l, exp_half (B m l)]
    simp only [map_add, _root_.add_apply, add_div, sub_div, exp_add, exp_sub]
    field_simp [σ_ne]

/-- If theta functions of type (B, χ) are homogeneous coordinates of a projective embedding of a
uniformised group, then the Riemann form of B is positive. -/
private lemma New.Uniformisation.isPosRiemann_of_hasThetaCoords
    {A : Over (AlgebraicGeometry.Spec (CommRingCat.of ℂ))} [AddObj A] {ι V : Type} [Finite ι]
    [FinComplexSpace V] (u : Uniformisation (O := ℂ) A V) {N : LineBundle A.left ι}
    (hN : IsProjEmbedding (ι := ι) N A.hom) {B : ThetaTori.LatticeForm u.lattice} {χ : V → ℂ}
    {θ : V → ι → ℂ} (h_theta : HasThetaCoords u.lattice (atGeneric u.expMap) N B χ θ) :
    IsPosRiemann B := by
  refine ⟨fun v hv ↦ not_le.1 fun h_le ↦ hv ?_⟩
  -- If the Riemann form is not positive at `v`, then `θ (t • v)` is a multiple of `θ 0`. As `N`
  -- separates points, `u.expMap` is constant on the line through `v`, so `v = 0`.
  have h_line (t : ℂ) : u.expMap (t • v) = u.expMap 0 := by
    have h_mult : θ (t • v) = (t * t * B v v / 2).exp • θ 0 := funext fun j ↦
      h_theta.isAppellHumbert.apply_smul_of_nonpos (hf := h_theta.mem_thetaSpace j) v h_le t
    exact OverMorphism.ext (hN.eq_of_isHomogeneousCoords (by simp)
      (by simpa only [h_mult, atGeneric_eq] using h_theta.hasFieldCoords (t • v))
      ((h_theta.hasFieldCoords 0).smul (exp_ne_zero _).isUnit) (N.exists_landsIn _))
  exact ContinuousLinearMap.toSpanSingleton_inj.1
    (u.linear_ext fun t : ℂ ↦ by simpa using h_line t)

/-- Let `e : V → G` be additive and zero on the lattice `L`. Let `Φ x x = 1`, with `Φ (e z) ∘ e` not
zero near `z` and `(Φ (e 0) / Φ (e z)) ∘ e` analytic at `z`. Let `C` have no zero, with `C 0 0 = 1`,
and let `C (e x) (e y)`, times `Φ` at `x - y` and `x + y` over `Φ²` at `x` and `y`, be analytic at
each `(a, b)`. Then some `σ` without zero, with `σ * Φ (e z) ∘ e` analytic at `z`, has a factor
of automorphy given by Appell–Humbert data. -/
private lemma New.exists_isAppellHumbert_of_analyticAt {V : Type} [FinComplexSpace V]
    {L : Submodule ℤ V} [IsFullRankLattice L] {G : Type*} [AddGroup G] {e : V →+ G}
    (hL : ∀ l ∈ L, e l = 0) {Φ C : G → G → ℂ} (Φ_self : ∀ x : G, Φ x x = 1)
    (Φ_ne : ∀ z : V, ∀ᶠ w : V in nhds z, Φ (e z) (e w) ≠ 0)
    (Φ_an : ∀ z : V, AnalyticAt ℂ (fun w : V ↦ Φ (e 0) (e w) / Φ (e z) (e w)) z)
    (C_zero : C 0 0 = 1) (C_ne : ∀ x y : G, C x y ≠ 0)
    (C_an : ∀ a b : V, AnalyticAt ℂ (fun ((x, y) : V × V) ↦
      C (e x) (e y) * Φ (e (a - b)) (e (x - y)) * Φ (e (a + b)) (e (x + y)) /
        (Φ (e a) (e x) * Φ (e b) (e y)) ^ 2) (a, b)) :
    ∃ (σ : V → ℂ) (B : RealComplexForm V),
      (∀ z : V, σ z ≠ 0) ∧
      (∀ z : V, AnalyticAt ℂ (fun w : V ↦ σ w * Φ (e z) (e w)) z) ∧
      (∀ l ∈ L, ∀ z : V, σ (z + l) = σ z * exp (B l z) * σ l / σ 0) ∧
      IsAppellHumbert (L := L) B fun l : V ↦ σ l / σ 0 / exp (B l l / 2) := by
  -- The diagonal of `C_an` gives `σ`, a solution of the doubling equation.
  obtain ⟨σ, q, σ_ne, σ_an, σ_double⟩ : ∃ (σ : V → ℂ) (q : V →L[ℂ] V →L[ℂ] ℂ),
      (∀ z : V, σ z ≠ 0) ∧ (∀ z : V, AnalyticAt ℂ (fun w : V ↦ σ w * Φ (e z) (e w)) z) ∧
      ∀ z : V, σ (z + z) = σ z ^ 4 * (exp (q z z) * C (e z) (e z)) := by
    refine exists_analyticAt_mul_double_eq (Φ := fun z w : V ↦ Φ (e z) (e w)) (Φ_self _) Φ_ne Φ_an
      (by simp [C_zero]) (fun _ ↦ C_ne _ _) fun a ↦ ?_
    refine ((C_an a a).comp₂ analyticAt_id analyticAt_id).congr (.of_forall fun x ↦ ?_)
    simp only [id, sub_self, Φ_self]
    ring
  -- `W` compares `C` with the trivialisation given by `σ`; it is entire and has no zero.
  let W : V × V → ℂ := fun (x, y) ↦ (σ x * σ y) ^ 2 * C (e x) (e y) / σ (x - y) / σ (x + y)
  have W_ne (u : V × V) : W u ≠ 0 := by simp [W, σ_ne, C_ne]
  have W_an : ∀ u : V × V, AnalyticAt ℂ W u := by
    rintro ⟨a, b⟩
    -- `W` is the function of `C_an` times `(σ * Φ)²` at `x` and `y`, divided by `σ * Φ` at `x - y`
    -- and `x + y`: the factors `Φ`, which are not zero near `(a, b)`, cancel.
    have h_num : AnalyticAt ℂ
        (fun (x, y) ↦ (σ x * Φ (e a) (e x) * (σ y * Φ (e b) (e y))) ^ 2) (a, b) :=
      (((σ_an a).comp_of_eq analyticAt_fst rfl).mul ((σ_an b).comp_of_eq analyticAt_snd rfl)).pow 2
    have h_den : AnalyticAt ℂ (fun (x, y) ↦ σ (x - y) * Φ (e (a - b)) (e (x - y)) *
        (σ (x + y) * Φ (e (a + b)) (e (x + y)))) (a, b) :=
      ((σ_an (a - b)).comp_of_eq (analyticAt_fst.sub analyticAt_snd) rfl).mul
        ((σ_an (a + b)).comp_of_eq (analyticAt_fst.add analyticAt_snd) rfl)
    refine (((C_an a b).mul h_num).div h_den (by simp [σ_ne, Φ_self])).congr ?_
    filter_upwards [(C_an a b).continuousAt.eventually_ne (y := 0) (by simp [Φ_self, C_ne])]
    simp +contextual [W, fieldEq]
  -- By `σ_double` and the parallelogram identity for `q`, the quotient `W (2x, 2y) / W (x, y) ^ 4`
  -- depends only on `e x` and `e y`.
  obtain ⟨T, hT⟩ : ∃ T : V × V →L[ℂ] V →L[ℂ] ℂ,
      ∀ x y : V, HasFDerivAt (fun z : V ↦ W (x, z)) (W (x, y) • T (x, y)) y := by
    refine exists_linear_logDeriv_of_periodic (L := L) W_ne W_an fun x y l hl ↦ ?_
    simp [W, add_add_add_comm x x, add_sub_add_comm, σ_double, hL l hl, exp_add, exp_sub]
    field [σ_ne, C_ne]
  -- The factor of automorphy `σ (l + ·) / σ` has constant logarithmic derivative.
  have h_log (l : L) : ∃ a : V →L[ℂ] ℂ, ∀ z : V,
      HasFDerivAt (fun w : V ↦ σ (l + w) / σ w) ((σ (l + z) / σ z) • a) z := by
    obtain ⟨l, hl⟩ := l
    -- The factors `Φ` cancel in the quotient, so it is analytic.
    have h_an : AnalyticAt ℂ (fun w : V ↦ σ (l + w) / σ w) 0 :=
      (((σ_an (l + 0)).comp (by fun_prop)).div (σ_an 0) (by simp [σ_ne, Φ_self])).congr
        ((Φ_ne 0).mono (by simp +contextual [hL l hl, mul_div_mul_right]))
    refine exists_const_logDeriv (l := l) W_ne hT (by simp [σ_ne]) h_an.differentiableAt
      fun x y ↦ ?_
    simp [W, add_assoc, add_sub_assoc, hL l hl]
    field [σ_ne]
  obtain ⟨B, σ_add, hB_symm⟩ := exists_factor_of_automorphy (L := L) σ_ne h_log
  have σ_double_mem (l : V) (hl : l ∈ L) : σ (l + l) = σ l ^ 4 * exp (q l l) := by
    rw [σ_double, hL l hl, C_zero, mul_one]
  exact ⟨σ, B, σ_ne, σ_an, σ_add, isAppellHumbert_of_double_eq σ_ne σ_double_mem σ_add hB_symm⟩

/-- The existence half of the Appell–Humbert theorem. Let e : V → A(ℂ) be a uniformisation with
kernel L, and N a linear system that embeds A, whose class satisfies the parallelogram law
`New.Pic.ParallelogramLaw`. Then there are Appell–Humbert data (L, B, χ) with positive Riemann form
and theta functions θ_i of type (B, χ) such that θ(z) is a vector of homogeneous coordinates of e(z)
for N, for all z in V. -/
lemma New.Uniformisation.appell_humbert {A : Over (AlgebraicGeometry.Spec (CommRingCat.of ℂ))}
    [AddObj A] {ι V : Type} [Finite ι] [FinComplexSpace V] (u : Uniformisation (O := ℂ) A V)
    {N : LineBundle A.left ι} (hN : IsProjEmbedding (ι := ι) N A.hom)
    (h_par : N.picClass.ParallelogramLaw) :
    ∃ (B : ThetaTori.LatticeForm u.lattice) (χ : V → ℂ) (θ : V → ι → ℂ),
      HasThetaCoords u.lattice (atGeneric u.expMap) N B χ θ ∧ IsPosRiemann B := by
  -- The parallelogram law trivialises a bundle `X` on `A × A`, with values `C`. From it we build
  -- a trivialisation `σ` of the pullback of `N` to `V` whose factor of automorphy is given by
  -- Appell–Humbert data, and let `θ z` be `σ z` times the homogeneous coordinates of `e z` in the
  -- chart `J (e z)`. Positivity of the Riemann form follows for any theta coordinates.
  suffices h_coords : ∃ (B : ThetaTori.LatticeForm u.lattice) (χ : V → ℂ) (θ : V → ι → ℂ),
      HasThetaCoords u.lattice (atGeneric u.expMap) N B χ θ by
    obtain ⟨B, χ, θ, h_theta⟩ := h_coords
    exact ⟨B, χ, θ, h_theta, u.isPosRiemann_of_hasThetaCoords hN h_theta⟩
  obtain ⟨e, L, -, hL, h_imm, -⟩ := u
  dsimp at h_imm ⊢
  replace hL : ∀ l ∈ L, e l = 0 := fun l ↦ (hL l).1
  have h_hol (z : V) : HolomorphicAt (fun x : V ↦ (e x).1) z := (h_imm z).1
  -- `X = (p^* N ⊗ s^* N)² ⊗ ((p + s)^* N ⊗ (p - s)^* N)⁻¹` for the two projections `p`, `s`; by the
  -- parallelogram law it has a frame `w`, a section without zero.
  let p := fst A A
  let s := snd A A
  let X := (((N.pull p.1).mul (N.pull s.1)).pow 2).mul
    ((N.pull (p + s).1).mul (N.pull (p - s).1)).inv
  have ⟨w, (hw : X.IsFrame w)⟩ := picClass_eq_iff.1 (by simpa using! (h_par p s).symm)
  -- A chart `J x` of `N` at each point; `Φ x y` changes from the chart at `y` to the chart at `x`.
  have h_cover (x : ComplexPoint A) : ∃ i : ι, LandsIn x.1 (N.opens i) := N.exists_landsIn x.1
  choose J hJ using h_cover
  have h_lifts {x : ComplexPoint A} :
      N.IsHomogeneousCoords x.1 fun j ↦ N.transition (J x) j (.of ℂ) x.1 :=
    hN.isLinearSystem.isHomogeneousCoords_transition (hJ x)
  have h_in {x y : ComplexPoint A} :
      LandsIn (lift x y).1 (X.opens (fun _ ↦ (J x, J y), J (x + y), J (x - y))) := by
    simp +zetaDelta [AddMonObj.comp_add, AddGrpObj.comp_sub, *, pow, ← comp_left, -lift_left,
      -fst_left, -snd_left]
  let Φ (x y : ComplexPoint A) : ℂ := N.transition (J y) (J x) (.of ℂ) y.1
  have Φ_self (x : ComplexPoint A) : Φ x x = 1 := N.transition_self _ _ _ (hJ _)
  have Φ_ne (z : V) : ∀ᶠ w : V in nhds z, Φ (e z) (e w) ≠ 0 :=
    (h_hol z (isRegularOn_ofSection 0) (hJ _)).1.mono (by simp [Φ, h_lifts _])
  have h_coord (j : ι) (z : V) :
      AnalyticAt ℂ (fun w : V ↦ N.transition (J (e w)) j (.of ℂ) (e w).1 / Φ (e z) (e w)) z :=
    (h_hol z (hN.isLinearSystem.isRegularOn_transition ..) (hJ _)).2.congr
      ((Φ_ne z).mono fun _ h ↦ ((h_lifts _).2 j h.isUnit).trans (by simp [Φ, fieldEq]))
  -- `C x y` is the value of the frame at `(x, y)`; in the fixed charts at `(a, b)` it is analytic.
  choose C hC using fun x y : ComplexPoint A ↦ hw.2 _ _ _ (h_in (x := x) (y := y))
  have C_an (a b : V) : AnalyticAt ℂ (fun (x, y) ↦
      C (e x) (e y) / C 0 0 * Φ (e (a - b)) (e (x - y)) * Φ (e (a + b)) (e (x + y)) /
        (Φ (e a) (e x) * Φ (e b) (e y)) ^ 2) (a, b) := by
    have h_pair : HolomorphicAt (fun u : V × V ↦ (lift (e u.1) (e u.2)).1) (a, b) :=
      ((h_hol _).comp analyticAt_fst).lift hN ((h_hol _).comp analyticAt_snd)
    obtain ⟨h_near, h_an⟩ := h_pair (hw.1.1 _) h_in
    refine (h_an.div_const (c := C 0 0)).congr (h_near.mono fun z hz ↦ ?_)
    refine (congrArg (· / (C 0 0 : ℂ)) (hw.1.2 _ _ _ _ hz h_in)).trans ?_
    -- the change of charts for `X` is the stated quotient of the changes of charts `Φ` for `N`
    have hz_charts :
        (LandsIn (e z.1).1 (N.opens (J (e a))) ∧ LandsIn (e z.2).1 (N.opens (J (e b)))) ∧
        LandsIn (e z.1 + e z.2).1 (N.opens (J (e a + e b))) ∧
        LandsIn (e z.1 - e z.2).1 (N.opens (J (e a - e b))) := by
      simpa +zetaDelta [AddMonObj.comp_add, AddGrpObj.comp_sub, pow, ← comp_left, -lift_left,
        -fst_left, -snd_left] using hz
    simp +zetaDelta [eq_inv_of_mul_eq_one_left
        ((N.transition_trans _ _ _ _ _ _ (hJ _) _).trans (N.transition_self ..)),
      AddMonObj.comp_add, AddGrpObj.comp_sub, *, pow, ← comp_left, fieldEq, -lift_left, -fst_left,
      -snd_left]
  -- This gives a trivialisation `σ` whose factor of automorphy comes from Appell–Humbert data.
  obtain ⟨σ, B, σ_ne, σ_an, σ_add, h_data⟩ :=
    exists_isAppellHumbert_of_analyticAt (C := fun x y ↦ C x y / C 0 0) hL Φ_self Φ_ne
      (h_coord (J (e 0))) (by simp) (by simp) C_an
  let χ (l : V) : ℂ := σ l / σ 0 / exp (B l l / 2)
  let θ (z : V) : ι → ℂ := σ z • fun j ↦ N.transition (J (e z)) j (.of ℂ) (e z).1
  have θ_mem (j : ι) : (θ · j) ∈ RealComplexForm.thetaSpace (L := L) χ B := by
    refine ⟨fun z ↦ (((σ_an z).mul (h_coord j z)).congr ((Φ_ne z).mono ?_)).differentiableAt,
      fun l hl z ↦ ?_⟩
    · simp +contextual [θ, fieldEq]
    · simp [θ, χ, σ_add l hl, hL l hl, exp_add, fieldEq]
  exact ⟨B, χ, θ, hN.isLinearSystem, h_data, θ_mem, fun z ↦ h_lifts.smul (σ_ne z).isUnit⟩
