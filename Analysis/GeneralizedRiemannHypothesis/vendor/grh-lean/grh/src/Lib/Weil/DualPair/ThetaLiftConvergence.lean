import Lib.Adelic.AutomorphicForms.RealConvolution
import Lib.DiscreteSeries.CuspKernel
import Lib.Weil.DualPair.WeilAction

/-!
# Growth of theta kernels and convergence of theta lifts

This file proves growth estimates for theta kernels `(g, h) ↦ θ (ω (g, h) φ)` on the product of
the adelic groups of two spaces `S` and `T`, for a representation `ω`, a functional `θ` and a
vector `φ`. Using reduction theory, it first bounds the norm of `ω (g₀, γ g)`, for fixed `g₀` and
a suitable rational translate `γ g`, by a power of the height `New.Space.height` of `g`. The lift
`New.Space.lift` of a function `y` integrates the kernel against `y g` over `[S] = Γ_S \ G_S`.
For `y` of rapid decay the lift converges, the lifts from `S` and from `T` are transposes of each
other, and the adjoint of the lift for the Petersson products is the descent.

## Main definitions and results

* `New.ThetaKernel.moderate_growth`: the kernel grows at most like a power of the heights
  `New.Space.height`.
* `New.ThetaKernel.integrable_theta_mul`, `New.ThetaKernel.liftBilin`,
  `New.ThetaKernel.exists_clm_lift`: for `y` of rapid decay (`New.Space.rapidFunctions`) the lift
  converges, is bilinear in `φ` and `y`, and is continuous in `φ`.
* `New.ThetaKernel.integral_mul_lift_eq_integral_mul_lift_swap`,
  `New.ThetaKernel.petersson_lift_eq_petersson_descent`: the lifts from `S` and from `T` are
  transposes of each other, and the descent is the adjoint of the lift.

Notions from other files:
* `New.G`: The adelic unitary group G = G_∞ × G_f for signs s at the infinite places and the
  identity matrix at the finite places.
* `New.Space`: A hermitian space with a point: a matrix J over E and x in GL_n(𝔸) with xᴴJx equal to
  diag(s) at the infinite places and 1 at the finite places; Γ = x⁻¹U(J)(E)x.
* `New.Space.IsAutomorphic`, `New.Space.IsRapid`: a function F is automorphic if it is continuous,
  left Γ-invariant and right invariant under an open subgroup of G_f; it is rapid if |F(g)|·ht(g)^B
  is bounded for every B, and moderate (`New.Space.IsModerate`) if |F(g)| ≤ C·ht(g)^A for some C and
  A.

## Relation to the literature

Known; see `Lib.Weil.DualPair.KernelDecay` for sources.
-/

noncomputable section

/-!
## Bounds on the operators of a theta kernel

Let `Θ` be a theta kernel (`New.ThetaKernel`) for spaces `S` and `V`, acting by ω on a Banach space.
-/

namespace New.ThetaKernel

open Matrix Space G Norms.L2Operator Prod
open NumberField (InfinitePlace)
open DiscreteSeries (exists_conj_mem_dilationGroup)

variable {E n n' : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {s : n → ℤˣ} {t : n' → ℤˣ}
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {S : Space E n s} {V : Space E n' t} (Θ : ThetaKernel X S V)

/-- The operator norms ‖ω(k)‖ of a theta kernel on a Banach space are bounded for k in a compact
subset of the product of the two adelic groups (Banach–Steinhaus). -/
lemma exists_norm_le_of_isCompact {K : Set (G E s × G E t)} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ k ∈ K, ‖Θ.ω k‖ ≤ C := by
  -- Each orbit map is continuous, hence bounded on `K`; then apply the Banach–Steinhaus theorem.
  have orbit_bdd (φ : X) : ∃ C : ℝ, ∀ k : K, ‖Θ.ω k φ‖ ≤ C := by
    simpa only [Subtype.forall] using
      hK.exists_bound_of_continuousOn (f := fun k ↦ Θ.ω k φ) (by fun_prop)
  simpa only [Subtype.forall] using banach_steinhaus orbit_bdd

/-- One step of reduction: for `g` an adelic point of the unitary group of `V`, there is an
archimedean point `y` with operator norm at most `2` at every infinite place such that the height of
`g (y,1)⁻¹` is at most half the height of `g`, or at most `2`. Height is 1/λ, where λ is the first
minimum, cut off at 1, of `V` moved by `g`. -/
theorem _root_.New.Space.exists_height_mul_inv_le_max (V : Space E n' t) (g : G E t) :
    ∃ y : GInf E t, (∀ τ : InfinitePlace E, ‖((y τ : GL n' ℂ) : Matrix n' n' ℂ)‖ ≤ 2) ∧
      V.height (g * (y, 1)⁻¹) ≤ max (V.height g / 2) 2 := by
  -- The point `y` doubles the lattice vectors of length below `1` and at most halves the others.
  let W : Space E n' t := V.move g
  -- The lattice vectors of length below `1` are orthogonal to one another, so they span an
  -- isotropic space.
  let A (w : InfinitePlace E) : Matrix n' {ξ ∈ W.baseLattice | ‖W.archCoords ξ‖ < 1} ℂ :=
    fun i ξ ↦ W.archCoords ξ (w, i)
  have h_iso (w : InfinitePlace E) : (A w)ᴴ * (signMatrix t * A w) = 0 := by
    ext ⟨ξ, hξ, hξ_short⟩ ⟨η, hη, hη_short⟩
    refine (stdForm_dotProduct_fst (W.vecAtPoint ξ) (W.vecAtPoint η) w).symm.trans ?_
    rw [stdForm_vecAtPoint,
      form_eq_zero_of_norm_mul_lt_one hξ hη (by grw [hη_short.le, mul_one, hξ_short])]
    simp
  -- `y w` is within distance `1` of `1` and is a dilation along this space by the factor `2`.
  have h_dilation (w : InfinitePlace E) : ∃ z : USign t,
      dist (z : Matrix n' n' ℂ) 1 ≤ 1 ∧ ((z : GL n' ℂ) : Matrix n' n' ℂ) * A w = (2 : ℂ) • A w := by
    obtain ⟨z, hz_near, hz_dil, -⟩ := exists_conj_mem_dilationGroup (h_iso w) 1 one_pos
    exact ⟨z, hz_near, by simpa [one_add_one_eq_two] using hz_dil⟩
  choose y y_near y_dil using h_dilation
  have y_norm (w : InfinitePlace E) : ‖((y w : GL n' ℂ) : Matrix n' n' ℂ)‖ ≤ 2 := by
    grw [norm_le_norm_add_const_of_dist_le (y_near w), (IsStarProjection.one _).norm_le,
      one_add_one_eq_two]
  -- At `g y⁻¹` the lattice is no larger, and a vector has at least half its length at `g`, and
  -- twice it if that is below `1`.
  let W' : Space E n' t := V.move (g * (y⁻¹, 1))
  have h_half (ξ : n' → E) : (ξ ∈ W'.baseLattice → ξ ∈ W.baseLattice) ∧
      ‖W.archCoords ξ‖ ≤ 2 * ‖W'.archCoords ξ‖ := by
    -- The coordinates of `ξ` at `g` are those at `g y⁻¹` moved by `(y⁻¹, 1)`, which has norm at
    -- most `2` at every infinite place and is the identity at the finite places.
    have h_norm (w : InfinitePlace E) : ‖(adeleMatrix (y⁻¹, 1)).map fun a : 𝔸 E ↦ a.1 w‖ ≤ 2 :=
      (U.norm_inv _).trans_le (y_norm w)
    have h_crd : W.vecAtPoint ξ = (1 : ℕ) • adeleMatrix (y⁻¹, 1) *ᵥ W'.vecAtPoint ξ := by
      -- `-inv_mk`: with it simp expands inverses of pairs, such as `(y⁻¹, 1)⁻¹` into `(y, 1)`.
      simp [W, W', -inv_mk, vecAtPoint_move, adeleMatrix]
    simpa [ite_mem, Matrix.one_apply] using
      W.mem_and_norm_le_of_vecAtPoint ξ W' ξ (adeleMatrix (y⁻¹, 1)) 1 h_norm h_crd
  have h_double (ξ : n' → E) (hξ : ξ ∈ W.baseLattice) (hξ_short : ‖W.archCoords ξ‖ < 1) :
      W'.archCoords ξ = (2 : ℂ) • W.archCoords ξ := by
    have h_vec : W'.vecAtPoint ξ = adeleMatrix ((y, 1) : G E t) *ᵥ W.vecAtPoint ξ := by
      simp [W, W', vecAtPoint_move, adeleMatrix_mul]
    ext ⟨w, i⟩
    calc W'.archCoords ξ (w, i) = evalInf w ((adeleMatrix ((y, 1) : G E t) *ᵥ W.vecAtPoint ξ) i) :=
        congrArg (fun v : n' → 𝔸 E ↦ evalInf w (v i)) h_vec
      _ = (((y w : GL n' ℂ) : Matrix n' n' ℂ) * A w) i ⟨ξ, hξ, hξ_short⟩ :=
        (evalInf w).map_mulVec _ _ i
      _ = ((2 : ℂ) • W.archCoords ξ) (w, i) := by
        rw [y_dil]
        rfl
  have h_min : min (2 * W.firstMinimum) 2⁻¹ ≤ W'.firstMinimum := by
    refine le_firstMinimum_iff.mpr ⟨min_le_of_right_le (by norm_num), fun ξ hξ hξ_ne ↦ ?_⟩
    obtain ⟨h_lattice, h_le⟩ := h_half ξ
    by_cases hξ_short : ‖W.archCoords ξ‖ < 1
    · -- A short vector has twice its length at `g y⁻¹`.
      have h_norm_eq : ‖W'.archCoords ξ‖ = 2 * ‖W.archCoords ξ‖ := by
        simp [h_double ξ (h_lattice hξ) hξ_short, norm_smul]
      exact min_le_of_left_le (by linarith [firstMinimum_le (h_lattice hξ) hξ_ne])
    · -- A long vector keeps at least half its length.
      exact min_le_of_right_le (by linarith)
  refine ⟨y, y_norm, ?_⟩
  calc V.height (g * (y, 1)⁻¹) = W'.firstMinimum⁻¹ := by simp [height, W']
    _ ≤ (min (2 * W.firstMinimum) 2⁻¹)⁻¹ :=
      inv_anti₀ (lt_min (mul_pos two_pos firstMinimum_pos) (by norm_num)) h_min
    _ ≤ max (V.height g / 2) 2 := by
      rcases min_choice (2 * W.firstMinimum) 2⁻¹ with h_eq | h_eq <;>
        simp [h_eq, height, W, div_eq_mul_inv]

/-- Reduction theory with a height bound: there is a compact set `Ω` such that every `g` has a
rational `γ` and a real point `x` with `γ g x⁻¹ ∈ Ω` and operator norm at most the height of `g`
at every infinite place. Here `x` is the product of a list `l` of real points of norm at most `2`,
and `2 ^ l.length` is at most the height of `g`. -/
theorem _root_.New.Space.exists_reduction_norm_le_height (V : Space E n' t) :
    ∃ Ω : Set (G E t), IsCompact Ω ∧ ∀ g : G E t, ∃ γ ∈ V.Γ, ∃ l : List (GInf E t),
      γ * g * (l.prod, 1)⁻¹ ∈ Ω ∧
      (∀ τ : InfinitePlace E, ‖((l.prod τ : GL n' ℂ) : Matrix n' n' ℂ)‖ ≤ V.height g) ∧
      2 ^ l.length ≤ V.height g ∧
      ∀ y ∈ l, ∀ τ : InfinitePlace E, ‖((y τ : GL n' ℂ) : Matrix n' n' ℂ)‖ ≤ 2 := by
  -- Let `2 ^ k ≤ height g < 2 ^ (k + 1)`. After `k` halving steps the height is at most `2`, and
  -- Mahler's criterion applies.
  obtain ⟨Ω, hΩ, h_mahler⟩ := V.mahler_criterion 2
  -- By induction on `k`: `g` of height at most `2 ^ (k + 1)` is reduced by `k` steps.
  have h_reduce (k : ℕ) (g : G E t) (hg : V.height g ≤ 2 ^ (k + 1)) :
      ∃ γ ∈ V.Γ, ∃ l : List (GInf E t), l.length = k ∧ γ * g * (l.prod, 1)⁻¹ ∈ Ω ∧
        (∀ τ : InfinitePlace E, ‖((l.prod τ : GL n' ℂ) : Matrix n' n' ℂ)‖ ≤ 2 ^ k) ∧
        ∀ y ∈ l, ∀ τ : InfinitePlace E, ‖((y τ : GL n' ℂ) : Matrix n' n' ℂ)‖ ≤ 2 := by
    induction k generalizing g with
    | zero =>
      obtain ⟨γ, hγ, h_mem⟩ := h_mahler g (by simpa using hg)
      refine ⟨γ, hγ, [], rfl, by simpa [mul_def] using h_mem, fun τ ↦ ?_, by simp⟩
      simpa using (IsStarProjection.one _).norm_le
    | succ k ih =>
      -- One halving step by `y`, then the induction hypothesis at `g y⁻¹`.
      obtain ⟨y, hy_norm, hy_height⟩ := V.exists_height_mul_inv_le_max g
      have h_height : V.height (g * (y, 1)⁻¹) ≤ 2 ^ (k + 1) :=
        hy_height.trans (max_le (by linarith [pow_succ (2 : ℝ) (k + 1)])
          (le_self_pow₀ one_le_two k.succ_ne_zero))
      obtain ⟨γ, hγ, l, rfl, h_mem, hl_norm, hl_factors⟩ := ih _ h_height
      refine ⟨γ, hγ, l ++ [y], by simp, by simpa [mul_assoc] using h_mem, fun τ ↦ ?_, ?_⟩
      · simpa [pow_succ] using norm_mul_le_of_le (hl_norm τ) (hy_norm τ)
      · simpa [or_imp, forall_and] using ⟨hl_factors, hy_norm⟩
  refine ⟨Ω, hΩ, fun g ↦ ?_⟩
  obtain ⟨k, h_le, h_lt⟩ := exists_nat_pow_near (one_le_height g) one_lt_two
  obtain ⟨γ, hγ, l, rfl, h_mem, hl_norm, hl_factors⟩ := h_reduce k g h_lt.le
  exact ⟨γ, hγ, l, h_mem, fun τ ↦ (hl_norm τ).trans h_le, h_le, hl_factors⟩

/-- Fix `g₀` in the group of `S`. For every large exponent `a`, each `g` in the group of `V` has a
rational translate `γ g` such that the operator `ω (g₀, γ g)` has norm at most
`(2 * height g) ^ a`. -/
theorem eventually_exists_norm_omega_le_mul_height_pow (g₀ : G E s) :
    ∀ᶠ a : ℕ in Filter.atTop, ∀ g : G E t, ∃ γ ∈ V.Γ,
      ‖Θ.ω (g₀, γ * g)‖ ≤ 2 ^ a * V.height g ^ a := by
  -- Write `γ g = z x` with `z` in a compact set and `x` a product of `k` real points of norm at
  -- most `2`, where `2 ^ k ≤ height g`. Each of the `k + 1` factors acts with norm at most `2 ^ a`.
  obtain ⟨Ω, hΩ, h_reduce⟩ := V.exists_reduction_norm_le_height
  -- The real points `(x, 1)` with `‖x_τ‖ ≤ 2` at every infinite place.
  let B : Set (G E t) := (Set.univ.pi fun _ : InfinitePlace E ↦
    {y : USign t | ‖((y : GL n' ℂ) : Matrix n' n' ℂ)‖ ≤ 2}) ×ˢ {1}
  have hB : IsCompact B :=
    (isCompact_univ_pi fun _ ↦ isCompact_U_norm_le 2).prod isCompact_singleton
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ ({g₀, 1} : Set (G E s)) ×ˢ (Ω ∪ B), ‖Θ.ω x‖ ≤ C :=
    Θ.exists_norm_le_of_isCompact ((isCompact_singleton.insert g₀).prod (hΩ.union hB))
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_ge_atTop C] with a ha g
  -- Each factor acts with norm at most `2 ^ a`, by induction on the list.
  have h_prod {z : G E t} (hz : z ∈ Ω) (l : List (GInf E t))
      (hl : ∀ y ∈ l, ∀ τ : InfinitePlace E, ‖((y τ : GL n' ℂ) : Matrix n' n' ℂ)‖ ≤ 2) :
      ‖Θ.ω (g₀, z * (l.prod, 1))‖ ≤ 2 ^ a * (2 ^ a) ^ l.length := by
    induction l using List.reverseRecOn with
    | nil => simpa [mul_def] using (hC (g₀, z) (by simp [hz])).trans ha
    | append_singleton l y ih =>
      have hy : ‖Θ.ω (1, y, 1)‖ ≤ 2 ^ a := (hC (1, y, 1) (by simp [B, hl y (by simp)])).trans ha
      calc ‖Θ.ω (g₀, z * ((l ++ [y]).prod, 1))‖
          = ‖Θ.ω (g₀, z * (l.prod, 1)) * Θ.ω (1, y, 1)‖ := by simp [mul_def, mul_assoc, ← map_mul]
        _ ≤ 2 ^ a * (2 ^ a) ^ l.length * 2 ^ a := by
            grw [norm_mul_le, ih fun x hx ↦ hl x (by simp [hx]), hy]
        _ = 2 ^ a * (2 ^ a) ^ (l ++ [y]).length := by simp [pow_succ, mul_assoc]
  obtain ⟨γ, hγ, l, h_mem, -, h_length, h_factors⟩ := h_reduce g
  have h_le : ‖Θ.ω (g₀, γ * g)‖ ≤ 2 ^ a * (2 ^ a) ^ l.length := by
    simpa only [inv_mul_cancel_right] using h_prod h_mem l h_factors
  exact ⟨γ, hγ, by grw [h_le, pow_right_comm, h_length]⟩

omit [CMType E] in
/-- The real Weil representation of a pair of ranks `n`, `n'`, which depends on `γ`, `γ'` only
through a scalar of modulus one, has at `(y, y')` operator norm at most the norm of the vacuum times
`(‖y‖ ‖y'‖) ^ (n n')`, where the norm of a real point is the product of the operator norms of its
components at the infinite places. -/
theorem _root_.New.norm_realPairWeil_le [NumberField E] (γ γ' : InfinitePlace E → ℤ)
    (y : GInf E s) (y' : GInf E t) :
    ‖realPairWeil γ γ' (y, y')‖ ≤ ‖(Fock.vacVector : PairFock E s t)‖ *
      ((∏ τ : InfinitePlace E, ‖((y τ : GL n ℂ) : Matrix n n ℂ)‖) *
        ∏ τ : InfinitePlace E, ‖((y' τ : GL n' ℂ) : Matrix n' n' ℂ)‖) ^
          (Fintype.card n * Fintype.card n') := by
  -- The determinants have modulus one, and at each place the multiplier is a minor of size at most
  -- `n n'` of the matrix of `x ↦ y' x y⁻¹`.
  have h_det : ‖realPairWeil γ γ' (y, y')‖ = ‖Fock.realWeil (pairHomInf (y, y'))‖ := by
    change ‖(_ : ℂ) • Fock.realWeil (pairHomInf (y, y'))‖ = _
    simp [norm_smul]
  have h_multiplier : Fock.realMultiplier (pairHomInf (y, y')) =
      ∏ τ : InfinitePlace E, Fock.realMultiplier (Fock.pairHom t s (y τ, y' τ)) :=
    Fock.realMultiplier_blockU _
  rw [h_det, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  grw [Fock.norm_realWeil_le, h_multiplier, norm_prod]
  gcongr with τ
  grw [Fock.norm_realMultiplier_le, Fock.norm_pairHom_le, Fintype.card_prod,
    mul_comm (Fintype.card n')]

/-- Let `S` and `T` be hermitian spaces of ranks `n` and `n'`, let `a` and `b` be automorphic
characters, and let `pairWeil S T a b` be the resulting Weil representation of the product of the
two adelic unitary groups. For a compact set `Ξ` of adelic points there is a constant `C`, depending
on `S`, `T`, `a`, `b` and `Ξ`, such that for every `z` in `Ξ` and all archimedean points `y`, `y'`
(placed in the infinite components of the two groups), the operator
`pairWeil S T a b (z ((y, 1), (y', 1)))` has norm at most `C (‖y‖ ‖y'‖) ^ (n n')`. Here the norm of
an archimedean point is the product of the operator norms of its components at the infinite places,
and the exponent is the product of the cardinalities of `n` and `n'`. -/
theorem _root_.New.exists_norm_pairWeil_mul_real_le [WeilData E] (S : Space E n s)
    (T : Space E n' t) (a b : AutChar E) {Ξ : Set (G E s × G E t)} (hΞ : IsCompact Ξ) :
    ∃ C : ℝ, ∀ z ∈ Ξ, ∀ (y : GInf E s) (y' : GInf E t),
      ‖pairWeil S T a b (z * ((y, 1), (y', 1)))‖ ≤ C *
        ((∏ τ : InfinitePlace E, ‖((y τ : GL n ℂ) : Matrix n n ℂ)‖) *
          ∏ τ : InfinitePlace E, ‖((y' τ : GL n' ℂ) : Matrix n' n' ℂ)‖) ^
            (Fintype.card n * Fintype.card n') := by
  -- The operators are bounded on `Ξ`; at a real point the characters have modulus one and the
  -- multiplier is a product of minors of size at most `n n'`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z ∈ Ξ, ‖pairWeil S T a b z‖ ≤ C :=
    (pairThetaKer S T a b).exists_norm_le_of_isCompact hΞ
  refine ⟨C * ‖(S.hom T).vacElem‖, fun z hz y y' ↦ ?_⟩
  have h_char : ‖pairWeil S T a b ((y, 1), (y', 1))‖ =
      ‖(S.hom T).ω (G.onHom ((y, 1), (y', 1)))‖ := by
    change ‖pairChar a b _ • (S.hom T).ω _‖ = _
    simp [norm_smul, pairChar_apply, Circle.norm_coe]
  have h_multiplier : weilMultiplier (G.onHom (((y, 1), (y', 1)) : G E s × G E t)) =
      ∏ τ : InfinitePlace E, Fock.realMultiplier (Fock.pairHom t s (y τ, y' τ)) := by
    simp [weilMultiplier, G.onHom_eq, Prod.mk_one_one, finMultiplier_eq_one_of_mem]
  have hC_nonneg : 0 ≤ C := (norm_nonneg _).trans (hC z hz)
  rw [map_mul, ← Finset.prod_mul_distrib, ← Finset.prod_pow, mul_assoc]
  grw [norm_mul_le, hC z hz, h_char, norm_omega_le, h_multiplier, norm_prod]
  gcongr with τ
  grw [Fock.norm_realMultiplier_le, Fock.norm_pairHom_le, Fintype.card_prod,
    mul_comm (Fintype.card n')]

end New.ThetaKernel

namespace New

/-! ## Convergence and adjointness of theta lifts of rapid functions -/

section Lift

open MeasureTheory Space

variable {E n n' : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {s : n → ℤˣ} {t : n' → ℤˣ}
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {S : Space E n s} {T : Space E n' t} {φ : X} {y : G E s → ℂ} {y' : G E t → ℂ}
  (K : ThetaKernel X S T)

/-- The theta lift from S with datum φ is the function h ↦ ∫_{Γ_S\G} θ(ω(g, h)φ) y(g) dg on the
group of T. -/
def Space.lift (φ : X) (y : G E s → ℂ) (h : G E t) : ℂ :=
  ∫ g : G E s, K.θ (K.ω (g, h) φ) * y g ∂S.quotMeasure

variable (S T) in
/-- A continuous function `weightFn` of moderate growth on the adelic unitary group of `S`, with a
continuous map `comparisonMap` to the group of `T` whose heights are bounded by a constant times the
heights in `S`. -/
structure Space.ModerateWeight where
  /-- The weight function, continuous on the group of `S`. -/
  weightFn : C(G E s, ℂ)
  /-- A continuous map from the group of `S` to the group of `T`. -/
  comparisonMap : C(G E s, G E t)
  /-- The weight function has moderate growth for `S`. -/
  isModerate : S.IsModerate weightFn
  /-- The height in `T` of the image of `g` is at most a constant times the height of `g` in `S`. -/
  height_le : ∃ C : ℝ, ∀ g : G E s, T.height (comparisonMap g) ≤ S.height g * C

omit [CompleteSpace X] in
/-- Translating the argument of the lift on the right by `k` translates the datum: the lift of `y`
with datum `φ` at `h k` is the lift with datum `K.ω (1, k) φ` at `h`. -/
lemma lift_mul_right (h k : G E t) : lift K φ y (h * k) = lift K (K.ω (1, k) φ) y h := by
  simp [lift, rep_apply_apply]

namespace ThetaKernel

/-- The theta kernel for the pair `T`, `S`. It uses the representation `(h, g) ↦ ω (g, h)` of the
pair of groups in the other order, and the same functional `K.θ`. Its lifts are the transposed
lifts of `K`. -/
@[simps]
abbrev swap : ThetaKernel X T S where
  ω := K.ω.comp MulEquiv.prodComm.toMonoidHom
  θ := K.θ
  continuous := by
    simp
    fun_prop
  rat_mul := by simp_all [K.rat_mul]

omit [CompleteSpace X] in
/-- The kernel `g ↦ θ (ω (g, h) φ)` is left invariant under the rational points `S.Γ`. -/
lemma theta_rat_mul {h : G E t} :
    ∀ γ ∈ S.Γ, ∀ g : G E s, K.θ (K.ω (γ * g, h) φ) = K.θ (K.ω (g, h) φ) :=
  fun γ hγ g ↦ by simpa only [one_mul] using K.rat_mul hγ (one_mem _) g h φ

omit [CompleteSpace X] in
/-- If the datum `φ` is fixed by `ω ((1, k), 1)` for `k` in an open subgroup `L` of `G_f`, the
kernel `g ↦ θ (ω (g, h) φ)` is automorphic for `S`: continuous, left invariant under `S.Γ`, and of
some level. -/
lemma isAutomorphic (L : OpenSubgroup (Gf E n)) (hL_fix : ∀ k ∈ L, K.ω ((1, k), 1) φ = φ)
    (h : G E t) : S.IsAutomorphic fun g : G E s ↦ K.θ (K.ω (g, h) φ) := by
  refine ⟨by fun_prop, K.theta_rat_mul, L, fun k hk g ↦ ?_⟩
  nth_rw 2 [← hL_fix k hk]
  simp [rep_apply_apply]

/-- Moderate growth of theta kernels: for a kernel (ω, θ) for S, T there are C and A with
|θ(ω(g, h)φ)| ≤ C‖φ‖(ht(g) ht(h))^A for all g, h and all data φ. -/
lemma moderate_growth :
    ∃ (C : ℝ) (A : ℕ), ∀ (g : G E s) (h : G E t) (φ : X),
      ‖K.θ (K.ω (g, h) φ)‖ ≤ C * ‖φ‖ * (S.height g * T.height h) ^ A := by
  -- Reduce each variable separately, with one exponent `A` for both: the kernel does not change
  -- under left multiplication by a rational pair `(γ, δ)`, and `K.ω (γ * g, δ * h)` is the product
  -- of `K.ω (γ * g, 1)` and `K.ω (1, δ * h)`, each bounded by
  -- `eventually_exists_norm_omega_le_mul_height_pow`.
  obtain ⟨A, h_left, h_right⟩ : ∃ A : ℕ,
      (∀ g : G E s, ∃ γ ∈ S.Γ, ‖K.swap.ω (1, γ * g)‖ ≤ 2 ^ A * S.height g ^ A) ∧
      ∀ h : G E t, ∃ δ ∈ T.Γ, ‖K.ω (1, δ * h)‖ ≤ 2 ^ A * T.height h ^ A :=
    ((K.swap.eventually_exists_norm_omega_le_mul_height_pow 1).and
      (K.eventually_exists_norm_omega_le_mul_height_pow 1)).exists
  refine ⟨‖K.θ‖ * 2 ^ A * 2 ^ A, A, fun g h φ ↦ ?_⟩
  obtain ⟨γ, hγ, hγ_le⟩ := h_left g
  obtain ⟨δ, hδ, hδ_le⟩ := h_right h
  calc _ = ‖K.θ ((K.swap.ω (1, γ * g) * K.ω (1, δ * h)) φ)‖ := by
        simp [K.rat_mul hγ hδ, rep_apply_apply]
    _ ≤ ‖K.θ‖ * (2 ^ A * S.height g ^ A * (2 ^ A * T.height h ^ A) * ‖φ‖) := by
        grw [K.θ.le_opNorm, ContinuousLinearMap.le_opNorm, norm_mul_le_of_le hγ_le hδ_le]
    _ = _ := by ring

/-- For fixed `h` and `φ`, the kernel `g ↦ θ (ω (g, h) φ)` has moderate growth on the group of
`S`: it is at most a constant times a power of the height. -/
lemma isModerate (φ : X) (h : G E t) : S.IsModerate fun g : G E s ↦ K.θ (K.ω (g, h) φ) := by
  obtain ⟨C, A, h_growth⟩ := K.swap.moderate_growth
  exact ⟨C * ‖φ‖ * T.height h ^ A, A, fun g ↦ by simpa [mul_pow, ← mul_assoc] using h_growth h g φ⟩

section

omit [CompleteSpace X]

/-- The lift is left invariant under the rational points `T.Γ`. -/
lemma fixesLeft_lift : T.Γ.FixesLeft (lift K φ y) :=
  fun γ hγ h ↦ by simp [← K.rat_mul (one_mem _) hγ _ h, lift]

/-- Equivariance of the theta lift: for a theta kernel and y automorphic on the group of S, the
lift of y with datum φ, at hl, equals the lift of g ↦ y(gk) with datum ω(k, l)φ, at h. -/
lemma lift_equivariant (hy : S.IsAutomorphic y) (φ : X) (k : G E s) (l h : G E t) :
    lift K φ y (h * l) = lift K (K.ω (k, l) φ) (fun g : G E s ↦ y (g * k)) h := by
  obtain ⟨hy_cont, hy_rat, -⟩ := hy
  -- Translate the variable of integration by `k`; the integrand is left invariant under `S.Γ`.
  have h_rat : S.Γ.FixesLeft fun g : G E s ↦ K.θ (K.ω (g, h * l) φ) * y g :=
    fun γ hγ g ↦ by simp only [K.theta_rat_mul γ hγ g, hy_rat γ hγ g]
  obtain ⟨h_shift, -⟩ := integral_comp_mul_right k h_rat
  calc lift K φ y (h * l) = ∫ g, K.θ (K.ω (g * k, h * l) φ) * y (g * k) ∂S.quotMeasure :=
      h_shift.symm
    _ = lift K (K.ω (k, l) φ) (fun g : G E s ↦ y (g * k)) h := by simp [lift, rep_apply_apply]

/-- For `y` automorphic, the lift with datum `ω (k, 1) φ` is the lift of `g ↦ y (g k⁻¹)` with
datum `φ`. -/
lemma lift_omega_left (hy : S.IsAutomorphic y) (k : G E s) :
    lift K (K.ω (k, 1) φ) y = lift K φ fun g : G E s ↦ y (g * k⁻¹) := by
  funext h
  have h_eq : lift K (K.ω (k, 1) φ) y (h * 1) =
      lift K (K.ω (k⁻¹, 1) (K.ω (k, 1) φ)) (fun g : G E s ↦ y (g * k⁻¹)) h :=
    K.lift_equivariant hy (K.ω (k, 1) φ) k⁻¹ 1 h
  simpa [lift, rep_apply_apply] using h_eq

end

/-- For `y` automorphic of rapid decay for `S` (`S.rapidFunctions`), the integrand
`θ (ω (g, h) φ) y (g)` of the lift is bounded in `g`: there are `C` and `A` with
`|θ (ω (g, h) φ) y (g)| ≤ ht(h)^A |C| ‖φ‖` for all `φ`, `g` and `h`. -/
lemma exists_norm_theta_mul_le (hy : y ∈ S.rapidFunctions) :
    ∃ (C : ℝ) (A : ℕ), ∀ (φ : X) (g : G E s) (h : G E t),
      ‖K.θ (K.ω (g, h) φ) * y g‖ ≤ T.height h ^ A * |C| * ‖φ‖ := by
  -- The kernel grows like a power `A` of both heights; the decay of `y` absorbs the height of `g`.
  obtain ⟨C, A, h_growth⟩ := K.moderate_growth
  obtain ⟨-, hy_rapid⟩ : S.IsAutomorphic y ∧ S.IsRapid y := hy
  obtain ⟨D, h_decay⟩ : ∃ D : ℝ, ∀ g : G E s, ‖y g‖ * S.height g ^ A ≤ D := hy_rapid A
  refine ⟨|C| * D, A, fun φ g h ↦ ?_⟩
  have hg_pos : 0 < S.height g := S.height_pos g
  have hh_pos : 0 < T.height h := T.height_pos h
  calc _ ≤ |C| * ‖φ‖ * (S.height g * T.height h) ^ A * ‖y g‖ := by
        grw [norm_mul, h_growth, le_abs_self C]
    _ = T.height h ^ A * (|C| * (‖y g‖ * S.height g ^ A)) * ‖φ‖ := by ring
    _ ≤ T.height h ^ A * |(|C| * D)| * ‖φ‖ := by grw [h_decay, ← le_abs_self (|C| * D)]

/-- For `y` automorphic of rapid decay for `S`, the integrand `g ↦ θ (ω (g, h) φ) y (g)` of the
lift is integrable on `S.Γ \ G`. -/
lemma integrable_theta_mul (hy : y ∈ S.rapidFunctions) (φ : X) (h : G E t) :
    Integrable (fun g : G E s ↦ K.θ (K.ω (g, h) φ) * y g) S.quotMeasure := by
  obtain ⟨hy_aut, hy_rapid⟩ : S.IsAutomorphic y ∧ S.IsRapid y := hy
  exact (hy_rapid.mul (K.isModerate φ h)).integrable (.mul (by fun_prop) hy_aut.continuous)

variable (hr : y ∈ S.rapidFunctions) in
include hr in
/-- The theta lift (φ, y) ↦ `New.Space.lift` K φ y as a ℂ-bilinear map from X and rapidly
decaying automorphic functions for S to functions on the group of T. The definition also takes an
argument `hr : y ∈ S.rapidFunctions` for a function `y` that the map does not use. -/
def liftBilin : X →ₗ[ℂ] S.rapidFunctions.1 →ₗ[ℂ] G E t → ℂ :=
  LinearMap.mk₂ ℂ (fun φ y ↦ lift K φ y)
    (by simp [add_mul, funext_iff, integral_add, integrable_theta_mul, lift])
    (by simp [funext_iff, lift, ← integral_const_mul, ← mul_assoc])
    (by simp [funext_iff, mul_add, integral_add, integrable_theta_mul, lift])
    (by simp [funext_iff, mul_left_comm, lift, ← integral_const_mul])

/-- For y automorphic of rapid decay for S and each h in the group of T, the value at h of the
theta lift of y is a continuous linear functional of the datum φ. -/
lemma exists_clm_lift (hy : y ∈ S.rapidFunctions) :
    ∃ L : G E t → X →L[ℂ] ℂ, ∀ (φ : X) (h : G E t), lift K φ y h = L h φ := by
  -- `L h` is the strong integral over `g` of the functionals `y g • K.θ ∘L K.ω (g, h)`.
  refine ⟨fun h ↦ strongIntegral S.quotMeasure fun g ↦ y g • K.θ ∘L K.ω (g, h), fun φ h ↦ ?_⟩
  simp [strongIntegral_apply, mul_comm (y _), integrable_theta_mul, hy, lift]

/-- The theta lift of an automorphic function `y` of rapid decay for `S`, with any datum `φ`, is a
continuous function on the group of `T`. -/
lemma continuous_lift (hy : y ∈ S.rapidFunctions) : Continuous (lift K φ y) := by
  -- The value at `h` is the value at `1` of the lift with datum `K.ω (1, h) φ`, and the value at
  -- `1` is a continuous linear functional of the datum.
  obtain ⟨L, hL⟩ : ∃ L : G E t → X →L[ℂ] ℂ, ∀ (ψ : X) (h : G E t), lift K ψ y h = L h ψ :=
    K.exists_clm_lift hy
  have h_value (h : G E t) : lift K φ y h = L 1 (K.ω (1, h) φ) := by
    rw [← hL, ← lift_mul_right, one_mul]
  have h_orbit : Continuous fun h : G E t ↦ K.ω (1, h) φ := by fun_prop
  rw [funext h_value]
  exact (L 1).continuous.comp h_orbit

/-- The theta lift of an automorphic function `y` of rapid decay for `S` has moderate growth on the
group of `T`: its norm is at most a constant times a power of the height. -/
lemma isModerate_lift (hy : y ∈ S.rapidFunctions) : T.IsModerate (lift K φ y) := by
  -- The integrand is bounded by a constant times a power of the height of `h`, and the quotient
  -- `[S]` has finite volume.
  obtain ⟨C, A, h_bound⟩ : ∃ (C : ℝ) (A : ℕ), ∀ (ψ : X) (g : G E s) (h : G E t),
      ‖K.θ (K.ω (g, h) ψ) * y g‖ ≤ T.height h ^ A * |C| * ‖ψ‖ :=
    K.exists_norm_theta_mul_le hy
  refine ⟨S.quotMeasure.real Set.univ * |C| * ‖φ‖, A, fun h ↦ ?_⟩
  calc ‖lift K φ y h‖
      = ‖∫ g : G E s, K.θ (K.ω (g, h) φ) * y g ∂S.quotMeasure‖ := rfl
    _ ≤ T.height h ^ A * |C| * ‖φ‖ * S.quotMeasure.real Set.univ :=
        norm_integral_le_of_norm_le_const (.of_forall fun g ↦ h_bound φ g h)
    _ = S.quotMeasure.real Set.univ * |C| * ‖φ‖ * T.height h ^ A := by ring

/-- For y, y' automorphic of rapid decay on S, T, the Petersson product of y' with the lift of y
is linear in the datum. -/
lemma isLinearMap_petersson_lift (hy : y ∈ S.rapidFunctions) (hy' : y' ∈ T.rapidFunctions) :
    IsLinearMap ℂ fun φ : X ↦ T.petersson y' (lift K φ y) := by
  obtain ⟨L, hL⟩ : ∃ L : G E t → X →L[ℂ] ℂ, ∀ (φ : X) (h : G E t), lift K φ y h = L h φ :=
    K.exists_clm_lift hy
  obtain ⟨h_aut, h_decay⟩ := star_mem_rapidFunctions hy'
  have h_int (φ : X) : Integrable (fun h : G E t ↦ star (y' h) * L h φ) T.quotMeasure := by
    have h_rapid : T.IsRapid (lift K φ y * star y') := h_decay.mul (K.isModerate_lift hy)
    have h_cont : Continuous (lift K φ y * star y') := (K.continuous_lift hy).mul h_aut.continuous
    simpa only [← hL, mul_comm, Pi.mul_def, Pi.star_apply] using h_rapid.integrable h_cont
  refine ⟨fun φ φ' ↦ ?_, fun c φ ↦ ?_⟩
  · simpa only [petersson, hL, map_add, mul_add, starRingEnd_apply] using
      integral_add (h_int φ) (h_int φ')
  · simp only [petersson, hL, map_smul, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

/-- Let y and F be of rapid decay for S and U, and w a `New.Space.ModerateWeight` from U to T, with
weight function `M = w.weightFn` and map `j = w.comparisonMap`. Then
`(v, g) ↦ M(v) F(v) θ(ω(g, j v) φ) y(g)` is integrable for the product of the quotient measures. -/
lemma integrable_prod_weightFn (hy : y ∈ S.rapidFunctions) {m : Type} [Fintype m] [DecidableEq m]
    {u : m → ℤˣ} {F : G E u → ℂ} {U : Space E m u} (w : U.ModerateWeight T)
    (hF : F ∈ U.rapidFunctions) (φ : X) :
    Integrable (fun p : G E u × G E s ↦ (⇑w.weightFn * F) p.1 *
      (K.θ (K.ω (p.2, w.comparisonMap p.1) φ) * y p.2)) (U.quotMeasure.prod S.quotMeasure) := by
  -- The integrand is continuous and bounded: the height of `w.comparisonMap v` is at most a
  -- multiple of that of `v`, and the rapid decay of `w.weightFn * F` absorbs its power.
  obtain ⟨C, A, h_bound⟩ := K.exists_norm_theta_mul_le hy
  obtain ⟨B, h_ht⟩ := w.height_le
  obtain ⟨⟨hF_cont, -⟩, hF_rapid⟩ : U.IsAutomorphic F ∧ U.IsRapid F := hF
  obtain ⟨⟨hy_cont, -⟩, -⟩ : S.IsAutomorphic y ∧ S.IsRapid y := hy
  obtain ⟨D, h_decay⟩ : ∃ D : ℝ, ∀ v : G E u, ‖(⇑w.weightFn * F) v‖ * U.height v ^ A ≤ D :=
    hF_rapid.mul w.isModerate A
  refine .of_bound (by fun_prop) (D * |B ^ A| * |C| * ‖φ‖) (.of_forall fun (v, g) ↦ ?_)
  have hv_pos : 0 < U.height v := U.height_pos v
  have hj_pos : 0 < T.height (w.comparisonMap v) := T.height_pos _
  calc _ ≤ ‖(⇑w.weightFn * F) v‖ * ((U.height v * B) ^ A * |C| * ‖φ‖) := by
        grw [norm_mul, h_bound, h_ht]
    _ = ‖(⇑w.weightFn * F) v‖ * U.height v ^ A * B ^ A * |C| * ‖φ‖ := by ring
    _ ≤ _ := by grw [le_abs_self (B ^ A), h_decay]

/-- For a kernel (ω, θ), y automorphic and rapid on S, and y' automorphic and rapid on T, ∫_{[T]}
y'·(lift of y by φ) equals ∫_{[S]} y·(transposed lift of y' by φ). -/
lemma integral_mul_lift_eq_integral_mul_lift_swap (hy : y ∈ S.rapidFunctions)
    (hy' : y' ∈ T.rapidFunctions) :
    ∫ h : G E t, y' h * lift K φ y h ∂T.quotMeasure =
      ∫ g : G E s, y g * lift K.swap φ y' g ∂S.quotMeasure := by
  -- Fubini for `y' h * K.θ (K.ω (g, h) φ) * y g`, integrable by `integrable_prod_weightFn` for the
  -- weight `1` and the identity map.
  let w : T.ModerateWeight T := ⟨1, .id _, ⟨1, 0, by simp⟩, ⟨1, by simp⟩⟩
  have h_int : Integrable (fun p : G E t × G E s ↦ y' p.1 * (K.θ (K.ω (p.2, p.1) φ) * y p.2))
      (T.quotMeasure.prod S.quotMeasure) := by
    simpa [w] using K.integrable_prod_weightFn hy w hy' φ
  calc _ = ∫ h, ∫ g, y' h * (K.θ (K.ω (g, h) φ) * y g) ∂S.quotMeasure ∂T.quotMeasure := by
        simp [lift, ← integral_const_mul]
    _ = ∫ g, ∫ h, y' h * (K.θ (K.ω (g, h) φ) * y g) ∂T.quotMeasure ∂S.quotMeasure :=
        integral_integral_swap h_int
    _ = _ := by simp [mul_comm, mul_left_comm, lift, ← integral_const_mul]

/-- On automorphic functions of rapid decay, the adjoint of the lift for the Petersson products is
the descent, which sends `y'` to the conjugate of the transposed lift of the conjugate of `y'`. -/
lemma petersson_lift_eq_petersson_descent (hy : y ∈ S.rapidFunctions)
    (hy' : y' ∈ T.rapidFunctions) :
    T.petersson y' (lift K φ y) = S.petersson (star (lift K.swap φ (star y'))) y := by
  simpa only [petersson, starRingEnd_apply, Pi.star_apply, star_star, mul_comm (y _)] using
    K.integral_mul_lift_eq_integral_mul_lift_swap hy (star_mem_rapidFunctions hy')

end ThetaKernel

end Lift

end New

end
