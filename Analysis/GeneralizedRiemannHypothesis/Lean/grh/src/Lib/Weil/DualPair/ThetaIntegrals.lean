import Lib.SiegelWeil.SingularForms.CentreCoefficients
import Lib.Weil.DualPair.FiniteAction
import Lib.Weil.DualPair.KernelDecay
import Lib.Weil.DualPair.MixedModel

/-!
# Terms of theta kernels at rational matrices and basic laws of theta integrals

This file studies the theta kernel `New.pairTheta S T α β f` of a pair of hermitian spaces (S, T)
and the theta integral `New.Exchange.thetaIntegral S T α β f`, which is its integral over `[U(T)]`.
When S is split along an isotropic subspace (`New.Space.Splitting`), the terms of the kernel at
rational matrices are invariant under (x, h) ↦ (γ x, γ h) for rational γ in U(T). Some results
concern data with real part a Fock vector `v`, finite part `y ↦ φ (π y)` at the places `A` (where
`π` reads the components at `A`), and the vacuum elsewhere. For such data the file describes how the
two unitary groups act.

## Main definitions and results

* `New.Space.Splitting.exists_tsum_thetaTerm_le`: the terms are absolutely summable, with moderate
  growth in h.
* `New.Space.Splitting.exists_tsum_thetaTerm_schrodingerOp_le`: under a support condition on Ψ the
  sum of their absolute values is bounded in h.
* `New.Space.Splitting.hasIntegrableTerms_integrated_schrodingerOp`: so this sum is integrable over
  the adelic quotient of U(T) (`New.Space.Splitting.HasIntegrableTerms`).
* `New.Exchange.ReadsAt.pairWeil_localDatum_of_mem_stdLevel`, `New.Exchange.thetaIntegral_pairWeil`:
  how the two unitary groups act.
* `New.Exchange.IsTargetBounded`: a growth bound on the kernel, under which the integral is linear
  in the datum (`New.Exchange.exists_linear_thetaIntegral`) and automorphic
  (`New.Exchange.IsTargetBounded.isAutFunction_thetaIntegral`).
* `New.Exchange.ReadsAt.isTargetBounded`: the bound holds when `F ≠ 0`, `v` has all moments finite
  and `φ` is locally constant of compact support and vanishes off the right invertible matrices.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.𝒮`: The Banach space 𝒮(V) of integrable functions c on 𝔸^n with c(x) = ∫ c(y)β(y,x)e(x−y) dy,
  under the L¹ norm; β is the adelic bicharacter and e the vacuum function `New.vacuumFn`.
* `New.pairWeil`: The action ω_{a,b}(g, h) = a(det h) b(det g)⁻¹ ω(x ↦ hxg⁻¹) on 𝒮(Hom(S, T)).
* `New.Space.integrated`, `New.Space.schrodingerOp`: The operators f ↦ v ⊗ f for a Fock vector v and
  f ↦ Ψ ⊗ f for a function Ψ on finite adelic vectors.

## Relation to the literature

Known; see `Lib.Weil.DualPair.ThetaLiftConvergence` for sources.
-/

/-!
## Terms of the theta kernel at rational matrices

Let S be split along an isotropic subspace (`New.Space.Splitting`, with frames k, l and complement
i). For a rational matrix x, `New.Space.Splitting.thetaTerm` is the term θ((ω(g, h) f)[x]) of the
theta kernel of the pair (S, T), where the slice f ↦ f[x] is `New.Space.Splitting.homSlice`.
-/

namespace New.Space.Splitting

open Complex Matrix ENNReal ContinuousLinearMap

variable {E : Type} [Field E] [CMType E] [WeilData E]
  {n n' n₀ p : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n₀]
  [DecidableEq n₀] [Fintype p] [DecidableEq p] {s : n → ℤˣ} {s' : n' → ℤˣ} {s₀ : n₀ → ℤˣ}
  {S : Space E n s} {S₀ : Space E n₀ s₀} (D : S.Splitting S₀ p) (T : Space E n' s')
  (a b : AutChar E) (f : 𝒮 (S.hom T)) (g : G E s) (γ : U T.J) (x : Matrix n' p E) (h : G E s')

/-- For split S and a rational matrix x, the term θ((ω_{a,b}(g,h)f)[x]) of the theta kernel. Here
f[x] is the slice (`homSlice`) of f over the maps that send the isotropic frame `D.k` to x. -/
noncomputable def thetaTerm : ℂ :=
  θ (S₀.hom T) (D.homSlice T (T.x⁻¹.val * x.map toAdele) (pairWeil S T a b (g, h) f))

/-- The function h ↦ ∑ₓ |thetaTerm(g, x, h) · y(h)|, summed over rational matrices x, has finite
integral for the measure `T.quotMeasure` of the adelic quotient of U(T). The weight y is an optional
argument; without it y = 1. -/
abbrev HasIntegrableTerms (y : G E s' → ℂ := fun _ : G E s' ↦ 1) : Prop :=
  ∫⁻ h : G E s', ∑' x : Matrix n' p E, ‖D.thetaTerm T a b f g x h * y h‖ₑ ∂T.quotMeasure < ⊤

/-- For a rational point γ of U(T), the term `New.Space.Splitting.thetaTerm` is unchanged when (x,
h) is replaced by (γ x, γ h). -/
lemma thetaTerm_ratEmbed_mul :
    D.thetaTerm T a b f g ((γ : Matrix n' n' E) * x) (T.ratEmbed γ * h) =
      D.thetaTerm T a b f g x h := by
  -- θ F is the value of F at 0, and the rational point (1, γ) acts by a linear substitution
  have h_rat (c : AutChar E) (F : 𝒮 (S₀.hom T)) :
      θ (S₀.hom T) (pairWeil S₀ T c b (1, T.ratEmbed γ) F) = θ (S₀.hom T) F := by
    rw [theta_apply, theta_apply, pairWeil_of_mem_Gamma S₀ T c b (one_mem _) ⟨γ, rfl⟩, mulVec_zero]
  unfold thetaTerm
  -- ω(g, γh) = ω(1, γ) ω(g, h), and 1 is a Levi element: `homSlice_levi` moves γ⁻¹ onto γx
  rw [← one_mul g, ← Prod.mk_mul_mk, ← rep_apply_apply, ← div_mul_cancel a, ← D.levi.map_one,
    homSlice_levi, ← map_inv, adeleMatrix_ratEmbed, ← ratMap, ratMap_mul_toAdele, map_smul]
  -- the Levi element 1 has determinant 1, so the scalar of `homSlice_levi` is 1
  simp [h_rat]

open scoped Matrix.Norms.L2Operator in
/-- For fixed g there are C and B such that every point h of U(T) has a rational translate γ h with
‖ω(g, γ h)‖ ≤ C ht(h)^B. -/
lemma _root_.New.exists_mem_norm_pairWeil_le_mul_height_pow (S : Space E n s) (T : Space E n' s')
    (a b : AutChar E) (g : G E s) :
    ∃ (C : ℝ) (B : ℕ), 0 ≤ C ∧ ∀ h : G E s', ∃ γ ∈ T.Γ,
      ‖pairWeil S T a b (g, γ * h)‖ ≤ C * T.height h ^ B := by
  -- Write γ h = z y with z in a compact set and y real of norm at most ht(h) at each infinite
  -- place, and bound ω((g, z)(1, y)) by a power of the norm of y.
  obtain ⟨Ω, hΩ, h_reduce⟩ := T.exists_reduction_norm_le_height
  obtain ⟨C, hC⟩ :=
    exists_norm_pairWeil_mul_real_le S T a b ((isCompact_singleton (x := g)).prod hΩ)
  let N : ℕ := Fintype.card n * Fintype.card n'
  let c : ℝ := ∏ τ : NumberField.InfinitePlace E, ‖(((1 : GInf E s) τ : GL n ℂ) : Matrix n n ℂ)‖
  refine ⟨|C| * c ^ N, Fintype.card (NumberField.InfinitePlace E) * N, by positivity, fun h ↦ ?_⟩
  obtain ⟨γ, hγ, l, hz, hy, -⟩ := h_reduce h
  have h_eq : ((g, γ * h) : G E s × G E s') =
      (g, γ * h * (l.prod, 1)⁻¹) * (((1 : GInf E s), 1), (l.prod, 1)) :=
    Prod.ext (mul_one g).symm (inv_mul_cancel_right _ _).symm
  have h_norm : ∏ τ : NumberField.InfinitePlace E, ‖((l.prod τ : GL n' ℂ) : Matrix n' n' ℂ)‖ ≤
      T.height h ^ Fintype.card (NumberField.InfinitePlace E) := by
    simpa using Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun τ (_ : τ ∈ Finset.univ) ↦ hy τ
  refine ⟨γ, hγ, ?_⟩
  grw [h_eq, hC _ (Set.mk_mem_prod rfl hz) 1 l.prod, le_abs_self C, h_norm, mul_pow,
    ← pow_mul, mul_assoc]

/-- Let `D` split `S` over `S₀` and fix g ∈ G E s. There are C and B such that for all f in the data
space 𝒮(Hom(S,T)) and all h ∈ G E s', the sum over rational n' × p matrices x of
|θ((ω_{a,b}(g,h)f)[x])| (`D.thetaTerm T a b f g x h`, with f[x] the slice of f over the maps sending
`D.k` to x) is at most |C| ‖f‖ ht(h)^B in [0, ∞]. Here ht = `T.height` is 1 over the first minimum,
cut off at 1, of T moved by h. -/
lemma exists_tsum_thetaTerm_le :
    ∃ (C : ℝ) (B : ℕ), ∀ (f : 𝒮 (S.hom T)) (h : G E s'),
      ∑' x : Matrix n' p E, ‖D.thetaTerm T a b f g x h‖ₑ ≤
        ENNReal.ofReal (|C| * ‖f‖ * T.height h ^ B) := by
  -- Move h by a rational δ to where ω is bounded by a power of the height; the terms are only
  -- permuted (`thetaTerm_ratEmbed_mul`), and the norms of the slices of the moved datum `F` have
  -- sum at most M ‖F‖.
  obtain ⟨C, B, hC, h_reduce⟩ := exists_mem_norm_pairWeil_le_mul_height_pow S T a b g
  obtain ⟨M, hM⟩ := (D.homSource T).tsum_enorm_slice_le
  refine ⟨‖θ (S₀.hom T)‖ * M * C, B, fun f h ↦ ?_⟩
  obtain ⟨_, ⟨δ, rfl⟩, hδ⟩ := h_reduce h
  let d : Matrix n' n' E := δ.val.val
  set F : 𝒮 (S.hom T) := pairWeil S T a b (g, T.ratEmbed δ * h) f
  have h_inj : (fun x : Matrix n' p E ↦ Function.uncurry (d * x)).Injective :=
    Function.uncurry_injective.comp (mul_right_injective_of_invertible d)
  calc ∑' x : Matrix n' p E, ‖D.thetaTerm T a b f g x h‖ₑ
    _ ≤ ∑' x : Matrix n' p E, ‖θ (S₀.hom T)‖ₑ *
          ‖(D.homSource T).slice (toAdele ∘ Function.uncurry (d * x)) F‖ₑ := by
      gcongr with x
      grw [← thetaTerm_ratEmbed_mul (γ := δ), thetaTerm, homSlice_eq_slice, le_opENorm]
      rfl
    _ ≤ ‖θ (S₀.hom T)‖ₑ * (M * ‖F‖ₑ) := by
      grw [ENNReal.tsum_mul_left, tsum_comp_le_tsum_of_injective h_inj
        fun y : n' × p → E ↦ ‖(D.homSource T).slice (toAdele ∘ y) F‖ₑ, hM]
    _ ≤ ENNReal.ofReal (|‖θ (S₀.hom T)‖ * M * C| * ‖f‖ * T.height h ^ B) := by
      -- `‖F‖ ≤ ‖ω(g, δh)‖ ‖f‖`, and `‖ω(g, δh)‖ ≤ C ht(h) ^ B` by the choice of `δ`
      grw [abs_of_nonneg (show 0 ≤ ‖θ (S₀.hom T)‖ * M * C by positivity), mul_right_comm _ C,
        mul_assoc _ C, ← hδ, le_opENorm]
      simp [mul_assoc, mul_comm ‖f‖ₑ]

/-- If a rational map `y` from `S` to `T` kills the isotropic frame `D.k`, its Heisenberg operator
does not change the theta functional of the term (`homSlice`) of a rational matrix `x`. -/
lemma theta_homSlice_rho_ratMap {y : Matrix n' n E} (hy : y * D.k = 0) :
    θ (S₀.hom T) (D.homSlice T (T.x⁻¹.val * x.map toAdele)
        (ϱ (S.hom T) (matrixToVec (T.ratMap S y)) f)) =
      θ (S₀.hom T) (D.homSlice T (T.x⁻¹.val * x.map toAdele) f) := by
  -- By `homSlice_rho` the operator acts on the term through the rational map `y * D.i`, which
  -- `θ` does not see, and the value of the additive character at a rational point, which is `1`.
  have h_k : T.ratMap S y * D.kAdelic = 0 := by
    rw [kAdelic, ratMap_mul_toAdele, hy, Matrix.map_zero _ (map_zero toAdele), Matrix.mul_zero]
  have h_i : matrixToVec (T.ratMap S y * D.iAdelic) =
      (S₀.hom T).vecAtPoint (matrixToVec (y * D.i)) := by
    rw [iAdelic, ratMap_mul_ratMap, vecAtPoint_hom]
  have h_rat : ((T.x⁻¹.val * (y * D.l).map toAdele)ᴴ * stdForm E s' *
      (T.x⁻¹.val * x.map toAdele + T.x⁻¹.val * x.map toAdele)).trace =
        toAdele (2 * ((y * D.l)ᴴ * T.J * x).trace) := by
    rw [Matrix.mul_add, gram_at_point_eq_map, trace_add, ← AddMonoidHom.map_trace, two_mul, map_add]
  rw [homSlice_rho, h_k, lAdelic, ratMap_mul_toAdele, h_i, add_zero, add_zero, h_rat, ← map_mul,
    stdAddChar_toAdele]
  simp [theta_apply, rho_apply, apply_vecAtPoint]

/-- The rational maps `z (c • (D.k | D.i))ᴴ S.J` kill the isotropic frame `D.k`, so their Heisenberg
operators do not change the theta functional of the term of a rational matrix `x`. -/
lemma theta_homSlice_rho_ratMap_frame (c : E) (z : Matrix n' (p ⊕ n₀) E) :
    θ (S₀.hom T) (D.homSlice T (T.x⁻¹.val * x.map toAdele)
        (ϱ (S.hom T) (matrixToVec (T.ratMap S (z * (c • D.k.fromCols D.i)ᴴ * S.J))) f)) =
      θ (S₀.hom T) (D.homSlice T (T.x⁻¹.val * x.map toAdele) f) := by
  have h_orth : (D.k.fromCols D.i)ᴴ * S.J * D.k = 0 := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul, D.gram_kk,
      D.gram_ik, fromRows_zero]
  refine D.theta_homSlice_rho_ratMap T f x ?_
  rw [conjTranspose_smul, Matrix.mul_assoc z, Matrix.mul_assoc z, Matrix.smul_mul, Matrix.smul_mul,
    h_orth, smul_zero, Matrix.mul_zero]

omit [WeilData E] in
/-- A multiple of a rational matrix `c` by a nonzero integer has its columns in
`(S.move g).latticeBall Z` for some Z: their coordinates at the point of S moved by g are integral
at the finite places and of norm ≤ Z at the infinite places. -/
lemma _root_.New.Space.exists_smul_col_mem_latticeBall {q : Type} [Fintype q] (c : Matrix n q E) :
    ∃ (d : ℕ) (Z : ℝ), d ≠ 0 ∧ ∀ j : q, ((d : E) • c).col j ∈ (S.move g).latticeBall Z := by
  obtain ⟨d, hd, h_int⟩ :=
    exists_forall_mul_mem_Ô fun i : n × q ↦ (S.coordMatrix g c i.1 i.2).2
  let len (j : q) : EuclideanSpace ℂ (NumberField.InfinitePlace E × n) :=
    (S.move g).archCoords (((d : E) • c).col j)
  refine ⟨d, ‖len‖, hd, fun j ↦ ⟨fun i ↦ ?_, norm_le_pi_norm len j⟩⟩
  have h_entry : (S.move g).vecAtPoint ((d : E) • c.col j) i = d * S.coordMatrix g c i j := by
    rw [LinearMap.map_smulₛₗ, vecAtPoint_move, map_natCast]
    rfl
  change ((S.move g).vecAtPoint ((d : E) • c.col j) i).2 ∈ Ô E
  rw [h_entry]
  exact h_int (i, j)
omit [WeilData E] in
/-- If a nonzero rational column `x` of `T` is paired with a finite adelic map `y` whose restriction
to the columns of `c` at `g` is right invertible after a ring map `φ`, then the pairing (finite part
of `T.coordMatrix k x`)ᴴ · y · (finite part of `S.coordMatrix g (d • c)`) is nonzero for every
nonzero natural `d`. -/
lemma _root_.New.Space.coordMatrix_mul_natCast_smul_ne_zero {q : Type} [Fintype q] [DecidableEq q]
    {R : Type*} [CommRing R] [Nontrivial R] (φ : 𝔸f E →+* R) {x : Matrix n' Unit E} (hx : x ≠ 0)
    (k : G E s') {g : G E s} {c : Matrix n q E} {d : ℕ} (hd : d ≠ 0) {y : n' × n → 𝔸f E}
    (hy : HasLeftInv ((vecToMatrix y * (S.coordMatrix g c).map Prod.snd).map φ)ᵀ) :
    ((T.coordMatrix k x).map Prod.snd)ᴴ *
      (vecToMatrix y * (S.coordMatrix g ((d : E) • c)).map Prod.snd) ≠ 0 := by
  have h_smul : (S.coordMatrix g ((d : E) • c)).map Prod.snd =
      (d : 𝔸f E) • (S.coordMatrix g c).map Prod.snd := by
    simp [coordMatrix, Nat.cast_smul_eq_nsmul, Matrix.map_smul]
  rw [h_smul, Matrix.mul_smul, Matrix.mul_smul, Ne, (isUnit_natCast_finAdele hd).smul_eq_zero]
  simpa using T.coordMatrix_mul_ne_zero hx 1 hy


/-- Let `D` split `S` over `S₀`, let `Ψ` be Schwartz–Bruhat above a set `P` of finite places
disjoint from its conjugate, and let `v` be a Fock vector whose moments `fockMoment N v` are all
finite. Suppose that for every y with Ψ y ≠ 0, the product y·c becomes right invertible after a ring
map `φ` from the finite adeles to a nonzero ring, where c is the finite part of the coordinates
g⁻¹x_S⁻¹(k | i) (x_S the point of S) of the frame `(D.k | D.i)` spanning the orthogonal complement
of `D.k`. Then for f = v ⊗ Ψ ⊗ vac = ∫ v(y) ϱ(y)(Ψ⊗ e) dy, with e the vacuum of 𝒮(Hom(S,T)), the sum
over rational n' × p matrices x of |θ((ω_{a,b}(g,k)f)[x])| (`thetaTerm`, f[x] the slice of f over
the maps sending `D.k` to x) is bounded uniformly in k ∈ G E s'. -/
lemma exists_tsum_thetaTerm_schrodingerOp_le {P : Set (FinPlace E)} (hP : Set.IsConjDisjoint P)
    {Ψ : (n' × n → 𝔸f E) → ℂ} (hΨ : IsSchwartzBruhat P Ψ)
    {v : Fock.fockSpace (realSigns E (homSigns s s'))} {R : Type*} [CommRing R] [Nontrivial R]
    (φ : 𝔸f E →+* R) (hv : Exchange.IsSchwartzVector v) {g : G E s}
    (h_supp : ∀ y : n' × n → 𝔸f E, Ψ y ≠ 0 →
      HasLeftInv ((vecToMatrix y * (S.coordMatrix g (D.k.fromCols D.i)).map Prod.snd).map φ)ᵀ) :
    ∃ C : NNReal, ∀ k : G E s',
      ∑' x : Matrix n' p E, ‖D.thetaTerm T a b
        (integrated (S.hom T) v (schrodingerOp (S.hom T) P Ψ (vacElem (S.hom T)))) g x k‖ₑ ≤ C := by
  -- A sum over finitely many `x` is the value of a functional `ℓ = ∑ u_x θ(·[x])` with phases
  -- `u_x`. The decay estimate `exists_norm_pairWeil_schrodingerOp_mul_pow_le`, with `N = 0`,
  -- `ρ = 1` and `H` the height of `k`, turns the bound `|C| ‖f‖ H ^ B` for `ℓ ∘ ω` into a bound
  -- free of `H` at the datum `F`.
  obtain ⟨C, B, h_sum⟩ : ∃ (C : ℝ) (B : ℕ), ∀ (f : 𝒮 (S.hom T)) (k : G E s'),
      ∑' x : Matrix n' p E, ‖D.thetaTerm T a b f g x k‖ₑ ≤
        ENNReal.ofReal (|C| * ‖f‖ * T.height k ^ B) := D.exists_tsum_thetaTerm_le T a b g
  have h_phases (z : ℂ) : ∃ u : ℂ, ‖u‖ = 1 ∧ (‖z‖ : ℂ) = u * z := exists_norm_eq_mul_self z
  choose u hu_norm hu_mul using h_phases
  obtain ⟨d, Z, hd, h_col⟩ : ∃ (d : ℕ) (Z : ℝ), d ≠ 0 ∧ ∀ j : p ⊕ n₀,
      ((d : E) • D.k.fromCols D.i).col j ∈ (S.move g).latticeBall Z :=
    exists_smul_col_mem_latticeBall g (D.k.fromCols D.i)
  set F : 𝒮 (S.hom T) := integrated (S.hom T) v (schrodingerOp (S.hom T) P Ψ (vacElem (S.hom T)))
  obtain ⟨K, h_bound⟩ : ∃ K : ℝ, ∀ (k : G E s') (ℓ : 𝒮 (S.hom T) →L[ℂ] ℂ),
      (∀ f : 𝒮 (S.hom T), ‖ℓ (pairWeil S T a b (g, k) f)‖ ≤ |C| * ‖f‖ * T.height k ^ B) →
      (2 < T.height k → ∃ (x : Matrix n' Unit E) (c : Matrix n (p ⊕ n₀) E) (r r' : ℝ),
        IsShortPair g k ℓ Ψ x c r r' (Z * (2 / T.height k))) →
      ‖ℓ (pairWeil S T a b (g, k) F)‖ ≤ K := by
    obtain ⟨K, h_decay⟩ := exists_norm_pairWeil_schrodingerOp_mul_pow_le (p := Unit) (q := p ⊕ n₀)
      (S := S) (T := T)
      (Ψ := Ψ) a b hP vacElem_mem_finitePart 0 B |C| Z
    refine ⟨K * (Fock.fockMoment (0 + B) v).toReal, fun k ℓ hℓ h_ex ↦ ?_⟩
    simpa using h_decay v g k ℓ 1 (T.height k) (hv (0 + B)) le_rfl (height_pos k)
      (by simpa using hℓ) (by simpa using h_ex)
  refine ⟨K.toNNReal, fun k ↦ tsum_le_of_sum_le' bot_le fun t ↦ ?_⟩
  let ℓ : 𝒮 (S.hom T) →L[ℂ] ℂ := ∑ x ∈ t, u (D.thetaTerm T a b F g x k) •
    θ (S₀.hom T) ∘L D.homSlice T (T.x⁻¹.val * x.map toAdele)
  have h_apply (f : 𝒮 (S.hom T)) : ℓ (pairWeil S T a b (g, k) f) =
      ∑ x ∈ t, u (D.thetaTerm T a b F g x k) * D.thetaTerm T a b f g x k := by
    simp [ℓ, thetaTerm]
  have h_sum_eq (f : 𝒮 (S.hom T)) : ∑ x ∈ t, ‖D.thetaTerm T a b f g x k‖ₑ =
      ENNReal.ofReal (∑ x ∈ t, ‖D.thetaTerm T a b f g x k‖) := by simp [ofReal_sum_of_nonneg]
  have h_growth (f : 𝒮 (S.hom T)) :
      ‖ℓ (pairWeil S T a b (g, k) f)‖ ≤ |C| * ‖f‖ * T.height k ^ B := by
    rw [h_apply]
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_mul, hu_norm, one_mul]
    rw [← ofReal_le_ofReal_iff (by bound [T.height_pos k]), ← h_sum_eq]
    exact (ENNReal.sum_le_tsum t).trans (h_sum f k)
  have h_inv (z : Matrix n' (p ⊕ n₀) E) (f : 𝒮 (S.hom T)) :
      ℓ (ϱ (S.hom T) (matrixToVec (T.ratMap S (z * ((d : E) • D.k.fromCols D.i)ᴴ * S.J))) f) =
        ℓ f := by
    simp only [ℓ, _root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
      theta_homSlice_rho_ratMap_frame]
  -- For `H > 2` the lattice at `k` has a short isotropic vector `x ≠ 0`; by the support condition
  -- it pairs non-trivially with the columns of the frame.
  have h_pair (h_ht : 2 < T.height k) :
      ∃ (x : Matrix n' Unit E) (c : Matrix n (p ⊕ n₀) E) (r r' : ℝ),
        IsShortPair g k ℓ Ψ x c r r' (Z * (2 / T.height k)) := by
    obtain ⟨x, hx_ne, hx_iso, hx_short⟩ : ∃ x : Matrix n' Unit E, x ≠ 0 ∧ xᴴ * T.J * x = 0 ∧
        ∀ j : Unit, x.col j ∈ (T.move k).latticeBall (2 / T.height k) :=
      T.exists_short_isotropic h_ht
    exact ⟨x, (d : E) • D.k.fromCols D.i, 2 / T.height k, Z,
      { short_target := hx_short
        short_source := h_col
        mul_le := (mul_comm _ _).le
        isotropic := .inl hx_iso
        invariant := h_inv
        ne_zero_or_mean_eq_zero := .inl fun y hy ↦
          coordMatrix_mul_natCast_smul_ne_zero T φ hx_ne k hd (h_supp y hy) }⟩
  have h_phase : ℓ (pairWeil S T a b (g, k) F) = (∑ x ∈ t, ‖D.thetaTerm T a b F g x k‖ : ℝ) := by
    simp only [h_apply, ← hu_mul, Complex.ofReal_sum]
  calc ∑ x ∈ t, ‖D.thetaTerm T a b F g x k‖ₑ
    _ = ENNReal.ofReal ‖ℓ (pairWeil S T a b (g, k) F)‖ := by
      rw [h_sum_eq, h_phase, Complex.norm_of_nonneg (by positivity)]
    _ ≤ ENNReal.ofReal K := ofReal_le_ofReal (h_bound k ℓ h_growth h_pair)

/-- Let `D` split `S` over `S₀`, let `Ψ` be Schwartz–Bruhat above a set `P` of finite places
disjoint from its conjugate, and let `v` be a Fock vector whose moments `fockMoment N v` are all
finite. Suppose that whenever Ψ(y) ≠ 0, the product y·c becomes right invertible under a ring map φ:
𝔸_f → R ≠ 0, where c is the finite part of the coordinates g⁻¹x_S⁻¹(k | i) of the frame
`(D.k | D.i)`. Then for f = v ⊗ Ψ ⊗ vac = ∫ v(y) ϱ(y)(Ψ⊗ e) dy (e the vacuum of 𝒮(Hom(S,T))), the
function h ↦ ∑_ξ |θ((ω_{a,b}(g,h)f)[ξ])| has finite integral over the adelic quotient of U(T)
(`HasIntegrableTerms`), with ξ over rational n' × p matrices and f[ξ] the slice of f over the maps
sending `D.k` to ξ. -/
lemma hasIntegrableTerms_integrated_schrodingerOp {P : Set (FinPlace E)} (hP : Set.IsConjDisjoint P)
    {Ψ : (n' × n → 𝔸f E) → ℂ} (hΨ : IsSchwartzBruhat P Ψ)
    {v : Fock.fockSpace (realSigns E (homSigns s s'))} {R : Type*} [CommRing R] [Nontrivial R]
    (φ : 𝔸f E →+* R) (hv : Exchange.IsSchwartzVector v) {g : G E s}
    (h_supp : ∀ y : n' × n → 𝔸f E, Ψ y ≠ 0 →
      HasLeftInv ((vecToMatrix y * (S.coordMatrix g (D.k.fromCols D.i)).map Prod.snd).map φ)ᵀ) :
    D.HasIntegrableTerms T a b (integrated (S.hom T) v
      (schrodingerOp (S.hom T) P Ψ (vacElem (S.hom T))))
      g := by
  -- The integrand is bounded and the measure is finite.
  obtain ⟨C, h_le⟩ := D.exists_tsum_thetaTerm_schrodingerOp_le T a b hP hΨ φ hv h_supp
  exact IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal _
    ⟨C, fun k ↦ by simpa only [mul_one] using h_le k⟩

end New.Space.Splitting

/-!
## The theta integral: group actions, linearity and automorphy

`New.Exchange.IsSchwartzVector v` says that all moments of the Fock vector `v` are finite.
`New.schwartzBruhat U` is the space of locally constant functions with compact support that vanish
outside `U`.
-/

namespace New.Exchange

open Matrix MeasureTheory Space CompactlyCoherentSpace

variable {E : Type} {n n' : Type} {F : Type} [Field E] [CMType E] [WeilData E] [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n'] {s : n → ℤˣ} {s' : n' → ℤˣ}
  {μ : NumberField.InfinitePlace E → ℤ} (S : Space E n s) (T : Space E n' s')
  -- `v` is the real part of a datum: a vector of the Fock model of `Hom(S, T)` at the real places
  {v : Fock.fockSpace (realSigns E (homSigns s s'))} [SemilocalField F]
  {A : Set (FinPlace E)} {φ : Matrix n' n F → ℂ} {π : 𝔸f E →+* F} {U : Set (Matrix n' n F)}
  (𝔠 : SplitTameChar E μ)

section

omit [WeilData E]

/-- The components at `P` of the matrix of `g`, entry by entry, form `atPlaces P g`. -/
lemma map_evalPlaces_eq_atPlaces {P : Finset (FinPlace E)} (g : Gf E n) :
    g.val.val.map (evalPlaces P) = (atPlaces P g).val :=
  rfl

/-- The components at `P` of the conjugate transpose of `g` are those of `g⁻¹`. -/
lemma transpose_map_star_eq_atPlaces_inv {P : Finset (FinPlace E)} (g : Gf E n) :
    (g.val.val.map ((evalPlaces P).comp (starRingEnd (𝔸f E))))ᵀ = (atPlaces P g⁻¹).val := by
  have h_inv : g⁻¹.val.val = g.val.valᴴ := New.U.inv_val_eq_conjTranspose g
  rw [← map_evalPlaces_eq_atPlaces, h_inv]
  rfl

/-- The components at `P` of the conjugate transpose of `g` are those of `g⁻¹`. The components of
`g` at `P` form `atPlaces P g`. -/
lemma atPlaces_star {P : Finset (FinPlace E)} (g : Gf E n) :
    (g.val.val.map ((evalPlaces P).comp (starRingEnd (𝔸f E))))ᵀ = (atPlaces P g⁻¹).val ∧
    g.val.val.map (evalPlaces P) = (atPlaces P g).val :=
  ⟨transpose_map_star_eq_atPlaces_inv g, map_evalPlaces_eq_atPlaces g⟩

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
/-- If `π` reads the components at `A` and `φ` is locally constant of compact support and
vanishes outside `U`, then `y ↦ φ (π y)` is Schwartz–Bruhat above `A`. -/
lemma ReadsAt.isSchwartzBruhat (h_read : ReadsAt A π) (hφ : φ ∈ schwartzBruhat U) :
    IsSchwartzBruhat A fun x : n' × n → 𝔸f E ↦ φ ((vecToMatrix x).map π) := by
  obtain ⟨-, -, hπ, σ, hσ, h_section, h_idem⟩ := h_read
  -- The compact set is the image of `tsupport φ` under the section `σ`, entry by entry.
  refine ⟨fun x ↦ ?_, hφ.1.comp_continuous (by continuity),
    (fun y ↦ σ ∘ matrixToVec y) '' tsupport φ,
    hφ.2.1.image (by fun_prop [matrixToVec]), fun x hx ↦ ?_⟩
  · -- `π (idem A * a) = π (σ (π a)) = π a`.
    simp [vecToMatrix, Matrix.map, ← h_idem, h_section]
  · exact ⟨(vecToMatrix x).map π, subset_closure hx, funext fun p ↦ h_idem (x p)⟩

end

/-! ### A growth bound, and linearity of the theta integral -/

/-- The theta integral over [U(T)] of the datum `localDatum` with real part `v`, the function `Φ`
at the ramified places `𝔠.ramifiedPlaces` of the split tame character `𝔠`, and the vacuum elsewhere;
both characters are `rankTwist 𝔠.character⁻¹ n`, that is ν⁻¹υ^⌊n/2⌋ with n = rk S and υ restricted
to the norm-one ideles. -/
noncomputable abbrev thetaLarge
    (v : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns s s'))))
    (Φ : Matrix n' n (LocProd 𝔠.ramifiedPlaces) → ℂ) : G E s → ℂ :=
  thetaIntegral S T (rankTwist 𝔠.character⁻¹ n) (rankTwist 𝔠.character⁻¹ n)
    (localDatum S T v Φ 𝔠.readsAt)

/-- There are B and C with |θ^{S,T}_{α,β}(f)(g,h)| ≤ C·ht(g)^B for all characters α, β and all
g, h: polynomial growth in g, uniformly in h. -/
def IsTargetBounded (f : 𝒮 (S.hom T)) : Prop :=
  ∃ (B : ℕ) (C : ℝ), ∀ (α β : AutChar E) (g : G E s) (h : G E s'),
    ‖pairTheta S T α β f (g, h)‖ ≤ C * S.height g ^ B

/-- On the data that satisfy `New.Exchange.IsTargetBounded` the theta integral agrees with a linear
map. -/
lemma exists_linear_thetaIntegral (α β : AutChar E) :
    ∃ Λ : 𝒮 (S.hom T) →ₗ[ℂ] G E s → ℂ, ∀ {f : 𝒮 (S.hom T)}, IsTargetBounded S T f →
      Λ f = thetaIntegral S T α β f := by
  -- Integration is linear on the subspace of integrable functions; extend it to a linear form
  -- `I` on all functions and apply `I` to the kernel, which is linear in `f`.
  let L : Submodule ℂ (G E s' → ℂ) := .ofLinearComb {u | Integrable u T.quotMeasure}
    ⟨0, integrable_zero (G E s') ℂ T.quotMeasure⟩ fun _ hu _ hv a b ↦ (hu.smul a).add (hv.smul b)
  let int : L →ₗ[ℂ] ℂ :=
    { toFun u := ∫ h, (u : G E s' → ℂ) h ∂T.quotMeasure
      map_add' u v := integral_add u.property v.property
      map_smul' c u := integral_smul c (u : G E s' → ℂ) }
  obtain ⟨I, hI⟩ := int.exists_extend
  use .pi fun g ↦ I ∘ₗ .pi fun h ↦ θ (S.hom T) ∘L pairWeil S T α β (g, h)
  intro f ⟨B, C, h_bound⟩
  funext g
  -- under `IsTargetBounded S T f` the kernel is bounded in `h`, hence integrable
  have h_int : Integrable (fun h ↦ pairTheta S T α β f (g, h)) T.quotMeasure :=
    .of_bound (by fun_prop) _ (.of_forall (h_bound α β g))
  exact LinearMap.congr_fun hI ⟨_, h_int⟩

/-- The product of the local fields at the nonempty set `𝔠.ramifiedPlaces` is nontrivial. -/
instance : Nontrivial (LocProd 𝔠.ramifiedPlaces) := Pi.nontrivial_at 𝔠.nonempty.coe_sort.some

variable {S T} {α β : AutChar E} {f : 𝒮 (S.hom T)} {g : Gf E n} {h : Gf E n'}

/-! ### The action of the two unitary groups -/

/-- Let `π` read the components at `A` and `φ` be locally constant of compact support. The datum
`localDatum S T v φ r` has real part `v`, finite part `y ↦ φ (π y)` at the places of `A` and the
vacuum elsewhere. A pair `(g, h)` of finite elements that stabilise the standard lattices moves
`φ` to `x ↦ φ (π(h⁻¹) * x * π(g))`, up to the scalar `α(det h) · β(det g)⁻¹`. -/
lemma ReadsAt.pairWeil_localDatum_of_mem_stdLevel (r : ReadsAt A π) (hφ : φ ∈ schwartzBruhat U)
    (hg : g ∈ stdLevel E n) (hh : h ∈ stdLevel E n') :
    pairWeil S T α β (g, h) (localDatum S T v φ r) =
      (α.val (detFin s' h) * (β.val (detFin s g))⁻¹).val •
        localDatum S T v (fun x : Matrix n' n F ↦ φ (h⁻¹.val.val.map π * x * g.val.val.map π))
          r := by
  -- An integral pair moves the function `φ` and the vacuum together
  -- (`pairWeil_schrodingerOp_of_mem`), and it acts on the vacuum by the stated scalar
  -- (`pairWeil_eq_smul_of_projOn_eq`); `π` is multiplicative on matrices.
  simp [pairWeil_schrodingerOp_of_mem r.disjoint_star (hΨ := r.isSchwartzBruhat hφ),
    pairWeil_eq_smul_of_projOn_eq ⊤, hg, hh]

/-- Acting on the datum by a pair `p` translates the theta integral on the right by `p.1`; the
component `p.2` in the group integrated over has no effect. -/
lemma thetaIntegral_pairWeil (p : G E s × G E s') (g : G E s) :
    thetaIntegral S T α β (pairWeil S T α β p f) g = thetaIntegral S T α β f (g * p.1) := by
  -- `thetaIntegral` is the lift of the constant function `1` for the kernel with its two groups
  -- swapped; `lift_equivariant` moves `p.1` to the argument, and translating `1` by `p.2` changes
  -- nothing.
  have h_lift :
      lift (pairThetaKer S T α β).swap f (fun _ : G E s' ↦ 1) (g * p.1) =
        lift (pairThetaKer S T α β).swap (pairWeil S T α β (p.1, p.2) f) (fun _ : G E s' ↦ 1) g :=
    (pairThetaKer S T α β).swap.lift_equivariant (isAutomorphic_const T 1) f p.2 p.1 g
  simpa [lift, thetaIntegral, pairTheta] using h_lift.symm

/-! ### Automorphy, and data that satisfy the growth bound -/

/-- Under `New.Exchange.IsTargetBounded` the theta integral is continuous and left invariant under
the rational points. -/
lemma IsTargetBounded.isAutFunction_thetaIntegral (hf : IsTargetBounded S T f) :
    IsAutFunction S (thetaIntegral S T α β f) := by
  obtain ⟨B, C, h_bound⟩ := hf
  refine ⟨isCoherentWith.continuous_iff.mpr fun K hK ↦ ?_, fun γ hγ g ↦ ?_⟩
  · -- on a compact set `K` the kernel is bounded by a constant: dominated convergence
    obtain ⟨D, hD⟩ := S.exists_mul_height_pow_le hK C
    have h_dom (g : G E s) (hg : g ∈ K) (h : G E s') : ‖pairTheta S T α β f (g, h)‖ ≤ D :=
      (h_bound α β g h).trans (hD g 1 (one_mem _) (by simpa using hg))
    exact continuousOn_of_dominated (by fun_prop) (fun g hg ↦ .of_forall (h_dom g hg))
      (integrable_const D) (.of_forall (by fun_prop))
  · -- the kernel itself is left invariant under the rational points
    simp [thetaIntegral, pairTheta, (pairThetaKer S T α β).theta_rat_mul, hγ]

/-- Let `π` read the components at `A` in a ring `F ≠ 0`. If `v` has all moments finite and `φ` is
locally constant of compact support and vanishes off the right invertible matrices, then the datum
`localDatum S T v φ r` (real part `v`, `y ↦ φ (π y)` at `A`, the vacuum elsewhere) satisfies
`New.Exchange.IsTargetBounded`. -/
lemma ReadsAt.isTargetBounded (r : ReadsAt A π) [Nontrivial F] (hv : IsSchwartzVector v)
    (hφ : φ ∈ schwartzBruhat fun x : Matrix n' n F ↦ HasLeftInv xᵀ) :
    IsTargetBounded S T (localDatum S T v φ r) := by
  -- `pairTheta_decay_of_onto` bounds `‖θ (g, h)‖ * height h ^ N` by
  -- `C * fockMoment M v * height g ^ B`; take `N = 0` and the trivial characters.
  have h_onto (y : n' × n → 𝔸f E) (hy : φ ((vecToMatrix y).map π) ≠ 0) :
      HasLeftInv ((vecToMatrix y).map π)ᵀ :=
    hφ.2.2 hy
  obtain ⟨B, M, C, h_decay⟩ :=
    pairTheta_decay_of_onto S T 1 1 π r.disjoint_star (r.isSchwartzBruhat hφ) h_onto 0
  refine ⟨B, C * (Fock.fockMoment M v).toReal, fun α β g h ↦ ?_⟩
  -- The characters only contribute a factor of modulus one to the kernel.
  simpa [pairWeil, pairTheta, Circle.norm_coe] using h_decay v g h (hv M)

end New.Exchange
