import Lib.DiscreteSeries.Bruhat.ComplexPlace
import Lib.SiegelWeil.Formula.LagrangianZeroTerms
import New.OneLift.ComparisonOperator.GluedLattices
import New.OneLift.FalseLifts.BottomOfTower

/-!
# Vanishing of theta descents from W to W plus hyperbolic planes

`New.SiegelWeil.DescentsVanish W V a S Y` says that all theta descents of a function `Y` on
`U(V)(𝔸)` to `U(W)(𝔸)` vanish. The descents are twisted by the character `a` of `U(1)`, with data
that are the vacuum at the places of `S` and their conjugates. This file proves the inductive step
`New.SiegelWeil.descentsVanish_add_planes`: the vanishing passes from `W` to `W'`, the sum of `W`
and hyperbolic planes, each plane multiplying `a` by `New.WeilData.upsilonU1`. This holds when `V`
is definite of large rank and `Y` is killed by a Hecke polynomial at a suitable point.

## Main definitions and results

* `New.SiegelWeil.descentsVanish_add_planes`: The inductive step of the tower of descents.
* `New.SiegelWeil.eq_zero_of_heckePolyOp_eq_zero`: Small roots: let `F` be a bounded function on
  the adelic unitary group of signs `t`, of rank `card m`, that is spherical at the split place
  `w` of norm `q`. If the Hecke polynomial at `w`, taken at a point `X` with
  `q ^ (card m + 1) * |X| ≤ 1`, kills `F`, then `F` is zero.

## The steps of the argument

* The inductive step `New.SiegelWeil.descentsVanish_add_planes`: the zero term contributes nothing
  (`New.SiegelWeil.DescentsVanish.integral_homSlice_eq_zero`), the rest is bounded
  (`New.SiegelWeil.exists_norm_theta_sub_zeroTerm_le`), the descent inherits a Hecke equation
  (`New.SiegelWeil.lift_eq_zero_of_heckePolyOp_eq_zero`), and its root is too small
  (`New.SiegelWeil.eq_zero_of_heckePolyOp_eq_zero`).

Notions from other files:
* `New.pairWeil`: the Weil representation of U(W) × U(V) on the data space 𝒮(Hom(W, V)), twisted by
  two characters of U(1); `New.Space.θ` is the theta functional on that space.
* `New.Space.projOn`: the projection whose fixed vectors are the data that are the vacuum at the
  places of a set `S` and their conjugates. For `S` the complement of the places of the level and
  their conjugates, these are the test vectors.
* `New.heckePolyOp`: the operator ∑ (−X)^i q^(i choose 2) T_{w,i}, q the order of the residue field
  at w; `New.sphericalAt π w` is the space of vectors spherical at w.
* `New.Space.Splitting`: `D : W'.Splitting W p` writes `W'` as `W` plus `card p` hyperbolic planes,
  with isotropic frame `D.k`; it is adapted (`IsBaseAdapted D`) if its adelic frames are orthonormal
  at the infinite and integral at the finite places. `D.homSource V` is the splitting of
  `Hom(W', V)` that it induces, `D.zeroTerm` is the constant term along the isotropic frame, and the
  slice `D.homSlice V x` is the zero term of the translate by `x`, a datum on `Hom(W, V)`.

## Relation to the literature

See `New.OneLift.FalseLifts.PeriodsOfFalseLifts` for related work.
-/

namespace New.SiegelWeil

open Matrix MeasureTheory WeilData Exchange Space Splitting Finset Fintype Real G Fock

variable {E r n m p : Type} [Field E] [CMType E] [WeilData E] [Fintype r] [DecidableEq r]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p] {s : r → ℤˣ}
  {t : m → ℤˣ} {W : Space E r s} {W' : Space E m t} {V : Space E n 1} {a : AutChar E}
  {Y : G E (1 : n → ℤˣ) → ℂ}

omit [WeilData E] in
/-- Small roots: let `F` be a bounded function on the adelic unitary group of signs `t`, of rank
`card m`, that is spherical at the split place `w` of norm `q`. If the Hecke polynomial at `w`,
taken at a point `X` with `q ^ (card m + 1) * |X| ≤ 1`, kills `F`, then `F` is zero. -/
lemma eq_zero_of_heckePolyOp_eq_zero {F : G E t → ℂ} {w : FinPlace E} {X : ℂ} (hw : w.IsSplit)
    (hF_sph : F ∈ sphericalAt (finRightRep E t) w) (hF : heckePolyOp (finRightRep E t) hw X F = 0)
    (hX : w.q ^ (card m + 1) * ‖X‖ ≤ 1) (hF_bdd : BddAbove (.range fun g : G E t ↦ ‖F g‖)) :
    F = 0 := by
  -- The relation `hF` is a sum of translations, one for each subspace `U` of `𝔽_w ^ m`, and the
  -- term `U = ⊥` has coefficient one. The total weight of all terms is below two, so `‖F‖` is at
  -- most a combination of its translates of total weight below one.
  let cosetRep (U : Submodule (ResField w) (m → ResField w)) : G E t :=
    (1, ofSplitPlace hw (transposeGL (basicCosetRep U)))
  have h_rel (g : G E t) : ∑ U, heckePolyCoeff X U * F (g * cosetRep U) = 0 := by
    simpa [heckePolyOp_eq_sum hw hF_sph] using congrFun hF g
  have h_geom : (∑ j ∈ range (card m), w.q ^ j : ℝ) ≤ w.q ^ card m :=
    mod_cast (Nat.geomSum_lt w.one_lt_q fun _ ↦ mem_range.1).le
  have h_half : w.q ^ card m * ‖X‖ ≤ 1 / 2 := by
    have hq : (2 : ℝ) ≤ w.q := mod_cast w.one_lt_q
    rw [pow_succ', mul_assoc] at hX
    nlinarith [(by positivity : 0 ≤ w.q ^ card m * ‖X‖)]
  -- The `q`-binomial theorem at the point `-‖X‖` computes the total weight.
  have h_weight : ∑ U : Submodule (ResField w) (m → ResField w), ‖heckePolyCoeff X U‖ < 2 :=
    calc _ = ∏ j ∈ range (card m), (1 + w.q ^ j * ‖X‖) := by
          simpa [← Complex.ofReal_inj, heckePolyCoeff, card_ResField] using
            q_binomial_submodule m (ResField w) ⊤ (-‖X‖)
      _ ≤ exp (∑ j ∈ range (card m), w.q ^ j * ‖X‖) := prod_one_add_le_exp_sum _ (by bound)
      _ ≤ exp (1 / 2) := by grw [← sum_mul, h_geom, h_half]
      _ < 2 := (lt_log_iff_exp_lt two_pos).1 (by linarith [log_two_gt_d9])
  -- Isolate the term `U = ⊥` of the relation at `g / cosetRep ⊥`.
  have h_isolate (g : G E t) :
      2 * ‖F g‖ ≤ ∑ U, ‖heckePolyCoeff X U‖ * ‖F (g / cosetRep ⊥ * cosetRep U)‖ := by
    simpa [h_rel, two_mul, le_sub_iff_add_le] using
      norm_sum_le (univ.erase ⊥) fun U ↦ heckePolyCoeff X U * F (g / cosetRep ⊥ * cosetRep U)
  exact funext fun g ↦ norm_le_zero_iff.1 (maximum_principle hF_bdd (heckePolyCoeff X)
    (fun g U ↦ g / cosetRep ⊥ * cosetRep U) h_weight h_isolate g)

/-- The descent of a function `Y` on `U(T)(𝔸)` to `U(S)(𝔸)` by the datum `φ` is the integral of `Y`
against the theta kernel of `φ` over the adelic quotient of `U(T)`. -/
lemma lift_pairThetaKer_swap_apply {s' : n → ℤˣ} (S : Space E r s) (T : Space E n s')
    (a b : AutChar E) (φ : 𝒮 (S.hom T)) (Y : G E s' → ℂ) (g : G E s) :
    lift (pairThetaKer S T a b).swap φ Y g =
      ∫ h : G E s', θ (S.hom T) (pairWeil S T a b (g, h) φ) * Y h ∂T.quotMeasure :=
  rfl

/-- Let `D` be an adapted splitting of `W'` into `W` and hyperbolic planes: its adelic frames are
orthonormal at the infinite and integral at the finite places. If the datum `φ` on `Hom(W', V)` is
the vacuum at the places of `S`, then so is its slice `D.homSlice V 0 φ`, a datum on `Hom(W, V)`,
namely the zero term of `φ` along the isotropic frame. -/
lemma projOn_homSlice_zero (D : W'.Splitting W p) [IsBaseAdapted D] {S : Set (FinPlace E)}
    {φ : 𝒮 (W'.hom V)} (hφ : ((W'.hom V).projOn S) φ = φ) :
    projOn (W.hom V) S (D.homSlice V 0 φ) = D.homSlice V 0 φ := by
  have h_coord : finCoord (0 : n × p → 𝔸 E) = 0 := by simp [finCoord, funext_iff]
  simpa [hφ, slice_zero, homSlice, boxIndicator, h_coord] using
    ((isAdapted_homSource D V).omega_projOn_adelic_of_isMixedLaw isMixedLaw_slice 0 φ
      (S := S)).symm

/-- Let `D` split `W'` into `W` and `card p` hyperbolic planes, with adelic frames that are
orthonormal at the infinite and integral at the finite places (`IsBaseAdapted`). Suppose that the
integral of `Y` over the adelic quotient of `U(V)` against the theta kernel of the pair `W, V`,
twisted by `a (det h)`, is zero for every datum that is vacuum at `S` (`DescentsVanish`). Then for
such a datum `φ` on `Hom(W', V)` and every `g` in `U(W')(𝔸)`, the integral of `Y` against the zero
term of the kernel of `φ` is zero. -/
lemma DescentsVanish.integral_homSlice_eq_zero {S : Set (FinPlace E)}
    (h_vanish : DescentsVanish W V a S Y) (D : W'.Splitting W p) [IsBaseAdapted D]
    {φ : 𝒮 (W'.hom V)} (hφ : ((W'.hom V).projOn S) φ = φ) (g : G E t) :
    ∫ h : G E (1 : n → ℤˣ), θ (W.hom V)
      (D.homSlice V 0 (pairWeil W' V (a * upsilonU1 ^ card p) 1 (g, h) φ)) * Y h
      ∂V.quotMeasure = 0 := by
  -- Iwasawa: `g κ` is a unipotent element times a Levi element `(u, g₀)`, with `κ` in the maximal
  -- compact subgroup.
  obtain ⟨κ, hκ, u, -, -, c, z, g₀, h_iwasawa : g * κ = D.radicalElement c z * D.levi (u, g₀)⟩ :=
    D.iwasawa g (wt := 0)
  have h_factor (h : G E (1 : n → ℤˣ)) :
      (g, h) = (D.radicalElement c z, 1) * (D.levi (u, g₀), h) * (κ⁻¹, 1) := by simp [← h_iwasawa]
  -- The translate of `φ` by `κ⁻¹` and its slice at `0` are the vacuum at `S`.
  let φ' : 𝒮 (W'.hom V) := pairWeil W' V (a * upsilonU1 ^ card p) 1 (κ⁻¹, 1) φ
  have hφ' : projOn (W'.hom V) S φ' = φ' :=
    projOn_pairWeil hφ (κ⁻¹, 1) (by simp [mem_stdLevel_iff.1 hκ.2])
  have h_descent : ∫ h : G E (1 : n → ℤˣ),
      θ (W.hom V) (pairWeil W V a 1 (g₀, h) (D.homSlice V 0 φ')) * Y h ∂V.quotMeasure = 0 :=
    congrFun (h_vanish _ (projOn_homSlice_zero D hφ')) g₀
  -- On the slice at `0` the unipotent element acts trivially and the Levi element by a scalar
  -- `ν` times `pairWeil W V a 1 (g₀, h)`, so the integral is a multiple of the descent of `Y`
  -- to `W` at `g₀`.
  let ν : ℂ := (((1 : AutChar E).spaceChar (card n)).val u.det).val⁻¹ * √(ideleAbs u.det) ^ card n
  have h_slice (h : G E (1 : n → ℤˣ)) :
      D.homSlice V 0 (pairWeil W' V (a * upsilonU1 ^ card p) 1 (g, h) φ) =
        ν • pairWeil W V a 1 (g₀, h) (D.homSlice V 0 φ') := by
    simp only [h_factor h, map_mul, mul_apply_eq_comp, homSlice_radicalElement,
      homSlice_levi, Matrix.mul_zero, Matrix.zero_mul]
    simp [φ', ν]
  simp only [h_slice, map_smul, smul_eq_mul, mul_assoc, integral_const_mul, h_descent, mul_zero]

/-- Let `D` split one hyperbolic plane off `W'`, with isotropic vector `k`. The induced splitting
`D.homSource V` of `Hom(W', V)` has the adelic frame `kAdelic`, and `ϱ` is the action of
translations on data. The theta functional minus its zero term along that frame is, at `φ`, the
mean over `b` of `θ φ - θ (ϱ (kAdelic b) φ)`, so a bound `B` for these differences bounds it. -/
lemma norm_theta_sub_zeroTerm_le (D : W'.Splitting W Unit) {φ : 𝒮 (W'.hom V)} {B : ℝ}
    (h_diff : ∀ b : n × Unit → 𝔸 E, ‖θ (W'.hom V) φ -
      θ (W'.hom V) (ϱ (W'.hom V) ((D.homSource V).kAdelic *ᵥ b) φ)‖ ≤ B) :
    ‖(θ (W'.hom V) - θ (W.hom V) ∘L (D.homSource V).zeroTerm) φ‖ ≤ B := by
  have h_periodic : IsContPeriodic (New.ratVectors E (n × Unit))
      fun b ↦ φ ((D.homSource V).kAdelic *ᵥ b) := by
    simpa using (D.homSource V).isContPeriodic_along_k φ 0
  have h_mean : (θ (W'.hom V) - θ (W.hom V) ∘L (D.homSource V).zeroTerm) φ =
      quotMean (New.ratVectors E (n × Unit)) fun b ↦ θ (W'.hom V) φ -
        θ (W'.hom V) (ϱ (W'.hom V) ((D.homSource V).kAdelic *ᵥ b) φ) := by
    simp [quotMean, integral_sub, zeroTerm_apply, h_periodic.integrable_out]
  simpa only [h_mean] using norm_quotMean_le _ h_diff

/-- Let `D` split one hyperbolic plane off `W'`, with isotropic vector `k`. The theta functional
minus its zero term along `k` is invariant under the translations by the rational maps
`z kᴴ J`, where `J` is the matrix of `W'`. -/
lemma theta_sub_zeroTerm_rho_ratMap (D : W'.Splitting W Unit) (z : Matrix n Unit E)
    (φ : 𝒮 (W'.hom V)) :
    (θ (W'.hom V) - θ (W.hom V) ∘L (D.homSource V).zeroTerm)
        (ϱ (W'.hom V) (matrixToVec (V.ratMap W' (z * D.kᴴ * W'.J))) φ) =
      (θ (W'.hom V) - θ (W.hom V) ∘L (D.homSource V).zeroTerm) φ := by
  have h_theta : θ (W'.hom V) (ϱ (W'.hom V) (matrixToVec (V.ratMap W' (z * D.kᴴ * W'.J))) φ) =
      θ (W'.hom V) φ := by simp [← vecAtPoint_hom]
  -- The translation lies in the span of the isotropic frame of `Hom(W', V)`.
  have h_span : matrixToVec (V.ratMap W' (z * D.kᴴ * W'.J)) =
      (D.homSource V).kAdelic *ᵥ matrixToVec (V.dualFrame.1 * V.coordMatrix 1 z) := by
    rw [homSource_kAdelic, kronecker_mulVec_eq_matrixToVec]
    simp [Space.ratMap, W'.map_J, lCoord, kAdelic, coordMatrix, Matrix.mul_assoc]
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, h_theta]
  rw [h_span, zeroTerm_rho_kAdelic]

omit [WeilData E] in
/-- Let `D` split one hyperbolic plane off `W'`, with isotropic vector `k`. The height of a point
`g` is the inverse of the first minimum, cut off at `1`, of the space moved by `g` (`W'.move g`).
For every point `g` there is a rational `γ` such that, if that height exceeds `2`, then `k` lies in
the lattice of the space moved by `γ g` and has length at most `2 / height g` there. -/
lemma exists_col_k_mem_latticeBall (D : W'.Splitting W Unit) (g : G E t) :
    ∃ γ : U W'.J, 2 < W'.height g → ∀ j : Unit,
      D.k.col j ∈ (W'.move (W'.ratEmbed γ * g)).latticeBall (2 / W'.height g) := by
  obtain h_low | h_high := le_or_gt (W'.height g) 2
  · exact ⟨1, fun h ↦ absurd h h_low.not_gt⟩
  -- By Witt's theorem a rational `γ` carries a short isotropic vector `ξ` at `g` to `k`.
  obtain ⟨ξ, hξ_ne, hξ_iso, hξ_short⟩ := W'.exists_short_isotropic h_high
  have hξ_inv : HasLeftInv ξ := .of_ne_zero fun h_col ↦ hξ_ne (ext_col fun () ↦ h_col)
  obtain ⟨γ, hγ⟩ : ∃ γ : U W'.J, (γ : Matrix m m E) * ξ = D.k :=
    W'.witt hξ_inv ⟨_, D.gram_lk⟩ (hξ_iso.trans D.gram_kk.symm)
  refine ⟨γ, fun _ j ↦ ?_⟩
  -- `γ` carries the lattice and the length at `g` to those at `γ g`.
  obtain ⟨h_mem, h_short⟩ := hξ_short j
  rw [← hγ]
  change (γ : Matrix m m E) *ᵥ ξ.col j ∈ _
  constructor
  · rw [← SetLike.mem_coe, baseLattice_move_ratEmbed_mul]
    exact Set.mem_image_of_mem _ h_mem
  · rwa [norm_archCoords_move_ratEmbed_mul_mulVec]

open IsDualFamily in
/-- Let `D` split one hyperbolic plane off `W'`, with isotropic vector `k`, and let the columns `dⱼ`
of `d` be a basis of `V`. Let `θ₀` be the zero term of the theta functional `θ` along the isotropic
frame of `D.homSource V`, the splitting of `Hom(W', V)` induced by `D`, and let `ϱ` be the action by
translations on data. Then the mean of `(θ - θ₀) (ϱ u φ)` over the adelic points `u` of the span of
the maps `dⱼ ⟨k, ·⟩` (`rankOneMaps`), modulo the rational ones, is zero. -/
lemma subspaceMean_theta_sub_zeroTerm_eq_zero (D : W'.Splitting W Unit) {d : Matrix n n E}
    (hd : IsUnit d) (φ : 𝒮 (W'.hom V)) :
    (W'.hom V).subspaceMean (Submodule.span E (Set.range (W'.rankOneMaps d D.k).col))
      (fun u : n × m → 𝔸 E ↦
        (θ (W'.hom V) - θ (W.hom V) ∘L (D.homSource V).zeroTerm) (ϱ (W'.hom V) u φ)) = 0 := by
  -- The span is that of the isotropic frame of `D.homSource V`; `θ₀` is the mean of `θ` along it.
  let D' : (W'.hom V).Splitting (W.hom V) (n × Unit) := D.homSource V
  let L : Submodule E (n × m → E) := .span E (.range D'.k.col)
  have h_frame : L = .span E (.range (W'.rankOneMaps V.J⁻¹ D.k).col) := rfl
  have h_mem (γ : n × m → E) :
      γ ∈ L ↔ ∃ z : Matrix n Unit E, matrixToVec (z * (D.kᴴ * W'.J)) = γ := by
    rw [h_frame]
    exact mem_span_rankOneMaps_iff (isUnit_nonsing_inv_iff.2 V.isUnit_J) γ
  have h_span : Submodule.span E (Set.range (W'.rankOneMaps d D.k).col) = L :=
    Submodule.ext fun γ ↦ (mem_span_rankOneMaps_iff hd γ).trans (h_mem γ).symm
  have h_sum (b : n × Unit → 𝔸 E) :
      ∑ i : n × Unit, b i • (W'.hom V).vecAtPoint (D'.k.col i) = D'.kAdelic *ᵥ b := by
    have h_col (i : n × Unit) : (W'.hom V).vecAtPoint (D'.k.col i) = D'.kAdelic.col i := rfl
    ext1 j
    simp [h_col, mulVec, dotProduct, mul_comm]
  have h_inv : ∀ γ ∈ L, ∀ f : 𝒮 (W'.hom V),
      (θ (W'.hom V) - θ (W.hom V) ∘L D'.zeroTerm) (ϱ (W'.hom V) ((W'.hom V).vecAtPoint γ) f) =
        (θ (W'.hom V) - θ (W.hom V) ∘L D'.zeroTerm) f := by
    intro γ hγ f
    obtain ⟨z, rfl⟩ := (h_mem γ).1 hγ
    rw [vecAtPoint_hom, ← Matrix.mul_assoc]
    exact theta_sub_zeroTerm_rho_ratMap D z f
  have h_int : Integrable (fun b : (n × Unit → 𝔸 E) ⧸ New.ratVectors E (n × Unit) ↦
      φ (D'.kAdelic *ᵥ b.out)) (Measure.addHaarMeasure ⊤) := by
    simpa using (D'.isContPeriodic_along_k φ 0).integrable_out
  have h_term (b : n × Unit → 𝔸 E) :
      (θ (W'.hom V) - θ (W.hom V) ∘L D'.zeroTerm) (ϱ (W'.hom V) (D'.kAdelic *ᵥ b) φ) =
        φ (D'.kAdelic *ᵥ b) - D'.zeroTerm φ 0 := by
    simp [zeroTerm_rho_kAdelic, theta_apply]
  have h_iso : ∀ γ ∈ L, ∀ η ∈ L, star γ ⬝ᵥ (W'.hom V).J *ᵥ η = 0 := by
    simpa only [h_frame] using isotropic_span_rankOneMaps (.inr D.gram_kk)
  rw [h_span, subspaceMean_span_range _ _ (isContPeriodic_ratPoints h_iso h_inv φ)]
  simp only [h_sum, h_term]
  rw [quotMean, integral_sub h_int (integrable_const _), zeroTerm_apply]
  simp [quotMean]

/-- Let `D` split one hyperbolic plane off `W'`, and let `φ = v_P ⊗ Ψ ⊗ vac` be the datum made of
the Fock vector of a polynomial `P`, a function `Ψ` that is Schwartz–Bruhat at a set `A` of finite
places disjoint from its conjugate, and the vacuum at the other places. Twist the theta kernel by
`χ (det h)`, for any automorphic character `χ` of `U(1)`. After a rational translation `γ` of
`g ∈ U(W')(𝔸)`, the kernel of `φ` minus its zero term along the isotropic frame is bounded
uniformly in `g` and in `h ∈ U(V)(𝔸)`. -/
lemma exists_norm_theta_sub_zeroTerm_le (D : W'.Splitting W Unit) (χ : AutChar E)
    {A : Set (FinPlace E)} (hA : A.IsConjDisjoint)
    (P : MvPolynomial (NumberField.InfinitePlace E × n × m) ℂ) (Ψ : (n × m → 𝔸f E) → ℂ)
    [IsSchwartzBruhat A Ψ] :
    ∃ K : ℝ, ∀ g : G E t, ∃ γ ∈ W'.Γ, ∀ h : G E (1 : n → ℤˣ),
      ‖(θ (W'.hom V) - θ (W.hom V) ∘L (D.homSource V).zeroTerm) (pairWeil W' V χ 1 (γ * g, h)
        (integrated (W'.hom V) (polyVector (realSigns E (homSigns t 1)) P)
          (schrodingerOp (W'.hom V) A Ψ (vacElem (W'.hom V)))))‖ ≤ K := by
  -- The functional `ℓ = θ - θ₀` grows like a power of the height of `g`. Where that height exceeds
  -- two, `D.k` is short after a rational translation, and the decay cancels the growth. The
  -- estimate `exists_norm_pairWeil_schrodingerOp_mul_pow_le` treats small and large heights
  -- together.
  let ℓ : 𝒮 (W'.hom V) →L[ℂ] ℂ := θ (W'.hom V) - θ (W.hom V) ∘L (D.homSource V).zeroTerm
  let v : fockSpace (realSigns E (homSigns t 1)) := polyVector (realSigns E (homSigns t 1)) P
  obtain ⟨C, i, h_growth⟩ := (pairThetaKer W' V χ 1).swap.moderate_growth
  obtain ⟨c, h_basis⟩ := V.exists_short_basis_matrix
  obtain ⟨C', h_decay⟩ := exists_norm_pairWeil_schrodingerOp_mul_pow_le (S := W') (T := V) (p := n)
    (q := Unit) χ 1
    hA (Ψ := Ψ) vacElem_mem_finitePart 0 i (C + C) c
  refine ⟨C' * (fockMoment i v).toReal, fun g ↦ ?_⟩
  obtain ⟨γ, h_frame⟩ := exists_col_k_mem_latticeBall D g
  refine ⟨W'.ratEmbed γ, ⟨γ, rfl⟩, fun h ↦ ?_⟩
  set g' : G E t := W'.ratEmbed γ * g
  -- `γ` is rational, so the kernel at `g' = γ g` is the kernel at `g`.
  have h_growth' (φ : 𝒮 (W'.hom V)) : ‖θ (W'.hom V) (pairWeil W' V χ 1 (g', h) φ)‖ ≤
      C * ‖φ‖ * (V.height h * W'.height g) ^ i :=
    (congrArg norm ((pairThetaKer W' V χ 1).theta_rat_mul _ ⟨γ, rfl⟩ g)).trans_le (h_growth h g φ)
  have h_norm (φ : 𝒮 (W'.hom V)) :
      ‖ℓ (pairWeil W' V χ 1 (g', h) φ)‖ ≤ (C + C) * ‖φ‖ * (V.height h * W'.height g) ^ i := by
    refine norm_theta_sub_zeroTerm_le D fun b ↦ ?_
    grw [rho_pairWeil, norm_sub_le, h_growth', h_growth']
    simp [add_mul, Heisenberg.Rep.norm_map]
  -- `d` is a basis of `V` in the lattice at `h`, of bounded lengths.
  obtain ⟨d, hd⟩ := h_basis h
  have h_pair (h_high : 2 < W'.height g) : IsShortPair g' h ℓ Ψ d.val D.k (c * V.height h)
      (2 / W'.height g) (c * V.height h * (2 / W'.height g)) :=
    { short_target := hd
      short_source := h_frame h_high
      mul_le := le_rfl
      isotropic := .inr D.gram_kk
      invariant := theta_sub_zeroTerm_rho_ratMap D
      ne_zero_or_mean_eq_zero := .inr (subspaceMean_theta_sub_zeroTerm_eq_zero D d.isUnit) }
  have h_est : ‖ℓ (pairWeil W' V χ 1 (g', h)
        (integrated (W'.hom V) v (schrodingerOp (W'.hom V) A Ψ (vacElem (W'.hom V)))))‖ * W'.height
          g ^ 0 ≤
      C' * (fockMoment (0 + i) v).toReal * V.height h ^ (0 + 2 * i) :=
    h_decay v g' h ℓ (V.height h) (W'.height g) (fockMoment_polyVector_ne_top _ P)
      (one_le_height ..) (W'.height_pos g) h_norm fun h_high ↦ ⟨_, _, _, _, h_pair h_high⟩
  -- The height on the definite space `V` is one.
  have h_height : V.height h = 1 := by rw [height, firstMinimum_move_eq_one (by simp), inv_one]
  simpa only [h_height, pow_zero, one_pow, mul_one, zero_add] using h_est

/-- Let `D` be an adapted splitting of `W'` into `W` and one hyperbolic plane, and let `A` be a set
of finite places disjoint from its conjugate. If the descents of the automorphic function `Y` to
`W`, twisted by the character `a`, vanish for the data that are the vacuum off `A` and its
conjugate, then the descent of `Y` to `W'` by a datum `v_P ⊗ Ψ ⊗ vac` is bounded. This datum is the
vacuum `vacElem`, acted on by the function `Ψ`, Schwartz–Bruhat at `A` (`schrodingerOp`), and by the
Fock vector `v_P` of the polynomial `P` (`integrated`). -/
lemma DescentsVanish.bddAbove_lift {A : Set (FinPlace E)} (hA : A.IsConjDisjoint)
    (h_vanish : DescentsVanish W V a A.conjClosureᶜ Y) (hY : V.IsAutomorphic Y)
    (D : W'.Splitting W Unit) [IsBaseAdapted D]
    (P : MvPolynomial (NumberField.InfinitePlace E × n × m) ℂ) (Ψ : (n × m → 𝔸f E) → ℂ)
    [IsSchwartzBruhat A Ψ] :
    BddAbove (.range fun g : G E t ↦ ‖lift (pairThetaKer W' V (a * upsilonU1) 1).swap
      (integrated (W'.hom V) (polyVector (realSigns E (homSigns t 1)) P)
        (schrodingerOp (W'.hom V) A Ψ (vacElem (W'.hom V)))) Y g‖) := by
  set Θ : ThetaKernel (𝒮 (W'.hom V)) V W' := (pairThetaKer W' V (a * upsilonU1) 1).swap
  set φ : 𝒮 (W'.hom V) := integrated (W'.hom V) (polyVector (realSigns E (homSigns t 1)) P)
    (schrodingerOp (W'.hom V) A Ψ (vacElem (W'.hom V)))
  have hφ : projOn (W'.hom V) A.conjClosureᶜ φ = φ := by
    rw [projOn_integrated, projOn_schrodingerOp_vacElem _ disjoint_compl_right]
  let ℓ : 𝒮 (W'.hom V) →L[ℂ] ℂ := θ (W'.hom V) - θ (W.hom V) ∘L (D.homSource V).zeroTerm
  obtain ⟨K, hK⟩ := exists_norm_theta_sub_zeroTerm_le D (a * upsilonU1) hA P Ψ
  have hY_rapid : Y ∈ V.rapidFunctions := hY.mem_rapidFunctions fun _ _ ↦ rfl
  obtain ⟨B, hB⟩ := hY_rapid.2.bounded
  refine ⟨K * B * V.quotMeasure.real .univ, Set.forall_mem_range.2 fun g ↦ ?_⟩
  obtain ⟨γ, hγ, h_rest⟩ := hK g
  let F (h : G E (1 : n → ℤˣ)) : ℂ := ℓ (pairWeil W' V (a * upsilonU1) 1 (γ * g, h) φ) * Y h
  have hF_bound : ∀ᵐ h ∂V.quotMeasure, ‖F h‖ ≤ K * B :=
    .of_forall fun h ↦ norm_mul_le_of_le (h_rest h) (hB h)
  have hF_int : Integrable F V.quotMeasure :=
    .of_bound (Continuous.mul (by fun_prop) hY.continuous).aestronglyMeasurable _ hF_bound
  -- The zero term `θ₀` contributes nothing to the descent at `γ g`.
  have h_zero : ∫ h : G E (1 : n → ℤˣ), θ (W.hom V) ((D.homSource V).zeroTerm
      (pairWeil W' V (a * upsilonU1) 1 (γ * g, h) φ)) * Y h ∂V.quotMeasure = 0 := by
    simpa only [homSlice_zero, Fintype.card_unit, pow_one] using
      h_vanish.integral_homSlice_eq_zero D hφ (γ * g)
  have h_theta_int : Integrable
      (fun h ↦ θ (W'.hom V) (pairWeil W' V (a * upsilonU1) 1 (γ * g, h) φ) * Y h) V.quotMeasure :=
    Θ.integrable_theta_mul hY_rapid φ (γ * g)
  -- So we may replace `g` by `γ g` and `θ` by `θ - θ₀` in the descent.
  have h_eq : lift Θ φ Y g = ∫ h, F h ∂V.quotMeasure := by
    rw [← Θ.fixesLeft_lift γ hγ g, lift_pairThetaKer_swap_apply, ← sub_eq_zero,
      ← integral_sub h_theta_int hF_int, ← h_zero]
    simp [F, ℓ, sub_mul]
  simpa only [h_eq] using norm_integral_le_of_norm_le_const hF_bound

/-- The value `χ.frobValue m w`, which is `q ^ (card m / 2)` times the value at a uniformiser at
`w` of the Hecke character of `χ` for rank `card m`, has modulus `√q ^ card m`. -/
lemma norm_frobValue (χ : AutChar E) (m : Type) [Fintype m] (w : FinPlace E) :
    ‖χ.frobValue m w‖ = √w.q ^ card m := by
  simp [AutChar.frobValue, abs_of_nonneg]

/-- The product `∏_{i<k} (1 - q^i X)` is not zero if `1 < q` and `q^k |X| ≤ 1`. -/
lemma qPochhammer_ne_zero {q k : ℕ} {X : ℂ} (hq : 1 < q) (hX : q ^ k * ‖X‖ ≤ 1) :
    qPochhammer q k X ≠ 0 := by
  refine prod_ne_zero_iff.2 fun i hi h_zero ↦ ?_
  -- A vanishing factor gives `q^i |X| = 1` with `i < k`, so `1 < q^k |X|`.
  have h_one : (q : ℝ) ^ i * ‖X‖ = 1 := by simpa using congrArg norm (sub_eq_zero.1 h_zero).symm
  have hX_pos : 0 < ‖X‖ := norm_pos_iff.2 fun hX_zero ↦ by simp [hX_zero] at h_one
  have h_lt : (q : ℝ) ^ i < q ^ k := pow_lt_pow_right₀ (mod_cast hq) (mem_range.1 hi)
  linarith [mul_lt_mul_of_pos_right h_lt hX_pos]

/-- Let the automorphic function `Y` be spherical at the split place `w` and killed by the Hecke
polynomial at `X`. Let the base change of `χ` be unramified and the datum `φ` vacuum at `star w`.
Let `W'` have rank `card m` and `V` rank `card m + k`. If `|X|` is at most `q^(-k - card m/2)` and
`q^(-card m - 1 - k/2)`, and the descent of `Y` to `W'` by `φ` (`lift` by the theta kernel
`pairThetaKer` twisted by `χ`) is bounded, then that descent is zero. -/
lemma lift_eq_zero_of_heckePolyOp_eq_zero (hY : V.IsAutomorphic Y) {w : FinPlace E}
    (hw : w.IsSplit) {χ : AutChar E} (hχ : CharUnramifiedAt χ.baseChange.finPart (star w))
    (hY_sph : Y ∈ sphericalAt (finRightRep E 1) w) {X : ℂ}
    (hY_hecke : heckePolyOp (finRightRep E 1) hw X Y = 0) {φ : 𝒮 (W'.hom V)}
    (hφ : projOn (W'.hom V) {star w} φ = φ) {k : ℕ} (hk : card n = card m + k)
    (hX_factor : √w.q ^ (card m + 2 * k) * ‖X‖ ≤ 1)
    (hX_root : √w.q ^ (2 * (card m + 1) + k) * ‖X‖ ≤ 1)
    (h_bdd : BddAbove (.range fun g : G E t ↦ ‖lift (pairThetaKer W' V χ 1).swap φ Y g‖)) :
    lift (pairThetaKer W' V χ 1).swap φ Y = 0 := by
  -- The descent `F` is spherical at `w` and inherits a Hecke equation at `X'`, up to a product.
  obtain ⟨hF_sph, h_transfer⟩ := lift_swap_heckePolyOp hk hw hχ
    (by simp [CharUnramifiedAt] : CharUnramifiedAt (1 : AutChar E).baseChange.finPart (star w)) hφ
    (hY.mem_rapidFunctions fun _ _ ↦ rfl) hY_sph
  set F : G E t → ℂ := lift (pairThetaKer W' V χ 1).swap φ Y
  set X₀ : ℂ := χ.frobValue m (star w) * X with hX₀
  set X' : ℂ := w.q ^ k * χ.frobValue m (star w) / AutChar.frobValue 1 n (star w) * X with hX'
  have h_hecke : qPochhammer w.q k X₀ • heckePolyOp (finRightRep E t) hw X' F = 0 := by
    rw [← h_transfer, hY_hecke]
    simp [lift, funext_iff]
  -- Both size conditions are written in powers of `√q`.
  have h_sqrt (j : ℕ) : (w.q : ℝ) ^ j = √w.q ^ (2 * j) := by simp [pow_mul]
  have h_sqrt_pos : 0 < √(w.q : ℝ) := sqrt_pos.2 (mod_cast w.one_lt_q.le)
  have h_norm₀ : ‖X₀‖ = √w.q ^ card m * ‖X‖ := by simp [hX₀, norm_frobValue]
  have h_norm' : ‖X'‖ = √w.q ^ k * ‖X‖ := by
    have h_ratio : √(w.q : ℝ) ^ (2 * k) * √w.q ^ card m / √w.q ^ (card m + k) = √w.q ^ k := by
      field
    simp [hX', norm_frobValue, h_sqrt, hk, h_ratio]
  have h_factor : qPochhammer w.q k X₀ ≠ 0 := qPochhammer_ne_zero w.one_lt_q <| by
    rwa [h_norm₀, h_sqrt, ← mul_assoc, ← pow_add, add_comm]
  have h_small : w.q ^ (card m + 1) * ‖X'‖ ≤ 1 := by
    rwa [h_norm', h_sqrt, ← mul_assoc, ← pow_add]
  exact eq_zero_of_heckePolyOp_eq_zero hw hF_sph
    ((smul_eq_zero.1 h_hecke).resolve_left h_factor) h_small h_bdd

/-- With no plane to split off, the zero term is the whole kernel: if `W'` splits over `W` along an
empty frame and the descents of `Y` to `W` vanish, then so do those to `W'`. -/
lemma DescentsVanish.of_isEmpty {S : Set (FinPlace E)} (h_vanish : DescentsVanish W V a S Y)
    (D : W'.Splitting W p) [IsBaseAdapted D] [IsEmpty p] : DescentsVanish W' V a S Y := by
  refine fun φ hφ ↦ funext fun g ↦ ?_
  have h_whole (ψ : 𝒮 (W'.hom V)) : θ (W.hom V) (D.homSlice V 0 ψ) = θ (W'.hom V) ψ := by
    simp [univ_eq_empty, mulVec_eq_sum, homSlice, zeroTerm_apply]
  simpa only [lift_pairThetaKer_swap_apply, h_whole, Fintype.card_eq_zero, pow_zero, mul_one,
    Pi.zero_apply] using h_vanish.integral_homSlice_eq_zero D hφ g

/-- Let `Σ` consist of the places of `A` and their conjugates, and let the descents of the
automorphic function `Y` to `W`, twisted by the character `a`, by data that are vacuum off `Σ`
vanish. Let `w` be a split place off `Σ` with the base change of `a` unramified at `star w`. Let `Y`
be spherical at `w` and killed by the Hecke polynomial at a point `X` of modulus
`q^(1 - t' - r'/2)`, where `r'` is the rank of `W` and `r' + t'` that of `V`. If `W'` is `W` plus
`l = card p` hyperbolic planes and `r' + 2 l + 3 < t'`, then the descents of `Y` to `W'` twisted by
`a * upsilonU1 ^ l` vanish, with `upsilonU1` the restriction of the character `υ` of the Weil data
to norm-one ideles. -/
lemma descentsVanish_add_planes {A : Set (FinPlace E)} (hA : A.IsConjDisjoint)
    (h_vanish : DescentsVanish W V a A.conjClosureᶜ Y) (D : W'.Splitting W p) [IsBaseAdapted D]
    (hY : V.IsAutomorphic Y) {w : FinPlace E} (hw : w.IsSplit) (hw_off : w ∉ A.conjClosure)
    (ha : CharUnramifiedAt a.baseChange.finPart (star w))
    (hY_sph : Y ∈ sphericalAt (finRightRep E 1) w) {X : ℂ}
    (hX : ‖X‖ = (√w.q ^ card r * w.q ^ (card n - card r - 1))⁻¹)
    (hY_hecke : heckePolyOp (finRightRep E 1) hw X Y = 0)
    (h_rank : 2 * card r + 2 * card p + 3 < card n) :
    DescentsVanish W' V (a * upsilonU1 ^ card p) A.conjClosureᶜ Y := by
  induction' hl : card p with l ih generalizing m p
  · rw [card_eq_zero_iff] at hl
    simpa using h_vanish.of_isEmpty D
  -- It is enough to treat the data `φ = v_P ⊗ Ψ ⊗ vac`.
  refine .of_schrodingerOp hA hY fun P Ψ _ ↦ ?_
  set χ : AutChar E := a * upsilonU1 ^ (l + 1) with hχ_eq
  set φ : 𝒮 (W'.hom V) := integrated (W'.hom V) (polyVector (realSigns E (homSigns t 1)) P)
    (schrodingerOp (W'.hom V) A Ψ (vacElem (W'.hom V)))
  -- The descent is bounded: split off one plane, and use the induction hypothesis for the rest.
  have h_bdd : BddAbove (.range fun g : G E t ↦ ‖lift (pairThetaKer W' V χ 1).swap φ Y g‖) := by
    obtain ⟨D', hD', -⟩ := exists_isBaseAdapted_comp_removePlanes D
      (equivOfCardEq (by simp [hl, add_comm] : card (Unit ⊕ Fin l) = card p))
    have h_below : DescentsVanish (hyperbolicSum (Fin l) W) V (a * upsilonU1 ^ l) A.conjClosureᶜ
      Y :=
      ih (removePlanes (Fin l) W) (by grind [Fintype.card_fin]) (Fintype.card_fin l)
    simpa only [mul_assoc, ← pow_succ] using h_below.bddAbove_lift hA hY D' P Ψ
  have hχ : CharUnramifiedAt χ.baseChange.finPart (star w) := fun u hu ↦ by
    simp [hχ_eq, ha u hu, charUnramifiedAt_upsilon _ u hu]
  have hφ : projOn (W'.hom V) {star w} φ = φ := by
    rw [projOn_integrated, projOn_schrodingerOp_vacElem _ (by simpa [or_comm] using hw_off)]
  have h_card : card m = card r + 2 * (l + 1) := by rw [D.card_eq, hl]
  -- Here `|X|⁻¹ = √q ^ d` with `d = r' + 2 (t' - 1)`, and both exponents needed are at most `d`.
  have h_one_le : 1 ≤ √(w.q : ℝ) := one_le_sqrt.2 (mod_cast w.one_lt_q.le)
  have h_size {j : ℕ} (hj : j ≤ card r + 2 * (card n - card r - 1)) : √w.q ^ j * ‖X‖ ≤ 1 := by
    have h_norm : ‖X‖ = (√w.q ^ (card r + 2 * (card n - card r - 1)))⁻¹ := by
      rw [hX, pow_add, pow_mul, sq_sqrt (Nat.cast_nonneg _)]
    rw [h_norm, mul_inv_le_iff₀ (by positivity), one_mul]
    exact pow_le_pow_right₀ h_one_le hj
  obtain ⟨k, hk⟩ : ∃ k : ℕ, card n = card m + k := Nat.exists_eq_add_of_le (by omega)
  -- So both size conditions of `lift_eq_zero_of_heckePolyOp_eq_zero` hold.
  exact lift_eq_zero_of_heckePolyOp_eq_zero hY hw hχ hY_sph hY_hecke hφ hk (h_size (by omega))
    (h_size (by omega)) h_bdd

end New.SiegelWeil
