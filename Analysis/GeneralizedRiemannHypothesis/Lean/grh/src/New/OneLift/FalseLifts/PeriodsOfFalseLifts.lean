import New.OneLift.FalseLifts.HyperbolicPlaneStep

/-!
# The tower of descents and the periods of false lifts

This file applies the inductive step of `New.OneLift.FalseLifts.HyperbolicPlaneStep` to false lifts
`Ξ` on a definite space `I_n`. Such a `Ξ` is killed by the descent `O.normalizedDescent` to `W`, by
the hyperplane sums at the chosen places, and by one Hecke polynomial. The file builds the tower of
vanishing descents to `W ⊕ ℍ^N` and deduces that the periods of `Ξ` over the block `I_l` of
`I_n = I_N ⊕ I_l` vanish, written as class sums. Here `O` is a descent pair `(W, I_n)`
(`New.DescentPair`) of ranks `r < n`. It carries two finite families of finite places, the chosen
places `O.chosenPlace` and the twist places `O.twistPlace`, which together form the level
`O.places`, and a character `O.tamePart w` of each residue field; the results on the tower and on
periods assume `2 r + 2 N + 3 < n`.

## Main definitions and results

* `New.Rows.stdClassSum_gramForm_eq_zero`: Periods of false lifts vanish, as class sums.

## The steps of the argument

* The bottom of the tower: `New.Rows.lift_polyVector_blockDatum_eq_zero` passes from the harmonic
  polynomial to all polynomials, and `New.DescentPair.descentsVanish_of_hyperplaneSumsAnnihilate`
  passes from the block datum to all data.
* The tower `New.Rows.descentsVanish_hyperbolicSum`: all descents of the coefficients of `Ξ` to
  `W ⊕ ℍ^N` vanish, for data that are the vacuum off the places of the level.
* From descents to periods, for `I_n = I_N ⊕ I_l`:
  `New.Rows.integral_conj_pairTheta_mul_algFormCoeff_eq_zero` absorbs the kernel of `W` and applies
  `New.SiegelWeil.integral_blockEmb_eq_zero_of_descentsVanish`, which takes a Fourier coefficient
  and varies the datum.
* The theorem `New.Rows.stdClassSum_gramForm_eq_zero` writes the periods over the block `I_l` as
  class sums `New.stdClassSum`. `New.Rows.stdClassSum_gramForm_eq_zero_of_rank_one` is the case of
  false lifts from a line; that of false lifts on `V_j` is in
  `New.OneLift.ComparisonOperator.GluingMaps`.
* Two uses: `New.Rows.stdClassSum_period_eq_zero` for point forms, and
  `New.Rows.DividedSplitting.stdClassSum_inner_productForm_eq_zero` for the product forms
  `New.Rows.DividedSplitting.productForm` of the kernel vectors.

Notions from other files:
* `New.pairWeil`: the Weil representation of U(W) × U(V) on the data space 𝒮(Hom(W, V)), twisted by
  two characters of U(1); `New.Space.θ` is the theta functional on that space.
* `New.Space.projOn`: the projection whose fixed vectors are the data that are the vacuum at the
  places of a set `S` and their conjugates. For `S` the complement of the places of the level and
  their conjugates, these are the test vectors.
* `New.heckePolyOp`: the operator ∑ (−X)^i q^(i choose 2) T_{w,i}, q the order of the residue field
  at w; `New.sphericalAt π w` is the space of vectors spherical at w.
* `New.algFormCoeff`: the matrix coefficient `g ↦ L (ρ(g_∞⁻¹) φ(g_f))` of a form `φ` at a functional
  `L`, with `ρ` the representation `New.conjWeylRep` on the vectors `New.WeylIndex n κ → ℂ` and `L`
  often `New.gramForm ζ`, the invariant inner product with `ζ`.
* `New.SiegelWeil.descentsVanish_add_planes`: vanishing of descents passes from `W` to `W` plus
  hyperbolic planes for `Y` killed by a Hecke polynomial at a small point.

## Relation to the literature

Let V=V₁⊕V₂ with V₁ of small rank, and take a form on a definite U(V) that is killed by theta
descent, by the hyperplane sums at the chosen places (as good forms are), and by a Hecke polynomial
at one split place at the smallest root of lifts. Then it has zero theta periods over U(V₂), so the
forms built from these kernels are orthogonal to it. It is known that vanishing of lifts in a theta
tower kills theta periods on a subgroup. Related work: C. Wu, Poles of Eisenstein series and theta
lifts for unitary groups, arXiv 2104.11954, 2021; Ginzburg–Jiang–Soudry, Poles of L-functions and
theta liftings for orthogonal groups, 2009; Jiang–Wu, On (χ,b)-factors of cuspidal automorphic
representations of unitary groups I, 2016; Rallis, On the Howe duality conjecture, 1984.
-/

section MemberOrthogonality

namespace New.Rows

open Matrix MeasureTheory ComplexConjugate Sum Fintype SiegelWeil Exchange Space DescentPair
  WeilData Fock Gf G ThetaKernel AutChar Prod

variable {E r n N ι l : Type} [Field E] [CMType E] [Fintype r] [DecidableEq r] [Fintype n]
  [DecidableEq n] [Fintype N] [DecidableEq N] [Fintype l] [DecidableEq l] [WeilData E]
  {O : DescentPair E r n}

/-- Let `O` be a descent pair `(W, I_n)` that fits the parameter `l₀` on `W`, and let the descent
`O.normalizedDescent` to `W` kill the form `Ξ` on `I_n`. Then the descent to `W`, twisted by the
character `O.charW`, of the conjugate matrix coefficient (`algFormCoeff`) of `Ξ` at the highest
vector vanishes for every datum `v_P ⊗ O.blockDatum`, where `v_P` is the Fock vector of a polynomial
`P` and `O.blockDatum` is the finite datum of the pair. -/
lemma lift_polyVector_blockDatum_eq_zero {l₀ : NumberField.InfinitePlace E → r → ℤ} [Nonempty r]
    (h_fits : O.FitsParams l₀) {Ξ : O.FormV} (h_theta : O.normalizedDescent Ξ = 0)
    (P : MvPolynomial (NumberField.InfinitePlace E × n × r) ℂ) :
    lift (pairThetaKer O.W (stdSpace E n) O.charW 1).swap
      (integrated (O.W.hom (stdSpace E n)) (polyVector (realSigns E (homSigns O.signs 1)) P)
        O.blockDatum.val)
      (star (algFormCoeff 1 (gramForm (highestVector O.columnCount O.paramV)) Ξ.val)) = 0 := by
  let y : G E 1 → ℂ := star (ofAlgForm O.paramV 1 Ξ.val)
  let φ : 𝒮 (O.W.hom (stdSpace E n)) := integrated (O.W.hom (stdSpace E n))
    (polyVector (realSigns E (homSigns O.signs 1)) P) O.blockDatum.val
  -- `O.normalizedDescent Ξ` is a nonzero multiple of the conjugate of the descent `F` by the
  -- harmonic datum.
  let F : G E O.signs → ℂ :=
    lift O.pairThetaKernel.swap (O.fockDatum (highestVector O.columnCount O.paramV)) y
  have h_harmonic : F = 0 := by
    rw [normalizedDescent_eq_smul_star_lift_swap, smul_eq_zero, star_eq_zero] at h_theta
    exact h_theta.resolve_left (by simp [-card_pi])
  -- The descent by `φ` is `F` convolved with a test function `α` on the real points of `U(W)`.
  obtain ⟨α, hα⟩ := h_fits.isEdge.swapped.lift_isForm_and_eq_realConv _ ⟨P, rfl⟩
  obtain ⟨-, h_conv : lift O.pairThetaKernel.swap φ y = realConv α F⟩ :=
    hα O.pairThetaKernel.swap (f := O.blockDatum.val)
      (by simp [pairWeil_integrated O.W (stdSpace E n) O.charW O.charV])
      (isForm_ofAlgForm O.isHCParam_paramV Ξ.val).conj
  have h_poly : lift (pairThetaKer O.W (stdSpace E n) O.charW O.charV).swap φ y = 0 := by
    simp [h_conv, h_harmonic, realConv, funext_iff]
  -- The character `O.charV` only multiplies the descent by a character of `det g`.
  change lift (pairThetaKer O.W (stdSpace E n) O.charW 1).swap φ y = 0
  funext g
  simpa [lift_pairThetaKer_swap_apply, pairWeil_apply, mul_left_comm _ _⁻¹, mul_assoc,
    integral_const_mul] using congrFun h_poly g

open scoped Classical in
/-- Let the archimedean parameter `l₀` on `W` correspond to the parameter `O.paramV` on `I_n`,
compatibly with the weights of `O` (`O.FitsParams`), and let the residue characters
`χ_v = O.tamePart v` be nontrivial at the twist places. Let the algebraic form `Ξ` on `U(I_n)` be
killed by
* each product over the chosen places `v` of the sums `∑ χ_v(det s)⁻¹ s` over the invertible
  `s = 1 + u λ_v`, for rows `λ_v` that are not all zero,
* the theta descent `O.normalizedDescent` to `W`,
* the Hecke polynomial at the number `O.liftHeckeRoot w`, for a split place `w` of norm `q` off the
  level.

If `2 card r + 2 card N + 3 < card n`, then the theta descents to `W ⊕ ℍ^N` of the conjugate matrix
coefficient of `Ξ` at any vector `ζ` vanish, for all data of the Weil representation that are the
vacuum at the finite places other than those of the level and their conjugates
(`DescentsVanish`). -/
lemma descentsVanish_hyperbolicSum {l₀ : NumberField.InfinitePlace E → r → ℤ} [Nonempty r]
    (h_fits : O.FitsParams l₀) (h_ramified : ∀ i : O.TwistIndex, O.tamePart (O.twistPlace i) ≠ 1)
    {Ξ : O.FormV} (h_hyperplane : O.HyperplaneSumsAnnihilate Ξ)
    (h_theta : O.normalizedDescent Ξ = 0) {w : FinPlace E} {hw : star w ≠ w}
    {hw_off : w ∉ O.places.conjClosure}
    (h_hecke : O.heckePolyOnForms hw hw_off (O.liftHeckeRoot w) Ξ = 0)
    (h_rank : 2 * card r + 2 * card N + 3 < card n) (ζ : WeylIndex n O.columnCount → ℂ) :
    DescentsVanish (hyperbolicSum N O.W) (stdSpace E n) (O.charW * upsilonU1 ^ card N)
      O.places.conjClosureᶜ (star (algFormCoeff 1 (gramForm ζ) Ξ.val)) := by
  let y (ζ : WeylIndex n O.columnCount → ℂ) : G E 1 → ℂ := star (algFormCoeff 1 (gramForm ζ) Ξ.val)
  have hy (ζ : WeylIndex n O.columnCount → ℂ) : (stdSpace E n).IsAutomorphic (y ζ) :=
    isAutomorphic_star_algFormCoeff _ Ξ
  let ζ₀ : WeylIndex n O.columnCount → ℂ := highestVector O.columnCount O.paramV
  -- First take the highest vector `ζ₀`. The descents to `W` vanish, and
  -- `descentsVanish_add_planes` applies at `w`, to the conjugate of the point `O.liftHeckeRoot w`.
  have h_bottom : DescentsVanish O.W (stdSpace E n) O.charW O.places.conjClosureᶜ (y ζ₀) :=
    descentsVanish_of_hyperplaneSumsAnnihilate _ h_ramified h_hyperplane
      (lift_polyVector_blockDatum_eq_zero h_fits h_theta)
  have h_disj : O.places.IsConjDisjoint := by grind [O.apart.star_ne]
  have h_sph : y ζ₀ ∈ sphericalAt (finRightRep E 1) w := by
    have h_fix (k : ↥(stdLevel E n ⊓ supportedOn n {w})) :
        algFormRep O.columnCount O.detExp k Ξ.val = Ξ.val := by
      simpa using mem_levelSpace.1 (Ξ.mem_sphericalAt hw_off) k
    simp [y, funext_iff, ← algFormCoeff_algFormRep, h_fix]
  have h_norm : ‖conj (O.liftHeckeRoot w)‖ = (√w.q ^ card r * w.q ^ (card n - card r - 1))⁻¹ := by
    simp [liftHeckeRoot, frobValue]
  have hy_hecke : heckePolyOp (finRightRep E 1) hw (conj (O.liftHeckeRoot w)) (y ζ₀) = 0 := by
    -- The conjugate coefficient is a conjugate-linear equivariant map `L` on forms.
    let L : AlgForm (E := E) n O.columnCount O.detExp →ₗ⋆[ℂ] G E 1 → ℂ :=
      (starLinearEquiv ℂ).toLinearMap ∘ₛₗ algFormCoeff 1 (gramForm ζ₀)
    calc _ = L (heckePolyOp (algFormRep O.columnCount O.detExp) hw (O.liftHeckeRoot w) Ξ.val) :=
        (map_heckePolyOp L _ (by simp [L, funext_iff, algFormCoeff_algFormRep])).symm
      _ = L 0 := congrArg L (congrArg Subtype.val h_hecke)
      _ = 0 := map_zero L
  have h_top : DescentsVanish (hyperbolicSum N O.W) (stdSpace E n) (O.charW * upsilonU1 ^ card N)
      O.places.conjClosureᶜ (y ζ₀) :=
    descentsVanish_add_planes h_disj h_bottom (removePlanes N O.W) (hy ζ₀) hw hw_off
      (HasWeight.charUnramifiedAt rfl rfl) h_sph h_norm hy_hecke h_rank
  -- For real `x` the translate of `y ζ₀` by `x` is the coefficient at `x ζ₀`, and these vectors
  -- span.
  refine fun φ hφ ↦ funext fun g ↦ ?_
  let coeff : (WeylIndex n O.columnCount → ℂ) →ₗ[ℂ] (stdSpace E n).rapidFunctions.toSubmodule :=
    { toFun ζ := ⟨y ζ, (hy ζ).mem_rapidFunctions fun _ _ ↦ rfl⟩
      map_add' := by simp [y, algFormCoeff, funext_iff]
      map_smul' := by simp [y, algFormCoeff, funext_iff] }
  let Θ : ThetaKernel (𝒮 ((hyperbolicSum N O.W).hom (stdSpace E n))) (stdSpace E n)
    (hyperbolicSum N O.W) :=
    (pairThetaKer (hyperbolicSum N O.W) (stdSpace E n) (O.charW * upsilonU1 ^ card N) 1).swap
  let descent : (WeylIndex n O.columnCount → ℂ) →ₗ[ℂ] ℂ := .proj g ∘ₗ Θ.liftBilin φ ∘ₗ coeff
  suffices h_descent : descent = 0 from LinearMap.congr_fun h_descent ζ
  refine eq_zero_of_forall_map_translate_highestVector_eq_zero O.isHCParam_paramV.injective
    O.detExp descent fun x ↦ ?_
  have h_translate : y (conjWeylRep O.columnCount O.detExp x ζ₀) = fun h ↦ y ζ₀ (h * (x, 1)) := by
    simp [funext_iff, y, algFormCoeff_apply, ← gramForm_conjWeylRep (e := O.detExp) x ζ₀]
  change lift Θ φ (y (conjWeylRep O.columnCount O.detExp x ζ₀)) g = 0
  rw [h_translate]
  exact congrFun (h_top.comp_mul_right (hy ζ₀) (by simp) φ hφ) g

variable {l₀ : NumberField.InfinitePlace E → r → ℤ} [Nonempty r]

open NumberField (InfinitePlace RingOfIntegers)

omit [Nonempty r] in
/-- At every point `p` of `U(W)(𝔸) × U(V)(𝔸)` some datum `φ` in `𝒮(Hom(W, V))` has a nonzero theta
kernel `pairTheta W V a b φ p`, twisted by the characters `a` and `b`. This `φ` can be chosen fixed
by `projOn (W.hom V) T`, the mean over the Heisenberg operators of integral vectors at the places of
`T` and their conjugates. -/
lemma exists_projOn_eq_pairTheta_ne_zero {s : r → ℤˣ} {t : n → ℤˣ} (W : Space E r s)
    (V : Space E n t) (a b : AutChar E) (T : Set (FinPlace E)) (p : G E s × G E t) :
    ∃ φ : 𝒮 (W.hom V), projOn (W.hom V) T φ = φ ∧ pairTheta W V a b φ p ≠ 0 := by
  -- The translate `φ₀` of the vacuum is not zero, so it is not zero at some real point `x`.
  let φ₀ : 𝒮 (W.hom V) := pairWeil W V a b p (vacElem _)
  have hφ₀ : φ₀ ≠ 0 := fun h_zero ↦ by
    simpa [φ₀] using congrArg (fun φ ↦ dataInner (W.hom V) φ φ) h_zero
  obtain ⟨x, hx⟩ : ∃ x, φ₀ (realVec x) ≠ 0 := not_forall.1 (mt eq_zero_of_apply_realVec_eq_zero hφ₀)
  -- Translate the vacuum by the real matrix `h⁻¹ x g`, where `p = (g, h)`.
  let x' : n × r → 𝔸 E := matrixToVec (p.2⁻¹.adeleMatrix * vecToMatrix (realVec x) *
    p.1.adeleMatrix)
  have hx' (i : n × r) (v : FinPlace E) : (x' i).2 v = 0 := by
    simp [x', matrixToVec, vecToMatrix, realVec, mul_apply, snd_sum]
  refine ⟨(W.hom V).ϱ x' (vacElem _), ?_, ?_⟩
  · rw [projOn_rho _ fun i v _ ↦ hx' i v, projOn_vacElem]
  · rwa [pairTheta, ← rho_pairWeil, theta_rho]

open scoped Classical in
/-- Let the archimedean parameter `l₀` on `W` correspond to the parameter `O.paramV` on `I_n`
(`O.FitsParams`), and let the residue characters `O.tamePart` be nontrivial at the twist places. A
false lift is here an algebraic form `Ξ` on the definite group `U(I_n)` with three properties. It is
killed by the hyperplane sums at the chosen places. It is killed by the theta descent
`O.normalizedDescent` to `W`. It is killed by the Hecke polynomial at a split place `w` off the
level, taken at the number `O.liftHeckeRoot w` of modulus `q^(1 - n + r / 2)`, `q` the norm of `w`.
Let `ε` split `I_n = I_N ⊕ I_l` with `2 r + 2 N + 3 < n`. Then the integral over `h₂` in the adelic
quotient of `U(I_l)` of the conjugate theta kernel of the pair `O.W, I_l` times the matrix
coefficient `algFormCoeff 1 (gramForm ζ) Ξ` at `(h₁, h₂) γ` is zero. This holds for every vector
`ζ`, every character `b` of `U(1)` twisting the kernel, all `g` and `h₁`, every finite `γ` supported
on `O.places`, and all data `φ` that are the vacuum off these places and their conjugates. -/
theorem integral_conj_pairTheta_mul_algFormCoeff_eq_zero (hO_fits : O.FitsParams l₀)
    (h_twist : ∀ i : O.TwistIndex, O.tamePart (O.twistPlace i) ≠ 1) {Ξ : O.FormV}
    (h_reflect : O.HyperplaneSumsAnnihilate Ξ) (hθ : O.normalizedDescent Ξ = 0)
    {w : FinPlace E} {hw : star w ≠ w} {hw_off : w ∉ O.places.conjClosure}
    (h_hecke : O.heckePolyOnForms hw hw_off (O.liftHeckeRoot w) Ξ = 0)
    (h_rank : 2 * card r + 2 * card N + 3 < card n) (ε : N ⊕ l ≃ n)
    (ζ : WeylIndex n O.columnCount → ℂ) (b : AutChar E) (g : G E O.signs) (h₁ : G E (1 : N → ℤˣ))
    {γ : Gf E n} (hγ : γ ∈ supportedOn n O.places) {φ : 𝒮 (O.W.hom (stdSpace E l))}
    (hφ : projOn (O.W.hom (stdSpace E l)) O.places.conjClosureᶜ φ = φ) :
    ∫ h₂ : G E (1 : l → ℤˣ), conj (pairTheta O.W (stdSpace E l) O.charW b φ (g, h₂)) *
      algFormCoeff 1 (gramForm ζ) Ξ.val (blockEmb (e := ε) elim_one_one.symm (h₁, h₂) * (1, γ))
      ∂(stdSpace E l).quotMeasure = 0 := by
  -- Absorb the theta kernel of `W` into the matrix coefficient and apply
  -- `integral_blockEmb_eq_zero_of_descentsVanish`. All functions are conjugated, as in
  -- `DescentsVanish`.
  let T : Set (FinPlace E) := O.places.conjClosureᶜ
  let diag : G E 1 × G E 1 →* G E 1 := blockEmb (e := ε) elim_one_one.symm
  let y : G E 1 → ℂ := star (algFormCoeff 1 (gramForm ζ) Ξ.val)
  have hy : (stdSpace E n).IsAutomorphic y := isAutomorphic_star_algFormCoeff _ Ξ
  -- The descents of the translate `y₁` to `W ⊕ ℍ^N` vanish, as `γ` is `1` off `O.places`.
  let y₁ (h : G E 1) : ℂ := y (h * (1, γ))
  have hy₁ : (stdSpace E n).IsAutomorphic y₁ := hy.comp_mul_right (1, γ)
  have hy₁_desc : DescentsVanish (hyperbolicSum N O.W) (stdSpace E n)
      (O.charW * upsilonU1 ^ card N) T y₁ :=
    (descentsVanish_hyperbolicSum hO_fits h_twist h_reflect hθ h_hecke h_rank ζ).comp_mul_right hy
      fun v hv ↦ by simp [mem_supportedOn.1 hγ v (hv ∘ .inl) (hv ∘ .inr)]
  -- Complete `φ` by a datum `φ''` on the first block whose kernel is not zero at `(g, h₁)`.
  obtain ⟨φ'', hφ'', hc''⟩ :=
    exists_projOn_eq_pairTheta_ne_zero O.W (stdSpace E N) O.charW b⁻¹ T (g, h₁)
  let Φ : 𝒮 (O.W.hom (stdSpace E n)) := boxProd (homSigns_sum_target (e := ε) (by simp)) φ'' φ
  have hΦ : projOn _ T Φ = Φ := by rw [← boxProd_projOn, hφ'', hφ]
  let ϑ (h : G E 1) : ℂ := pairTheta O.W (stdSpace E n) O.charW 1 Φ (g, h)
  let y₂ (h : G E 1) : ℂ := ϑ h * y₁ h
  have hy₂_rat : (stdSpace E n).Γ.FixesLeft y₂ := fun δ hδ h ↦
    congrArg₂ (· * ·) ((pairThetaKer O.W (stdSpace E n) O.charW 1).swap.theta_rat_mul δ hδ h)
      (hy₁.rat_mul δ hδ h)
  -- The level off the places of `O.places` fixes `y₂`: it fixes `Φ`, as the character of `W` is
  -- unramified, and it fixes `Ξ` and commutes with `γ`.
  have hy₂_level : HasLevel y₂ (stdLevel E n ⊓ supportedOn n T) := by
    intro k hk h
    have hk_off : k ∈ Gf.trivialOn n O.places := supportedOn_compl.le hk.2
    have h_datum : pairWeil O.W (stdSpace E n) O.charW 1 ((1, 1), (1, k)) Φ = Φ := by
      rw [pairWeil_eq_smul_of_projOn_eq _ hΦ (one_mem _) hk]
      simp [upsilonU1_detFin_eq_one_of_mem_stdLevel hk.1]
    have h_kernel : ϑ (h * (1, k)) = ϑ h := by
      simp only [ϑ]
      rw [← mul_one g, ← mk_mul_mk, pairTheta_mul, mul_one]
      exact congrArg (pairTheta O.W (stdSpace E n) O.charW 1 · (g, h)) h_datum
    have h_form : algFormRep O.columnCount O.detExp k Ξ.val = Ξ.val :=
      Ξ.algFormRep_eq_self_of_mem (inf_trivialOn_le_levelOf ⟨hk.1, hk_off⟩)
    have h_comm : h * (1, k) * (1, γ) = h * (1, γ) * (1, k) := by
      simp [mul_assoc h, (commute_supportedOn_trivialOn hγ hk_off).eq]
    simp only [y₂, y₁, y, h_kernel, h_comm, Pi.star_apply, ← algFormCoeff_algFormRep _ k, h_form]
  -- Kernels multiply in the sum `W ⊕ ℍ^N`, so a descent of `y₂` to `ℍ^N` is a descent of `y₁`.
  have hy₂_desc :
      DescentsVanish (hyperbolicSpace E N) (stdSpace E n) (1 * upsilonU1 ^ card N) T y₂ := by
    refine fun φ' hφ' ↦ funext fun g' ↦ ?_
    let Φ' : 𝒮 ((hyperbolicSum N O.W).hom (stdSpace E n)) := boxProd homSigns_sum_source φ' Φ
    have hΦ' : projOn _ T Φ' = Φ' := (boxProd_projOn ..).symm.trans (by rw [hφ', hΦ])
    have h_kernel (h : G E 1) :
        pairTheta (hyperbolicSum N O.W) (stdSpace E n) (O.charW * upsilonU1 ^ card N) 1 Φ'
          (.sum (g', g), h) =
          pairTheta (hyperbolicSpace E N) (stdSpace E n) (1 * upsilonU1 ^ card N) 1 φ' (g', h) * ϑ
            h := by
      rw [mul_comm O.charW, one_mul]
      exact (congrArg _ (pairWeil_boxProd_source ..)).trans (theta_boxProd_source ..)
    refine (integral_congr_ae (.of_forall fun h ↦ ?_)).trans
      (congrFun (hy₁_desc Φ' hΦ') (.sum (g', g)))
    change pairTheta (hyperbolicSpace E N) _ _ 1 φ' (g', h) * y₂ h =
      pairTheta (hyperbolicSum N O.W) _ _ 1 Φ' (.sum (g', g), h) * y₁ h
    rw [h_kernel, mul_assoc]
  have h_period : ∫ h₂, y₂ (diag (h₁, h₂)) ∂(stdSpace E l).quotMeasure = 0 :=
    integral_blockEmb_eq_zero_of_descentsVanish (.mul (by fun_prop) hy₁.continuous) hy₂_rat
      hy₂_level ε _ hy₂_desc h₁
  -- Kernels multiply in the sum `I_n = I_N ⊕ I_l` too.
  have h_factor (h₂ : G E 1) : ϑ (diag (h₁, h₂)) =
      pairTheta O.W (stdSpace E N) O.charW b⁻¹ φ'' (g, h₁) *
        pairTheta O.W (stdSpace E l) O.charW b φ (g, h₂) := by
    have h_mat : (diag (h₁, h₂)).adeleMatrix.submatrix ε ε = fromBlocks h₁.adeleMatrix 0 0
      h₂.adeleMatrix := by
      simp [diag, blockEmb]
    simp only [← inv_mul_cancel b, ϑ, pairTheta, Φ]
    rw [pairWeil_boxProd_target (by simp) _ _ _ _ h_mat, theta_boxProd_target (by simp) _ (by simp)]
  simp only [y₂, h_factor, mul_assoc, integral_const_mul, mul_eq_zero, hc'', false_or] at h_period
  rw [← star_eq_zero, ← starRingEnd_apply, ← integral_conj, ← h_period]
  simp [y₁, y, diag]

open scoped Classical in
/-- Let the archimedean parameter `l₀` on `W` correspond to the parameter `O.paramV` on `I_n`
(`O.FitsParams`), and let the residue characters `O.tamePart` be nontrivial at the twist places. Let
the algebraic form `Ξ` on `U(I_n)` be killed by the hyperplane sums at the chosen places. Let `Ξ`
also be killed by the theta descent `O.normalizedDescent` to `W`, and by the Hecke polynomial at the
number `O.liftHeckeRoot w` for a split place `w` off the level. Let `ε` split `I_n = I_N ⊕ I_l` with
`2 #r + 2 #N + 3 < #n`, and let `x` be supported on `O.places`. Let `ϑ` be a function on the finite
points of `U(I_l)` whose coordinates, moved by the real points, are multiples of conjugate theta
kernels of the pair `O.W, I_l` with data that are the vacuum off `O.places` and their conjugates.
Let the conjugate-linear map `C` carry its values to the space of values of `Ξ`, equivariantly for
the real points of `U(I_l)` acting by `conjWeylRep`, the representation of the given weight. Then
the invariant inner product `gramForm` of `C (ϑ h)` with `Ξ ((h₁, h) x)`, the block point being
`U.block ε (h₁, h)`, is left invariant under the rational points. Its class sum `stdClassSum` is
zero at every level `K` that fixes it. -/
theorem stdClassSum_gramForm_eq_zero (hO_fits : O.FitsParams l₀)
    (h_twist : ∀ i : O.TwistIndex, O.tamePart (O.twistPlace i) ≠ 1) {Ξ : O.FormV}
    (h_reflect : O.HyperplaneSumsAnnihilate Ξ) (hθ : O.normalizedDescent Ξ = 0)
    {w : FinPlace E} {hw : star w ≠ w} {hw_off : w ∉ O.places.conjClosure}
    (h_hecke : O.heckePolyOnForms hw hw_off (O.liftHeckeRoot w) Ξ = 0)
    (h_rank : 2 * card r + 2 * card N + 3 < card n) (ε : N ⊕ l ≃ n) {κ : InfinitePlace E → ℕ → ℕ}
    (C : (WeylIndex l κ → ℂ) →ₗ⋆[ℂ] WeylIndex n O.columnCount → ℂ)
    (hC : ∀ (g : GInf E (1 : n → ℤˣ)) (y : GInf E (1 : l → ℤˣ)) (ζ : WeylIndex l κ → ℂ),
      (∀ τ : InfinitePlace E, (g τ : GL n ℂ) = reindexGL ε (blockGL (1, y τ))) →
        conjWeylRep O.columnCount O.detExp g (C ζ) = C (conjWeylRep κ 0 y ζ))
    (ϑ : Gf E l → WeylIndex l κ → ℂ)
    (h_kernels : ∀ j : WeylIndex l κ, ∃ (c : ℂ) (g : G E O.signs) (b : AutChar E)
      (φ : 𝒮 (O.W.hom (stdSpace E l))),
      projOn (O.W.hom (stdSpace E l)) O.places.conjClosureᶜ φ = φ ∧
        ∀ (u : GInf E (1 : l → ℤˣ)) (h : Gf E l), conjWeylRep κ 0 u⁻¹ (ϑ h) j =
          c * conj (pairTheta O.W (stdSpace E l) O.charW b φ (g, u, h)))
    (h₁ : Gf E N) {x : Gf E n} (hx : x ∈ supportedOn n O.places) :
    let f (h : Gf E l) : ℂ := gramForm (C (ϑ h)) (Ξ (U.block ε (h₁, h) * x))
    (∀ δ ∈ (stdSpace E l).Γ, ∀ h : Gf E l, f (δ.2 * h) = f h) ∧
      ∀ (K : Subgroup (Gf E l)) [IsLevel K], K ≤ rightStabilizer f → stdClassSum K f = 0 := by
  intro f
  let diag : G E 1 × G E 1 →* G E 1 := blockEmb (e := ε) elim_one_one.symm
  -- One kernel and one matrix coefficient `y j` for each coordinate of `ϑ`.
  choose c g b φ hφ h_coord using h_kernels
  let y (j : WeylIndex l κ) : G E 1 → ℂ := algFormCoeff 1 (gramForm (C (Pi.single j 1))) Ξ.val
  let F (j : WeylIndex l κ) (h₂ : G E 1) : ℂ :=
    conj (pairTheta O.W (stdSpace E l) O.charW (b j) (φ j) (g j, h₂)) *
      y j (diag ((1, h₁), h₂) * (1, x))
  have hy (j : WeylIndex l κ) : (stdSpace E n).IsAutomorphic (y j) :=
    isAutomorphic_algFormCoeff Ξ.val
  have hF_cont (j : WeylIndex l κ) : Continuous (F j) :=
    .mul (by fun_prop) ((hy j).continuous.comp (by fun_prop))
  have hF_rat (j : WeylIndex l κ) : (stdSpace E l).Γ.FixesLeft (F j) := fun δ hδ h₂ ↦ by
    have h_diag : diag ((1, h₁), δ * h₂) = diag (1, δ) * diag ((1, h₁), h₂) := by
      rw [← map_mul diag, mk_mul_mk 1, one_mul]
    refine congrArg₂ (conj · * ·)
      ((pairThetaKer O.W (stdSpace E l) O.charW (b j)).swap.theta_rat_mul δ hδ h₂) ?_
    rw [h_diag, mul_assoc, (hy j).rat_mul (diag (1, δ)) (by simpa [diag])]
  have hF_int (j : WeylIndex l κ) : Integrable (F j) (stdSpace E l).quotMeasure :=
    (isRapid_of_isCocompact (hF_cont j) (hF_rat j)
      ((stdSpace E l).isCocompact_of_definite (by simp))).integrable (hF_cont j)
  -- The sum of the `c j * F j` is `f` at the finite part, since `C` is equivariant.
  have h_sum (u : GInf E (1 : l → ℤˣ)) (h : Gf E l) : ∑ j, c j * F j (u, h) = f h := by
    let k : GInf E (1 : n → ℤˣ) := (diag ((1, h₁), u, h)).1⁻¹
    have h_move : f h = gramForm (C (conjWeylRep κ 0 u⁻¹ (ϑ h)))
        (conjWeylRep O.columnCount O.detExp k (Ξ (U.block ε (h₁, h) * x))) := by
      rw [← hC k u⁻¹ (ϑ h) fun _ ↦ rfl, gramForm_conjWeylRep]
    simp only [F, ← mul_assoc (c _), ← h_coord, h_move]
    generalize conjWeylRep κ 0 u⁻¹ (ϑ h) = v
    conv_rhs => rw [pi_eq_sum_univ' v]
    simp [y, algFormCoeff_apply, -map_inv]
    rfl
  refine ⟨fun δ hδ h ↦ ?_, fun K _ hK ↦ ?_⟩
  · rw [← h_sum (δ.1 * 1) (δ.2 * h), ← h_sum 1 h]
    exact Finset.sum_congr rfl fun j _ ↦ congrArg (c j * ·) (hF_rat j δ hδ (1, h))
  -- The class sum of `f` is a linear combination of the periods of the `F j`.
  have h_class : ∫ h₂, ∑ j, c j * F j h₂ ∂(stdSpace E l).quotMeasure =
      (stdLevelIndex K : ℂ)⁻¹ * stdClassSum K f :=
    integral_quotMeasure_eq_classSum (fun δ hδ h₂ ↦ by simp only [hF_rat _ δ hδ h₂])
      (by simp [h_sum]) K hK (continuous_finsetSum _ fun j _ ↦ (hF_cont j).const_mul _)
  have h_period (j : WeylIndex l κ) : ∫ h₂, F j h₂ ∂(stdSpace E l).quotMeasure = 0 :=
    integral_conj_pairTheta_mul_algFormCoeff_eq_zero hO_fits h_twist h_reflect hθ h_hecke h_rank
      ε _ (b j) (g j) (1, h₁) hx (hφ j)
  simpa [integral_finsetSum _ fun j _ ↦ (hF_int j).const_mul _, integral_const_mul, h_period]
    using h_class

open scoped Classical in
/-- The case of `stdClassSum_gramForm_eq_zero` in which `ϑ h` is `kernelVector O b 𝔪 Ψ κ g h`, the
vector of the values at `(g, h)` of the conjugate theta kernels of the pair `O.W, I_l`, one for each
basis polynomial of weight `κ`, with the finite datum `Ψ` modulo the ideal `𝔪`, whose places lie in
the level `O.places`. Let the archimedean parameter `l₀` on `W = O.W` correspond to that on `I_n`
(`O.FitsParams`), and let the residue characters `O.tamePart` be nontrivial at the twist places. Let
the form `Ξ` on `U(I_n)` be killed by the hyperplane sums at the chosen places, by the theta descent
to `W`, and by the Hecke polynomial at the number `O.liftHeckeRoot w` for a split place `w` off the
level. Let `ε` split `I_n = I_N ⊕ I_l` with `2 #r + 2 #N + 3 < #n`, let `C` be conjugate-linear and
equivariant for the real points of the block `I_l` acting by `conjWeylRep`, and let `x` be supported
on `O.places`. If the level `K` fixes `Ψ` and its conjugate by `x` fixes `Ξ`, then the class sum
over `K` of the invariant inner product `gramForm` of `C (ϑ h)` with `Ξ ((h₁, h) x)` is zero. -/
lemma stdClassSum_gramForm_kernelVector_eq_zero (hO_fits : O.FitsParams l₀)
    (h_twist : ∀ i : O.TwistIndex, O.tamePart (O.twistPlace i) ≠ 1) {Ξ : O.FormV}
    (h_reflect : O.HyperplaneSumsAnnihilate Ξ) (hθ : O.normalizedDescent Ξ = 0)
    {w : FinPlace E} {hw : star w ≠ w} {hw_off : w ∉ O.places.conjClosure}
    (h_hecke : O.heckePolyOnForms hw hw_off (O.liftHeckeRoot w) Ξ = 0)
    (h_rank : 2 * card r + 2 * card N + 3 < card n) (ε : N ⊕ l ≃ n) {κ : InfinitePlace E → ℕ → ℕ}
    (C : (WeylIndex l κ → ℂ) →ₗ⋆[ℂ] WeylIndex n O.columnCount → ℂ)
    (hC : ∀ (g : GInf E (1 : n → ℤˣ)) (y : GInf E (1 : l → ℤˣ)) (ζ : WeylIndex l κ → ℂ),
      (∀ τ : InfinitePlace E, (g τ : GL n ℂ) = reindexGL ε (blockGL (1, y τ))) →
        conjWeylRep O.columnCount O.detExp g (C ζ) = C (conjWeylRep κ 0 y ζ))
    (b : AutChar E) {𝔪 : Modulus E} (h𝔪 : 𝔪.places ⊆ O.places) {Ψ : Matrix l r 𝔪.ResidueRing → ℂ}
    (g : G E O.signs) (h₁ : Gf E N) {x : Gf E n} (hx : x ∈ supportedOn n O.places)
    {K : Subgroup (Gf E l)} [hK : IsLevel K]
    (hΨ : ∀ k : stdLevel E l, (k : Gf E l) ∈ K → ∀ T : Matrix l r 𝔪.ResidueRing,
      Ψ ((𝔪.reductionGL k⁻¹).val * T) = Ψ T)
    (hΞ : ∀ k ∈ K, algFormRep O.columnCount O.detExp (x⁻¹ * U.block ε (1, k) * x) Ξ.val = Ξ.val) :
    stdClassSum K (fun h : Gf E l ↦
      gramForm (C (kernelVector O b 𝔪 Ψ κ g h)) (Ξ (U.block ε (h₁, h) * x))) = 0 := by
  -- The datum of the coordinate `j` is that of the basis polynomial `j`.
  let datum (j : WeylIndex l κ) : 𝒮 (O.W.hom (stdSpace E l)) := modDatum O.W (stdSpace E l) 𝔪 Ψ
    (polyVector _ (fockLetters O.signs O.numbering (-1) (nablaBasis ℂ _ κ j)))
  have h_vacuum (j : WeylIndex l κ) : projOn _ O.places.conjClosureᶜ (datum j) = datum j := by
    have h_disj : Disjoint 𝔪.places.conjClosure O.places.conjClosureᶜ :=
      Set.disjoint_compl_right_iff_subset.2 fun v hv ↦ hv.imp (h𝔪 ·) (h𝔪 ·)
    simp only [datum, modDatum, projOn_integrated, projOn_schrodingerOp_vacElem _ h_disj]
  -- A real point acts on the polynomial of the datum as on the Weyl module.
  have h_coord (j : WeylIndex l κ) (u : GInf E (1 : l → ℤˣ)) (h : Gf E l) :
      conjWeylRep κ 0 u⁻¹ (kernelVector O b 𝔪 Ψ κ g h) j =
        conj (pairTheta O.W (stdSpace E l) O.charW b (datum j) (g, u, h)) := by
    have h_def (i : WeylIndex l κ) : kernelVector O b 𝔪 Ψ κ g h i =
        conj (pairTheta O.W (stdSpace E l) O.charW b (datum i) (g, 1, h)) := rfl
    change (conjWeylMatrix κ 0 u⁻¹ *ᵥ kernelVector O b 𝔪 Ψ κ g h) j = _
    simp only [pairTheta, datum, modDatum, (by simp : (g, u, h) = (g, 1, h) * (1, u, 1)),
      ← rep_apply_apply, pairWeil_integrated_right, realPairWeil_fockLetters]
    simp [h_def, pairTheta, datum, modDatum, weylRep, schur_map, -map_inv, mulVec,
      dotProduct]
  -- It remains to show that `K` fixes the pairing: it fixes the kernel and the value of `Ξ`.
  refine (stdClassSum_gramForm_eq_zero hO_fits h_twist h_reflect hθ h_hecke h_rank ε C hC _
    (fun j ↦ ⟨1, g, b, datum j, h_vacuum j, by simp [h_coord]⟩) h₁ hx).2 K fun k hk h ↦ ?_
  lift k to stdLevel E l using hK.le hk
  have h_kernel : kernelVector O b 𝔪 Ψ κ g (h * k) = kernelVector O b 𝔪 Ψ κ g h := by
    have hΨk (T : Matrix l r 𝔪.ResidueRing) : Ψ ((𝔪.reductionGL k).val⁻¹ * T) = Ψ T := by
      simpa [-map_mul] using hΨ k hk T
    simp +unfoldPartialApp [kernelVector, modKernel_mul_stdLevel_right, hΨk]
  have h_form : Ξ (U.block ε (h₁, h * k) * x) = Ξ (U.block ε (h₁, h) * x) := by
    simpa [← mul_assoc, ← (U.block ε).map_mul, -map_mul] using
      congrArg (fun φ : AlgForm n O.columnCount O.detExp ↦ φ.val (U.block ε (h₁, h) * x)) (hΞ k hk)
  simp only [h_kernel, h_form]

/-- In rank one the idempotent `labelIdem` that the polynomial `X - 1` labels in the group algebra
of `GL_1(k)` is the mean over the group: each coefficient is the inverse of the group order. -/
lemma coeff_labelIdem_X_sub_one {k : Type} [Field k] [Finite k] (g : GL Unit k) :
    (labelIdem Unit (Polynomial.X - 1 : Polynomial k)).coeff g = (Nat.card (GL Unit k) : ℂ)⁻¹ := by
  -- The root `1` names the trivial character.
  have h_label : IsLabel (card Unit) (Polynomial.X - 1 : Polynomial k) :=
    ⟨Polynomial.monic_X_sub_C 1, (Polynomial.irreducible_X_sub_C 1).squarefree,
      Polynomial.natDegree_X_sub_C 1, by simp⟩
  have h_char : labelChar (faithfulChar k) (Polynomial.X - 1 : Polynomial k) =
      (detChar 1).rankPart 1 := by
    simpa using labelChar_X_sub_C (faithfulChar k) (1 : MulChar k ℂ)
  have h_value (s : GL Unit k) :
      (labelChar (faithfulChar k) (Polynomial.X - 1 : Polynomial k)).evalGL s = 1 := by
    simpa [h_char, Hall.evalGL, Hall.rankPart, detChar, -Matrix.det_unique,
      Matrix.det_eq_sign_charpoly_coeff] using MulChar.one_apply (R' := ℂ) s.det_ne_zero.isUnit
  simp only [labelIdem, ite_eq_left h_label, h_value]
  simp [groupAlgElem]

/-- Let `k` be a finite field, `χ ≠ 1` a character of `kˣ` and `l ≠ 0` a row of length one. The
hyperplane sum `∑ χ(det s)⁻¹ s` over the invertible `s = 1 + u l`, an element of the group algebra
of `GL_1(k)`, annihilates the idempotent of the label `X - 1`, the mean over the group. -/
lemma hyperplaneSum_mul_labelIdem_X_sub_one {k : Type} [Field k] [Finite k] {χ : MulChar k ℂ}
    (hχ : χ ≠ 1) {l : Unit → k} (hl : l ≠ 0) :
    hyperplaneSum χ l * labelIdem Unit (Polynomial.X - 1 : Polynomial k) = 0 := by
  classical
  -- The group fixes its mean, so a character sum remains.
  have : Fintype (GL Unit k) := .ofFinite _
  have h_sum : ∑ s : GL Unit k, (hyperplaneSum χ l).coeff s = 0 :=
    calc _ = ∑ s : GL Unit k with s ∈ hyperplaneGroup l, χ⁻¹ (s : Matrix Unit Unit k).det := by
          simp [coeff_hyperplaneSum_eq_ite, Finset.sum_filter]
      _ = 0 := (Finset.sum_subtype _ (by simp) _).trans (sum_inv_det_hyperplaneGroup_eq_zero hχ hl)
  ext x
  simp [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype, coeff_labelIdem_X_sub_one,
    ← Finset.sum_mul, h_sum]

open scoped Classical in
omit [WeilData E] in
/-- Let `O` be a descent pair `(W, I_n)` with `W` a line (index type `Unit`), and let the residue
characters `χ_w = O.tamePart w` be nontrivial at the chosen places `w`. The product of the groups
`GL_1(k_w)` acts on the forms on `U(I_n)` by `O.formAction`. Let `Ξ` lie in the image of the mean
over this product, which is the idempotent `tupleIdem` of the labels `X - 1`. Then `Ξ` is killed by
every tensor product (`piTensorElem`) of hyperplane sums `∑ χ_w(det s)⁻¹ s`, over the invertible
`s = 1 + u (v w)`, in which one row `v i` is not `0`. -/
lemma hyperplaneSum_apply_eq_zero_of_rank_one {O : DescentPair E Unit n}
    (h_chosen : ∀ i : O.ChosenIndex, O.tamePart (O.chosenPlace i) ≠ 1) {Ξ : O.FormV}
    (hΞ : Ξ ∈ (O.groupAlgAction (tupleIdem Unit fun _ : O.ChosenIndex ↦ Polynomial.X - 1)).range)
    (i : O.ChosenIndex) (v : ∀ i : O.ChosenIndex, Unit → ResField (O.chosenPlace i))
    (hv : v i ≠ 0) :
    O.formAction.asAlgebraHom
      (piTensorElem fun i : O.ChosenIndex ↦ hyperplaneSum (O.tamePart (O.chosenPlace i)) (v i)) Ξ =
      0 := by
  obtain ⟨y, rfl⟩ := hΞ
  have h_zero : (piTensorElem fun i ↦ hyperplaneSum (O.tamePart (O.chosenPlace i)) (v i)) *
      tupleIdem Unit (fun _ ↦ Polynomial.X - 1) = 0 :=
    piTensorElem_mul_eq_zero i (hyperplaneSum_mul_labelIdem_X_sub_one (h_chosen i) hv)
  rw [← Module.End.mul_apply, ← map_mul, h_zero, map_zero, LinearMap.zero_apply]

open scoped Classical in
/-- Periods of false lifts from a line vanish. Let the archimedean parameter `l₀` on `W` correspond
to that on `I_n` (`O.FitsParams`), and let the residue characters `O.tamePart` be nontrivial at all
places of the level. Let the form `Ξ` on `U(I_n)` be a false lift (`O.falseLiftsAt`): it lies in the
image of the mean over the product of the groups `GL_1(k_v)` at the chosen places `v`, and it is
killed by the theta descent `O.normalizedDescent` to `W` and by the Hecke polynomial at the number
`O.liftHeckeRoot w` for a split place `w` off the level. Let `ε` split `I_n = I_N ⊕ I_l` with
`2 #N + 5 < #n`, and let `x` be supported on `O.places`. Let each coordinate of `ϑ`, moved by the
real points of `U(I_l)`, be a multiple of a conjugate theta kernel (`pairTheta`) of the pair
`O.W, I_l` whose datum is the vacuum off `O.places` and their conjugates. Let `C` be
conjugate-linear and equivariant for the real points of `U(I_l)`, which act by the representation
`conjWeylRep` of the given weight. Then the invariant inner product `gramForm` of `C (ϑ h)` with
`Ξ ((h₁, h) x)` is left invariant under the rational points, and its class sum is zero at every
level `K` that fixes it. -/
theorem stdClassSum_gramForm_eq_zero_of_rank_one {O : DescentPair E Unit n}
    {l₀ : InfinitePlace E → Unit → ℤ} (hO_fits : O.FitsParams l₀)
    (h_chosen : ∀ i : O.ChosenIndex, O.tamePart (O.chosenPlace i) ≠ 1)
    (h_twist : ∀ i : O.TwistIndex, O.tamePart (O.twistPlace i) ≠ 1)
    {w : FinPlace E} {hw : star w ≠ w} {hw_off : w ∉ O.places.conjClosure} {Ξ : O.FormV}
    (hΞ : Ξ ∈ O.falseLiftsAt hw hw_off (tupleIdem Unit fun _ : O.ChosenIndex ↦ Polynomial.X - 1)
      O.normalizedDescent.ker)
    (ε : N ⊕ l ≃ n) (h_rank : 2 * card N + 5 < card n) {κ : InfinitePlace E → ℕ → ℕ}
    (C : (WeylIndex l κ → ℂ) →ₗ⋆[ℂ] WeylIndex n O.columnCount → ℂ)
    (hC : ∀ (g : GInf E (1 : n → ℤˣ)) (y : GInf E (1 : l → ℤˣ)) (ζ : WeylIndex l κ → ℂ),
      (∀ τ : InfinitePlace E, (g τ : GL n ℂ) = reindexGL ε (blockGL (1, y τ))) →
        conjWeylRep O.columnCount O.detExp g (C ζ) = C (conjWeylRep κ 0 y ζ))
    (ϑ : Gf E l → WeylIndex l κ → ℂ)
    (h_kernels : ∀ j : WeylIndex l κ, ∃ (c : ℂ) (g : G E O.signs) (b : AutChar E)
      (φ : 𝒮 (O.W.hom (stdSpace E l))),
      projOn (O.W.hom (stdSpace E l)) O.places.conjClosureᶜ φ = φ ∧
        ∀ (u : GInf E (1 : l → ℤˣ)) (h : Gf E l), conjWeylRep κ 0 u⁻¹ (ϑ h) j =
          c * conj (pairTheta O.W (stdSpace E l) O.charW b φ (g, u, h)))
    (h₁ : Gf E N) {x : Gf E n} (hx : x ∈ supportedOn n O.places) :
    let f (h : Gf E l) : ℂ := gramForm (C (ϑ h)) (Ξ (U.block ε (h₁, h) * x))
    (∀ δ ∈ (stdSpace E l).Γ, ∀ h : Gf E l, f (δ.2 * h) = f h) ∧
      ∀ (K : Subgroup (Gf E l)) [IsLevel K], K ≤ rightStabilizer f → stdClassSum K f = 0 := by
  obtain ⟨⟨hΞ_range, hΞ_hecke⟩, hΞ_descent⟩ := hΞ
  exact stdClassSum_gramForm_eq_zero hO_fits h_twist
    (hyperplaneSum_apply_eq_zero_of_rank_one h_chosen hΞ_range) hΞ_descent hΞ_hecke
    (by grind [card_unit]) ε C hC ϑ h_kernels h₁ hx

set_option backward.isDefEq.respectTransparency false in -- for rewriting products in `Gf`
omit [WeilData E] [Nonempty r] in
/-- Conjugates of the second block fix forms. Let `ε` split `I_n = I_N ⊕ I_l`, with `U.block ε` the
block diagonal embedding; `reduceAt` is reduction to the residue field and `inclMatrix e` the matrix
of the columns `e` of `1`. Let `A` in the maximal level `stdLevel E n` have columns `O.incl` equal
to `Y` at the chosen places, and rows `e'`, which lie in the block `N` through `rowInBlock`, equal
to the rows `O.incl` of `1` at the twist places. If `x` is supported at the chosen places and
`x⁻¹ (1, k) x` lies in `stdLevel E n` and fixes `Y`, then right translation (`algFormRep`) by the
conjugate of `(1, k)` by `x * A` fixes every form `Ξ`. -/
lemma algFormRep_conj_block_apply_eq_self (Ξ : O.FormV) (ε : N ⊕ l ≃ n) {x : Gf E n}
    (hx : x ∈ supportedOn n (.range O.chosenPlace)) {e' : r ↪ n} {rowInBlock : r → N}
    (he' : ⇑e' = ε ∘ inl ∘ rowInBlock) {A : stdLevel E n}
    {Y : ∀ i : O.ChosenIndex, Matrix n r (ResField (O.placeAt (inl i)))}
    (hA_col : ∀ i : O.ChosenIndex, (stdLevel.reduceAt (O.placeAt (inl i)) A).val *
      inclMatrix (ResField (O.placeAt (inl i))) O.incl = Y i)
    (hA_row : ∀ i : O.TwistIndex, (stdLevel.reduceAt (O.placeAt (inr i)) A).valᵀ *
      inclMatrix (ResField (O.placeAt (inr i))) e' =
        inclMatrix (ResField (O.placeAt (inr i))) O.incl)
    (k : stdLevel E l) (h_mem : x⁻¹ * U.block ε (1, k) * x ∈ stdLevel E n)
    (h_fixY : ∀ i : O.ChosenIndex,
      (stdLevel.reduceAt (O.placeAt (inl i)) ⟨_, h_mem⟩).val * Y i = Y i) :
    algFormRep O.columnCount O.detExp ((x * A.val)⁻¹ * U.block ε (1, k) * (x * A.val)) Ξ.val =
      Ξ.val := by
  let c : stdLevel E n := A⁻¹ * ⟨_, h_mem⟩ * A
  -- At the chosen places the columns `O.incl` of `c` are those of `1`, as `x⁻¹ (1, k) x` fixes `Y`.
  have h_col (i : O.ChosenIndex) :
      (stdLevel.reduceAt (O.placeAt (inl i)) c).1 * inclMatrix _ O.incl = inclMatrix _ O.incl := by
    simp [c, hA_col, h_fixY, inv_mul_eq_iff_eq_mul_of_invertible, -elim_inl, Matrix.mul_assoc]
  -- At the twist places the point `x` is trivial, so `x⁻¹ (1, k) x` reduces to the block matrix
  -- `(1, k)`; it fixes the rows `e'`. So the rows `O.incl` of `c` are those of `1`.
  have h_row (i : O.TwistIndex) :
      (stdLevel.reduceAt (O.placeAt (inr i)) c).1ᵀ * inclMatrix _ O.incl = inclMatrix _ O.incl := by
    obtain ⟨h_blk, h_red⟩ : ∃ h : U.block ε (1, k.1) ∈ stdLevel E n,
      stdLevel.reduceAt (O.twistPlace i) ⟨_, h⟩ =
        reindexGL ε (blockGL (1, stdLevel.reduceAt (O.twistPlace i) k)) := by
      simpa using! map_block_eq_blockGL (reduceAt (O.twistPlace i)) ε 1 k
    have h_eq : stdLevel.reduceAt (O.twistPlace i) ⟨_, h_mem⟩ = stdLevel.reduceAt (O.twistPlace i)
      ⟨_, h_blk⟩ :=
      (MonoidHom.eq_iff _).2
        (stdLevel.reduceAt_eq_one_of_atPlace (by simp [atPlace_twistPlace_eq_one hx]))
    have h_fix_rows : (stdLevel.reduceAt (O.twistPlace i) ⟨_, h_mem⟩).1ᵀ * inclMatrix _ e' =
        inclMatrix _ e' := by
      rw [h_eq.trans h_red, mul_inclMatrix]
      simp [← ext_iff, reindex_equiv ε, inclMatrix, he', eq_comm (α := N), Matrix.one_apply]
    -- Cancel `A` on both sides; `O.placeAt (inr i)` is `O.twistPlace i` by definition.
    simpa [c, ← hA_row, transpose_nonsing_inv, Matrix.mul_right_inj_of_invertible, -elim_inr,
      Matrix.mul_assoc] using! h_fix_rows
  -- By `smul_chosenGLRep_eq_apply_of_triangular`, `c` then acts on `Ξ` as the block `1`.
  simpa [c, mul_assoc, ← Pi.one_def] using (O.smul_chosenGLRep_eq_apply_of_triangular Ξ c 1
    (fun i ↦ by simpa using h_col i) (fun i ↦ by simpa using h_row i)).symm

open scoped Classical in
/-- Periods against point forms vanish. Let `O` be a descent pair `(W, I_n)`; its level `O.places`
consists of the chosen places and the twist places. Let the archimedean parameter `l₀` on `W`
correspond to that on `I_n` (`O.FitsParams`), and let the residue characters `O.tamePart` be
nontrivial at the twist places. Let the form `Ξ` on `U(I_n)` be killed by three things: the
hyperplane sums (character sums over the matrices `1 + u λ`) at the chosen places, the theta descent
`O.normalizedDescent` to `W`, and the Hecke polynomial `O.heckePolyOnForms` at the number
`O.liftHeckeRoot w` for a split place `w` off the level. Let `ε` split `I_n = I_N ⊕ I_l` with
`2 #r + 2 #N + 3 < #n`. Let `C`, from vectors of weight `κ` to vectors of weight `O.columnCount`, be
conjugate-linear and equivariant (`conjWeylRep`) for the real points of the second block. Let `x` be
supported at the chosen places. Let the level `K` fix the datum `Ψ` modulo the ideal `𝔪`, and after
conjugation by `x` fix the matrices `Y i`, each with independent columns. The places of `𝔪` lie in
`O.places` and the rows `e'` in the block `I_N`. Let `f h` be the inner product of `Ξ` with the
point form at `(h₁, h) x`. This form is supported on the class of `(h₁, h) x A` with value
`C (kernelVector O b 𝔪 Ψ κ g h)` there. Here `A = pointLift hY e'` is an integral point with columns
`Y` at the chosen places. The vector `kernelVector O b 𝔪 Ψ κ g h` lists the values at `(g, h)` of
the conjugate theta kernels of the pair `W, I_l` with datum `Ψ`, twisted by `b`, one for each basis
polynomial of weight `κ`. Then the class sum of `f` over `K` (the sum over the double cosets
weighted by `1 / #Aut`) is zero. -/
lemma stdClassSum_period_eq_zero (hO_fits : O.FitsParams l₀)
    (h_twist : ∀ i : O.TwistIndex, O.tamePart (O.twistPlace i) ≠ 1) {Ξ : O.FormV}
    (h_reflect : O.HyperplaneSumsAnnihilate Ξ) (hθ : O.normalizedDescent Ξ = 0)
    {w : FinPlace E} {hw : star w ≠ w} {hw_off : w ∉ O.places.conjClosure}
    (h_hecke : O.heckePolyOnForms hw hw_off (O.liftHeckeRoot w) Ξ = 0)
    (h_rank : 2 * card r + 2 * card N + 3 < card n) (ε : N ⊕ l ≃ n) {κ : InfinitePlace E → ℕ → ℕ}
    {Y : ∀ i : O.ChosenIndex, Matrix n r (ResField (O.placeAt (inl i)))} {e' : r ↪ n}
    (hY : ∀ i : O.ChosenIndex, Function.Injective (Y i).mulVec)
    (C : (WeylIndex l κ → ℂ) →ₗ⋆[ℂ] WeylIndex n O.columnCount → ℂ)
    (hC : ∀ (g : GInf E (1 : n → ℤˣ)) (y : GInf E (1 : l → ℤˣ)) (ζ : WeylIndex l κ → ℂ),
      (∀ τ : InfinitePlace E, (g τ : GL n ℂ) = reindexGL ε (blockGL (1, y τ))) →
        conjWeylRep O.columnCount O.detExp g (C ζ) = C (conjWeylRep κ 0 y ζ))
    {b : AutChar E} {𝔪 : Modulus E} (h𝔪 : 𝔪.places ⊆ O.places) {Ψ : Matrix l r 𝔪.ResidueRing → ℂ}
    {g : G E O.signs} {h₁ : Gf E N} {x : Gf E n} (hx : x ∈ supportedOn n (.range O.chosenPlace))
    {K : Subgroup (Gf E l)} [hK : IsLevel K] {f : Gf E l → ℂ}
    (hf : ∀ h : Gf E l, f h = inner ℂ
      (pointForm (Y := Y) (U.block ε (h₁, h) * x) hY e' (C (kernelVector O b 𝔪 Ψ κ g h))) Ξ)
    {rowInBlock : r → N} (he' : ⇑e' = ε ∘ inl ∘ rowInBlock)
    (hK_fix : ∀ k : stdLevel E l, (k : Gf E l) ∈ K →
      (∀ T : Matrix l r 𝔪.ResidueRing, Ψ ((𝔪.reductionGL k⁻¹).val * T) = Ψ T) ∧
      ∃ h_mem : x⁻¹ * U.block ε (1, k) * x ∈ stdLevel E n, ∀ i : O.ChosenIndex,
        (stdLevel.reduceAt (O.placeAt (inl i)) ⟨_, h_mem⟩).val * Y i = Y i) :
    stdClassSum K f = 0 := by
  -- The point form evaluates `Ξ` at `(h₁, h) x * A` for the integral element
  -- `A = pointLift hY e'`: its columns are `Y` at the chosen places, its rows `e'` the rows
  -- `O.incl` of `1` at the twist places.
  let A : stdLevel E n := pointLift hY e'
  obtain ⟨hA_on, hA_col, hA_row⟩ := isPointLift_pointLift hY e'
  have h_value (h : Gf E l) : f h =
      gramForm (C (kernelVector O b 𝔪 Ψ κ g h)) (Ξ (U.block ε (h₁, h) * (x * A.val))) := by
    rw [hf, inner_pointForm, mul_assoc]
  have h_supp : x * A.val ∈ supportedOn n O.places :=
    mul_mem (supportedOn_mono (by simp) hx) hA_on
  have hΨ (k : stdLevel E l) (hk : (k : Gf E l) ∈ K) (T : Matrix l r 𝔪.ResidueRing) :
      Ψ ((𝔪.reductionGL k⁻¹).val * T) = Ψ T :=
    (hK_fix k hk).1 T
  -- The conjugate of the level by `x * A` fixes `Ξ`.
  have hΞ (k : Gf E l) (hk : k ∈ K) :
      algFormRep O.columnCount O.detExp ((x * A.val)⁻¹ * U.block ε (1, k) * (x * A.val)) Ξ.val =
        Ξ.val := by
    lift k to stdLevel E l using hK.le hk
    obtain ⟨-, h_mem, h_fixY⟩ := hK_fix k hk
    exact algFormRep_conj_block_apply_eq_self Ξ ε hx he' hA_col hA_row k h_mem h_fixY
  rw [funext h_value]
  exact stdClassSum_gramForm_kernelVector_eq_zero hO_fits h_twist h_reflect hθ h_hecke h_rank
    ε C hC b h𝔪 g h₁ h_supp hΨ hΞ

omit [WeilData E] [Nonempty r] in
/-- Forms are fixed by the second block near the point of a divided lattice. A `DividedSplitting`
`V` is a splitting `V.ε` of `I_n = I_N ⊕ I_l` with the indices of `W` and those of a further index
type `ι` embedded in `N`; the embedding `z` is a parameter without conditions. A divided lattice `L`
is a lattice `γ 𝒪ⁿ`, with `γ = L.point` supported at the chosen places of `O`, that lies between
`ϖ 𝒪ⁿ` and `𝒪ⁿ` there, for the idele `ϖ = O.genIdele`. Every form `Ξ` in `O.FormV` on `U(I_n)` is
fixed by right translation (`algFormRep`) by `γ⁻¹ (1, k) γ`, with `(1, k) = U.block V.ε (1, k)`, if
the integral point `k` of the second block `I_l` is `1` modulo the square of the product of the
chosen places (`O.chosenModulusSq`). -/
lemma DividedSplitting.algFormRep_conj_block_eq_self {z : r ↪ l} (V : DividedSplitting N l ι O z)
    {Ξ : O.FormV} (L : DividedLattice O) (k : stdLevel E l)
    (hk : O.chosenModulusSq.reductionGL k = 1) :
    algFormRep O.columnCount O.detExp (L.point⁻¹ * U.block V.ε (1, k) * L.point) Ξ.val = Ξ.val := by
  -- The block `(1, k)` is integral, and it is `1` modulo the square of the chosen places.
  obtain ⟨h_mem, h_block⟩ := map_block_eq_blockGL O.chosenModulusSq.reduction V.ε 1 k
  have h_one : O.chosenModulusSq.reductionGL ⟨_, h_mem⟩ = 1 := by
    rw [Modulus.reductionGL] at hk ⊢
    rw [h_block, hk, map_one, mk_one_one, map_one, map_one]
  -- The conjugate is integral and `1` modulo the chosen places; at the twist places it fixes the
  -- first block.
  obtain ⟨h_mem', h_conj⟩ := L.reduceAt_conj_eq_one _ h_one
  have h_incl : ⇑O.incl = V.ε ∘ inl ∘ V.fixedEmb := (funext V.equiv_inl_fixedEmb).symm
  have h_fixY (i : O.ChosenIndex) : (stdLevel.reduceAt (O.placeAt (inl i)) ⟨_, h_mem'⟩).1 *
      inclMatrix _ O.incl = inclMatrix _ O.incl := by
    have h_red : stdLevel.reduceAt (O.placeAt (inl i)) ⟨_, h_mem'⟩ = 1 := h_conj i
    rw [h_red]
    exact Matrix.one_mul _
  -- So `algFormRep_conj_block_apply_eq_self` applies with `A = 1`.
  have h_col (i : O.ChosenIndex) : (stdLevel.reduceAt (O.placeAt (inl i)) (1 : stdLevel E n)).1 *
      inclMatrix (ResField (O.placeAt (inl i))) O.incl = inclMatrix _ O.incl := by
    rw [map_one, Units.val_one, Matrix.one_mul]
  have h_row (i : O.TwistIndex) : (stdLevel.reduceAt (O.placeAt (inr i)) (1 : stdLevel E n)).1ᵀ *
      inclMatrix (ResField (O.placeAt (inr i))) O.incl = inclMatrix _ O.incl := by
    rw [map_one, Units.val_one, transpose_one, Matrix.one_mul]
  simpa using algFormRep_conj_block_apply_eq_self Ξ V.ε L.mem_supportedOn h_incl h_col h_row k
    h_mem'
    h_fixY

open scoped Classical in
/-- Slices of false lifts are orthogonal to theta kernels. Let `O` be a descent pair `(W, I_n)`, and
let `V` split `I_n = I_N ⊕ I_l` with the indices of `W` and those of a further index type `ι`
embedded in `N`. Let `L` be a divided lattice `γ 𝒪ⁿ`, with `γ = L.point` supported at the chosen
places. Let the archimedean parameter `l₀` on `W` correspond to that on `I_n` (`O.FitsParams`), and
let the residue characters `O.tamePart` be nontrivial at the twist places. Let the form `Ξ` on
`U(I_n)` be killed by the hyperplane sums at the chosen places, by the theta descent to `W` and by
the Hecke polynomial at the number `O.liftHeckeRoot w`, for a split place `w` off the level, and let
`2 #r + 2 #N + 3 < #n`. Let `ϖ` generate the square of the product of the chosen places. The product
form `V.productForm L (x, h) y η` is supported on the class of `(x, h) γ`, with value the Cartan
product of `y`, of weight `O.colsPlus`, and `η`, of weight `O.colsMinus`. Take for `η` the conjugate
of `kernelVector … g h`, the vector of the conjugate theta kernels at `(g, h)` of the pair `W, I_l`
with any datum `Ψ` modulo `ϖ`. Then the class sum over `h`, at the principal level `ϖ` of `U(I_l)`,
of the inner product of this form with `Ξ` is zero. -/
lemma DividedSplitting.stdClassSum_inner_productForm_eq_zero {z : r ↪ l}
    (V : DividedSplitting N l ι O z) (hO_fits : O.FitsParams l₀)
    (h_twist : ∀ i : O.TwistIndex, O.tamePart (O.twistPlace i) ≠ 1) {Ξ : O.FormV}
    (h_reflect : O.HyperplaneSumsAnnihilate Ξ) (hθ : O.normalizedDescent Ξ = 0)
    {w : FinPlace E} {hw : star w ≠ w} {hw_off : w ∉ O.places.conjClosure}
    (h_hecke : O.heckePolyOnForms hw hw_off (O.liftHeckeRoot w) Ξ = 0)
    (h_rank : 2 * card r + 2 * card N + 3 < card n) {ϖ : RingOfIntegers E} [Fact (ϖ ≠ 0)]
    (hϖ : O.chosenModulusSq.ideal = Ideal.span {ϖ}) (L : DividedLattice O)
    (x : Gf E N) (y : WeylIndex N O.colsPlus → ℂ) (b : AutChar E)
    (Ψ : Matrix l r O.chosenModulusSq.ResidueRing → ℂ) (g : G E O.signs) :
    stdClassSum (principalLevel l ϖ) (fun h : Gf E l ↦ inner ℂ (V.productForm L (x, h) y
      (star (kernelVector O b O.chosenModulusSq Ψ O.colsMinus g h))) Ξ) = 0 := by
  -- Apply the vanishing of periods to the conjugate-linear map `ζ ↦ y · conj ζ` and the point `γ`.
  let C : (WeylIndex l O.colsMinus → ℂ) →ₗ⋆[ℂ] WeylIndex n O.columnCount → ℂ :=
    cartanProduct V.ε 1 y ∘ₛₗ (starLinearEquiv ℂ).1
  -- `C` is equivariant for the real group of the second block.
  have hC (g : GInf E (1 : n → ℤˣ)) (u : GInf E (1 : l → ℤˣ)) (ζ : WeylIndex l O.colsMinus → ℂ)
      (hg : ∀ τ : InfinitePlace E, (g τ : GL n ℂ) = reindexGL V.ε (blockGL (1, u τ))) :
      conjWeylRep O.columnCount O.detExp g (C ζ) = C (conjWeylRep O.colsMinus 0 u ζ) := by
    have h_inv (τ : InfinitePlace E) : (g τ).1.1⁻¹ = (g τ).1.1ᴴ := by
      simpa using U.form_mul_inv_eq (g τ)
    -- In the first block the columns of `conj g` are those of `1`; in the second those of its
    -- inverse transpose, which is `g`, are given by `u`.
    have h_first (τ : InfinitePlace E) : ((g τ).1.1.map conj).submatrix id (V.ε ∘ inl) =
        (1 : Matrix n n ℂ).submatrix id (V.ε ∘ inl) := by
      simp [hg, ← ext_iff, reindex_equiv V.ε, Matrix.one_apply]
    have h_second (τ : InfinitePlace E) : ((g τ).1.1ᴴ.map conj)ᵀ.submatrix id (V.ε ∘ inr) =
        (1 : Matrix n n ℂ).submatrix id (V.ε ∘ inr) * (u τ).1.1.map (conj ∘ conj) := by
      simp [hg, ← ext_iff, Matrix.mul_apply, reindex_equiv V.ε, Matrix.one_apply]
    -- `conjWeylRep` acts through the conjugate matrix `gc`, which `weylRep_mulVec_cartanProduct`
    -- moves into `cartanProduct`; there it acts on the two factors by the Schur maps of those
    -- columns.
    let gc (τ : InfinitePlace E) : GL n ℂ := GeneralLinearGroup.map conj (g τ).1
    suffices h_factors : cartanProduct V.ε gc y (star ζ) =
        cartanProduct V.ε 1 y (star (conjWeylRep O.colsMinus 0 u ζ)) by
      simpa [gc, C, conjWeylRep, weylRep_mulVec_cartanProduct, V.hasColumnsBelow,
        HasColumnsBelow] using! h_factors
    simp [gc, conjWeylRep, cartanProduct, weylRep, star_mulVec, ← mulVec_transpose,
      conjTranspose_transpose, V.hasColumnsBelow.2.schur_mul_schur, ← map_inv, h_inv, h_first,
      h_second]
  have C_apply (ζ : WeylIndex l O.colsMinus → ℂ) : C ζ = cartanProduct V.ε 1 y (star ζ) := rfl
  simp_rw [DividedSplitting.productForm, LinearMap.comp_apply, inner_classForm, ← C_apply]
  refine stdClassSum_gramForm_kernelVector_eq_zero hO_fits h_twist h_reflect hθ h_hecke h_rank V.ε
    C hC b (by simp [places_levelModulus_false]) g x (supportedOn_mono (by simp) L.mem_supportedOn)
    (fun k hk ↦ by simp [(Modulus.mem_principalLevel_iff hϖ k).1 hk]) fun k hk ↦ ?_
  lift k to stdLevel E l using principalLevel_le_stdLevel hk
  exact V.algFormRep_conj_block_eq_self L k ((Modulus.mem_principalLevel_iff hϖ k).1 hk)

end New.Rows

end MemberOrthogonality
