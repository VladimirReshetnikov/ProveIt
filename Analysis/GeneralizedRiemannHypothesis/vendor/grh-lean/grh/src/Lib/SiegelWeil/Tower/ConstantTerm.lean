import Lib.SiegelWeil.SingularForms.UnimodularCoefficients
import Lib.SiegelWeil.Tower.LineTerms
import Lib.SiegelWeil.Tower.PrincipalIdeles
import Lib.Weil.DualPair.ThetaIntegrals

/-!
# The constant term of a theta integral, unfolded along isotropic lines

The constant term, along an isotropic line of the source space `W'`, of the theta kernel and of the
theta integral over the unitary group of the target space.

* `New.Exchange.constTermAt`: the term of a rational vector of the target; it is 0 unless the vector
  is isotropic.
* `New.Exchange.hasSum_constTermAt`, `New.Exchange.integral_thetaIntegral_lineRadical`: the constant
  term of the theta kernel is the sum of these, and, if the kernel is bounded on the target group
  (`IsTargetBounded`), that of the theta integral is the integral of this sum over the target group.
* `New.Exchange.radicalSubgroup`, `New.Exchange.radicalHaar`: the radical of the stabiliser of a
  line of the target space and its Haar measure; `New.Exchange.lintegral_radicalHaar_conj_lineLevi`
  gives the module of conjugation by the Levi factor.
* `New.Exchange.exists_unfold_constant_term`: if the term of the zero vector vanishes and the
  integrand is integrable, the sum unfolds along the isotropic lines (one orbit, by Witt's theorem)
  to an integral in Iwasawa coordinates.

Throughout, `A : W'.Splitting W Unit` writes the source space `W'` as a hyperbolic plane plus `W`.
Where the target space is `V'`, it is split in the same way by `X : V'.Splitting V Unit`, and
`splittingLine X` is the isotropic line spanned by the vector `X.k`. The bracket `[U(V)]` denotes
the quotient of the adelic unitary group `G E t` of `V` by its rational points.

Notions from other files:
* `New.Space.Splitting`: A decomposition V = (lE^p ⊕ kE^p) ⊥ iV₀ over E: isotropic frames l, k with
  l*Jk = 1, an isometry i from V₀ orthogonal to both, and rk V = rk V₀ + 2p.
* `New.Space.Splitting.radicalElement`, `New.Exchange.lineRadical`, `New.Exchange.lineLevi`:
  elements of the unipotent radical and of the Levi factor of the stabiliser of the isotropic line.
* `New.Space.Splitting.homSlice`: The term f[x], a datum on Hom(W, V), of a datum f on Hom(W', V)
  at the value x on k; θ(f) is the sum of the θ(f[x]) over rational x, and
  `New.Space.Splitting.thetaTerm` is θ((ω(g, h) f)[x]), with ω the Weil representation
  `New.pairWeil` of the pair.
* `New.pairTheta`, `New.Exchange.thetaIntegral`: the theta kernel θ(ω(g, h) f) and its integral
  over h in [U(V)].
* `New.Exchange.lineTerm`: for an adele ξ, the map `lineTerm A X true ξ` from data on Hom(W', V') to
  data on Hom(W, V) sends f to the zero term (the mean along the line of `X`) of the term
  f[ξ • X.k]; the model `false` does the same with the roles of the two lines exchanged.

## Relation to the literature

Known; see `Lib.SiegelWeil.Tower.LargeSideConstantTerm` for sources.
-/

noncomputable section

namespace New.Exchange

open Matrix MeasureTheory Measure Units MulAction Space Splitting Submodule Pointwise Function Equiv
  WeilData

variable {E : Type} [Field E] [CMType E] [WeilData E] {n n' r r' : Type} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r] [Fintype r'] [DecidableEq r']
  {s : n → ℤˣ} {s' : n' → ℤˣ} {t : r → ℤˣ} {t' : r' → ℤˣ} {W : Space E n s} {W' : Space E n' s'}
  {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit) (X : V'.Splitting V Unit)
  (a b : AutChar E)

/-- The probability measure on the parameters of `lineRadical`: the product of the measures of
adelic matrices modulo rational matrices. Integration against it is the mean over the radical of
the stabiliser of the line modulo its rational points, that is, the constant term. -/
abbrev radicalMeasure : Measure (Matrix n Unit (𝔸 E) × Matrix Unit Unit (𝔸 E)) :=
  (ratMatrices E n Unit).quotMeasure.prod (ratMatrices E Unit Unit).quotMeasure

open scoped Classical in
/-- The term of the rational vector `x` of `V` in the constant term along the line of `A`: zero
unless `x` is isotropic, and then the mean of the term of `x` in the theta kernel of `f` over the
radical modulo its centre and its rational points. -/
def constTermAt (x : Matrix r Unit E) (f : 𝒮 (W'.hom V)) : ℂ :=
  if xᴴ * V.J * x = 0 then
    ⨍ y : Matrix n Unit (𝔸 E), A.thetaTerm V 1 1 f (lineRadical A (y, 0)) x 1
      ∂(ratMatrices E n Unit).quotMeasure
  else 0

/-- The term of the rational vector `x` in the theta kernel at the point `lineRadical A q` of the
radical: the central coordinate `q.2` acts by the character `ψ (tr (xᴴ J x q.2))`, where `ψ` is the
standard additive character and `J` the Gram matrix of `V`, and `q.1` gives the point at which the
term `f[x] = A.homSlice V (V.x⁻¹ x) f` is evaluated. The matrices `V.x⁻¹` and `W.x⁻¹` pass to the
adelic coordinates in which the forms are the standard ones, `stdForm`; `matrixToVec` flattens a
matrix to a vector. The right side does not involve the characters `a`, `b`. -/
lemma thetaTerm_lineRadical (x : Matrix r Unit E) (f : 𝒮 (W'.hom V))
    (q : Matrix n Unit (𝔸 E) × Matrix Unit Unit (𝔸 E)) :
    A.thetaTerm V a b f (lineRadical A q) x 1 =
      (stdAddChar E (q.2 * (xᴴ * V.J * x).map toAdele).trace : ℂ) *
        A.homSlice V (V.x⁻¹.val * x.map toAdele) f
          (matrixToVec (V.x⁻¹.val * x.map toAdele * (W.x⁻¹.val * q.1)ᴴ * stdForm E s)) := by
  -- `θ` is evaluation at `0`, and the Heisenberg operator `ϱ` translates the argument.
  rw [Splitting.thetaTerm, homSlice_radicalElement, gram_at_point_eq_map]
  simp [← mul_assoc, ← map_mul, theta_apply, rho_apply, Heisenberg.beta_zero_left]

/-- The term `constTermAt A x f` is the integral of the term of `x` in the theta kernel of `f` over
the whole radical modulo its rational points, for any automorphic characters `a` and `b`. -/
lemma constTermAt_eq_integral (x : Matrix r Unit E) (f : 𝒮 (W'.hom V)) :
    constTermAt A x f = ∫ q : Matrix n Unit (𝔸 E) × Matrix Unit Unit (𝔸 E),
      A.thetaTerm V a b f (lineRadical A q) x 1 ∂radicalMeasure := by
  classical
  -- The indicator of `xᴴ * V.J * x = 0` is the mean of the character `ψ (tr (xᴴ * V.J * x * z))`
  -- of `z`, so the left side is an integral over the product.
  have h_indicator : (if xᴴ * V.J * x = 0 then 1 else 0 : ℂ) =
      ∫ z : Matrix Unit Unit (𝔸 E), (stdAddChar E ((xᴴ * V.J * x).map toAdele * z).trace : ℂ)
        ∂(ratMatrices E Unit Unit).quotMeasure := by
    rw [← isDualFamily_ratMatrices.quotMean_eq_ite, ← average_quotMeasure_eq_quotMean _ volume
      (isDualFamily_ratMatrices.periodic _), average_eq_integral]
  rw [constTermAt, ← mul_boole, h_indicator, average_eq_integral, ← integral_prod_mul]
  congr with q
  simp [thetaTerm_lineRadical, trace_mul_comm q.2, mul_comm (stdAddChar E _ : ℂ)]

/-- The terms `constTermAt` of all rational vectors of `V` sum to the constant term of the theta
kernel of `f`, that is, to its integral over the radical of the stabiliser of the line of `A`
modulo rational points. -/
lemma hasSum_constTermAt {f : 𝒮 (W'.hom V)} :
    HasSum (fun x : r → E ↦ constTermAt A (replicateCol Unit x) f)
      (∫ q : Matrix n Unit (𝔸 E) × Matrix Unit Unit (𝔸 E),
        pairTheta W' V a b f (lineRadical A q, 1) ∂radicalMeasure) := by
  -- Integrate the expansion `hasSum_theta_homSlice` of the theta kernel term by term.
  let bound (x : Matrix r Unit E) : ℝ :=
    ‖(W.hom V).θ‖ * ‖(A.homSource V).slice (toAdele ∘ uncurry x) f‖
  have h_summable : Summable bound :=
    (((A.homSource V).summable_norm_slice f).mul_left _).comp_injective uncurry_injective
  -- Up to a scalar of norm one, each term is a value of the function `slice x f`.
  have h_le (x : Matrix r Unit E) (q) : ‖A.thetaTerm V a b f (lineRadical A q) x 1‖ ≤ bound x := by
    rw [thetaTerm_lineRadical, norm_mul, Circle.norm_coe, one_mul, homSlice_eq_slice]
    exact norm_apply_le (W.hom V) _ _
  have h_expand (q) : HasSum (fun x : Matrix r Unit E ↦ A.thetaTerm V a b f (lineRadical A q) x 1)
      (pairTheta W' V a b f (lineRadical A q, 1)) :=
    A.hasSum_theta_homSlice V (pairWeil W' V a b (lineRadical A q, 1) f)
  let column : (r → E) ≃ Matrix r Unit E := piCongrRight fun _ ↦ (funUnique Unit E).symm
  change HasSum ((fun x : Matrix r Unit E ↦ constTermAt A x f) ∘ column) _
  simp_rw [column.hasSum_iff, constTermAt_eq_integral A a b]
  exact hasSum_integral_of_dominated_convergence (fun x _ ↦ bound x)
    (fun x ↦ by fun_prop [Splitting.thetaTerm]) (fun x ↦ .of_forall (h_le x))
    (.of_forall fun _ ↦ h_summable) (by simp) (.of_forall h_expand)

/-- The term of the zero vector is the theta functional of `Hom(W, V)` at the term of `f` at `0`. -/
lemma constTermAt_zero (f : 𝒮 (W'.hom V)) :
    constTermAt A 0 f = θ (W.hom V) (A.homSlice V 0 f) := by
  simp [constTermAt, Splitting.thetaTerm, homSlice_radicalElement, matrixToVec_zero,
    Heisenberg.Rep.rho_zero_apply, theta_apply]

/-- For `ξ ≠ 0`, the term of the rational vector `ξ • X.k` on the isotropic line of `X` in the
constant term along the line of `A` (`constTermAt A`, defined as the mean of its theta term over the
radical) equals the theta functional of `Hom(W, V)` at `lineTerm A X true ξ f`. That is the
translate of `f` by `ξ • X.kAdelic * A.kCoord` (`X.kAdelic` is the adelic vector spanning the line
of `X`, `A.kCoord` the coordinate along the `k`-frame of `A`), followed by the zero terms along the
line of `A` and then of `X`. -/
lemma constTermAt_smul_k {ξ : E} (hξ : ξ ≠ 0) {f : 𝒮 (W'.hom V')} :
    constTermAt A (ξ • X.k) f = θ (W.hom V) (lineTerm A X true (toAdele ξ) f) := by
  -- The right side is the mean of a periodic function `F` over `𝔸 ^ n` modulo `E ^ n`.
  let F (y : Unit × n → 𝔸 E) : ℂ := A.homSlice V' (toAdele ξ • X.kAdelic) f
    ((X.homTarget W).iAdelic *ᵥ 0 + (X.homTarget W).kAdelic *ᵥ y)
  have hF : IsContPeriodic (ratVectors E (Unit × n)) F :=
    (X.homTarget W).isContPeriodic_along_k _ 0
  have h_mean : θ (W.hom V) (lineTerm A X true (toAdele ξ) f) =
      quotMean (ratVectors E (Unit × n)) F := Splitting.zeroTerm_apply _ 0
  -- Substitute `y ↦ ξ • yᴴ`, which is onto as `ξ ≠ 0` and keeps rational points.
  let φ : Matrix n Unit (𝔸 E) →+ (Unit × n → 𝔸 E) :=
    .mk' (fun y ↦ toAdele ξ • matrixToVec yᴴ) (by simp [matrixToVec_add])
  have h_cont : Continuous φ := show Continuous fun y : Matrix n Unit (𝔸 E) ↦
    toAdele ξ • matrixToVec yᴴ by fun_prop [matrixToVec]
  have h_rat : ∀ y ∈ ratMatrices E n Unit, φ y ∈ ratVectors E (Unit × n) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨ξ • matrixToVec xᴴ, by aesop (add simp conjTranspose_map_toAdele)⟩
  have h_surj : Surjective φ := fun y ↦ ⟨(toAdele ξ⁻¹ • vecToMatrix y)ᴴ, by
    simp [φ, smul_smul, ← map_mul, hξ, star_toAdele, matrixToVec_smul, matrixToVec_vecToMatrix]⟩
  have hFφ : IsContPeriodic (ratMatrices E n Unit) fun y ↦ F (φ y) :=
    ⟨hF.1.comp h_cont, fun γ hγ y ↦ by simp only [map_add, hF.2 _ (h_rat γ hγ)]⟩
  have h_iso : (ξ • X.k)ᴴ * V'.J * (ξ • X.k) = 0 := by simp
  have h_integrand (y : Matrix n Unit (𝔸 E)) :
      A.thetaTerm V' 1 1 f (lineRadical A (y, 0)) (ξ • X.k) 1 = F (φ y) := by
    simp only [thetaTerm_lineRadical, F, homTarget_kAdelic]
    simp [X.k.map_smulₛₗ _ toAdele, φ, kAdelic, kronecker_mulVec_eq_matrixToVec, dualFrame,
      Matrix.mul_assoc, matrixToVec_smul, mulVec_smul, vecToMatrix_matrixToVec, -transpose_mul]
  rw [h_mean, ← quotMean_comp _ φ hF h_rat h_surj h_cont,
    ← average_quotMeasure_eq_quotMean _ volume hFφ]
  simp only [constTermAt, ite_eq_left h_iso, h_integrand]

/-- Suppose the theta kernel of `f` grows at most like a power of the height on the group of `W'`,
uniformly on the group of `V` (`IsTargetBounded`). Then the constant term at `g` along the line of
`A` of the theta integral of `f` (characters `a`, `b` of [U(1)]) equals the integral over `h` in
`[U(V)]` of the sum of `constTermAt` over the rational vectors `x` of `V` for
`pairWeil W' V a b (g, h) f`. That constant term is the mean over the radical `lineRadical` modulo
its rational points. A term `constTermAt` is zero unless `x` is isotropic, and otherwise the mean of
the term of `x` in the theta kernel over the radical modulo its centre and rational points. Here
`[U(V)]` is the adelic unitary group `G E t` of `V` modulo its rational points. -/
lemma integral_thetaIntegral_lineRadical {f : 𝒮 (W'.hom V)} (hf : IsTargetBounded W' V f)
    (g : G E s') :
    ∫ q : Matrix n Unit (𝔸 E) × Matrix Unit Unit (𝔸 E),
        thetaIntegral W' V a b f (lineRadical A q * g) ∂radicalMeasure =
      ∫ h : G E t, ∑' x : r → E, constTermAt A (replicateCol Unit x) (pairWeil W' V a b (g, h) f)
        ∂V.quotMeasure := by
  obtain ⟨B, C, h_growth⟩ := hf
  obtain ⟨K, hK, h_cover⟩ := exists_isCompact_rat_mul_radicalElement_mem A
  -- The radical is compact modulo rational points, so the height, which is invariant under
  -- them, is bounded on its translate by `g`.
  obtain ⟨D, hD⟩ : ∃ D : ℝ, ∀ x : G E s', ∀ γ ∈ W'.Γ,
      γ * x ∈ (fun y ↦ y * g) '' K → C * W'.height x ^ B ≤ D :=
    exists_mul_height_pow_le (hK.image_of_continuous _) C
  have h_bound (q) (h : G E t) : ‖pairTheta W' V a b f (lineRadical A q * g, h)‖ ≤ D := by
    obtain ⟨y, z, h_rat, h_mem⟩ := h_cover (W.x⁻¹.val * q.1) (toAdele (2 : E) • q.2)
    exact (h_growth a b _ h).trans (hD _ (A.radicalElement y z) h_rat ⟨_, h_mem, mul_assoc _ _ g⟩)
  -- Sum the terms by `hasSum_constTermAt`; what remains is Fubini for a bounded continuous kernel.
  simp only [(hasSum_constTermAt A a b).tsum_eq, ← pairTheta_mul, Prod.mk_mul_mk, one_mul,
    thetaIntegral]
  exact integral_integral_swap (.of_bound (by fun_prop) D (.of_forall fun p ↦ h_bound p.1 p.2))

/-- Coordinates on the radical of the stabiliser of a line: a column and a hermitian scalar. -/
abbrev RadicalCoord (E r : Type) [Field E] [CMType E] : Type :=
  Matrix r Unit (𝔸 E) × selfAdjoint (Matrix Unit Unit (𝔸 E))

/-- The hermitian part `(b + b*) / 2`. -/
def hermitianPart (b : Matrix Unit Unit (𝔸 E)) : selfAdjoint (Matrix Unit Unit (𝔸 E)) :=
  ⟨_, .add_star_self (toAdele (2⁻¹ : E) • b)⟩

/-- The point of the radical of the stabiliser of the line of `X` with given coordinates. -/
def radicalPoint (p : RadicalCoord E r) : G E t' := X.radicalElement p.1 p.2.val

omit [WeilData E] in
lemma coe_hermitianPart (b : Matrix Unit Unit (𝔸 E)) :
    (hermitianPart b).val = toAdele (2⁻¹ : E) • (b + bᴴ) := by
  simp [hermitianPart, star_eq_conjTranspose, star_toAdele, smul_add]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- The point `X.radicalElement c b` depends only on the hermitian part of `b`. -/
lemma radicalPoint_hermitianPart (c : Matrix r Unit (𝔸 E)) (b : Matrix Unit Unit (𝔸 E)) :
    radicalPoint X (c, hermitianPart b) = X.radicalElement c b := by
  -- `b` enters the matrix only through `b + bᴴ`.
  have h_sum : (hermitianPart b).val + (hermitianPart b).valᴴ = b + bᴴ := by
    simp [coe_hermitianPart, star_toAdele]
    match_scalars <;> grind
  exact G.ext_adeleMatrix (by simp only [radicalPoint, radicalElement, G.adeleMatrix_ofMatrix,
    h_sum])

/-- The coordinates `radicalPoint X` embed a column and a hermitian scalar as a closed subset of
the adelic unitary group of `V'`. -/
lemma isClosedEmbedding_radicalPoint : Topology.IsClosedEmbedding (radicalPoint X) := by
  -- The coordinates are read off from the blocks of the matrix, by a continuous left inverse.
  let blocks (g : G E t') : RadicalCoord E r := (-X.iCoord * g.adeleMatrix * X.lAdelic,
    hermitianPart (-toAdele (j : E) • X.kCoord * g.adeleMatrix * X.lAdelic))
  refine LeftInverse.isClosedEmbedding (f := blocks) ?_
    (by fun_prop [hermitianPart]) (by fun_prop [radicalPoint])
  rintro ⟨c, b, hb⟩
  have hb_eq : bᴴ = b := IsHermitian.eq hb
  have h_iBlock : -X.iCoord * (X.radicalElement c b).adeleMatrix * X.lAdelic = c := by
    simp [radicalElement, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
      G.adeleMatrix_ofMatrix]
  have h_kBlock : -toAdele (j : E) • X.kCoord * (X.radicalElement c b).adeleMatrix * X.lAdelic =
      b + toAdele (2⁻¹ * j : E) • (cᴴ * stdForm E t * c) := by
    simp [radicalElement, hb_eq, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
      Matrix.sub_mul, G.adeleMatrix_ofMatrix]
    match_scalars <;> grind
  -- The second summand is skew-hermitian, as `star j = -j`.
  refine Prod.ext h_iBlock (Subtype.ext ?_)
  simp only [blocks, radicalPoint, h_kBlock, coe_hermitianPart]
  simp [hb_eq, Matrix.mul_assoc, star_toAdele, star_j, conjTranspose_stdForm]
  match_scalars <;> grind

/-- The group law of the radical in coordinates: the columns add, and the hermitian scalars add
with a correction, the hermitian part of the product of `j` (the chosen element of `E` with
`star j = -j`) and the pairing of the two columns for the standard form. -/
lemma radicalPoint_mul (x q : RadicalCoord E r) :
    radicalPoint X x * radicalPoint X q = radicalPoint X
      (x.1 + q.1, x.2 + hermitianPart (toAdele (j : E) • x.1ᴴ * stdForm E t * q.1) + q.2) := by
  let z : Matrix Unit Unit (𝔸 E) := toAdele (j : E) • x.1ᴴ * stdForm E t * q.1
  have h_part : x.2 + hermitianPart z + q.2 = hermitianPart (x.2.val + z + q.2.val) := by
    ext : 1
    simp [coe_hermitianPart, IsHermitian.eq x.2.prop, IsHermitian.eq q.2.prop]
    match_scalars <;> grind
  rw [h_part, radicalPoint_hermitianPart, radicalPoint, radicalPoint, radicalElement_mul]

/-- The radical of the stabiliser of the line of `X`, as a subgroup of the adelic unitary group of
`V'`: the range of the coordinates `radicalPoint X`. -/
def radicalSubgroup : Subgroup (G E t') :=
  Subgroup.ofDiv (Set.range (radicalPoint X)) (Set.range_nonempty (radicalPoint X)) <| by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    rw [radicalPoint, radicalPoint, radicalElement_inv, radicalElement_mul]
    exact ⟨_, radicalPoint_hermitianPart X _ _⟩

/-- The radical consists of the elements `X.radicalElement c b`, with `b` not necessarily
hermitian. -/
lemma mem_radicalSubgroup_iff (g : G E t') :
    g ∈ radicalSubgroup X ↔
      ∃ (c : Matrix r Unit (𝔸 E)) (b : Matrix Unit Unit (𝔸 E)), X.radicalElement c b = g :=
  ⟨fun ⟨⟨c, b⟩, hg⟩ ↦ ⟨c, b, hg⟩,
    fun ⟨c, b, hg⟩ ↦ ⟨(c, hermitianPart b), (radicalPoint_hermitianPart X c b).trans hg⟩⟩

lemma radicalElement_mem_radicalSubgroup (c : Matrix r Unit (𝔸 E)) (b : Matrix Unit Unit (𝔸 E)) :
    X.radicalElement c b ∈ radicalSubgroup X :=
  (mem_radicalSubgroup_iff X _).2 ⟨c, b, rfl⟩

lemma isClosed_radicalSubgroup : IsClosed (radicalSubgroup X : Set (G E t')) :=
  (isClosedEmbedding_radicalPoint X).isClosed_range

/-- The coordinates `radicalPoint X` as a homeomorphism onto the radical. -/
def radicalHomeomorph : RadicalCoord E r ≃ₜ radicalSubgroup X :=
  (isClosedEmbedding_radicalPoint X).toHomeomorph

/-- The measure on the radical that corresponds to the additive Haar measure on its coordinates. -/
def radicalHaar : Measure (radicalSubgroup X) :=
  (volume.prod addHaar).map (radicalHomeomorph X)

/-- The measure `radicalHaar X` is a left Haar measure on the radical. -/
instance isHaarMeasure_radicalHaar : IsHaarMeasure (radicalHaar X) := by
  let e := radicalHomeomorph X
  -- In coordinates a left translation is a skew product of translations.
  have h_inv : IsMulLeftInvariant (radicalHaar X) := by
    refine ⟨fun ⟨_, x, rfl⟩ ↦ ?_⟩
    let T (q : RadicalCoord E r) : RadicalCoord E r :=
      (x.1 + q.1, x.2 + hermitianPart (toAdele (j : E) • x.1ᴴ * stdForm E t * q.1) + q.2)
    have hT : MeasurePreserving T (volume.prod addHaar) (volume.prod addHaar) :=
      (measurePreserving_add_left _ x.1).skew_product (g := fun c b ↦ (T (c, b)).2)
        (Continuous.measurable (by fun_prop [hermitianPart]))
        (by simp [T, map_add_left_eq_self, Matrix.mul_assoc])
    refine ((e.measurable.measurePreserving _).of_semiconj hT (fun q ↦ ?_) (by fun_prop)).map_eq
    exact Subtype.ext (radicalPoint_mul X x q).symm
  exact { IsFiniteMeasureOnCompacts.map _ e, h_inv,
    e.continuous.isOpenPosMeasure_map e.surjective with }

/-- An integral over the radical, written in the coordinates `radicalPoint X`. -/
lemma lintegral_radicalHaar (f : G E t' → ENNReal) :
    ∫⁻ n : radicalSubgroup X, f n ∂radicalHaar X =
      ∫⁻ q : RadicalCoord E r, f (radicalPoint X q) ∂volume.prod addHaar :=
  (radicalHomeomorph X).measurableEmbedding.lintegral_map _

/-- Conjugation by the Levi element `lineLevi X (u, h)`, for an idele `u` and a point `h` of the
adelic unitary group of `V`, multiplies integrals over the radical by `|u| ^ (rk V + 1)`, where
`|u| = ideleAbs u` is the module of `u`. -/
lemma lintegral_radicalHaar_conj_lineLevi (p : (𝔸 E)ˣ × G E t) (f : G E t' → ENNReal)
    (hf : Measurable f) :
    ∫⁻ n : radicalSubgroup X, f (lineLevi X p * n * (lineLevi X p)⁻¹) ∂radicalHaar X =
      ENNReal.ofReal (ideleAbs p.1 ^ (Fintype.card r + 1)) *
        ∫⁻ n : radicalSubgroup X, f n ∂radicalHaar X := by
  -- With `p = (u, h)` and `a = u⁻¹`, conjugation acts by `c ↦ h * c * aᴴ` and `b ↦ a * b * aᴴ`;
  -- these maps scale the measures by `|u| ^ rk V` (as `|det h| = 1`) and by `|u|`.
  let a : GL Unit (𝔸 E) := .scalar Unit p.1⁻¹
  let h : GL r (𝔸 E) := p.2.toUnitary
  let C₁ (c : Matrix r Unit (𝔸 E)) : Matrix r Unit (𝔸 E) := h.val * c * (star a).val
  let C₂ (b : selfAdjoint (Matrix Unit Unit (𝔸 E))) : selfAdjoint (Matrix Unit Unit (𝔸 E)) :=
    ⟨a.val * b.val * star a.val, .conjugate b.prop a.val⟩
  have h_conj (q : RadicalCoord E r) :
      lineLevi X p * radicalPoint X q * (lineLevi X p)⁻¹ = radicalPoint X (Prod.map C₁ C₂ q) :=
    mul_inv_eq_of_eq_mul (X.levi_conj_radicalElement q.1 q.2 a p.2)
  have hC₁ : MeasurePreserving C₁ volume
      (ENNReal.ofReal (ideleAbs ((star a).det ^ Fintype.card r * h.det))⁻¹ • volume) :=
    ⟨Continuous.measurable (by fun_prop), volume_map_mul_mul_adele h (star a)⟩
  have hC₂ : MeasurePreserving C₂ addHaar (ENNReal.ofReal (ideleAbs a.det)⁻¹ • addHaar) :=
    ⟨by fun_prop, map_conjugate_selfAdjoint (a := a) addHaar⟩
  have h_det : ideleAbs h.det = 1 := ideleAbs_eq_one_of_mem_unitary p.2.det.prop
  have hC : MeasurePreserving (Prod.map C₁ C₂) (volume.prod addHaar)
      (ENNReal.ofReal (ideleAbs p.1 ^ (Fintype.card r + 1)) • volume.prod addHaar) := by
    convert hC₁.prod hC₂
    simp [a, h_det, pow_succ', prod_smul_left, prod_smul_right, smul_smul,
      ideleAbs_nonneg_and_ne_zero, det_star, ideleAbs_star]
  rw [lintegral_radicalHaar X fun g ↦ f (lineLevi X p * g * (lineLevi X p)⁻¹),
    lintegral_radicalHaar X f]
  simp only [h_conj]
  exact (hC.lintegral_comp (hf.comp (isClosedEmbedding_radicalPoint X).measurable)).trans
    (lintegral_smul_measure _ _)

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum Finset.prod Finset.univ in
/-- The Levi factor meets the radical only in the identity: if the Levi element `lineLevi X p` lies
in the radical, then `p = 1`. -/
lemma eq_one_of_levi_mem_radical {p : (𝔸 E)ˣ × G E t}
    (hp : lineLevi X p ∈ radicalSubgroup X) : p = 1 := by
  obtain ⟨a, g⟩ := p
  obtain ⟨c, b, h_eq⟩ := (mem_radicalSubgroup_iff X _).1 hp
  -- Compare the two diagonal blocks that determine `a` and `g`.
  have h_mat : (lineLevi X (a, g)).adeleMatrix = (X.radicalElement c b).adeleMatrix := by rw [h_eq]
  have ha : a = 1 := by
    simpa [lineLevi, Splitting.levi, radicalElement, ← ext_iff, Matrix.one_apply, Matrix.mul_assoc,
      G.adeleMatrix_ofMatrix, Matrix.mul_add, coord_mul_frame_mul, coord_mul_frame, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul] using congrArg (X.kCoord * · * X.kAdelic) h_mat
  have hg : g.adeleMatrix = 1 := by
    simpa [lineLevi, Splitting.levi, radicalElement, Matrix.mul_assoc, G.adeleMatrix_ofMatrix,
      Matrix.mul_add,
      coord_mul_frame_mul, coord_mul_frame, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
      using congrArg (X.iCoord * · * X.iAdelic) h_mat
  exact Prod.ext ha (G.ext_adeleMatrix (hg.trans G.adeleMatrix_one.symm))

section

omit [WeilData E]

/-- Unfolding on the product of the ideles and the adelic unitary group of `V`: the Haar integral
of a measurable `f` is the integral, against the product of the quotient measures, of the sum of
`f (d * m)` over the pairs `d` of a principal idele and a rational point of the group. -/
lemma lintegral_levi_unfold (f : (𝔸 E)ˣ × G E t → ENNReal) (hf : Measurable f) :
    ∫⁻ m : (𝔸 E)ˣ × G E t, f m ∂(haar.prod volume) =
      ∫⁻ m : (𝔸 E)ˣ × G E t, ∑' d : principalAdeleUnits E × V.Γ,
        f (Prod.map (principalAdeleUnits E).subtype V.Γ.subtype d * m)
        ∂((principalAdeleUnits E).quotMeasure haar).prod V.quotMeasure := by
  have h_unitary (u : (𝔸 E)ˣ) :
      ∫⁻ h : G E t, f (u, h) = ∑' γ : V.Γ, ∫⁻ h : G E t, f (u, γ * h) ∂V.quotMeasure := by
    rw [← lintegral_orbitMeasure_lintegral (ν := count (α := V.Γ)) (by fun_prop),
      ← lintegral_tsum (by fun_prop)]
    simp only [lintegral_count, Subgroup.smul_def, _root_.smul_eq_mul]
  -- Unfold in the idele variable, then in the unitary one.
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop),
    ← lintegral_orbitMeasure_lintegral (ν := count (α := principalAdeleUnits E)) (by fun_prop)]
  refine lintegral_congr fun u ↦ ?_
  rw [lintegral_count, lintegral_tsum (by fun_prop), ENNReal.tsum_prod']
  simp [h_unitary, Subgroup.smul_def]

/-- The rational isotropic line of the splitting `X`: the span of the vector `X.k`. -/
def splittingLine : Submodule E (r' → E) := E ∙ X.k.col ()

/-- The rational points of the stabiliser of the isotropic line `splittingLine X`, as a subgroup of
the adelic unitary group of `V'`. -/
def lineStabilizer : Subgroup (G E t') :=
  (stabilizer (U V'.J) (splittingLine X)).map V'.ratEmbed

/-- The rational stabiliser of the isotropic line of `X` consists of the rational points (`V'.Γ`)
that multiply the vector `X.kAdelic` spanning the line by a unit of `E`. -/
lemma mem_lineStabilizer_iff (g : G E t') :
    g ∈ lineStabilizer X ↔
      g ∈ V'.Γ ∧ ∃ ξ : Eˣ, X.ActsOnFrame g (scalar Unit (toAdele ξ.val)) := by
  -- A rational point `γ` fixes the span of `X.k` iff it multiplies `X.k` by a unit `ξ`; pass to
  -- the adeles by the injective map `vecAtPoint`.
  have h_rat (γ : U V'.J) : γ ∈ stabilizer (U V'.J) (splittingLine X) ↔
      ∃ ξ : Eˣ, X.ActsOnFrame (V'.ratEmbed γ) (scalar Unit (toAdele ξ.val)) := by
    have h_frame (ξ : Eˣ) : X.ActsOnFrame (V'.ratEmbed γ) (scalar Unit (toAdele ξ.val)) ↔
        ∀ i : r', ((V'.ratEmbed γ).adeleMatrix *ᵥ V'.vecAtPoint (X.k.col ())) i =
          V'.vecAtPoint (X.k.col ()) i * toAdele ξ.val := by
      simp only [ActsOnFrame, ← ext_iff, Unique.forall_iff, scalar_apply, mul_diagonal]
      rfl
    have h_span : γ ∈ stabilizer (U V'.J) (splittingLine X) ↔
        ∃ ξ : Eˣ, ξ • X.k.col () = γ.val.val *ᵥ X.k.col () := by
      rw [← span_singleton_eq_span_singleton, eq_comm]
      simp [splittingLine, Subgroup.smul_def, Units.smul_def, smul_span]
    simp only [h_span, h_frame, ← V'.vecAtPoint_injective.eq_iff, ← ratEmbed_mulVec_vecAtPoint]
    simp [Units.smul_def, funext_iff, mul_comm (toAdele _), eq_comm]
  simp only [lineStabilizer, Space.Γ, Subgroup.mem_map, MonoidHom.mem_range, h_rat]
  grind

/-- The rational stabiliser of the line is discrete, as a subset of the rational points. -/
instance : DiscreteTopology (lineStabilizer X) :=
  DiscreteTopology.of_subset (inferInstance : DiscreteTopology V'.Γ)
    fun g hg ↦ ((mem_lineStabilizer_iff X g).1 hg).1

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum Finset.prod Finset.univ in
/-- The embedding `lineLevi X` of the Levi factor is continuous. -/
lemma continuous_lineLevi : Continuous (lineLevi X) := by
  have h_mat (p : (𝔸 E)ˣ × G E t) : (lineLevi X p).adeleMatrix =
      X.kAdelic * diagonal (fun _ : Unit ↦ p.1⁻¹.val) * X.kCoord +
        X.iAdelic * p.2.adeleMatrix * X.iCoord +
        X.lAdelic * (diagonal fun _ : Unit ↦ p.1.val)ᴴ * X.lCoord := by
    simp [lineLevi, Splitting.levi, G.adeleMatrix_ofMatrix]
  simp only [G.continuous_iff, h_mat]
  fun_prop

end

/-- The Iwasawa decomposition for the isotropic line of `X`: every `g` is the product of an element
of the radical, a Levi element and an element of the maximal compact subgroup. -/
lemma exists_eq_radicalElement_mul_lineLevi_mul (g : G E t') :
    ∃ (c : Matrix r Unit (𝔸 E)) (z : Matrix Unit Unit (𝔸 E)) (m : (𝔸 E)ˣ × G E t)
      (κ : maxCompact E t'), g = X.radicalElement c z * lineLevi X m * κ := by
  obtain ⟨κ, hκ, a, -, -, c, z, g₀, hg⟩ := X.iwasawa g (wt := 0)
  -- The block `a` is a scalar `u⁻¹`, so `X.levi (a, g₀)` is by definition `lineLevi X (u, g₀)`.
  obtain ⟨u, rfl⟩ : ∃ u : (𝔸 E)ˣ, GeneralLinearGroup.scalar Unit u⁻¹ = a :=
    ⟨a.det⁻¹, by ext <;> simp⟩
  exact ⟨c, z, (u, g₀), ⟨κ, hκ⟩⁻¹, eq_mul_inv_of_mul_eq hg⟩

omit [WeilData E] in
/-- The Levi element of a principal idele `u` and a rational point `g₀` lies in the rational
stabiliser of the isotropic line of `X`. -/
lemma lineLevi_mem_lineStabilizer {u : (𝔸 E)ˣ} (hu : u ∈ principalAdeleUnits E) {g₀ : G E t}
    (hg₀ : g₀ ∈ V.Γ) : lineLevi X (u, g₀) ∈ lineStabilizer X := by
  obtain ⟨ξ, rfl⟩ := hu
  have h_levi : lineLevi X (Units.map (toAdele (E := E)).toMonoidHom ξ, g₀) =
      X.levi (GeneralLinearGroup.map toAdele (.scalar Unit ξ⁻¹), g₀) :=
    congrArg (fun a ↦ X.levi (a, g₀)) (by ext <;> simp)
  -- The element is rational by `h_levi`, and it acts on the line by `ξ⁻¹`.
  exact (mem_lineStabilizer_iff X _).2
    ⟨by simpa only [h_levi] using X.levi_mem_Gamma _ hg₀, ξ⁻¹, X.actsOnFrame_levi _ g₀⟩

/-- An element of the rational stabiliser of the isotropic line of `X` is moved into the radical by
the Levi element of a principal idele and a rational point. -/
lemma exists_radicalElement_eq_mul_lineLevi {g : G E t'} (hg : g ∈ lineStabilizer X) :
    ∃ u ∈ principalAdeleUnits E, ∃ g₀ ∈ V.Γ,
      ∃ (c : Matrix r Unit (𝔸 E)) (b : Matrix Unit Unit (𝔸 E)),
        X.radicalElement c b = g * lineLevi X (u, g₀) := by
  obtain ⟨⟨γ, hγ⟩, ξ, hξ⟩ := (mem_lineStabilizer_iff X g).1 hg
  -- Levi decomposition `g = radicalElement c b * levi (ξ, g₀)`; the block `g₀` is rational.
  obtain ⟨c, b, a, g₀, h_eq, ha, hg₀⟩ := X.exists_eq_radicalElement_mul_levi hξ
  have hg₀_rat : g₀ ∈ V.Γ := by
    -- The block of the rational point `γ` at `V`, in the rational coordinates of `V`.
    let M : Matrix r r E := V.J⁻¹ * X.iᴴ * V'.J * γ.val.val * X.i
    have hM : M.map toAdele = V.x.val * g₀.adeleMatrix * V.x⁻¹.val := by
      simp [M, ← hγ, iCoord, hg₀, iAdelic, adeleMatrix_ratEmbed, V'.map_J, map_J_inv, Space.ratMap,
        Matrix.mul_assoc, conjTranspose_map_toAdele]
    exact V.mem_Gamma_iff_range.2 (mem_ratMatrices.1 ⟨M, hM⟩)
  obtain rfl : a = .scalar Unit (ξ.map toAdele.toMonoidHom) := Units.ext ha
  refine ⟨_, ⟨ξ, rfl⟩, g₀⁻¹, inv_mem hg₀_rat, c, b, ?_⟩
  simp [lineLevi, ← Prod.inv_mk, h_eq]

/-- The radical is compact modulo its intersection with the rational stabiliser of the isotropic
line of `X`. -/
lemma isCocompact_lineStabilizer_subgroupOf :
    ((lineStabilizer X).subgroupOf (radicalSubgroup X)).IsCocompact := by
  obtain ⟨K, hK, h_cover⟩ := exists_isCompact_rat_mul_radicalElement_mem X
  refine ⟨_, hK.preimage_val (isClosed_radicalSubgroup X), fun ⟨g, hg⟩ ↦ ?_⟩
  obtain ⟨c, b, rfl⟩ := (mem_radicalSubgroup_iff X g).1 hg
  obtain ⟨y, z, hγ, hγK⟩ := h_cover c b
  have h_stab : X.radicalElement y z ∈ lineStabilizer X :=
    (mem_lineStabilizer_iff X _).2 ⟨hγ, 1, by simp [actsOnFrame_radicalElement, ActsOnFrame]⟩
  exact ⟨⟨_, radicalElement_mem_radicalSubgroup X y z⟩, h_stab, hγK⟩

/-- Iwasawa coordinates modulo the rational stabiliser `P` of the isotropic line of `X`. Let `F` be
measurable and left invariant under the radical (the `X.radicalElement x y`) and under `P`. Put
`Θ ((u, h), κ) = |u| ^ (rk V + 1) F (lineLevi X (u, h) κ)`, and let `ν` be the product of the
quotient measures for ideles `u` modulo `Eˣ` and for `h` modulo the rational points, and of the
Haar measure for `κ` in the maximal compact subgroup. If `Θ` is integrable, then `F` is integrable
modulo `P`, and its integral is `c` times that of `Θ`, where `c ≠ 0` does not depend on `F`. -/
lemma exists_integral_lineStabilizer :
    ∃ c ≠ (0 : ℝ), ∀ F : G E t' → ℂ, Measurable F →
      (∀ (x : Matrix r Unit (𝔸 E)) (y : Matrix Unit Unit (𝔸 E)) (h : G E t'),
        F (X.radicalElement x y * h) = F h) →
      (lineStabilizer X).FixesLeft F →
      let Θ : ((𝔸 E)ˣ × G E t) × maxCompact E t' → ℂ := fun ((u, h), κ) ↦
        (ideleAbs u ^ (Fintype.card r + 1) : ℝ) * F (lineLevi X (u, h) * κ)
      let ν : Measure (((𝔸 E)ˣ × G E t) × maxCompact E t') :=
        (((principalAdeleUnits E).quotMeasure haar).prod V.quotMeasure).prod haar
      Integrable Θ ν →
        Integrable F ((lineStabilizer X).quotMeasure volume) ∧
        ∫ h : G E t', F h ∂(lineStabilizer X).quotMeasure volume = c * integral ν Θ := by
  -- Check the hypotheses of `integral_quotMeasure_iwasawa` for the radical, the Levi factor and
  -- its rational points `δ d`.
  let δ : principalAdeleUnits E × V.Γ → (𝔸 E)ˣ × G E t :=
    Prod.map (principalAdeleUnits E).subtype V.Γ.subtype
  have h_iwasawa (g : G E t') :
      ∃ (n : radicalSubgroup X) (m : (𝔸 E)ˣ × G E t) (κ : maxCompact E t'),
        g = n * lineLevi X m * κ := by
    obtain ⟨c, z, h_eq⟩ := exists_eq_radicalElement_mul_lineLevi_mul X g
    exact ⟨⟨_, radicalElement_mem_radicalSubgroup X c z⟩, h_eq⟩
  have h_decomp (g : G E t') (hg : g ∈ lineStabilizer X) :
      ∃ d : principalAdeleUnits E × V.Γ, g * lineLevi X (δ d) ∈ radicalSubgroup X := by
    obtain ⟨u, hu, g₀, hg₀, h_rad⟩ := exists_radicalElement_eq_mul_lineLevi X hg
    exact ⟨(⟨u, hu⟩, ⟨g₀, hg₀⟩), (mem_radicalSubgroup_iff X _).2 h_rad⟩
  obtain ⟨c, hc, h_unfold⟩ := integral_quotMeasure_iwasawa
    (fun m : (𝔸 E)ˣ × G E t ↦ ideleAbs m.1 ^ (Fintype.card r + 1)) (μ := volume)
    (ν := haar.prod volume) (κ := haar) (i := lineLevi X) (α := _) (hi := continuous_lineLevi X)
    (hN := isClosed_radicalSubgroup X) (hw := by fun_prop) (hw_pos := by simp [ideleAbs_pos])
    (h_dec := h_iwasawa) (h_conj := lintegral_radicalHaar_conj_lineLevi X)
    (h_triv := fun _ ↦ eq_one_of_levi_mem_radical X)
    (hδ := .prodMap Subtype.val_injective Subtype.val_injective) (hα := lintegral_levi_unfold)
    (hδ_mem := fun d ↦ lineLevi_mem_lineStabilizer X d.1.prop d.2.prop) (hΓ := h_decomp)
    (h_cocpt := isCocompact_lineStabilizer_subgroupOf X)
  refine ⟨c, hc, fun F hF h_rad h_stab ↦ h_unfold F hF (fun n hn h ↦ ?_) h_stab⟩
  obtain ⟨x, y, rfl⟩ := (mem_radicalSubgroup_iff X n).1 hn
  exact h_rad x y h

section Lines

variable (f : 𝒮 (W'.hom V')) (g : G E s')

/-- The sum of the terms `constTermAt` of the datum `f` moved by `(g, h)`, over the rational
vectors that span `y`. -/
def lineSum (y : Submodule E (r' → E)) (h : G E t') : ℂ :=
  ∑' x : (fun x : r' → E ↦ E ∙ x) ⁻¹' {y},
    constTermAt A (replicateCol Unit x.val) (pairWeil W' V' a b (g, h) f)

/-- The vectors that span the isotropic line of `X` are the `ξ • X.k` with `ξ` in `Eˣ`, so `lineSum`
over this line is the sum of their terms `constTermAt A` for `pairWeil W' V' a b (g, h) f`. This sum
equals the sum over `ξ ∈ Eˣ` of the theta values `θ (W.hom V)` of `lineTerm A X true ξ` applied to
that datum. Here `lineTerm A X true ξ` is translation by `ξ • X.kAdelic * A.kCoord` (`X.kAdelic` is
the adelic vector spanning the line of `X`, `A.kCoord` the coordinate along the `k`-frame of `A`),
followed by the zero term along the line of `A` and then the one along the line of `X`. -/
lemma lineSum_splittingLine (h : G E t') :
    lineSum A a b f g (splittingLine X) h =
      ∑' ξ : Eˣ, θ (W.hom V) (lineTerm A X true (toAdele ξ.val) (pairWeil W' V' a b (g, h) f)) := by
  have h_ne : X.k.col () ≠ 0 := fun h_zero ↦ by
    simpa [show X.k = 0 from ext fun i _ ↦ congrFun h_zero i] using X.gram_lk
  have h_span (x : r' → E) : (∃ ξ : Eˣ, ξ • X.k.col () = x) ↔ (E ∙ x) = splittingLine X := by
    rw [splittingLine, eq_comm, span_singleton_eq_span_singleton]
  let spanning : Eˣ ≃ (fun x : r' → E ↦ E ∙ x) ⁻¹' {splittingLine X} :=
    (ofInjective _ ((smul_left_injective E h_ne).comp val_injective)).trans
      (subtypeEquivRight h_span)
  rw [lineSum, ← spanning.tsum_eq]
  exact tsum_congr fun ξ ↦ constTermAt_smul_k A X ξ.ne_zero

/-- `lineSum A a b f g y h` is the sum, over the rational vectors spanning the subspace `y`, of
their terms `constTermAt A` in the constant term of the datum `pairWeil W' V' a b (g, h) f`. This
sum is unchanged when a rational point `γ` of the unitary group of `V'` moves `y` to `γ • y` and `h`
to `V'.ratEmbed γ * h`, where `V'.ratEmbed γ` is the image of `γ` in the adelic group. -/
lemma lineSum_smul (γ : U V'.J) (y : Submodule E (r' → E)) (h : G E t') :
    lineSum A a b f g (γ • y) (V'.ratEmbed γ * h) = lineSum A a b f g y h := by
  -- `γ` carries the vectors that span `y` to those that span `γ • y`.
  have h_span (x : r' → E) : (E ∙ x) = y ↔ (E ∙ γ • x) = γ • y := by
    rw [← smul_left_cancel_iff γ]
    simp [Subgroup.smul_def, Units.smul_def, smul_span]
  let σ : (fun x : r' → E ↦ E ∙ x) ⁻¹' {y} ≃ (fun x : r' → E ↦ E ∙ x) ⁻¹' {γ • y} :=
    (toPerm γ).subtypeEquiv h_span
  rw [lineSum, lineSum, ← σ.tsum_eq]
  refine tsum_congr fun x ↦ ?_
  have h_col : replicateCol Unit (σ x).val = γ.val.val * replicateCol Unit x.val := rfl
  simp only [h_col, constTermAt_eq_integral A a b]
  congr with q
  simpa [Splitting.thetaTerm, rep_apply_apply] using
    A.thetaTerm_ratEmbed_mul V' a b f (lineRadical A q * g) γ (replicateCol Unit x.val) h

/-- The sum of the terms along a line is a measurable function of the point `h`. -/
lemma measurable_lineSum (y : Submodule E (r' → E)) : Measurable (lineSum A a b f g y) := by
  refine .tsum fun x ↦ ?_
  simp only [constTermAt_eq_integral A a b]
  refine StronglyMeasurable.measurable (.integral_prod_left (Continuous.stronglyMeasurable ?_))
  fun_prop [Splitting.thetaTerm]

/-- Moving a datum `f` by an element of the radical of the stabiliser of the isotropic line of `X`
in the Weil representation `pairWeil` does not change `lineTerm A X true ξ f`, the zero term along
that line of the term of `f` at `ξ • X.kAdelic`. -/
lemma lineTerm_pairWeil_radicalElement (ξ : 𝔸 E) (x : Matrix r Unit (𝔸 E))
    (y : Matrix Unit Unit (𝔸 E)) :
    lineTerm A X true ξ (pairWeil W' V' a b (1, X.radicalElement x y) f) =
      lineTerm A X true ξ f := by
  -- Move `X.radicalElement x y` through `A.homSlice`, where it fixes `X.kAdelic`, and through the
  -- zero term along `X`, where its Levi part is `(1, 1)`.
  have h_char (c : AutChar E) : c / upsilonU1 * upsilonU1 ^ Fintype.card Unit = c := by simp
  have h_source (z : Matrix r' Unit (𝔸 E)) :
      A.homSlice V' z (pairWeil W' V' a b (1, X.radicalElement x y) f) =
        pairWeil W V' (a / upsilonU1) b (1, X.radicalElement x y)
          (A.homSlice V' ((X.radicalElement x y)⁻¹.adeleMatrix * z) f) := by
    have h_levi := A.homSlice_levi V' (a / upsilonU1) b 1 1 (X.radicalElement x y) z f
    rw [h_char, Prod.mk_one_one, map_one] at h_levi
    simp [h_levi]
  obtain ⟨h_frame, h_block⟩ : X.ActsOnFrame (X.radicalElement x y) 1 ∧
      X.iCoord * ((X.radicalElement x y).adeleMatrix * X.iAdelic) = 1 :=
    X.exists_eq_radicalElement_iff.1 ⟨x, y, rfl⟩
  have h_zero (a' : AutChar E) (f' : 𝒮 (W.hom V')) :
      (X.homTarget W).zeroTerm (pairWeil W V' a' b (1, X.radicalElement x y) f') =
        (X.homTarget W).zeroTerm f' := by
    have h_law := X.homTarget_zeroTerm_pairWeil W a' (b / upsilonU1) (X.radicalElement x y) 1 1
      h_frame (h_block.trans G.adeleMatrix_one.symm) 1 f'
    rw [h_char] at h_law
    simp [h_law, Prod.mk_one_one]
  simp [lineTerm, h_source, h_zero, radicalElement_inv, actsOnFrame_radicalElement]

/-- Suppose the term `constTermAt A 0` of the zero vector in the constant term of
`pairWeil W' V' a b (g, h) f` vanishes. Suppose also that the subspace `y` has nonzero `lineSum`,
the sum of the terms `constTermAt A` of this datum over the rational vectors spanning `y`. Then `y`
is spanned by a nonzero isotropic vector, so by Witt's theorem a rational point of the unitary group
`U V'.J` moves it to the isotropic line `splittingLine X` spanned by `X.k`. -/
lemma splittingLine_mem_orbit {h : G E t'}
    (h_zero : constTermAt A 0 (pairWeil W' V' a b (g, h) f) = 0) {y : Submodule E (r' → E)}
    (hy : lineSum A a b f g y h ≠ 0) : splittingLine X ∈ orbit (U V'.J) y := by
  obtain ⟨⟨x, rfl⟩, hx⟩ : ∃ x : (fun x : r' → E ↦ E ∙ x) ⁻¹' {y},
      constTermAt A (replicateCol Unit x.val) (pairWeil W' V' a b (g, h) f) ≠ 0 :=
    not_forall.1 fun h_all ↦ hy (by simp only [lineSum, h_all, tsum_zero])
  have hx_ne : x ≠ 0 := fun hx_zero ↦ hx (by simpa [hx_zero] using h_zero)
  have hx_iso : (replicateCol Unit x)ᴴ * V'.J * replicateCol Unit x = 0 :=
    by_contra fun h_ne ↦ hx (ite_eq_right h_ne)
  obtain ⟨γ, hγ⟩ : ∃ γ : U V'.J, γ.val.val * replicateCol Unit x = X.k :=
    V'.witt (.of_ne_zero hx_ne) ⟨_, X.gram_lk⟩ (by rw [hx_iso, X.gram_kk])
  have h_col : γ • x = X.k.col () := congrArg (fun M ↦ M.col ()) hγ
  exact ⟨γ, by simp [splittingLine, ← h_col, Subgroup.smul_def, Units.smul_def, smul_span]⟩

end Lines

/-- Unfolding along the isotropic lines. Let `F h` be the datum `f` moved by `(g, h)`. In Iwasawa
coordinates `((u, h), κ)` with measure `ν` (ideles `u` modulo `Eˣ`, `h` modulo the rational points,
`κ` in the maximal compact subgroup), let `Θ` be `|u| ^ (rk V + 1)` times the sum over `ξ` in `Eˣ`
of the theta values of `lineTerm A X true ξ` at `F (lineLevi X (u, h) κ)`, which belong to the
vectors `ξ • X.k` that span the isotropic line of `X`. If the term `constTermAt A` of the zero
vector vanishes and `Θ` is integrable, then the integral of the sum of the terms of all rational
vectors, over the group of `V'` modulo its rational points, is `c` times the integral of `Θ`, where
`c ≠ 0` depends only on the splittings `A` and `X`. -/
lemma exists_unfold_constant_term :
    ∃ c ≠ (0 : ℝ), ∀ (a b : AutChar E) (f : 𝒮 (W'.hom V')) (g : G E s'),
      let F (h : G E t') : 𝒮 (W'.hom V') := pairWeil W' V' a b (g, h) f
      let Θ : ((𝔸 E)ˣ × G E t) × maxCompact E t' → ℂ := fun ((u, h), κ) ↦
        (ideleAbs u ^ (Fintype.card r + 1) : ℝ) * ∑' ξ : Eˣ,
          θ (W.hom V) (lineTerm A X true (toAdele ξ.val) (F (lineLevi X (u, h) * κ)))
      let ν : Measure (((𝔸 E)ˣ × G E t) × maxCompact E t') :=
        (((principalAdeleUnits E).quotMeasure haar).prod V.quotMeasure).prod haar
      (∀ h : G E t', constTermAt A 0 (F h) = 0) → Integrable Θ ν →
        ∫ h : G E t', ∑' x : r' → E, constTermAt A (replicateCol Unit x) (F h) ∂V'.quotMeasure =
          c * integral ν Θ := by
  -- Group the terms by the line they span. Only the lines in the orbit of `splittingLine X`
  -- contribute, so the integral unfolds to its stabiliser; then pass to Iwasawa coordinates.
  obtain ⟨c, hc, h_iwasawa⟩ := exists_integral_lineStabilizer X
  refine ⟨c, hc, fun a b f g ↦ ?_⟩
  intro F Θ ν h_zero h_int
  have h_countable : Countable (Submodule E (r' → E)) :=
    Surjective.countable (f := fun S : Finset (r' → E) ↦ span E (S : Set (r' → E)))
      IsNoetherian.noetherian
  let lines : Set (Submodule E (r' → E)) := {y | splittingLine X ∈ orbit (U V'.J) y}
  let Φ : G E t' → ℂ := lineSum A a b f g (splittingLine X)
  have h_radical (x : Matrix r Unit (𝔸 E)) (y : Matrix Unit Unit (𝔸 E)) (h : G E t') :
      Φ (X.radicalElement x y * h) = Φ h := by
    have h_mul : (g, X.radicalElement x y * h) = (1, X.radicalElement x y) * (g, h) := by simp
    simp only [Φ, lineSum_splittingLine, h_mul, ← rep_apply_apply, lineTerm_pairWeil_radicalElement]
  have h_supp (h : G E t') : support (fun y ↦ lineSum A a b f g y h) ⊆ lines :=
    fun y ↦ splittingLine_mem_orbit A X a b f g (h_zero h)
  have hΘ : Θ = fun ((u, h), κ) ↦
      (ideleAbs u ^ (Fintype.card r + 1) : ℝ) * Φ (lineLevi X (u, h) * κ) := by
    simp only [Φ, Θ, F, lineSum_splittingLine]
  obtain ⟨hΦ_int, hΦ_eq⟩ : Integrable Φ ((lineStabilizer X).quotMeasure volume) ∧
      ∫ h, Φ h ∂(lineStabilizer X).quotMeasure volume = c * integral ν Θ := by
    rw [hΘ] at h_int ⊢
    exact h_iwasawa Φ (measurable_lineSum A a b f g _) h_radical
      (fixesLeft_map_stabilizer (lineSum_smul A a b f g) rfl) h_int
  obtain ⟨-, h_unfold, -⟩ := integral_tsum_orbit_of_lt_top_or_integrable (Γ := V'.Γ) (μ := volume)
    (D := lines)
    (S := lineStabilizer X) V'.ratEmbed_injective rfl (measurable_lineSum A a b f g)
    (lineSum_smul A a b f g) rfl (fun _ ↦ .rfl) (.inr hΦ_int)
  calc ∫ h, ∑' x : r' → E, constTermAt A (replicateCol Unit x) (F h) ∂V'.quotMeasure
      = ∫ h, ∑' y : lines, lineSum A a b f g y h ∂V'.quotMeasure := by
        congr with h
        rw [tsum_subtype_eq_of_support_subset (h_supp h)]
        exact ((hasSum_constTermAt A a b).summable.hasSum.tsum_fiberwise _).tsum_eq.symm
    _ = ∫ h, Φ h ∂(lineStabilizer X).quotMeasure volume := h_unfold
    _ = c * integral ν Θ := hΦ_eq

end New.Exchange

end
