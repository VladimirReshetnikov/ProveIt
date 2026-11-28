import Lib.Adelic.TraceFormula.ChangingSigns
import Lib.Adelic.TraceFormula.ReduciblePolynomials
import Lib.Weil.Periods.Grading

/-!
# Kernels of levels as forms, and unfolding of orbital integrals

This file shows that the conjugate of the kernel of a level `K` is a form of type `e`. It expands
the kernel of `e ⊗ (a ⋆ 1_K)` in an orthonormal basis of forms. It writes `vol K` times the trace
on forms as the integral over `[G] = Γ \ G` of the kernel on the diagonal. It introduces classes
of pairs (finite frame, rational matrix) and orbital integrals, and it unfolds the term of an
irreducible characteristic polynomial into orbital integrals. It ends with triple kernels, the
rotation of triples and the trace property of this rotation.

## Main definitions and results

* `New.Space.exists_kernel_form`, `New.Space.partialKernel_convIndicator_eq_sum`: the conjugate of
  the kernel of a level `K` is a form, and the kernel of `e ⊗ (a ⋆ 1_K)`, for `a` in the group
  algebra of `G_f`, expands in an orthonormal basis.
* `New.Space.volume_mul_trace_eq`: the volume of the level times the trace on forms is the integral
  over `Γ \ G` of the kernel on the diagonal.
* `New.frameClass`, `New.Space.orbitalIntegral_unfold`: classes of pairs (finite frame, rational
  matrix) index the conjugacy classes of all spaces at once, and for irreducible `R` the term of `R`
  unfolds into orbital integrals.

Notions from other files:
* `New.Space E n s`: a hermitian form `J` over `E` with an adelic frame `x` in which it is `diag s`
  at infinity and `1` at the finite places. `V.ratEmbed` embeds `U(J)(E)` in `G = G_∞ × G_f` with
  image `Γ = V.Γ`, and `V.quotMeasure` integrates over `[G] = Γ \ G`.
* `New.IsCuspKernel B e`: `e` is a minimal convolution idempotent on `G_∞` with moment of order
  `B + 1` and decay of order `B`.
* `V.polyTerm k φ S γ x`: the value of `k ⊗ φ` at `x⁻¹ γ x` if the characteristic polynomial of `γ`
  lies in `S`, and `0` otherwise.
* `V.formRep e`: the action of `G_f` on the forms of type `e`, which are the bounded automorphic
  functions on `G` fixed by `e`; a level `K` is an open subgroup of the standard compact subgroup.

## Relation to the literature

Known; see `Lib.Adelic.TraceFormula.TraceComparison` for sources.
-/

noncomputable section

/-! ## The kernel of a level is a form -/

open MeasureTheory Fintype

/-- Let `e` be a cusp kernel of order `B > 8 n ^ 2` on the real group of a space `V` and `K` a
level, that is, an open subgroup of the standard compact subgroup of `G_f`. For fixed `x` there is a
form of type `e` (a bounded automorphic function fixed by `e`) of level `K` whose conjugate is the
kernel `g ↦ ∑_γ (e ⊗ 1_K)(x γ g)`, the sum over the rational points. -/
theorem New.Space.exists_kernel_form {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
    [Nonempty n] {s : n → ℤˣ} (V : Space E n s) {e : GInf E s → ℂ} {B : ℕ} (hB : 8 * card n ^ 2 < B)
    (he : IsCuspKernel B e) (x : G E s) (K : Subgroup (Gf E n)) [hK : IsLevel K] :
    ∃ k : levelSpace (V.formRep e) K, ∀ g : G E s, starRingEnd ℂ (k.val g) =
      ∑' γ : V.Γ, e (x * γ * g).1 * Set.indicator K 1 (x * γ * g).2 := by
  classical
  -- The conjugate is `F g = ∑_γ (e ⊗ 1_K)(g⁻¹ γ x⁻¹)`. The moduli of its terms have a bounded sum,
  -- each term is fixed by `e`, and `F` is left invariant under `V.Γ` and of level `K`.
  let φ : TestFunction (Gf E n) := TestFunction.indicator hK.isOpen hK.isCompact
  let F (g : G E s) : ℂ := V.partialKernel e φ .univ g x⁻¹
  obtain ⟨C, hC, h_bound⟩ := V.exists_tsum_enorm_kernelTerm_le_height hB φ he.decay
  have h_height : 0 < V.height x⁻¹ := V.height_pos x⁻¹
  have he_meas : Measurable e := he.continuous.measurable
  have hF_bdd : IsBoundedMeasurable F :=
    ⟨Measurable.stronglyMeasurable (by fun_prop [partialKernel]), _, fun g ↦
      norm_tsum_le_of_tsum_enorm_le (by positivity) (h_bound .univ g x⁻¹)⟩
  have hF_fix : realConv e F = F :=
    V.realConv_partialKernel φ he.toIsIdempotentKernel fun g ↦ h_bound .univ g x⁻¹
  have hF_rat : V.Γ.FixesLeft F := by
    rintro _ ⟨ν, rfl⟩ g
    exact V.partialKernel_ratEmbed_mul φ (fun _ ↦ .rfl) g x⁻¹
  have hF_level : HasLevel F K := V.hasLevel_partialKernel
    (fun u hu y ↦ by simp [φ, TestFunction.indicator, Set.indicator,
      K.mul_mem_cancel_left (inv_mem hu)]) .univ x⁻¹
  obtain ⟨k, hk⟩ : ∃ k : levelSpace (V.formRep e) K, k.val.val = realConv e F :=
    exists_form_eq_realConv ⟨K, hK.isOpen⟩ hF_bdd hF_rat hF_level he.toIsIdempotentKernel
  refine ⟨k, fun g ↦ ?_⟩
  -- Conjugate term by term and replace `γ` by `γ⁻¹`, using `e y⁻¹ = conj (e y)`.
  have hφ_inv (y : Gf E n) : starRingEnd ℂ (φ.1 y⁻¹) = Set.indicator K 1 y := by
    simp [φ, TestFunction.indicator, Set.indicator, apply_ite (starRingEnd ℂ)]
  have h_term (γ : U V.J) :
      starRingEnd ℂ (V.kernelTerm e φ (Set.univ.indicator 1) g γ⁻¹ x⁻¹) =
        e (x * V.ratEmbed γ * g).1 * Set.indicator K 1 (x * V.ratEmbed γ * g).2 := by
    rw [kernelTerm, show g⁻¹ * V.ratEmbed γ⁻¹ * x⁻¹ = (x * V.ratEmbed γ * g)⁻¹ by simp [mul_assoc],
      Prod.fst_inv, Prod.snd_inv, he.apply_inv, map_mul, map_mul, hφ_inv, Complex.conj_conj,
      Set.indicator_univ, Pi.one_apply, map_one, one_mul]
  let i : U V.J ≃ V.Γ := (MonoidHom.ofInjective V.ratEmbed_injective).toEquiv
  calc starRingEnd ℂ (k.val g) = starRingEnd ℂ (F g) := by rw [← hF_fix, ← hk]
    _ = starRingEnd ℂ (∑' γ : U V.J, V.kernelTerm e φ (Set.univ.indicator 1) g γ⁻¹ x⁻¹) :=
        congrArg _ ((Equiv.inv (U V.J)).tsum_eq fun γ ↦ V.kernelTerm e φ _ g γ x⁻¹).symm
    _ = ∑' γ : V.Γ, e (x * γ * g).1 * Set.indicator K 1 (x * γ * g).2 := by
        rw [Complex.conj_tsum, ← i.tsum_eq]
        exact tsum_congr h_term

/-! ## Orbital integrals and the comparison of traces -/

open NumberField Measure Matrix Polynomial Module Subgroup Complex MulAction New.Variety Finset
  Equiv Real ConjAct ENNReal
open scoped Norms.L2Operator InnerProductSpace ComplexOrder

namespace New

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]

/-- Classes of pairs `(x, y)` of a finite adelic frame `x`, up to the unitary group on the right,
and an invertible rational matrix `y`, under `z • (x, y) = (z x, z y z⁻¹)` for rational `z`. For a
space `V` the class of `(V.xFin, γ)` records the conjugacy class of the rational isometry `γ`, so
that the conjugacy classes of different spaces can be compared. A pair is stored as a marked triple
with the trivial mark. -/
abbrev FrameClass (E n : Type) [Field E] [CMType E] [Fintype n] [DecidableEq n] : Type :=
  orbitRel.Quotient (GL n E) (MarkedTriple (U (1 : Matrix n n (𝔸f E))) Unit)

/-- The class of a frame and a rational matrix. -/
def frameClass (a : GL n (𝔸f E) × GL n E) : FrameClass E n :=
  Quotient.mk (orbitRel (GL n E) (MarkedTriple (U 1) Unit)) (⟦a.1⟧, a.2, ())

/-- Two pairs of a finite adelic frame and a rational matrix have the same class if and only if a
rational matrix `z` carries the coset `x' G_f` to `x G_f` and conjugates `y'` to `y`; here `G_f` is
the unitary group of the identity over the finite adeles. -/
lemma frameClass_eq_iff {x x' : GL n (𝔸f E)} {y y' : GL n E} :
    frameClass (x, y) = frameClass (x', y') ↔
      ∃ z : GL n E, x⁻¹ * toFinGL z * x' ∈ U 1 ∧ z * y' * z⁻¹ = y := by
  refine Quotient.eq.trans (exists_congr fun z ↦ ?_)
  -- Write out the action of `z` on a marked triple and compare the components.
  change ((⟦toFinGL z * x'⟧, z * y' * z⁻¹, ()) :
    (GL n (𝔸f E) ⧸ U (1 : Matrix n n (𝔸f E))) × GL n E × Unit) = (⟦x⟧, y, ()) ↔ _
  rw [Prod.mk.injEq, Prod.mk.injEq, eq_comm]
  simp [← QuotientGroup.eq, mul_assoc]

/-- The classes of the pairs `(x, y)` in which `y` has the characteristic polynomial `R` and is an
elliptic isometry, with the signs `ε` on its eigenlines, of a form for which `x` is an orthonormal
frame. -/
def signedClasses (R : E[X]) (ε : InfinitePlace E → n → ℤˣ) : Set (FrameClass E n) :=
  {c : FrameClass E n | ∃ (x : GL n (𝔸f E)) (y : GL n E),
    y.1.charpoly = R ∧ HasSignType ε 1 y {1} x ∧ frameClass (x, y) = c}

namespace Space

variable {s : n → ℤˣ} (V : Space E n s) {B : ℕ} {k e : GInf E s → ℂ}

/-- The term `(k ⊗ φ)(x⁻¹ γ x)` of a rational point `γ`. -/
def orbitalIntegrand (k : GInf E s → ℂ) (φ : Gf E n → ℂ) (γ : U V.J) (x : G E s) : ℂ :=
  k (x⁻¹ * V.ratEmbed γ * x).1 * φ (x⁻¹ * V.ratEmbed γ * x).2

/-- The orbital integral `I_γ`: the integral of the term of `γ` over `G` modulo the rational
centraliser of `γ`. -/
def orbitalIntegral (k : GInf E s → ℂ) (φ : Gf E n → ℂ) (γ : U V.J) : ℂ :=
  ∫ x : G E s, V.orbitalIntegrand k φ γ x ∂((centralizer {γ}).map V.ratEmbed).quotMeasure

/-- For a function `k` on the real group and `φ` on the finite adelic one, the contribution of the
class `c` to the integral of the terms with polynomial `R`: the sum of their integrals against
`V.quotMeasure` for the rational points `γ` such that `(V.xFin, γ)` lies in `c`. -/
def classIntegral (k : GInf E s → ℂ) (φ : Gf E n → ℂ) (R : E[X]) (c : FrameClass E n) : ℂ :=
  ∑' γ : (fun γ : U V.J ↦ frameClass (V.xFin, (γ : GL n E))) ⁻¹' {c},
    ∫ x : G E s, V.polyTerm k φ {R} γ x ∂V.quotMeasure

/-- Let `y` be a finite adelic orthonormal frame of the form `β` and `V` a space with form `J` and
finite frame `V.xFin`. A rational matrix `z` carries `y` into the coset `V.xFin G_f` if and only if
`zᴴ J z = β`. -/
lemma mem_U_one_iff_gram_eq {y : GL n (𝔸f E)} {z : GL n E} {β : Matrix n n E}
    (hy : (y : Matrix n n (𝔸f E))ᴴ * β.map (algebraMap E (𝔸f E)) * y = 1) :
    V.xFin⁻¹ * toFinGL z * y ∈ U 1 ↔ (z : Matrix n n E)ᴴ * V.J * z = β := by
  -- `V.xFin` is a frame of `V.J` and `y` is a frame of `β`; compose the changes of basis.
  have h_map : (z.1ᴴ * V.J * z.1).map (algebraMap E (𝔸f E)) =
      (toFinGL z).1ᴴ * V.J.map (algebraMap E (𝔸f E)) * (toFinGL z).1 :=
    map_conjTranspose_mul_mul _ (by simp) _ _
  refine ⟨fun hz ↦ map_injective (algebraMap E (𝔸f E)).injective (h_map.trans ?_), fun hz ↦ ?_⟩
  · -- The three factors of `toFinGL z = V.xFin * (V.xFin⁻¹ * toFinGL z * y) * y⁻¹` carry `V.J` to
    -- `1`, `1` to `1`, and `1` to `β`.
    simpa [mul_assoc] using
      gram_mul_of_gram_eq (gram_mul_of_gram_eq V.gram_xFin hz) (gram_inv_of_gram_eq hy)
  · -- The factors of `V.xFin⁻¹ * toFinGL z * y` carry `1` to `V.J`, to `β`, then to `1`.
    exact gram_mul_of_gram_eq
      (gram_mul_of_gram_eq (gram_inv_of_gram_eq V.gram_xFin) (by rw [← h_map, hz])) hy

/-- For a space `V = (J, x)`, let `V.xFin` be the finite part of `x`. Pairs of a finite adelic frame
and a rational matrix are identified under `(x, y) ~ (z x, z y z⁻¹)` for rational `z`, with frames
taken up to the unitary group on the right. Two rational points `γ`, `δ` of `U(J)`, each paired with
the frame `V.xFin`, give the same class exactly if they are conjugate in `U(J)(E)`. -/
lemma frameClass_eq_iff_mem_orbit (γ δ : U V.J) :
    frameClass (V.xFin, (δ : GL n E)) = frameClass (V.xFin, (γ : GL n E)) ↔
      γ ∈ orbit (ConjAct (U V.J)) δ := by
  refine frameClass_eq_iff.trans ?_
  simp only [V.mem_U_one_iff_gram_eq gram_xFin, mem_orbit_conjAct, isConj_iff, Subtype.ext_iff,
    Subgroup.coe_mul, Subgroup.coe_inv, Subtype.exists, mem_U, exists_prop]

/-- The component of a rational point `γ` at an infinite place `w` is the image of the matrix `γ`
under the embedding at `w`, read in the frame `V.x` of the space. -/
lemma coe_ratEmbed_fst (γ : U V.J) (w : InfinitePlace E) :
    ((V.ratEmbed γ).1 w : Matrix n n ℂ) =
      ((V.x.map (evalInf w))⁻¹ : GL n ℂ) * (γ : Matrix n n E).map (Φ w) *
        (V.x.map (evalInf w) : GL n ℂ) := by
  have h_comp : evalInf w ∘ toAdele = (Φ w : E → ℂ) := rfl
  change (V.ratEmbed γ).adeleMatrix.map (evalInf w) = _
  rw [adeleMatrix_ratEmbed, Matrix.map_mul, Matrix.map_mul, Matrix.map_map, h_comp, ← map_inv]
  rfl

/-- The term of a rational point `γ` for its own characteristic polynomial is the integrand of the
orbital integral of `γ`. -/
lemma polyTerm_charpoly (k : GInf E s → ℂ) (φ : Gf E n → ℂ) (γ : U V.J) :
    V.polyTerm k φ {(γ : Matrix n n E).charpoly} γ = V.orbitalIntegrand k φ γ := by
  funext x
  simp [kernelTerm, orbitalIntegrand]

/-- Translating `x` on the left by a rational point `t` that commutes with `γ` does not change
`x⁻¹ γ x`. -/
lemma conj_ratEmbed_mul {γ t : U V.J} (ht : Commute γ t) (x : G E s) :
    (V.ratEmbed t * x)⁻¹ * V.ratEmbed γ * (V.ratEmbed t * x) = x⁻¹ * V.ratEmbed γ * x := by
  simp only [_root_.mul_inv_rev, mul_assoc, (ht.map V.ratEmbed).left_comm, inv_mul_cancel_left]

/-- The integrand of the orbital integral of `γ` is left invariant under the image in `G` of the
rational centraliser of `γ`. -/
lemma fixesLeft_orbitalIntegrand (k : GInf E s → ℂ) (φ : Gf E n → ℂ) (γ : U V.J) :
    ((centralizer {γ}).map V.ratEmbed).FixesLeft (V.orbitalIntegrand k φ γ) := by
  rintro _ ⟨t, ht, rfl⟩ x
  rw [orbitalIntegrand, V.conj_ratEmbed_mul (ht γ rfl), orbitalIntegrand]

/-- The term of `γ` is measurable if the kernel `k` on the real group is. -/
@[fun_prop] lemma measurable_orbitalIntegrand (hk : Measurable k) (φ : TestFunction (Gf E n))
    (γ : U V.J) : Measurable (V.orbitalIntegrand k φ γ) := by
  have hφ : Measurable φ.1 := φ.2.1.continuous.measurable
  fun_prop [orbitalIntegrand]

/-- For a hermitian space `V = (J, x)` over the CM field `E`, let `V.xFin` be the finite part of
`x`. If the contribution `V.classIntegral k φ R c` of the class `c` to the terms with polynomial `R`
is not zero, then `c` is the class of `(V.xFin, γ)` for some rational isometry `γ` of `J`
(`γ : U V.J`) with characteristic polynomial `R`. -/
lemma exists_frameClass_eq_of_classIntegral_ne_zero {φ : Gf E n → ℂ} {R : E[X]} {c : FrameClass E n}
    (hc : V.classIntegral k φ R c ≠ 0) :
    ∃ γ : U V.J, (γ : Matrix n n E).charpoly = R ∧ frameClass (V.xFin, (γ : GL n E)) = c := by
  by_contra h_none
  refine hc ((tsum_congr fun γ ↦ ?_).trans tsum_zero)
  have h_ne : γ.1.1.1.charpoly ∉ ({R} : Set E[X]) := fun h ↦ h_none ⟨γ.1, h, γ.2⟩
  simp only [kernelTerm, Set.indicator_of_notMem h_ne, zero_mul, integral_zero]

/-! ### The kernel -/

/-- Let `e` be a cusp kernel, `K` a level, and `F` the form of type `e` and level `K` whose
conjugate is the kernel of `e ⊗ 1_K` at `g`. The inner product of `F` with a form `v` of this type
and level is `vol K` times the value of `v` at `g`. -/
lemma inner_kernel_form {K : Subgroup (Gf E n)} [hK : IsLevel K] (he : IsCuspKernel B e)
    {g : G E s} {F : levelSpace (V.formRep e) K}
    (hF : ∀ g' : G E s, starRingEnd ℂ ((F : V.Form e).1 g') =
      ∑' γ : V.Γ, e (g⁻¹ * γ * g').1 * Set.indicator K 1 (g⁻¹ * γ * g').2)
    (v : levelSpace (V.formRep e) K) :
    ⟪F, v⟫_ℂ = volume.real (K : Set (Gf E n)) * (v : V.Form e).1 g := by
  classical
  -- Unfold the sum over `V.Γ`, and use that `K` and `e` fix `v`.
  let χ : Gf E n → ℂ := Set.indicator K 1
  have hχ : ∫ y, χ y = volume.real (K : Set (Gf E n)) := by
    simp [χ, Pi.one_def, integral_indicator_const, hK.isOpen.measurableSet]
  have hχ_int : Integrable χ :=
    .of_integral_ne_zero (hχ.trans_ne (ofReal_ne_zero.2 (measureReal_pos_of_isLevel K).ne'))
  have h_int : Integrable fun y : G E s ↦ e (g⁻¹ * y).1 * χ (g⁻¹ * y).2 * v.1.1 y :=
    v.1.2.isBoundedMeasurable.integrable_mul_comp
      (.comp_mul_left (μ := volume) (he.integrable.mul_prod hχ_int) g⁻¹) id measurable_id
  calc ⟪F, v⟫_ℂ
      = ∫ y : G E s, e (g⁻¹ * y).1 * χ (g⁻¹ * y).2 * v.1.1 y := by
        rw [← (integral_quotMeasure_tsum V.Γ h_int).2]
        have h_rat (γ : V.Γ) (y : G E s) : v.1.1 (γ * y) = v.1.1 y := v.1.2.rat_mul γ γ.2 y
        -- Insert the kernel for the conjugate of `F` in the Petersson product.
        simp [χ, inner_eq_petersson, petersson, hF, h_rat, mul_assoc, ← tsum_mul_right]
    _ = ∫ y : G E s, e y.1 * v.1.1 (g * (y.1, 1)) * χ y.2 := by
        rw [← integral_mul_left_eq_self _ g]
        congr with y
        -- Where `χ` is not `0`, right translation by the finite part fixes `v`, of level `K`.
        have h_level (hy : y.2 ∈ K) : v.1.1 (g * y) = v.1.1 (g * (y.1, 1)) := by
          simpa [Prod.mul_def] using mem_levelSpace_formRep_iff.1 v.2 y.2 hy (g.1 * y.1, g.2)
        simp +contextual [χ, Set.indicator, h_level]
    _ = realConv e v.1.1 g * ∫ y, χ y := integral_prod_mul (fun y ↦ e y * v.1.1 (g * (y, 1))) _
    _ = volume.real (K : Set (Gf E n)) * v.1.1 g := by
        rw [v.1.2.realConv_eq he.integrable, hχ, mul_comm]

/-- The kernel for the characteristic function of the level: if `e` is a cusp kernel of order
`B ≥ 13 n ^ 3`, `K` a level and `b` an orthonormal basis of the forms of type `e` and level `K`,
then `∑_γ (e ⊗ 1_K)(g⁻¹ γ g') = vol K ∑_i b_i(g) conj(b_i(g'))`. -/
theorem tsum_kernel_eq_sum {K : Subgroup (Gf E n)} [hK : IsLevel K] [Nonempty n]
    (hB : 13 * card n ^ 3 ≤ B) (he : IsCuspKernel B e) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (levelSpace (V.formRep e) K)) (g g' : G E s) :
    ∑' γ : V.Γ, e (g⁻¹ * γ * g').1 * Set.indicator K 1 (g⁻¹ * γ * g').2 =
      volume.real (K : Set (Gf E n)) *
        ∑ i : ι, (b i : V.Form e).1 g * starRingEnd ℂ ((b i : V.Form e).1 g') := by
  -- The conjugate of the left side is a form `F` in `g'`; expand it in the basis.
  obtain ⟨F, hF⟩ : ∃ F : levelSpace (V.formRep e) K, ∀ g' : G E s, starRingEnd ℂ (F.1.1 g') =
      ∑' γ : V.Γ, e (g⁻¹ * γ * g').1 * Set.indicator K 1 (g⁻¹ * γ * g').2 :=
    V.exists_kernel_form (eight_mul_sq_lt_of_thirteen_mul_cube_le card_pos hB) he g⁻¹ K
  let ev : levelSpace (V.formRep e) K →ₗ[ℂ] ℂ :=
    { toFun v := v.1.1 g', map_add' _ _ := rfl, map_smul' _ _ := rfl }
  have h_expand : ev F = ∑ i : ι, ⟪b i, F⟫_ℂ * ev (b i) := by
    simpa only [_root_.map_sum, map_smul, smul_eq_mul] using congrArg ev (b.sum_repr' F).symm
  calc _ = starRingEnd ℂ (ev F) := (hF g').symm
    _ = ∑ i : ι, ⟪F, b i⟫_ℂ * starRingEnd ℂ (ev (b i)) := by
        simp only [h_expand, _root_.map_sum, map_mul, inner_conj_symm]
    _ = volume.real (K : Set (Gf E n)) * ∑ i : ι, (b i).1.1 g * starRingEnd ℂ (ev (b i)) := by
        simp only [V.inner_kernel_form he hF, Finset.mul_sum, mul_assoc]

/-- The kernel: let `e` be a cusp kernel of order `B ≥ 13 n ^ 3`, `K` a level, `b` an orthonormal
basis of the forms of type `e` and level `K`, and `a` an element of the group algebra of `G_f`. Then
the kernel `∑_γ (e ⊗ (a ⋆ 1_K))(g⁻¹ γ g')`, the sum over all rational points, is
`vol K ∑_i (a b_i)(g) conj(b_i(g'))`. Here `convIndicator` forms `a ⋆ 1_K`. -/
theorem partialKernel_convIndicator_eq_sum {K : Subgroup (Gf E n)} [hK : IsLevel K] [Nonempty n]
    (hB : 13 * card n ^ 3 ≤ B) (he : IsCuspKernel B e) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (levelSpace (V.formRep e) K)) (a : MonoidAlgebra ℂ (Gf E n))
    (g g' : G E s) :
    V.partialKernel e (convIndicator hK.isOpen hK.isCompact a) .univ g g' =
      volume.real (K : Set (Gf E n)) * ∑ i : ι,
        ((V.formRep e).asAlgebraHom a (b i)).1 g * starRingEnd ℂ ((b i : V.Form e).1 g') := by
  classical
  -- Both sides are linear in `a`, and for a group element `h` this is the case of `1_K` at `g h`.
  have h_add (y y' : V.Form e) : (y + y').1 g = y.1 g + y'.1 g := rfl
  have h_smul (c : ℂ) (y : V.Form e) : (c • y).1 g = c * y.1 g := rfl
  induction a using MonoidAlgebra.induction_on with
  | of h =>
    simp only [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one, formRep_apply]
    rw [← V.tsum_kernel_eq_sum hB he b (g * (1, h)) g']
    let i : U V.J ≃ V.Γ := (MonoidHom.ofInjective V.ratEmbed_injective).toEquiv
    have hi (γ : U V.J) : (i γ : G E s) = V.ratEmbed γ := rfl
    rw [← i.tsum_eq]
    refine tsum_congr fun γ ↦ ?_
    simp [kernelTerm, convIndicator_single, Set.indicator, hi, mul_assoc]
  | add a a' ha ha' =>
    simp only [map_add, LinearMap.add_apply, h_add, add_mul, sum_add_distrib, mul_add]
    rw [← ha, ← ha', partialKernel, partialKernel, partialKernel,
      ← (V.summable_kernelTerm hB _ he.decay .univ g g').tsum_add
        (V.summable_kernelTerm hB _ he.decay .univ g g')]
    simp [kernelTerm, mul_add]
  | smul c a ha =>
    simp only [map_smul, LinearMap.smul_apply, h_smul, mul_assoc, ← Finset.mul_sum]
    rw [mul_left_comm, ← ha, partialKernel, partialKernel, ← tsum_mul_left]
    simp [kernelTerm, mul_left_comm _ c]

/-- Let `e` be a cusp kernel of order `B ≥ 13 n ^ 3`, `K` a level, and `T` an operator that acts as
the element `a` of the group algebra on the forms of type `e` and level `K`. Then `vol K` times the
trace of `T` is `V.geometricSide` of all polynomials at `a ⋆ 1_K`, that is, the integral over `[G]`
of the kernel of `e ⊗ (a ⋆ 1_K)` on the diagonal. -/
theorem volume_mul_trace_eq {K : Subgroup (Gf E n)} [hK : IsLevel K] [Nonempty n]
    (hB : 13 * card n ^ 3 ≤ B) (he : IsCuspKernel B e) {a : MonoidAlgebra ℂ (Gf E n)}
    {T : End ℂ (levelSpace (V.formRep e) K)}
    (hT : ∀ y : levelSpace (V.formRep e) K, (T y : V.Form e) = (V.formRep e).asAlgebraHom a y) :
    volume.real (K : Set (Gf E n)) * LinearMap.trace ℂ (levelSpace (V.formRep e) K) T =
      V.geometricSide hB he .univ (convIndicator hK.isOpen hK.isCompact a) := by
  have : Module.Finite ℂ (levelSpace (V.formRep e) K) := V.finite_levelSpace he ⟨K, hK.isOpen⟩
  let b := stdOrthonormalBasis ℂ (levelSpace (V.formRep e) K)
  -- Put `g' = g` in the expansion of the kernel and integrate.
  have h_diag (x : G E s) :
      ∑' γ : U V.J, V.polyTerm e (convIndicator hK.isOpen hK.isCompact a) .univ γ x =
        volume.real (K : Set (Gf E n)) * ∑ i, (T (b i)).1.1 x * starRingEnd ℂ ((b i).1.1 x) := by
    simp [hT, ← V.partialKernel_convIndicator_eq_sum hB he b a x x, partialKernel, kernelTerm]
  have h_int (v : levelSpace (V.formRep e) K) :
      Integrable (fun x ↦ (T v).1.1 x * starRingEnd ℂ (v.1.1 x)) V.quotMeasure :=
    (T v).1.2.memLp.integrable_mul v.1.2.memLp.star
  simp only [geometricSide_apply, h_diag]
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ h_int (b i),
    LinearMap.trace_eq_sum_inner T b]
  simp only [Submodule.coe_inner, inner_eq_petersson, petersson, mul_comm]

/-! ### Unfolding -/

/-- For a test function `φ` and a function `k` on the real group of a space `V` with decay of order
`B ≥ 13 n ^ 3`, the terms with an irreducible polynomial `R` converge absolutely in sum and
integral over `[G]`. -/
lemma lintegral_tsum_polyTerm_lt_top [Nonempty n] (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n))
    (hk : ∃ C : ℝ, ∀ g : GInf E s,
      ‖k g‖ * (∏ w : InfinitePlace E, ‖(g w : Matrix n n ℂ)‖) ^ B ≤ C)
    {R : E[X]} (hR : Irreducible R) :
    ∫⁻ x : G E s, ∑' γ : U V.J, ‖V.polyTerm k φ {R} γ x‖ₑ ∂V.quotMeasure < ∞ := by
  -- The sum over the `γ` with irreducible polynomial is bounded, and `[G]` has finite volume.
  obtain ⟨C, hC⟩ := V.exists_tsum_enorm_irreducibleTerm_le hB φ hk
  have h_le (γ : U V.J) (x : G E s) :
      ‖V.polyTerm k φ {R} γ x‖ₑ ≤ ‖V.irreducibleTerm k φ γ x‖ₑ := by
    by_cases hγ : (γ : Matrix n n E).charpoly = R
    · simp [kernelTerm, hγ, hR]
    · simp [kernelTerm, hγ]
  calc _ ≤ ∫⁻ _ : G E s, ENNReal.ofReal C ∂V.quotMeasure :=
        lintegral_mono fun x ↦ (ENNReal.tsum_le_tsum fun γ ↦ h_le γ x).trans (hC x)
    _ < ∞ := lintegral_const_lt_top ofReal_ne_top

/-- Let `φ` be a test function on `G_f`, let `k` be measurable on `G_∞` with
`‖k g‖ (∏_w ‖g_w‖) ^ B` bounded, where `B ≥ 13 n ^ 3`, and let `R` be irreducible. The integral over
`[G]` of the sum of the terms `(k ⊗ φ)(x⁻¹ γ x)`, over the rational points `γ` with characteristic
polynomial `R`, is the sum over all classes `c` of their contributions `V.classIntegral k φ R c`. -/
theorem hasSum_classIntegral [Nonempty n] (hB : 13 * card n ^ 3 ≤ B) (φ : TestFunction (Gf E n))
    (hk : ∃ C : ℝ, ∀ g : GInf E s,
      ‖k g‖ * (∏ w : InfinitePlace E, ‖(g w : Matrix n n ℂ)‖) ^ B ≤ C)
    (hk_meas : Measurable k) {R : E[X]} (hR : Irreducible R) :
    HasSum (V.classIntegral k φ R)
      (∫ x : G E s, ∑' γ : U V.J, V.polyTerm k φ {R} γ x ∂V.quotMeasure) := by
  -- Integrate term by term, and group the terms by the class of the rational point.
  have h_terms : HasSum (fun γ : U V.J ↦ ∫ x : G E s, V.polyTerm k φ {R} γ x ∂V.quotMeasure)
      (∫ x : G E s, ∑' γ : U V.J, V.polyTerm k φ {R} γ x ∂V.quotMeasure) :=
    hasSum_integral_of_lintegral_tsum_lt_top (V.lintegral_tsum_polyTerm_lt_top hB φ hk hR)
      fun γ ↦ Measurable.aestronglyMeasurable (by fun_prop)
  exact h_terms.tsum_fiberwise fun γ : U V.J ↦ frameClass (V.xFin, (γ : GL n E))

/-- Unfolding: let `φ` be a test function on `G_f` and `k` a measurable function on the real group
with `‖k g‖ (∏_w ‖g_w‖) ^ B` bounded, where `B ≥ 13 n ^ 3`. If the rational isometry `γ` has an
irreducible characteristic polynomial, then its term `(k ⊗ φ)(x⁻¹ γ x)` is integrable over `G`
modulo the rational centraliser. Moreover, its orbital integral equals the sum of the integrals over
`Γ \ G` of the terms of the rational points `γ'` whose pair `(V.xFin, γ')` lies in the class of
`(V.xFin, γ)`. Here `V.xFin` is the finite part of the frame of `V`. -/
theorem orbitalIntegral_unfold [Nonempty n] (hB : 13 * card n ^ 3 ≤ B) (φ : TestFunction (Gf E n))
    (hk : ∃ C : ℝ, ∀ g : GInf E s,
      ‖k g‖ * (∏ w : InfinitePlace E, ‖(g w : Matrix n n ℂ)‖) ^ B ≤ C)
    (hk_meas : Measurable k) {γ : U V.J} (hγ : Irreducible (γ : Matrix n n E).charpoly) :
    Integrable (V.orbitalIntegrand k φ γ) ((centralizer {γ}).map V.ratEmbed).quotMeasure ∧
    V.classIntegral k φ (γ : Matrix n n E).charpoly (frameClass (V.xFin, (γ : GL n E))) =
      V.orbitalIntegral k φ γ := by
  -- The fibre of `frameClass` through `γ` is its conjugacy class, an orbit of `ConjAct`.
  have h_equivariant (t : ConjAct (U V.J)) (δ : U V.J) (x : G E s) :
      V.polyTerm k φ {γ.1.1.charpoly} (t • δ) (V.ratEmbed (ofConjAct t) * x) =
        V.polyTerm k φ {γ.1.1.charpoly} δ x := by
    simp [kernelTerm, ConjAct.smul_def, mul_assoc, charpoly_mul_comm _ (_ * _⁻¹)]
  obtain ⟨h_int, -, h_sum⟩ := integral_tsum_orbit_of_lt_top_or_integrable
    (i := V.ratEmbed.comp ofConjAct.toMonoidHom)
    (Γ := V.Γ) (μ := volume) (S := (centralizer {γ}).map V.ratEmbed)
    (D := {δ : U V.J | frameClass (V.xFin, δ.1) = frameClass (V.xFin, γ.1)})
    (k := V.polyTerm k φ {γ.1.1.charpoly}) V.ratEmbed_injective rfl (by fun_prop) h_equivariant
    (congrArg _ (stabilizer_eq_centralizer γ)) (V.frameClass_eq_iff_mem_orbit γ)
    (.inl (V.lintegral_tsum_polyTerm_lt_top hB φ hk hγ))
  rw [polyTerm_charpoly] at h_int
  refine ⟨h_int, ?_⟩
  rw [classIntegral, orbitalIntegral, ← polyTerm_charpoly]
  -- `h_sum` says this, with the fibre of `frameClass` written as a set of rational points.
  exact h_sum

/-! ### Two lemmas on matrices, and triple kernels -/

/-- If the invertible matrix `k` conjugates `A` to a diagonal matrix with distinct entries `d`, then
a matrix `t` that commutes with `A` multiplies the `i`-th row of `k` by a scalar, the `i`-th
diagonal entry of `k t k⁻¹`. -/
lemma row_mul_eq_smul_of_commute {A t : Matrix n n ℂ} {k : (Matrix n n ℂ)ˣ} {d : n ↪ ℂ}
    (hk : SemiconjBy (k : Matrix n n ℂ) A (diagonal d)) (ht : Commute t A) (i : n) :
    diagonal (Pi.single i 1) * (k : Matrix n n ℂ) * t =
      (k * t * (k⁻¹ : (Matrix n n ℂ)ˣ)) i i •
        (diagonal (Pi.single i 1) * (k : Matrix n n ℂ)) := by
  -- `k t k⁻¹` commutes with `diagonal d`, so its `i`-th row vanishes off the diagonal.
  let M : Matrix n n ℂ := k * t * k⁻¹.1
  have h_comm : diagonal d * M = M * diagonal d := by
    simpa only [M, mul_assoc] using ((hk.mul_left ht).mul_left hk.units_inv_symm_left).eq.symm
  have h_off (b : n) (hb : b ≠ i) : M i b = 0 := by
    have h_entry : d i * M i b = M i b * d b := by simpa using congrFun₂ h_comm i b
    simpa [mul_comm (d i), d.injective.eq_iff, hb.symm] using h_entry
  have h_row : diagonal (Pi.single i 1) * M = M i i • diagonal (Pi.single i 1) := by
    ext a b
    obtain rfl | ha := eq_or_ne a i
    · obtain rfl | hb := eq_or_ne b a <;> simp [*, Ne.symm]
    · simp [ha, diagonal_apply]
  calc diagonal (Pi.single i 1) * k.1 * t = diagonal (Pi.single i 1) * M * k.1 := by
        simp only [M, mul_assoc, Units.inv_mul, mul_one]
    _ = M i i • (diagonal (Pi.single i 1) * k.1) := by rw [h_row, smul_mul_assoc]

omit [CMType E] in
/-- For a nonzero matrix `Q` and points `a`, `b` of the real group, multiplying `a` by `b` on the
right moves `log ‖Q a_w‖` by at most `‖b_w‖`, in the operator norm. -/
lemma abs_log_norm_mul_sub_le [Nonempty n] {Q : Matrix n n ℂ} (hQ : Q ≠ 0) (w : InfinitePlace E)
    (a b : GInf E s) :
    |‖Q * ((a * b) w : Matrix n n ℂ)‖.log - ‖Q * (a w : Matrix n n ℂ)‖.log| ≤
      ‖(b w : Matrix n n ℂ)‖ := by
  -- One side follows from `log r ≤ r`; the other too, as `b⁻¹` has the same norm as `b`.
  have h_le (a b : GInf E s) :
      ‖Q * ((a * b) w).1.1‖.log - ‖Q * (a w).1.1‖.log ≤ ‖(b w).1.1‖ := by
    have h_pos (c : GInf E s) : 0 < ‖Q * (c w).1.1‖ :=
      norm_pos_iff.2 ((c w).1.isUnit.mul_left_eq_zero.ne.2 hQ)
    calc _ = (‖Q * ((a * b) w).1.1‖ / ‖Q * (a w).1.1‖).log :=
          (log_div (h_pos _).ne' (h_pos _).ne').symm
      _ ≤ ‖Q * ((a * b) w).1.1‖ / ‖Q * (a w).1.1‖ := log_le_self (by positivity)
      _ ≤ ‖(b w).1.1‖ := by
          rw [div_le_iff₀' (h_pos a)]
          simpa [mul_assoc] using norm_mul_le (Q * (a w).1.1) (b w).1.1
  refine abs_sub_le_iff.2 ⟨h_le a b, .trans_eq ?_ (U.norm_inv (b w))⟩
  simpa using h_le (a * b) b⁻¹

/-- The measure on triples `(x, y, u)`, with `x` in `G` modulo the rational centraliser of `γ` and
`y`, `u` in the real group. -/
abbrev tripleMeasure (γ : U V.J) : Measure (G E s × GInf E s × GInf E s) :=
  ((centralizer {γ}).map V.ratEmbed).quotMeasure.prod (volume.prod volume)

/-- The integrand of `I_γ` with `e` written as a triple convolution, at a triple `(x, y, u)` with
`x` in `G` and `y`, `u` in the real group. For the kernel `p(a, b) = e(a⁻¹ b)` on the real group
its factor at infinity is `p(x, x y) p(x y, x y u) p(x y u, γ x)`. -/
def tripleKernel (e : GInf E s → ℂ) (φ : Gf E n → ℂ) (γ : U V.J)
    (p : G E s × GInf E s × GInf E s) : ℂ :=
  e p.2.1 * (e p.2.2 * e (p.2.2⁻¹ * (p.2.1⁻¹ * (p.1⁻¹ * V.ratEmbed γ * p.1).1))) *
    φ (p.1⁻¹ * V.ratEmbed γ * p.1).2

/-- The map of triples `(x, y, u)` that replaces the points `x, x y, x y u` by
`x y, x y u, x ((x⁻¹ γ x)_∞, 1)`. -/
def tripleRotate (γ : U V.J) (p : G E s × GInf E s × GInf E s) : G E s × GInf E s × GInf E s :=
  (p.1 * (p.2.1, 1), p.2.2, p.2.2⁻¹ * (p.2.1⁻¹ * (p.1⁻¹ * V.ratEmbed γ * p.1).1))

/-- The triple kernel is invariant under the rotation of triples. -/
lemma tripleKernel_tripleRotate (φ : Gf E n → ℂ) (γ : U V.J) (p : G E s × GInf E s × GInf E s) :
    V.tripleKernel e φ γ (V.tripleRotate γ p) = V.tripleKernel e φ γ p := by
  simp [tripleKernel, tripleRotate, mul_assoc]
  ring

/-- The triple kernel of `γ` is left invariant in `x` under the rational points commuting with
`γ`. -/
lemma tripleKernel_ratEmbed_mul (φ : Gf E n → ℂ) {γ t : U V.J} (ht : Commute γ t) (x : G E s)
    (q : GInf E s × GInf E s) :
    V.tripleKernel e φ γ (V.ratEmbed t * x, q) = V.tripleKernel e φ γ (x, q) := by
  simp only [tripleKernel, V.conj_ratEmbed_mul ht]

/-- The triple kernel of `γ` is measurable if the kernel `e` on the real group is. -/
@[fun_prop] lemma measurable_tripleKernel (φ : TestFunction (Gf E n)) (he : Measurable e)
    (γ : U V.J) : Measurable (V.tripleKernel e φ γ) := by
  have hφ : Measurable φ.1 := φ.2.1.continuous.measurable
  fun_prop [tripleKernel]

/-- The trace property: for a rational point `γ`, composing with the rotation `V.tripleRotate γ` of
triples does not change the integral for `V.tripleMeasure γ` of a measurable integrable function
`f`, integrable also after the rotation, that is left invariant in `x` under the rational
centraliser of `γ`. Here `V.tripleMeasure γ` lives on triples `(x, y, u)` in `G × G_∞ × G_∞`, with
`x` taken modulo that centraliser, and `V.tripleRotate γ` sends the points `x, x y, x y u` to
`x y, x y u, x ((x⁻¹ γ x)_∞, 1)`. -/
lemma integral_comp_tripleRotate {γ : U V.J} {f : G E s × GInf E s × GInf E s → ℂ}
    (hf_meas : Measurable f) (hf : Integrable f (V.tripleMeasure γ))
    (hf_rotate : Integrable (fun p : G E s × GInf E s × GInf E s ↦ f (V.tripleRotate γ p))
      (V.tripleMeasure γ))
    (hf_inv : ∀ t : U V.J, Commute γ t → ∀ (x : G E s) (q : GInf E s × GInf E s),
      f (V.ratEmbed t * x, q) = f (x, q)) :
    ∫ p : G E s × GInf E s × GInf E s, f (V.tripleRotate γ p) ∂V.tripleMeasure γ =
      ∫ p : G E s × GInf E s × GInf E s, f p ∂V.tripleMeasure γ := by
  -- The rotation translates `x` by `y` and then, at the translated point `x'`, applies to `(y, u)`
  -- a substitution `T x'` that preserves Haar measure.
  let ν : Measure (G E s) := ((centralizer {γ}).map V.ratEmbed).quotMeasure
  let μ : Measure (GInf E s × GInf E s) := volume.prod volume
  let T (x : G E s) (q : GInf E s × GInf E s) : GInf E s × GInf E s :=
    (q.2, q.2⁻¹ * ((x⁻¹ * V.ratEmbed γ * x).1 / q.1))
  have hT (x : G E s) : μ.map (T x) = μ := ((measurePreserving_prod_inv_mul_swap volume volume).comp
    ((measurePreserving_div_left volume _).prod (.id volume))).map_eq
  have h_rotate (x : G E s) (q : GInf E s × GInf E s) :
      V.tripleRotate γ (x, q) = (x * (q.1, 1), T (x * (q.1, 1)) q) := by
    simp [tripleRotate, T, div_eq_mul_inv, mul_assoc]
  have h_fix (q : GInf E s × GInf E s) (t : (centralizer {γ}).map V.ratEmbed) (x : G E s) :
      f (t • x, T (t • x) q) = f (x, T x q) := by
    obtain ⟨_, τ, hτ, rfl⟩ := t
    simp only [T, Subgroup.smul_def, smul_eq_mul, V.conj_ratEmbed_mul (hτ γ rfl),
      hf_inv τ (hτ γ rfl)]
  calc ∫ p, f (V.tripleRotate γ p) ∂V.tripleMeasure γ
      = ∫ q, ∫ x, f (x * (q.1, 1), T (x * (q.1, 1)) q) ∂ν ∂μ := by
        simpa only [h_rotate] using integral_prod_symm _ hf_rotate
    _ = ∫ q, ∫ x, f (x, T x q) ∂ν ∂μ := by
        congr with q
        exact (identDistrib_orbitMeasure_mul_right (F := fun x ↦ f (x, T x q)) (q.1, 1)
          (h_fix q) (by fun_prop)).integral_eq
    _ = ∫ x, ∫ q, f (x, q) ∂μ ∂ν := integral_integral_skew_product hT hf (by fun_prop)
    _ = ∫ p, f p ∂V.tripleMeasure γ := (integral_prod _ hf).symm

/-- Let `e` be a cusp kernel of order `B ≥ 13 (card n)^3`, `φ` a test function on `G_f`, and `γ` a
rational point of `U V.J` with irreducible characteristic polynomial. Let `a` be a measurable weight
on triples `(x, y, u)` (`x` in `G`; `y`, `u` in the real group) with `|a (x, y, u)| ≤ ‖y‖ ‖u‖`, each
norm being the product over the infinite places of the operator norms. Then `a` times
`V.tripleKernel e φ γ` is integrable for `V.tripleMeasure γ` (the measure on such triples with `x`
taken modulo the rational centraliser of `γ`). Here `V.tripleKernel e φ γ` is the integrand of `I_γ`
with `e` written as a triple convolution; its factor at infinity is
`p(x, x y) p(x y, x y u) p(x y u, γ x)` for `p(a, b) = e(a⁻¹ b)`. -/
lemma integrable_mul_tripleKernel [Nonempty n] (hB : 13 * card n ^ 3 ≤ B)
    (φ : TestFunction (Gf E n)) (he : IsCuspKernel B e) {γ : U V.J}
    (hγ : Irreducible (γ : Matrix n n E).charpoly) {a : G E s × GInf E s × GInf E s → ℝ}
    (ha_meas : Measurable a)
    (ha : ∀ (x : G E s) (y u : GInf E s), |a (x, y, u)| ≤
      (∏ w : InfinitePlace E, ‖(y w : Matrix n n ℂ)‖) *
        ∏ w : InfinitePlace E, ‖(u w : Matrix n n ℂ)‖) :
    Integrable (fun p : G E s × GInf E s × GInf E s ↦ a p * V.tripleKernel e φ γ p)
      (V.tripleMeasure γ) := by
  -- Compare with the integrand of `I_γ` for the kernel `‖·‖ ^ (-B)`, times the moments of order
  -- `B + 1` of `e` in `y` and in `u`.
  let N (y : GInf E s) : ℝ := ∏ w : InfinitePlace E, ‖(y w : Matrix n n ℂ)‖
  obtain ⟨C, h_decay⟩ : ∃ C : ℝ, ∀ x : GInf E s, ‖e x‖ * N x ^ B ≤ C := he.decay
  have h_meas : Measurable e := he.continuous.measurable
  have hN_pos (y : GInf E s) : 0 < N y := one_pos.trans_le (le_prod_opNorm y).1
  have hN_mul (a b : GInf E s) : N (a * b) ≤ N a * N b := (prod_le_prod₀
    (fun _ _ ↦ norm_nonneg _) fun _ _ ↦ norm_mul_le _ _).trans_eq prod_mul_distrib
  -- The kernel `‖·‖ ^ (-B)` has decay of order `B`, so its orbital integral converges.
  have h_inv_decay (y : GInf E s) : ‖((N y : ℂ) ^ B)⁻¹‖ * N y ^ B ≤ 1 := by
    simp [N, inv_mul_le_one]
  have h_orb : Integrable (V.orbitalIntegrand (fun y ↦ ((N y : ℂ) ^ B)⁻¹) φ γ)
      ((centralizer {γ}).map V.ratEmbed).quotMeasure :=
    (V.orbitalIntegral_unfold hB φ ⟨1, h_inv_decay⟩ (by fun_prop) hγ).1
  have h_moment : Integrable fun y : GInf E s ↦ ‖e y‖ * N y ^ (B + 1) := he.integrable_moment
  refine .mono' ((h_orb.norm.mul_prod (h_moment.mul_prod h_moment)).const_mul C) (by fun_prop)
    (.of_forall fun ⟨x, y, u⟩ ↦ ?_)
  let c : G E s := x⁻¹ * V.ratEmbed γ * x
  let z : GInf E s := u⁻¹ * (y⁻¹ * c.1)
  have hc : N c.1 ≤ N y * N u * N z := calc
    N c.1 = N (y * u * z) := by simp only [z, mul_assoc, mul_inv_cancel_left]
    _ ≤ N y * N u * N z := by grw [hN_mul, hN_mul]
  have hz : ‖e z‖ ≤ C * (N y * N u) ^ B / N c.1 ^ B := by
    rw [le_div_iff₀ (pow_pos (hN_pos _) B)]
    calc ‖e z‖ * N c.1 ^ B ≤ ‖e z‖ * (N y * N u * N z) ^ B := by gcongr
      _ = ‖e z‖ * N z ^ B * (N y * N u) ^ B := by ring
      _ ≤ C * (N y * N u) ^ B := by grw [h_decay z]
  calc ‖a (x, y, u) * V.tripleKernel e φ γ (x, y, u)‖
      = |a (x, y, u)| * (‖e y‖ * (‖e u‖ * ‖e z‖) * ‖φ.1 c.2‖) := by
        simp only [tripleKernel, norm_mul, norm_real, Real.norm_eq_abs, c, z]
    _ ≤ N y * N u * (‖e y‖ * (‖e u‖ * (C * (N y * N u) ^ B / N c.1 ^ B)) * ‖φ.1 c.2‖) := by
        gcongr
        exact ha x y u
    _ = C * (‖((N c.1 : ℂ) ^ B)⁻¹ * φ.1 c.2‖ *
          (‖e y‖ * N y ^ (B + 1) * (‖e u‖ * N u ^ (B + 1)))) := by
        rw [norm_mul, norm_inv, norm_pow, norm_real, Real.norm_of_nonneg (hN_pos _).le]
        ring

/-- Fubini's theorem for an integrable function of triples `(x, y, u)`, after a substitution `S` in
`(y, u)` that preserves measure. -/
lemma integral_tripleMeasure {γ : U V.J} {f : G E s × GInf E s × GInf E s → ℂ}
    (hf : Integrable f (V.tripleMeasure γ)) {S : GInf E s × GInf E s → GInf E s × GInf E s}
    (hS : MeasurePreserving S (volume.prod volume) (volume.prod volume)) :
    ∫ p : G E s × GInf E s × GInf E s, f p ∂V.tripleMeasure γ =
      ∫ x : G E s, ∫ y : GInf E s, ∫ u : GInf E s, f (x, S (y, u)) ∂volume ∂volume
        ∂((centralizer {γ}).map V.ratEmbed).quotMeasure := by
  obtain ⟨h_int, h_eq⟩ := ((MeasurePreserving.id _).prod hS).fubini hf
  rw [← h_eq]
  exact integral_congr_ae (h_int.prod_right_ae.mono fun x ↦ integral_prod _)

/-- Let `e` be a cusp kernel, `φ` a test function, and `b` a weight such that both integrands below
are integrable. As `e ⋆ e = e`, the weight may be read at `y u` or at `y` against the triple kernel
of `γ`: both integrals reduce to that of `b(x, y) p(x, x y) p(x y, γ x)` times the factor of `φ`,
where `p(g, h) = e(g⁻¹ h)` on the real group. -/
lemma integral_mul_tripleKernel_mul (φ : TestFunction (Gf E n)) (he : IsCuspKernel B e)
    {γ : U V.J} {b : G E s → GInf E s → ℝ}
    (h_mul : Integrable (fun p : G E s × GInf E s × GInf E s ↦
      b p.1 (p.2.1 * p.2.2) * V.tripleKernel e φ γ p) (V.tripleMeasure γ))
    (h_fst : Integrable (fun p : G E s × GInf E s × GInf E s ↦
      b p.1 p.2.1 * V.tripleKernel e φ γ p) (V.tripleMeasure γ)) :
    ∫ p : G E s × GInf E s × GInf E s, b p.1 (p.2.1 * p.2.2) * V.tripleKernel e φ γ p
        ∂V.tripleMeasure γ =
      ∫ p : G E s × GInf E s × GInf E s, b p.1 p.2.1 * V.tripleKernel e φ γ p
        ∂V.tripleMeasure γ := by
  -- On the left substitute `(y, u) ↦ (u, u⁻¹ y)`; then integrate over `u` on both sides.
  rw [V.integral_tripleMeasure h_mul (measurePreserving_prod_inv_mul_swap volume volume),
    V.integral_tripleMeasure h_fst (.id _)]
  congr with x
  congr with y
  -- On each side the factors that depend on `u` form a convolution `e ⋆ e = e`.
  let c : G E s := x⁻¹ * V.ratEmbed γ * x
  calc _ = ∫ u, b x y * (e u * e (u⁻¹ * y) * e (y⁻¹ * c.1) * φ.1 c.2) := by
        simp [tripleKernel, c, mul_assoc]
    _ = b x y * (e y * e (y⁻¹ * c.1) * φ.1 c.2) := by
        simp only [integral_const_mul, integral_mul_const, he.convolution_self]
    _ = ∫ u, b x y * V.tripleKernel e φ γ (x, y, u) := by
        simp only [tripleKernel, c, integral_const_mul, integral_mul_const, he.convolution_self]

end Space

end New

end
