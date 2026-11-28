import Lib.Adelic.Unitary.Defs
import Lib.General.Analysis.FourierTransforms
import Lib.General.NumberTheory.EmbeddingsAndDifferent

/-!
# Standard character, self-duality, strong approximation and one-sided Poisson summation

Let `E` be a totally complex field with adele ring `New.𝔸 E`, and let `New.toAdele` be the diagonal
embedding of `E`. `New.stdAddChar` is the standard additive character, and its finite part `New.ψf`
is trivial on the integral adeles `New.Ô`. The file shows that, over a CM field, rational points of
unitary groups are discrete in the adelic group. It treats the conductor and nondegeneracy of the
character, proves that `E` is its own annihilator (also for matrices), and proves strong
approximation for adeles and adelic matrices. It ends with a one-sided Poisson summation inequality
and the compact open group given by the inverse different among self-adjoint finite adeles.

## Main definitions and results

* `New.Space.discreteTopology_Gamma`: `New.Space.Γ` is discrete, because the rational matrices
  `New.ratMatrices` are discrete among the adelic ones. So the image under `New.Space.ratEmbed` of
  any subgroup is discrete.
* `New.stdAddChar_toAdele`, `New.mem_ratAdeles_of_stdAddChar_eq_one`: for `E` totally complex,
  `New.stdAddChar` is trivial on `E`. An adele that pairs trivially with all of `E` lies in `E`. So
  `E` is its own annihilator.
* `New.isDualFamily_ratAdeles`: the characters `x ↦ stdAddChar E (toAdele a * x)`, `a : E`, form a
  dual family for the adeles modulo `E`.
* `New.isDualFamily_ratMatrices`: the same for matrices, with the trace pairing.
* `New.strong_approximation`: strong approximation; `E` plus the adeles supported on a nonempty set
  `S` of finite places is dense in the adeles.
* `New.Exchange.denseRange_rat_matrix_add`: strong approximation for matrices.

Notions from other files:
* `New.𝔸f E`, `New.Ô E`: the finite adeles of `E` and the subring of integral finite adeles.
* `New.PlaceEmbedding.Φ`: a chosen complex embedding `Φ w` of `E` for each infinite place `w`; the
  adele ring `New.𝔸 E` is the product of one copy of `ℂ` for each `w` with `New.𝔸f E`.
* `New.ratAdeles`, `New.ratMatrices`: the images of `E` and of the matrices over `E` under
  `New.toAdele`, as additive subgroups.
* `New.IsDualFamily B₀ χ`: `i ↦ χ i` is an injective homomorphism to the continuous unitary
  characters trivial on `B₀`, and the common kernel of the `χ i` lies in `B₀`.

## Relation to the literature

Known result: Self-duality of a number field in its adeles, strong approximation and a Poisson
inequality. For totally complex fields only, the field is shown to be its own annihilator and the
pairing is shown to be non-degenerate. Strong approximation omits a nonempty set of finite places
and is deduced from duality. Poisson summation is proved only as an inequality, for nonnegative
integrable functions that are lower semicontinuous at the rational points of the sum. Source: J.
Tate, Fourier analysis in number fields and Hecke's zeta-functions, thesis 1950, in Cassels-Fröhlich
ch. XV, Theorem 4.1.4; for strong approximation, Cassels, ch. II §15.

See also `Lib.Adelic.Unitary.WeakApproximation`.
-/

/-!
## Rational points of a space embed injectively and discretely

For a hermitian space `V = (J, x)` (`New.Space`: a matrix `J` over the CM field `E` and an adelic
change of basis `x` that brings it to the standard form), `New.Space.ratEmbed` sends a rational
point `γ` of the unitary group of `J` to `x⁻¹ γ x` in the adelic group `New.G` (its underlying
adelic matrix is `adeleMatrix`), and `New.Space.embFin` is its finite part.
-/

namespace New

open NumberField Matrix Function Subtype

variable {E : Type*} [Field E] [CMType E]
  {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ} (V : Space E n s)

/-- The ring of finite adeles is nontrivial, since it maps to the completion at a finite place. -/
instance {E : Type*} [Field E] [NumberField E] : Nontrivial (𝔸f E) := by
  obtain ⟨w⟩ : Nonempty (FinPlace E) := (IsDedekindDomain.HeightOneSpectrum.equivMaximalSpectrum
    (RingOfIntegers.not_isField E)).nonempty
  exact (evalAt w).domain_nontrivial

namespace Space

lemma adeleMatrix_ratEmbed (γ : U V.J) :
    (V.ratEmbed γ).adeleMatrix = V.x⁻¹ * ((γ : GL n E) : Matrix n n E).map toAdele * V.x := rfl

/-- For a space `V = (J, x)`, the finite part of the change of basis `x`, in `GL n (𝔸f E)`. -/
@[local simp]
noncomputable def xFin : GL n (𝔸f E) := V.x.map (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E))

/-- For a space `V = (J, x)` and `γ` in the rational unitary group `U V.J`, the finite part
`V.embFin γ` of `x⁻¹ γ x` is, in `GL n (𝔸f E)`, the conjugate of `γ` by the finite part
`V.xFin` of `x`. -/
lemma coe_embFin (γ : U V.J) : (V.embFin γ : GL n (𝔸f E)) =
    V.xFin⁻¹ * GeneralLinearGroup.map (algebraMap E (𝔸f E)) (γ : GL n E) * V.xFin := by
  change GeneralLinearGroup.map (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E))
    (V.x⁻¹ * GeneralLinearGroup.map toAdele (γ : GL n E) * V.x) = _
  rw [map_mul, map_mul, map_inv]
  rfl

/-- For the standard space (`J = 1`, `x = 1`), the finite part of the embedding of rational points
applies `E → 𝔸f E` to each entry. -/
@[simp]
lemma _root_.New.stdSpace_embFin (γ : U (stdSpace E n).J) :
    ((stdSpace E n).embFin γ).val = GeneralLinearGroup.map (algebraMap E (𝔸f E)) γ := by
  simp [coe_embFin]

/-- The finite part `New.Space.embFin` of the embedding of rational points is injective. -/
instance fact_embFin_injective : Fact (Injective V.embFin) :=
  ⟨by simp [Injective, Gf.val_ext_iff, coe_embFin, GeneralLinearGroup.ext_iff]⟩

lemma ratEmbed_injective : Injective V.ratEmbed :=
  .of_comp (f := Prod.snd) V.fact_embFin_injective.out

/-- The group `V.Γ = x⁻¹ U(J)(E) x` of rational points of a space `V = (J, x)` is discrete, because
the rational matrices are discrete among the adelic ones. -/
instance discreteTopology_Gamma : DiscreteTopology V.Γ := by
  -- `V.toRatCoords : g ↦ x g x⁻¹` is a continuous injection of `V.Γ` into the rational matrices
  have h_mem (g : V.Γ) : (V.toRatCoords g : GL n (𝔸 E)).val ∈ ratMatrices E n n := by
    obtain ⟨γ, hγ⟩ : ∃ γ : U V.J, V.ratEmbed γ = g := g.prop
    exact ⟨(γ : GL n E), by simp [← hγ, ratEmbed, U.map]⟩
  let f (g : V.Γ) : ratMatrices E n n := ⟨(V.toRatCoords g : GL n (𝔸 E)), h_mem g⟩
  have hf_cont : Continuous f := .subtype_mk ((continuous_const.matrix_mul
    (G.continuous_adeleMatrix.comp continuous_subtype_val)).matrix_mul continuous_const) h_mem
  exact .of_continuous_injective hf_cont (by simp [f, Injective, Units.val_inj])

/-- The image in the adelic group of any subgroup of the rational points is discrete. -/
instance {S : Subgroup (U V.J)} : DiscreteTopology (Subgroup.map V.ratEmbed S) :=
  .of_subset V.discreteTopology_Gamma (S.map_le_range V.ratEmbed)

end Space

end New

/-!
## The standard adelic additive character: conductor, nondegeneracy, E self-dual

The finite part `New.ψf` sends `a` in `E` to exp(2πi Tr a).

* `New.forall_ψf_mul_eq_one_iff`: the annihilator of `New.Ô` is given by the inverse different.
-/

namespace New

open NumberField RingOfIntegers AddChar FractionalIdeal Finset Variety Algebra Int InfinitePlace

variable {E : Type*} [Field E] [NumberField E]

/-! ### The finite character -/

/-- The values of the character `ψf E` of the finite adeles are roots of unity. -/
lemma isOfFinOrder_ψf (x : 𝔸f E) : IsOfFinOrder (ψf E x : ℂ) := by
  -- some positive multiple `N * x` is integral, so the `N`-th power of `ψf E x` is one
  obtain ⟨N, hN, h_mem⟩ : ∃ N : ℕ, N ≠ 0 ∧ (N : 𝔸f E) * x ∈ Ô E := by
    simpa using exists_forall_mul_mem_Ô ![x]
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN.bot_lt, ?_⟩
  rw [← Circle.coe_pow, ← map_nsmul_eq_pow, nsmul_eq_mul, ψf_eq_one_of_mem h_mem, Circle.coe_one]

@[fun_prop]
lemma continuous_ψf : Continuous (ψf E) := by
  -- a character that is trivial on the open subring `Ô E` is continuous at zero
  have h_cont : ContinuousOn (ψf E) (Ô E) := continuousOn_const.congr fun _ ↦ ψf_eq_one_of_mem
  have h_zero : ContinuousAt (ψf E) 0 := isOpen_Ô.continuousOn_iff.1 h_cont (zero_mem _)
  exact continuous_of_continuousAt_one (toMonoidHom (ψf E)) h_zero

/-- The standard character at an adele `x` is `exp (-2πi ∑ w, 2 Re x_w)`, the sum being over the
infinite places, times `ψf E` of the finite part. -/
lemma stdAddChar_eq_mul_ψf (x : 𝔸 E) :
    stdAddChar E x = Real.fourierChar (-∑ w : InfinitePlace E, 2 * (x.1 w).re) * ψf E x.2 := rfl

@[fun_prop]
lemma continuous_stdAddChar : Continuous (stdAddChar E) := by
  simp only [funext stdAddChar_eq_mul_ψf]
  fun_prop

/-- Every value of `ψf E` is `exp (2πi q)` for a rational number `q`. -/
lemma exists_ψf_eq_fourierChar (x : 𝔸f E) : ∃ q : ℚ, ψf E x = Real.fourierChar q := by
  obtain ⟨a, ha⟩ : ∃ a : E, x - a ∈ Ô E := exists_sub_mem_Ô x
  exact ⟨trace ℚ E a, by rw [← ψf_coe, ← div_eq_one, ← map_sub_eq_div, ψf_eq_one_of_mem ha]⟩

/-- For a finite adele `x` of `E`, the character `ψf E` (the finite part of the standard additive
character) is trivial on `u * x` for all integral finite adeles `u ∈ Ô E` if and only if `d * x`
is integral for every `d` in the different of `E` over `ℚ`. -/
lemma forall_ψf_mul_eq_one_iff {x : 𝔸f E} :
    (∀ u ∈ Ô E, ψf E (u * x) = 1) ↔
      ∀ d ∈ differentIdeal ℤ (𝓞 E), algebraMap E (𝔸f E) d * x ∈ Ô E := by
  -- Choose `a` in `E` with `x - a` integral. The left side says that `a` lies in the trace dual
  -- of `𝓞 E`, the right side that it lies in the inverse different.
  obtain ⟨a, ha⟩ : ∃ a : E, x - a ∈ Ô E := exists_sub_mem_Ô x
  have h_mem (u : 𝓞 E) : algebraMap E (𝔸f E) u ∈ Ô E := algebraMap_mem_Ô.2 (isIntegral_coe u)
  have h_trace (u : 𝓞 E) :
      ψf E (algebraMap E (𝔸f E) u * x) = Real.fourierChar (trace ℚ E (u * a)) := by
    rw [← sub_add_cancel x a, mul_add, map_add_eq_mul, ψf_eq_one_of_mem (mul_mem (h_mem u) ha),
      one_mul,
      ← map_mul, ψf_coe]
  have h_int (d : 𝓞 E) : algebraMap E (𝔸f E) d * x ∈ Ô E ↔ IsIntegral ℤ (d * a) := by
    rw [← sub_add_cancel x a, mul_add, add_mem_cancel_left (mul_mem (h_mem d) ha), ← map_mul,
      algebraMap_mem_Ô]
  calc (∀ u ∈ Ô E, ψf E (u * x) = 1)
    -- `𝓞 E` is dense in `Ô E` and `ψf` is continuous, so it is enough to test on `𝓞 E`
    _ ↔ ∀ u : 𝓞 E, ψf E (algebraMap E (𝔸f E) u * x) = 1 :=
      ⟨fun h u ↦ h _ (h_mem u), fun h ↦ Subtype.forall'.2 (denseRange_algebraMap_Ô.eq h)⟩
    _ ↔ ∀ u : 𝓞 E, ∃ n : ℤ, trace ℚ E (u * a) = n := by
      simp only [h_trace, fourierChar_eq_one_iff, ← Rat.cast_intCast (α := ℝ), Rat.cast_inj]
    _ ↔ a ∈ dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
      simp [mem_dual, mul_comm a, eq_comm]
    -- the different is the inverse of the trace dual
    _ ↔ a ∈ (differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ := by
      rw [coeIdeal_differentIdeal ℤ ℚ E, inv_inv]
    _ ↔ ∀ d ∈ differentIdeal ℤ (𝓞 E), algebraMap E (𝔸f E) d * x ∈ Ô E := by
      simp [h_int, mem_inv_iff, differentIdeal_ne_bot, mul_comm a,
        IsIntegralClosure.isIntegral_iff (A := 𝓞 E)]

/-- A finite adele all of whose multiples are integral is zero. -/
lemma eq_zero_of_forall_mul_integral {a : 𝔸f E} (h_int : ∀ x : 𝔸f E, x * a ∈ Ô E) : a = 0 := by
  -- `a` lies in every neighbourhood `U` of zero: `U` contains some `N * Ô E`, and `N⁻¹ * a ∈ Ô E`
  suffices h_nhds : ∀ U ∈ nhds (0 : 𝔸f E), a ∈ U from pure_le_nhds_iff.1 h_nhds
  intro U hU
  obtain ⟨N, hN, h_sub⟩ : ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ Ô E, (N : 𝔸f E) * x ∈ U :=
    mem_nhds_zero_finAdele_iff.1 hU
  obtain ⟨u, hu⟩ : ∃ u : (𝔸f E)ˣ, u = (N : 𝔸f E) := isUnit_natCast_finAdele hN
  have h_mem : (N : 𝔸f E) * (↑u⁻¹ * a) ∈ U := h_sub _ (h_int _)
  rwa [← hu, u.mul_inv_cancel_left] at h_mem

/-- The pairing given by `ψf E`, the finite part of the standard additive character, separates
finite adeles: if `ψf E (t * a) = ψf E (t * b)` for all finite adeles `t`, then `a = b`. -/
lemma eq_of_forall_ψf_mul_eq {a b : 𝔸f E} (hab : ∀ t : 𝔸f E, ψf E (t * a) = ψf E (t * b)) :
    a = b := by
  -- Show that every multiple of `a - b` is integral; write the multiplier as `discr E • c`.
  refine eq_of_sub_eq_zero (eq_zero_of_forall_mul_integral fun x ↦ ?_)
  obtain ⟨c, rfl⟩ : ∃ c : 𝔸f E, (NumberField.discr E : E) • c = x :=
    MulAction.surjective₀ (cast_ne_zero.2 (discr_ne_zero E)) x
  have h_triv : ∀ u ∈ Ô E, ψf E (u * (c * (a - b))) = 1 := fun u _ ↦ by
    rw [← mul_assoc, mul_sub, map_sub_eq_div, hab (u * c), div_self']
  -- so `c * (a - b)` times the discriminant, an element of the different, is integral
  have h_mem : algebraMap E (𝔸f E) (NumberField.discr E : 𝓞 E) * (c * (a - b)) ∈ Ô E :=
    forall_ψf_mul_eq_one_iff.1 h_triv _ (discr_mem_differentIdeal E _)
  simpa [Algebra.smul_def, mul_assoc] using h_mem

/-- For a CM field `E`, the character `ψf E` is invariant under complex conjugation `star` of finite
adeles. -/
lemma ψf_star [IsCMField E] (x : 𝔸f E) : ψf E (star x) = ψf E x := by
  -- by density it is enough to take `x` in `E`, where conjugation preserves the trace
  have h_trace (a : E) : trace ℚ E (star a) = trace ℚ E a :=
    trace_eq_of_algEquiv starRingAut.toRatAlgEquiv a
  revert x
  exact denseRange_algebraMap_finAdele.eq fun a ↦ by simp [ψf_coe, h_trace]

variable [IsTotallyComplex E] [PlaceEmbedding E]

/-! ### Norm and trace through the chosen embeddings -/

/-- For `E` totally complex, the absolute norm of `x` is the product of the `‖Φ v x‖ ^ 2` over the
infinite places `v`, where `Φ v` is the chosen embedding at `v`. -/
lemma abs_norm_eq_prod_norm_sq (x : E) :
    |(Algebra.norm ℚ x : ℝ)| = ∏ v : InfinitePlace E, ‖Φ v x‖ ^ 2 := by
  simpa [← apply, mk_Φ] using (prod_eq_abs_norm x).symm

/-- For a nonzero algebraic integer `y` of a totally complex field, the product of the `‖Φ v y‖`
over the infinite places `v` is at least one; `Φ v` is the chosen embedding at `v`. -/
lemma one_le_prod_norm_Φ {y : E} (hy_int : IsIntegral ℤ y) (hy : y ≠ 0) :
    1 ≤ ∏ v : InfinitePlace E, ‖Φ v y‖ := by
  -- the square of the product is the absolute value of the norm, a nonzero integer
  obtain ⟨z, rfl⟩ : ∃ z : 𝓞 E, (z : E) = y := ⟨⟨y, hy_int⟩, rfl⟩
  have h_norm : (1 : ℝ) ≤ |(Algebra.norm ℚ (z : E) : ℝ)| := by
    rw [← coe_norm_int]
    exact_mod_cast one_le_abs (norm_ne_zero_iff.2 (by simpa using hy))
  rwa [abs_norm_eq_prod_norm_sq, prod_pow, one_le_sq_iff₀ (by positivity)] at h_norm

/-- For `E` totally complex, the trace of `x` is `∑ w, 2 Re (Φ w x)` over the infinite places `w`,
where `Φ w` is the chosen embedding at `w`. -/
lemma trace_eq_sum_Φ (x : E) : trace ℚ E x = ∑ w : InfinitePlace E, 2 * (Φ w x).re := by
  -- take real parts in the sum over all embeddings, which come in conjugate pairs
  have h_sum : (trace ℚ E x : ℂ) = ∑ σ : E →+* ℂ, σ x :=
    (trace_eq_sum_embeddings ℂ).trans ((RingHom.equivRatAlgHom E ℂ).sum_comp fun σ ↦ σ x).symm
  simpa [sum_embeddings_eq_sum_pairs, two_mul] using congrArg Complex.re h_sum

/-! ### The annihilator of the rational points -/

/-- For `E` totally complex, the standard additive character `stdAddChar E` of the adeles is trivial
on the diagonal image of `E`. -/
@[simp]
lemma stdAddChar_toAdele (x : E) : stdAddChar E (toAdele x) = 1 := by
  simp [trace_eq_sum_Φ, stdAddChar_eq_mul_ψf, map_neg_eq_inv, ψf_coe]

/-- Let `E` be totally complex, with chosen embeddings `Φ w` at the infinite places `w`.
If `∑ w, 2 * Re (Φ w b * z w)` is rational for every `b` in `E`, then
`z = fun w ↦ Φ w a` for some `a` in `E`. The factor `2` is the one in `New.trace_eq_sum_Φ`. -/
lemma exists_eq_Φ_of_forall_sum_re_rat {z : InfinitePlace E → ℂ}
    (h_trace : ∀ b : E, ∃ q : ℚ, ∑ w : InfinitePlace E, 2 * (Φ w b * z w).re = q) :
    ∃ a : E, z = fun w : InfinitePlace E ↦ Φ w a := by
  -- The images under `Φ` of an integral basis `v` form a real basis of the space; let `c` be the
  -- coordinates of `z`. Pairing `z` with the trace-dual basis shows that they are rational.
  let ι : Type _ := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let v : Module.Basis ι ℚ E := integralBasis E
  obtain ⟨c, hz⟩ : ∃ c : ι → ℝ, ∀ w : InfinitePlace E, z w = ∑ i : ι, c i * Φ w (v i) := by
    obtain ⟨e, he⟩ : ∃ e : mixedEmbedding.mixedSpace E ≃ₗ[ℝ] (InfinitePlace E → ℂ),
        ∀ x : E, e (mixedEmbedding E x) = fun w : InfinitePlace E ↦ Φ w x :=
      exists_mixedEquiv.imp fun _ ↦ And.right
    let β : Module.Basis ι ℝ (InfinitePlace E → ℂ) := (mixedEmbedding.latticeBasis E).map e
    have hβ (i : ι) (w : InfinitePlace E) : β i w = Φ w (v i) := by simp [β, v, ι, he]
    exact ⟨β.repr z, fun w ↦ by simpa [hβ] using (congrFun (β.sum_repr z) w).symm⟩
  have h_pair (b : E) :
      ∑ w : InfinitePlace E, 2 * (Φ w b * z w).re = ∑ i : ι, c i * trace ℚ E (b * v i) := by
    simp only [hz, trace_eq_sum_Φ, mul_sum, Complex.re_sum, map_mul, mul_left_comm (Φ _ b),
      Complex.re_ofReal_mul, mul_left_comm (2 : ℝ)]
    exact sum_comm
  have h_rat (j : ι) : ∃ q : ℚ, c j = q := by
    have h_coord : ∑ i : ι, c i * trace ℚ E (v.traceDual j * v i) = c j := by simp [apply_ite]
    simpa only [h_pair, h_coord] using h_trace (v.traceDual j)
  choose q hq using h_rat
  exact ⟨∑ i : ι, q i * v i, funext fun w ↦ by simp [hz, hq]⟩

/-- For `E` totally complex, an adele `x` with `ψ (a x) = 1` for all `a` in `E` lies in the diagonal
image `ratAdeles E` of `E`. Here `ψ = stdAddChar E` is the standard additive character. -/
lemma mem_ratAdeles_of_stdAddChar_eq_one {x : 𝔸 E}
    (hx : ∀ a : E, stdAddChar E (toAdele a * x) = 1) :
    x ∈ ratAdeles E := by
  let T (b : E) : ℝ := ∑ w : InfinitePlace E, 2 * (Φ w b * x.1 w).re
  have h_prod (b : E) : Real.fourierChar (-T b) * ψf E (b * x.2) = 1 := by
    simpa [T, stdAddChar_eq_mul_ψf] using hx b
  -- The values of `ψf` are `exp (2πi q)` with `q` rational, so the traces of the infinite part of
  -- `x` against `E` are rational; this makes the infinite part that of some `a` in `E`.
  have h_rat (b : E) : ∃ q : ℚ, T b = q := by
    obtain ⟨q, hq⟩ : ∃ q : ℚ, ψf E (b * x.2) = Real.fourierChar q := exists_ψf_eq_fourierChar _
    obtain ⟨n, hn⟩ : ∃ n : ℤ, -T b + q = n :=
      fourierChar_eq_one_iff.1 (by rw [map_add_eq_mul, ← hq, h_prod])
    exact ⟨q - n, by simp [← hn]⟩
  obtain ⟨a, h_inf⟩ : ∃ a : E, x.1 = fun w ↦ Φ w a := exists_eq_Φ_of_forall_sum_re_rat h_rat
  -- The finite parts need only have the same pairing with every `b` in `E`, which is dense.
  have h_fin (b : E) : ψf E (b * a) = ψf E (b * x.2) := by
    have h_trace : T b = trace ℚ E (b * a) := by simp only [T, h_inf, trace_eq_sum_Φ, map_mul]
    calc ψf E (b * a) = Real.fourierChar (T b) := by rw [← map_mul, ψf_coe, h_trace]
      _ = ψf E (b * x.2) := by rw [← inv_mul_eq_one, ← map_neg_eq_inv, h_prod]
  exact ⟨a, Prod.ext h_inf.symm (eq_of_forall_ψf_mul_eq (denseRange_algebraMap_finAdele.eq h_fin))⟩

/-- For `E` totally complex, the pairing `ψ (u x)` on the adeles given by the standard character
`ψ = stdAddChar E` is nondegenerate: if `ψ (u x) = 1` for all adeles `u`, then `x = 0`. -/
lemma eq_zero_of_forall_stdAddChar_eq_one {x : 𝔸 E} (hx : ∀ u : 𝔸 E, stdAddChar E (u * x) = 1) :
    x = 0 := by
  -- `x` is rational, and testing against the finite adeles shows that its finite part is zero
  obtain ⟨a, rfl⟩ : ∃ a : E, toAdele a = x := mem_ratAdeles_of_stdAddChar_eq_one fun b ↦
    hx (toAdele b)
  have h_fin : (a : 𝔸f E) = 0 := eq_of_forall_ψf_mul_eq fun t ↦ by
    simpa [stdAddChar_eq_mul_ψf] using hx (0, t)
  simpa using h_fin

end New

/-! ## A totally complex field is its own annihilator in its adeles, also for matrices -/

section AdeleSelfDual

open NumberField Matrix Circle

namespace New

variable {E m n : Type*} [Field E] [NumberField E]

/-- For a CM field `E`, the character `ψf E` (the finite part of the standard additive character)
takes the same value at a finite adele `x` and at its self-adjoint part `(x + star x) / 2`. -/
lemma ψf_inv_two_mul_add_star [IsCMField E] (x : 𝔸f E) :
    ψf E ((2⁻¹ : E) * (x + star x)) = ψf E x := by
  have h_star : ψf E ((2⁻¹ : E) * star x) = ψf E ((2⁻¹ : E) * x) := by
    simpa using ψf_star (((2⁻¹ : E) : 𝔸f E) * x)
  have h_add : ((2⁻¹ : E) : 𝔸f E) * x + (2⁻¹ : E) * x = x := by norm_num [← add_mul, ← map_add]
  rw [mul_add, AddChar.map_add_eq_mul, h_star, ← AddChar.map_add_eq_mul, h_add]

/-- For a field `E` with a CM type, the standard additive character `stdAddChar E` takes the same
value at an adele `x` and at its self-adjoint part `(x + star x) / 2`, where `star` is complex
conjugation and `toAdele` the diagonal embedding of `E`. -/
lemma stdAddChar_inv_two_mul_add_star {E : Type*} [Field E] [CMType E] (x : 𝔸 E) :
    stdAddChar E (toAdele 2⁻¹ * (x + star x)) = stdAddChar E x := by
  simp [stdAddChar_eq_mul_ψf, ψf_inv_two_mul_add_star, ← two_mul, map_ofNat]

variable [IsTotallyComplex E] [PlaceEmbedding E] [Fintype m] [Fintype n]

/-- A totally complex field `E` is its own annihilator in its adeles (Tate). Let
`ψ = stdAddChar E`. The characters `x ↦ ψ (a x)`, `a : E`, form a dual family (`IsDualFamily`): they
are continuous, unitary and trivial on the image `ratAdeles E` of `E`; they depend additively and
injectively on `a`; and an adele killed by all of them lies in `ratAdeles E`. -/
instance isDualFamily_ratAdeles :
    IsDualFamily (ratAdeles E) (fun (a : E) (x : 𝔸 E) ↦ stdAddChar E (toAdele a * x)) where
  periodic a := ⟨.subtype_val (by fun_prop),
    by simp [ratAdeles, mul_add, AddChar.map_add_eq_mul, ← map_mul]⟩
  add_left := by simp [add_mul, AddChar.map_add_eq_mul]
  add_right := by simp [mul_add, AddChar.map_add_eq_mul]
  norm_eq_one := by simp [norm_coe]
  -- the annihilator of `E` lies in `E`, and the pairing is nondegenerate
  mem_of_forall_eq_one x hx := mem_ratAdeles_of_stdAddChar_eq_one fun a ↦ coe_eq_one.1 (hx a)
  eq_zero_of_forall_eq_one a ha := (map_eq_zero toAdele).1 <|
    eq_zero_of_forall_stdAddChar_eq_one fun u ↦ by simpa [mul_comm u, coe_eq_one] using ha u

open scoped Classical in
/-- Self-duality for matrices. Let `ψ = stdAddChar E` be the standard character of the adeles. For
an `n × m` matrix `a` over `E`, consider the character `x ↦ ψ (tr (a x))` of the `m × n` adelic
matrices. These characters form a dual family (continuous unitary characters depending additively
and injectively on `a`) for the image `ratMatrices E m n` of the `m × n` matrices over `E`: they are
trivial on it, and their common kernel lies in it. -/
instance isDualFamily_ratMatrices :
    IsDualFamily (ratMatrices E m n) (fun (a : Matrix n m E) (x : Matrix m n (𝔸 E)) ↦
      stdAddChar E (trace (a.map toAdele * x))) where
  periodic a := by
    refine ⟨(continuous_stdAddChar.comp (by fun_prop)).subtype_val, ?_⟩
    -- for a rational matrix `γ` the trace of `a γ` lies in `E`, where `ψ` is trivial
    simp [mul_apply, ratMatrices, trace, mul_add, Finset.sum_add_distrib, AddChar.map_add_eq_mul,
      ← map_mul, ← map_sum]
  add_left := by simp [mul_apply, trace, add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul]
  add_right := by simp [mul_apply, trace, mul_add, Finset.sum_add_distrib, AddChar.map_add_eq_mul]
  norm_eq_one := by simp [norm_coe]
  -- Both claims reduce to one entry: the trace pairing with a matrix supported at `(j, i)`
  -- picks out the entry `(i, j)`.
  mem_of_forall_eq_one x hx := mem_ratMatrices.2 fun i j ↦
    mem_ratAdeles_of_stdAddChar_eq_one fun a ↦ by
    simpa [mul_apply, trace, single_apply, ite_and, coe_eq_one] using hx (.single j i a)
  eq_zero_of_forall_eq_one a ha := Matrix.ext fun i j ↦
    isDualFamily_ratAdeles.eq_zero_of_forall_eq_one (a i j) fun x ↦ by
      simpa [mul_apply, trace, single_apply, ite_and] using ha (.single j i x)

end New

end AdeleSelfDual

/-!
## Strong approximation for adeles and density of E at infinity

* `New.Exchange.idemAdele`: the idempotent adele that is `1` at the finite places in `S` and `0`
  elsewhere.
-/

namespace New

open Set QuotientAddGroup Rat MeasureTheory IsDualFamily

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] [PlaceEmbedding E]

/-- A number field has infinitely many finite places, since they surject onto the primes. -/
instance : Infinite (FinPlace E) :=
  .of_surjective _
    (HeightOneSpectrum.primesEquiv.surjective.comp (FinPlace.comap_surjective (castHom E)))

/-- The idempotent adele with component `1` at the finite places in `S`, and `0` at the other finite
places and at all infinite places. -/
noncomputable abbrev Exchange.idemAdele (S : Set (FinPlace E)) :
    (NumberField.InfinitePlace E → ℂ) × 𝔸f E := ((0, idem S) : 𝔸 E)

/-- If `S` is a nonempty set of finite places and the character `y ↦ ψ (r y)`, with `r : E` and `ψ`
the standard character, is trivial on all adeles `idemAdele S * u` supported on `S`, then
`r = 0`. -/
lemma eq_zero_of_forall_stdAddChar_mul_idemAdele {S : Set (FinPlace E)} (hS : S.Nonempty) {r : E}
    (hr : ∀ u : 𝔸 E, stdAddChar E (toAdele r * (Exchange.idemAdele S * u)) = 1) : r = 0 := by
  have h_zero : (toAdele r * Exchange.idemAdele S : 𝔸 E) = 0 :=
    eq_zero_of_forall_stdAddChar_eq_one fun u ↦ by rw [mul_comm u, mul_assoc, hr u]
  -- look at the component at a place `w ∈ S`, where the idempotent is `1`
  obtain ⟨w, hw⟩ := hS
  simpa [hw] using congrArg (fun y : 𝔸 E ↦ Valued.v (y.2 w)) h_zero

/-- Strong approximation for a totally complex field `E`. Let `S` be a nonempty set of finite
places. The sums `toAdele r + Exchange.idemAdele S * u`, with `r : E` and `u` an adele, are dense
in the adeles. These are the sums of an element of `E` and an adele that vanishes at infinity and
at the finite places outside `S`. -/
lemma strong_approximation {S : Set (FinPlace E)} (hS : S.Nonempty) :
    DenseRange fun p : E × 𝔸 E ↦ toAdele p.1 + Exchange.idemAdele S * p.2 := by
  -- The sums are the range of the additive map `σ`; let `B` be the closure of this subgroup. If
  -- `x ∉ B`, a continuous `f` on the quotient by `B` separates `x` from `0`. Subtract its mean:
  -- Fourier theory on the adeles modulo `E` shows that the result vanishes.
  let σ : E × 𝔸 E →+ 𝔸 E :=
    (toAdele (E := E)).toAddMonoidHom.coprod (AddMonoidHom.mulLeft (Exchange.idemAdele S))
  let B : AddSubgroup (𝔸 E) := σ.range.topologicalClosure
  have hB_closed : IsClosed (B : Set (𝔸 E)) := AddSubgroup.isClosed_topologicalClosure σ.range
  refine fun x ↦ by_contra fun hx : x ∉ B ↦ ?_
  obtain ⟨f, hf_cont, hf_ne⟩ : ∃ f : 𝔸 E ⧸ B → ℝ, Continuous f ∧ f x ≠ f 0 :=
    separatesPoints_continuous_of_t35Space (mt (eq_zero_iff x).1 hx)
  have h_per (r : E) (u y : 𝔸 E) : f (y + (toAdele r + Exchange.idemAdele S * u) : 𝔸 E) = f y :=
    congrArg f (mk_add_of_mem y (subset_closure ⟨(r, u), rfl⟩))
  let mean : ℂ := ⨍ q : 𝔸 E ⧸ ratAdeles E, (f q.out : ℂ) ∂.addHaarMeasure ⊤
  have h_isPer : IsContPeriodic (ratAdeles E) fun y : 𝔸 E ↦ f y - mean :=
    ⟨by fun_prop, by simpa [ratAdeles, add_comm] using fun r : E ↦ h_per r 0⟩
  have h_const : ∀ y : 𝔸 E, f y - mean = 0 := by
    -- It is enough that the Fourier coefficient vanishes at every `r` whose character is compatible
    -- with the translation symmetries of `f - mean` in the sense of `hr`.
    refine isDualFamily_ratAdeles.eq_zero_of_quotMean_mul_eq_zero h_isPer fun r
      (hr : ∀ (a : 𝔸 E) (c : ℂ), (∀ y : 𝔸 E, c * (f ↑(y + a) - mean) = f y - mean) →
        stdAddChar E (toAdele r * a) = c) ↦ ?_
    -- Such a character is `1` on the periods `idemAdele S * u`, so it is trivial.
    obtain rfl : r = 0 := eq_zero_of_forall_stdAddChar_mul_idemAdele hS fun u ↦
      Circle.ext (hr (Exchange.idemAdele S * u) 1 (by simpa using h_per 0 u))
    -- The coefficient at the trivial character is the mean of `f - mean`, which is zero.
    simp [mean, quotMean, integral_sub_average]
  exact hf_ne (Complex.ofReal_injective (sub_left_inj.1 ((h_const x).trans (h_const 0).symm)))

/-- The image of a totally complex field `E` under the embeddings `Φ w` chosen by
`PlaceEmbedding E`, one for each infinite place `w`, is dense in the product of copies of `ℂ`. -/
lemma denseRange_Φ : DenseRange (RingHom.pi Φ : E →+* NumberField.InfinitePlace E → ℂ) := by
  -- Apply strong approximation, with `S` the set of all finite places, to `(x, 0)` and pass to
  -- first components, where `Exchange.idemAdele S * u` contributes nothing.
  intro x
  have h_approx : ((x, 0) : 𝔸 E) ∈
      closure (range fun p : E × 𝔸 E ↦ toAdele p.1 + Exchange.idemAdele univ * p.2) :=
    strong_approximation univ_nonempty _
  have h_fst (r : E) (u : 𝔸 E) :
      (toAdele r + Exchange.idemAdele univ * u : 𝔸 E).1 = RingHom.pi Φ r :=
    funext fun w ↦ by simp
  refine map_mem_closure continuous_fst h_approx ?_
  rintro _ ⟨⟨r, u⟩, rfl⟩
  exact ⟨r, (h_fst r u).symm⟩

end New

/-! ## Strong approximation for adelic matrices -/

/-- Strong approximation for matrices over a field `E` with a CM type. Let `S` be a nonempty set of
finite places and `x` an invertible `n × n` adelic matrix. The matrices `x⁻¹ A + idemAdele S • B`,
with `A` over `E` and `B` adelic, are dense in the `n × m` adelic matrices. Here `idemAdele S` is
the adele that is `1` at the places in `S` and `0` at all other places. -/
lemma New.Exchange.denseRange_rat_matrix_add {E m n : Type*} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] {S : Set (FinPlace E)} (hS : S.Nonempty) (x : GL n (𝔸 E)) :
    DenseRange fun p : Matrix n m E × Matrix n m (𝔸 E) ↦
      x⁻¹.val * p.1.map toAdele + idemAdele (E := E) S • p.2 := by
  intro Y
  -- Strong approximation entry by entry: `x * Y` is a limit of matrices `A + idemAdele S • B`.
  have h_approx : x.val * Y ∈ closure (Set.range fun p : n → m → E × 𝔸 E ↦
      (Matrix.of fun i j ↦ (p i j).1).map toAdele + idemAdele S • Matrix.of fun i j ↦ (p i j).2) :=
    DenseRange.piMap (fun _ ↦ .piMap fun _ ↦ strong_approximation hS) _
  -- Multiply by `x⁻¹`, using `x⁻¹ * (A + idemAdele S • B) = x⁻¹ * A + idemAdele S • (x⁻¹ * B)`.
  rw [← Matrix.one_mul Y, ← x.inv_mul, Matrix.mul_assoc]
  refine map_mem_closure (f := fun Z ↦ x⁻¹.val * Z) (by fun_prop) h_approx ?_
  rintro _ ⟨p, rfl⟩
  refine ⟨(.of fun i j ↦ (p i j).1, x⁻¹.val * .of fun i j ↦ (p i j).2), ?_⟩
  simp only [Matrix.mul_add, Matrix.mul_smul]
  rfl

/-!
## One-sided Poisson summation on the adeles

The main result is `New.IsDualFamily.sum_le_of_fourier`: a finite sum of a non-negative integrable
function over rational points is at most any bound for the finite sums of the absolute values of its
Fourier transform over `E`. Only lower semicontinuity at these points is needed. The proof smooths
the function by a bump on the compact quotient of the adeles by `E` (`New.ratAdeles`) and applies
Fourier inversion there, with the standard character `New.stdAddChar`.
-/

section OneSidedPoisson

open MeasureTheory Measure Complex QuotientAddGroup NumberField Finset Circle

namespace New

/-- Smooth an integrable function `F` on the adeles by a continuous function `η` on `𝔸 E ⧸ E` with
`|η| ≤ 1`. The Fourier coefficient at `ξ : E` of `z ↦ ∫ η(z + x) F(x) dx` (a mean `quotMean` over
`𝔸 E ⧸ E`: the integral, for the Haar probability measure `addHaarMeasure ⊤`, of the value at a lift
`q.out` of each class `q`) is the coefficient of `η` times the Fourier transform
`∫ ψ(-ξ x) F(x) dx`. Here `ψ = stdAddChar E` is the standard character and `ratAdeles E` the image
of `E` in the adeles. -/
lemma IsDualFamily.quotMean_stdAddChar_mul_integral {E : Type*} [Field E] [NumberField E]
    [IsTotallyComplex E] [PlaceEmbedding E] {F : 𝔸 E → ℝ} (hF : Integrable F)
    {η : C(𝔸 E ⧸ ratAdeles E, ℝ)} (hη_le : ∀ q : 𝔸 E ⧸ ratAdeles E, ‖η q‖ ≤ 1) (ξ : E) :
    (quotMean (ratAdeles E) fun z : 𝔸 E ↦
        stdAddChar E (toAdele ξ * z) * ∫ x : 𝔸 E, (η ↑(z + x) * F x : ℂ)) =
      (quotMean (ratAdeles E) fun z : 𝔸 E ↦ stdAddChar E (toAdele ξ * z) * ofReal (η z)) *
        ∫ x : 𝔸 E, stdAddChar E (toAdele ξ * -x) * ofReal (F x) := by
  let ψ (z : 𝔸 E) : ℂ := stdAddChar E (toAdele ξ * z)
  have h_shift (x : 𝔸 E) : (quotMean (ratAdeles E) fun z ↦ ψ z * η ↑(z + x)) =
      (quotMean (ratAdeles E) fun z ↦ ψ z * η z) * ψ (-x) := by
    have h_per : IsContPeriodic (ratAdeles E) fun y : 𝔸 E ↦ ofReal (η ↑(y + x)) :=
      ⟨by fun_prop, by simp +contextual [← eq_zero_iff]⟩
    simpa [ψ, mul_comm] using (mul_quotMean_translate h_per ξ (-x)).symm
  -- `F` is integrable and the other factors are measurable and bounded by one
  have h_int : Integrable (fun p : (𝔸 E ⧸ ratAdeles E) × 𝔸 E ↦ ψ p.1.out * η (p.1 + p.2) * F p.2)
      ((addHaarMeasure ⊤).prod volume) :=
    (hF.comp_snd _).ofReal.bdd_mul (c := 1)
      ((isDualFamily_ratAdeles.periodic ξ).integrable_out.aestronglyMeasurable.comp_fst.mul
        (by fun_prop)) (.of_forall fun p ↦ by simpa [ψ, norm_coe] using hη_le _)
  -- exchange the mean over `z` and the integral over `x`, then apply `h_shift`
  simp only [ψ, quotMean, mk_add, out_eq'] at h_shift ⊢
  simp only [← integral_const_mul, ← mul_assoc]
  rw [integral_integral_swap h_int]
  simp only [integral_mul_const, h_shift]

/-- Upper bound for `∫ η F` by Fourier inversion on `𝔸 E ⧸ E`. Let `F` be integrable on the adeles
and `η` continuous on `𝔸 E ⧸ E` with values in `[0, 1]`. If `S` bounds the finite sums over `ξ : E`
of the absolute values of the Fourier transform `∫ ψ(-ξ x) F(x) dx`, then `∫ η F ≤ (∫ η) S`. Here
`ψ = stdAddChar E` is the standard character, `ratAdeles E` is the image of `E` under the diagonal
embedding `toAdele`, and `addHaarMeasure ⊤` is the Haar probability measure on the quotient. -/
lemma IsDualFamily.integral_mul_le_of_sum_norm_le {E : Type*} [Field E] [NumberField E]
    [IsTotallyComplex E] [PlaceEmbedding E] {S : ℝ} {F : 𝔸 E → ℝ} (hF : Integrable F)
    (hS : ∀ Y : Finset E, ∑ ξ ∈ Y, ‖∫ x : 𝔸 E, stdAddChar E (toAdele ξ * -x) * ofReal (F x)‖ ≤ S)
    {η : C(𝔸 E ⧸ ratAdeles E, ℝ)} (hη_nonneg : ∀ q : 𝔸 E ⧸ ratAdeles E, 0 ≤ η q)
    (hη_le : ∀ q : 𝔸 E ⧸ ratAdeles E, ‖η q‖ ≤ 1) :
    ∫ x : 𝔸 E, η x * F x ≤ (∫ q : 𝔸 E ⧸ ratAdeles E, η q ∂addHaarMeasure ⊤) * S := by
  set J : ℝ := ∫ q : 𝔸 E ⧸ ratAdeles E, η q ∂addHaarMeasure ⊤ with hJ
  have hJ_nonneg : 0 ≤ J := integral_nonneg hη_nonneg
  -- `G` is `F` smoothed by `η`: a continuous periodic function with `G 0 = ∫ η F`.
  let G (z : 𝔸 E) : ℂ := ∫ x : 𝔸 E, η ↑(z + x) * F x
  have hG_per : IsContPeriodic (ratAdeles E) G := by
    refine ⟨continuous_of_dominated (by fun_prop) (fun z ↦ .of_forall fun x ↦ ?_) hF.norm
      (.of_forall (by fun_prop)), by simp +contextual [G, ← eq_zero_iff]⟩
    grw [norm_mul, norm_real, hη_le, one_mul, norm_real]
  let coeff (ξ : E) (f : 𝔸 E → ℂ) : ℂ :=
    quotMean (ratAdeles E) fun z : 𝔸 E ↦ stdAddChar E (toAdele ξ * z) * f z
  have coeff_G (ξ : E) : coeff ξ G =
      coeff ξ (fun z ↦ η z) * ∫ x : 𝔸 E, stdAddChar E (toAdele ξ * -x) * ofReal (F x) :=
    quotMean_stdAddChar_mul_integral hF hη_le ξ
  have coeff_η (ξ : E) : ‖coeff ξ fun z ↦ η z‖ ≤ J :=
    (norm_integral_le_integral_norm _).trans (by simp [hJ, norm_coe, abs_of_nonneg, hη_nonneg])
  have h_sum_le (Y : Finset E) : ∑ ξ ∈ Y, ‖coeff ξ G‖ ≤ J * S := by
    simp only [coeff_G, norm_mul]
    grw [coeff_η, ← mul_sum, hS]
  -- Fourier inversion at `0`: the real part of every partial sum of the series is at most `J * S`.
  have h_inv : HasSum (fun ξ : E ↦ coeff ξ G) (G 0) := by
    simpa using isDualFamily_ratAdeles.fourier_inversion hG_per
      (summable_of_sum_le (fun _ ↦ norm_nonneg _) h_sum_le).of_norm (fun _ ↦ rfl) 0
  have h_re_le : (G 0).re ≤ J * S := le_of_tendsto' (hasSum_re h_inv) fun Y ↦
    (sum_le_sum fun ξ _ ↦ re_le_norm (coeff ξ G)).trans (h_sum_le Y)
  simpa [G, ← ofReal_mul, integral_complex_ofReal] using h_re_le

/-- Lower bound for `∫ η F` by folding the integral over `E`. Let `F ≥ 0` be integrable on `𝔸 E`
(for its `volume` measure, which is also used for `∫ x, η x * F x`), let `T` be a finite subset of
the image `ratAdeles E` of `E`, and let `η` be continuous on `𝔸 E ⧸ E` with values in `[0, 1]` and
positive integral; `η x` for `x : 𝔸 E` means `η` evaluated at the class of `x`. If every class at
which `η` is not zero contains a point `u` with `c ≤ ∑ t ∈ T, F (t + u)`, then `(∫ η) * c ≤ ∫ η F`,
where `∫ η` is taken for the Haar probability measure `addHaarMeasure ⊤` on the quotient. -/
lemma IsDualFamily.mul_le_integral_mul_of_le_sum {E : Type*} [Field E] [NumberField E]
    [IsTotallyComplex E] [PlaceEmbedding E] {c : ℝ} {F : 𝔸 E → ℝ} (hF : Integrable F)
    (hF_nonneg : 0 ≤ F) {T : Finset (ratAdeles E)} {η : C(𝔸 E ⧸ ratAdeles E, ℝ)}
    (hη_nonneg : ∀ q : 𝔸 E ⧸ ratAdeles E, 0 ≤ η q) (hη_le : ∀ q : 𝔸 E ⧸ ratAdeles E, ‖η q‖ ≤ 1)
    (hη_pos : 0 < ∫ q : 𝔸 E ⧸ ratAdeles E, η q ∂addHaarMeasure ⊤)
    (hη_supp : ∀ x : 𝔸 E, η x ≠ 0 → ∃ u : 𝔸 E, x - u ∈ ratAdeles E ∧ c ≤ ∑ t ∈ T, F (t + u)) :
    (∫ q : 𝔸 E ⧸ ratAdeles E, η q ∂addHaarMeasure ⊤) * c ≤ ∫ x : 𝔸 E, η x * F x := by
  -- `μ` computes integrals over `𝔸 E ⧸ E` and has total mass one.
  set μ : Measure (𝔸 E) := (ratAdeles E).quotMeasure
  have hJ_eq : ∫ q : 𝔸 E ⧸ ratAdeles E, η q ∂addHaarMeasure ⊤ = ∫ x : 𝔸 E, η x ∂μ := by
    simpa [μ, quotMean, integral_complex_ofReal, average_eq_integral] using
      (average_quotMeasure_eq_quotMean (ratAdeles E) volume (F := fun y ↦ ofReal (η y))
        ⟨by fun_prop, by simp +contextual [← eq_zero_iff]⟩).symm
  have hη_int : Integrable (fun x : 𝔸 E ↦ η x) μ := .of_integral_ne_zero (hη_pos.trans_eq hJ_eq).ne'
  have hη_add (g : ratAdeles E) (x : 𝔸 E) : η (g + x : 𝔸 E) = η x := by simp [(eq_zero_iff _).2]
  obtain ⟨h_int, h_fold⟩ :
      Integrable (fun p : 𝔸 E × ratAdeles E ↦ η p.1 * F (p.2 + p.1)) (μ.prod count) ∧
        ∫ x : 𝔸 E, ∫ g : ratAdeles E, η x * F (g + x) ∂count ∂μ = ∫ x : 𝔸 E, η x * F x := by
    simpa only [Function.comp_def, AddSubgroup.vadd_def, vadd_eq_add, hη_add] using
      (measurePreserving_addOrbitMeasure (H := ratAdeles E) (ν := count)).fubini
        (hF.bdd_mul (by fun_prop) (.of_forall fun x ↦ hη_le x))
  -- The inner sum over `E` is at least `η x * c`.
  have h_inner (x : 𝔸 E) (hx : Integrable (fun g : ratAdeles E ↦ η x * F (g + x)) count) :
      η x * c ≤ ∫ g : ratAdeles E, η x * F (g + x) ∂count := by
    obtain h_zero | h_pos : η x = 0 ∨ 0 < η x := (hη_nonneg x).eq_or_lt'
    · simp [h_zero]
    -- Keep the terms `g` with `g + x = t + u` for `t ∈ T`.
    obtain ⟨u, hux, hu⟩ := hη_supp x h_pos.ne'
    calc η x * c ≤ η x * ∑ t ∈ T, F (t + u) := by gcongr
      _ = ∑ g ∈ T.map (addRightEmbedding (-⟨x - u, hux⟩)), η x * F (g + x) := by
        simp [add_assoc, mul_sum]
      _ ≤ ∫ g : ratAdeles E, η x * F (g + x) ∂count :=
        sum_le_hasSum _ (fun g _ ↦ mul_nonneg h_pos.le (hF_nonneg (g + x)))
          (by simpa [count] using hasSum_integral_measure (μ := dirac) hx)
  rw [hJ_eq, ← integral_mul_const, ← h_fold]
  exact integral_mono_ae (hη_int.mul_const c) h_int.integral_prod_left
    (h_int.prod_right_ae.mono h_inner)

/-- One-sided Poisson summation on the adeles `𝔸 E` of a totally complex number field `E`, with the
diagonal embedding `toAdele` given by the chosen complex embeddings of `PlaceEmbedding`. Let `F ≥ 0`
be integrable and lower semicontinuous at each point of a finite set `T` of rational points
(elements of the image `ratAdeles E` of `E`). Put `F̂(ξ) = ∫ ψ(-toAdele ξ · x) F(x) dx`, where
`ψ = stdAddChar E` and `dx` is the measure `volume` on `𝔸 E`, for which `E` has covolume one (its
`quotMeasure` for `𝔸 E ⧸ E` has mass one); if `S` bounds `∑ ξ ∈ Y, ‖F̂(ξ)‖` for every finite set
`Y ⊂ E`, then `∑ t ∈ T, F t ≤ S`. -/
lemma IsDualFamily.sum_le_of_fourier {E : Type*} [Field E] [NumberField E] [IsTotallyComplex E]
    [PlaceEmbedding E] {S : ℝ} {F : 𝔸 E → ℝ} (hF : Integrable F) (hF_nonneg : 0 ≤ F)
    (T : Finset (ratAdeles E)) (hT : ∀ t ∈ T, LowerSemicontinuousAt F t)
    (hS : ∀ Y : Finset E, ∑ ξ ∈ Y, ‖∫ x : 𝔸 E, stdAddChar E (toAdele ξ * -x) * ofReal (F x)‖ ≤ S) :
    ∑ t ∈ T, F t ≤ S := by
  -- Let `m < ∑ t ∈ T, F t`. Smooth `F` by a bump `η` on `𝔸 E ⧸ E` supported where the sum of the
  -- translates still exceeds `m`. With `J = ∫ η`, the value `∫ η F` is at least `J m` (fold over
  -- `E`) and at most `J S` (Fourier inversion on the compact quotient).
  refine le_of_forall_lt_imp_le_of_dense fun m hm ↦ ?_
  let W : Set (𝔸 E) := {x : 𝔸 E | ∀ᶠ y : 𝔸 E in nhds x, m < ∑ t ∈ T, F (t + y)}
  have h_lsc : LowerSemicontinuousAt (fun y : 𝔸 E ↦ ∑ t ∈ T, F (t + y)) 0 :=
    lowerSemicontinuousAt_sum fun t ht ↦ .comp (by simpa using hT t ht) (by fun_prop)
  obtain ⟨η, hη_one, hη_compact, hη_supp, hη_mem⟩ : ∃ η : C(𝔸 E ⧸ ratAdeles E, ℝ),
      Set.EqOn η 1 {0} ∧ IsCompact (tsupport η) ∧ tsupport η ⊆ QuotientAddGroup.mk '' W ∧
        ∀ q : 𝔸 E ⧸ ratAdeles E, η q ∈ Set.Icc 0 1 :=
    exists_continuousMap_one_of_isCompact_subset_isOpen isCompact_singleton
      (isOpenMap_coe W isOpen_setOfPred_eventually_nhds)
      (Set.singleton_subset_iff.2 ⟨0, h_lsc m (by simpa using hm), mk_zero _⟩)
  have hη_nonneg (q : 𝔸 E ⧸ ratAdeles E) : 0 ≤ η q := (hη_mem q).1
  have hη_le (q : 𝔸 E ⧸ ratAdeles E) : ‖η q‖ ≤ 1 := by
    simpa [abs_of_nonneg, hη_nonneg] using (hη_mem q).2
  have hη_sum (x : 𝔸 E) (hx : η x ≠ 0) :
      ∃ u : 𝔸 E, x - u ∈ ratAdeles E ∧ m ≤ ∑ t ∈ T, F (t + u) := by
    obtain ⟨u, hu, hux⟩ : ∃ u ∈ W, (u : 𝔸 E ⧸ ratAdeles E) = x := hη_supp (subset_closure hx)
    exact ⟨u, eq_iff_sub_mem.1 hux.symm, hu.self_of_nhds.le⟩
  set J : ℝ := ∫ q : 𝔸 E ⧸ ratAdeles E, η q ∂addHaarMeasure ⊤
  have hJ_pos : 0 < J := η.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    hη_compact hη_nonneg (by simp [hη_one rfl])
  refine le_of_mul_le_mul_left ?_ hJ_pos
  calc J * m ≤ ∫ x : 𝔸 E, η x * F x :=
      mul_le_integral_mul_of_le_sum hF hF_nonneg hη_nonneg hη_le hJ_pos hη_sum
    _ ≤ J * S := integral_mul_le_of_sum_norm_le hF hS hη_nonneg hη_le

end New
end OneSidedPoisson

/-!
## The inverse different in self-adjoint adeles is compact and open

`New.selfAdjointCodifferent E M` is the group of self-adjoint finite adeles `z` (those with
`z̄ = z`) for which `M z` lies in the inverse different. For `M = 1` it normalises the Haar measure
on the self-adjoint finite adeles.
-/

section Codifferent

open NumberField AddSubgroup AddChar MeasureTheory Measure New Ideal

variable (E : Type*) [Field E] [NumberField E] [IsCMField E]

/-- The additive group of self-adjoint (conjugation-invariant) finite adeles `z` of `E` with
`ψf E (M * z * x) = 1` for all integral finite adeles `x ∈ Ô E`, that is, with `M * z` in the
inverse different. Here `ψf E` is the finite part of the standard additive character. -/
def New.selfAdjointCodifferent (M : 𝔸f E) : AddSubgroup (selfAdjoint (𝔸f E)) where
  carrier := {z : selfAdjoint (𝔸f E) | ∀ x ∈ Ô E, ψf E (M * z * x) = 1}
  add_mem' := by simp +contextual [mul_add, add_mul, map_add_eq_mul]
  zero_mem' := by simp
  neg_mem' := by simp +contextual [map_neg_eq_inv]

/-- For a CM field `E` and a finite adele `M`, the group `selfAdjointCodifferent E M` of
self-adjoint finite adeles `z` with `M * z` in the inverse different is open in the self-adjoint
finite adeles. -/
lemma New.isOpen_selfAdjointCodifferent (M : 𝔸f E) : (selfAdjointCodifferent E M).IsOpen := by
  -- the subgroup contains an open neighbourhood `U` of `0`
  let U : Set (selfAdjoint (𝔸f E)) := {z : selfAdjoint (𝔸f E) | M * z ∈ Ô E}
  have hU_open : IsOpen U := isOpen_Ô.preimage (by fun_prop)
  have hU_zero : 0 ∈ U := by simp [U]
  have hU_sub : U ⊆ selfAdjointCodifferent E M := fun z hz x hx ↦ ψf_eq_one_of_mem (mul_mem hz hx)
  exact isOpen_of_zero_mem_interior _ (mem_interior.2 ⟨U, hU_sub, hU_open, hU_zero⟩)

/-- For a CM field `E` and an invertible finite adele `M`, the group `selfAdjointCodifferent E M` of
self-adjoint finite adeles `z` with `M * z` in the inverse different is compact. -/
lemma New.isCompact_selfAdjointCodifferent {M : 𝔸f E} (hM : IsUnit M) :
    IsCompact (selfAdjointCodifferent E M : Set (selfAdjoint (𝔸f E))) := by
  -- The subgroup is open, hence closed, and lies in the compact set of `z` with `d M z ∈ Ô E`,
  -- where `d` is the norm of the different, a nonzero natural number that lies in the different.
  let d : ℕ := absNorm (differentIdeal ℤ (𝓞 E))
  have h_unit : IsUnit (d * M) :=
    (isUnit_natCast_finAdele (mt absNorm_eq_zero_iff.1 differentIdeal_ne_bot)).mul hM
  have h_compact : IsCompact {z : selfAdjoint (𝔸f E) | h_unit.unit • (z : 𝔸f E) ∈ Ô E} :=
    (isCompact_Ô.preimage_smul h_unit.unit).preimage_val
  refine h_compact.of_isClosed_subset (isClosed_of_isOpen _ (isOpen_selfAdjointCodifferent E M))
    fun z hz ↦ ?_
  -- By duality (`forall_ψf_mul_eq_one_iff`) every element of the different makes `M z` integral.
  have h_dual (u : 𝔸f E) (hu : u ∈ Ô E) : ψf E (u * (M * z)) = 1 := by rw [mul_comm, hz u hu]
  simpa [d, mul_assoc] using forall_ψf_mul_eq_one_iff.1 h_dual _ (absNorm_mem _)

/-- The Haar measure on the self-adjoint finite adeles that gives `New.selfAdjointCodifferent E 1`
mass one. -/
noncomputable instance : MeasureSpace (selfAdjoint (𝔸f E)) where
  volume := addHaarMeasure ⟨⟨selfAdjointCodifferent E 1,
    isCompact_selfAdjointCodifferent E isUnit_one⟩,
    by simp [(isOpen_selfAdjointCodifferent E 1).interior_eq]⟩

/-- The volume on the self-adjoint finite adeles is an additive Haar measure. -/
instance : IsAddHaarMeasure (volume : Measure (selfAdjoint (𝔸f E))) :=
  isAddHaarMeasure_addHaarMeasure _

/-- The group `selfAdjointCodifferent E 1` of self-adjoint finite adeles in the inverse different
has volume one. -/
@[simp]
lemma New.volume_selfAdjointCodifferent_one :
    volume (selfAdjointCodifferent E 1 : Set (selfAdjoint (𝔸f E))) = 1 :=
  addHaarMeasure_self

end Codifferent
