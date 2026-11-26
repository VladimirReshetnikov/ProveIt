import Lib.Adelic.AutomorphicForms.PAdicGauge
import Lib.CM.ChowlaSelberg
import Lib.Shimura.Uniformisation.HolomorphicFamilies
import Lib.Weil.Construction.FourierInversion
import New.Derivatives.Field.WeilData

/-!
# Scale of theta Taylor series, tight frames, jet series along lines

Let `P` be parameters, `d = P.d` and `K = ℚ(i√d)`. The file fixes the scale at which Taylor series
of theta functions are taken, and it builds theta functions from tight frames. For a space `V` with
all signs `1` and `f` in `New.Space.finitePart`, the function `New.Space.entireTheta f` is entire on
`ℂ^(places × n)`. A tight frame of length `M` is a finite family of vectors `y` of the lattice `𝔞₀`,
counted with multiplicities, such that `∑ y, (y† z) y = M z` for all `z` in `ℂ^places`, where `y`
stands for the vector of its images `τ y` under the CM type and `y† z = ∑ τ, conj (τ y) * z τ`.

## Main definitions and results

* `New.Parameters.areaScale` is `√(2π / √d)`, and `New.Parameters.periodFactor` is `vacuumRoot`
  divided by the unit of `New.CMLattice.chowla_selberg`.
* `New.Parameters.jetScale`: the scale `periodFactor * areaScale / cmPeriod`.
* `New.Parameters.isTightFrame_pow`: the powers of a primitive `q₁`-th root of unity are a tight
  frame of length `q₁`.
* `New.Space.taylor_line_eq_subst_jetSeries`: the Taylor series of `z ↦ entireTheta f (a • z)` on
  the line spanned by a vector `v` is the restriction of `jetSeries V a f`.
* `New.Parameters.IsResolutionProduct`: the theta functions of the rational translates of a vector
  are products of translated entire functions of linear forms; `IsResolutionProduct.theta_translate`
  and `IsResolutionProduct.jetSeries_translate` give their theta values and Taylor series.
* `New.Parameters.exists_isResolutionProduct_of_isTightFrame`: a product of monomial sections,
  pulled back along a tight frame, is the theta function of a vector with integral values.

Notions from other files:
* `New.Parameters`: a multiple `q₀` of `18480 = 16 · 3 · 5 · 7 · 11` and a prime `d` with
  `d ≡ q₀/2 - 1 mod q₀`. The CM field `E = P.E s` is generated over `K` by a primitive `q₁`-th root
  of unity `ζ`, `q₁ = P.q₁ s`, and `Φ τ : E →+* ℂ` is the embedding of its CM type at the infinite
  place `τ`.
* `New.finiteImage`: for a family `γ` in `E`, the finite adeles `α⁻¹ γ k`, with `α = P.α s` the
  idele of the fractional ideal `𝔞₀`; so `finiteImage id y ∈ Ô E` says that `y` lies in
  `𝔞₀ = E ∩ α Ô`.
* `New.PadicPlace`: a `p`-adic place of `ℂ`, that is, a ring homomorphism `ιₚ : ℂ →+* ℂ_[p]`.
* `New.Space.entireTheta`: for `f` in the space `𝒮 V` of a hermitian space `V`, the function
  `y ↦ θ(ϱ(y) f) exp(|y|²/2)` of a real vector `y` in Fock coordinates, with `θ` the theta
  functional `V.θ` and `ϱ` the Heisenberg representation `V.ϱ`.
* `finVec x`: the adelic vector with finite part `α x` and real part zero. So
  `V.ϱ (finVec (finiteImage γ)) f` is the translate of `f` by the finite image of `γ`.
* `New.CMLattice`: a lattice `C.Λ` in `ℂ`, stable under the integers of `K`, with a marked point of
  order two. Its hermitian form is `C.hermitianForm l z = (π / A) * conj l * z`, with `A = C.area`
  the area of a period parallelogram, and `C.twistedTranslate m l g` is the translate
  `z ↦ g (z + l)` times the Gaussian factor of the form `m • C.hermitianForm`. A section of degree
  `m` is multiplied by `C.multiplier l ^ m` under this translation for `l` in `C.Λ`, where
  `C.multiplier l` is a number of absolute value one.
* `pullForm φ B`: the pull-back `(u, v) ↦ B (φ u) (φ v)` of a form along a linear map `φ`.
* `New.Space.jetSeries`: the series whose coefficient of `z ^ k` is `a ^ |k| / k!` times the theta
  functional of `v ⊗ f`, where `v` is the Fock vector of the monomial `z ^ k`.

## Relation to the literature

A product of monomial sections of a CM curve, pulled back along a tight frame at scale `a / δ̄`, for
an integer `δ` of `K` and a point `a` of the lattice of the curve, is the theta function of a vector
of the finite part, by Fourier inversion. The theta value and the jet series of each rational
translate are the products of those of the translated sections. The values of the vector are
products of torsion values of monomials, so they are integral at every `p`-adic place. Eutactic
stars (sets of vectors that form a tight frame), the isogeny formula for theta functions and
integrality via torsion values are known from the literature. Related work: Conway–Sloane,
Low-dimensional lattices V, 1989; Finis, Divisibility of anticyclotomic L-functions and theta
functions with CM, 2006; Mumford, On the equations defining abelian varieties I, 1966.
-/

noncomputable section

/-! ## The CM curve and the constants fixing the scale -/

section PeriodDefs

open Real NeZero

namespace New.Parameters

variable (P : Parameters) (s : ℕ)

/-- The curve `𝓔 = ℂ / Ω₀ 𝓞_K`: a chosen CM lattice that is a complex multiple of `𝓞_K`.
See `latticeModule_cmCurve`. -/
def cmCurve : CMLattice P.d :=
  (QuadField.exists_cmLattice_latticeModule_eq_scaledIdeal (d := P.d) 1).choose

/-- The period of `K`: a nonzero complex number `Ω₀`, fixed once, such that the lattice of `cmCurve`
is `Ω₀ 𝓞_K`. See `latticeModule_cmCurve`. -/
def cmPeriod : ℂˣ :=
  (QuadField.exists_cmLattice_latticeModule_eq_scaledIdeal (d := P.d) 1).choose_spec.choose

variable {P} in
/-- The lattice of the CM curve `cmCurve` is `Ω₀ 𝓞_K`, the multiple by `Ω₀` of the unit ideal of
`K = ℚ(i√d)`. -/
lemma latticeModule_cmCurve :
    P.cmCurve.latticeModule = QuadField.scaledIdeal P.d (P.cmPeriod, 1) :=
  (QuadField.exists_cmLattice_latticeModule_eq_scaledIdeal (d := P.d) 1).choose_spec.choose_spec

/-- The number `u` chosen in the Chowla–Selberg formula `CMLattice.chowla_selberg` for
`cmCurve`. See `norm_iota_chowlaSelbergUnit` and `area_mul_norm_chowlaSelbergUnit_sq`. -/
def chowlaSelbergUnit : ℂ := P.cmCurve.chowla_selberg.choose

lemma norm_iota_chowlaSelbergUnit (p : ℕ) [Fact p.Prime] [PadicPlace p] :
    ‖ιₚ P.chowlaSelbergUnit‖ = 1 :=
  P.cmCurve.chowla_selberg.choose_spec.1 p

/-- The Chowla–Selberg formula for the conjugates of `cmCurve`: for every automorphism `σ` of `ℂ`
over `K`, the area of the lattice conjugate by `σ`, times `‖σ u‖²` for `u = chowlaSelbergUnit`, is
`π exp(c) 2π / √d`, where `c = chowlaSelbergConst d = γ - Re L'/L(1, χ_K)`. -/
lemma area_mul_norm_chowlaSelbergUnit_sq (σ : Gal(ℂ/P.K)) :
    (P.cmCurve.galConjugate σ).area * ‖σ P.chowlaSelbergUnit‖ ^ 2 =
      π * rexp (chowlaSelbergConst P.d) * (2 * π / √P.d) :=
  P.cmCurve.chowla_selberg.choose_spec.2 σ

/-- The number `√(2π / √d)`, as a unit of `ℂ`. -/
def areaScale : ℂˣ := Units.mk0 √(2 * π / √P.d) (by simp [pi_nonneg, ne])

/-- The quotient of `vacuumRoot` by `chowlaSelbergUnit`. Here `vacuumRoot` is `(chiFin α)⁻¹ ^ (1/f)`
with the principal branch of the complex power, `f` is the number of infinite places of `E`, and
`chiFin` is the character `x ↦ υ(x) |x| ^ (-1/2)` of the finite ideles, `υ` the splitting character
of the Weil data. The denominator is a unit at every `p`-adic place of `ℂ`, so the two numbers have
the same absolute value there. -/
def periodFactor : ℂ := P.vacuumRoot s / P.chowlaSelbergUnit

/-- The number `periodFactor * √(2π / √d) / Ω₀`. Taylor series of theta functions are taken at
multiples of this scale. -/
def jetScale : ℂ := P.periodFactor s * P.areaScale / P.cmPeriod

end New.Parameters

end PeriodDefs

/-!
## The lattice `𝔞₀` and the powers of `ζ`

The ideal `𝔞₀ conj 𝔞₀` is the inverse different of `E / K`. In comments `α` is the idele of `𝔞₀`,
and `P'(ζ)` is `relDifferentGen`, the value at `ζ` of the derivative of the `q₁`-th cyclotomic
polynomial, which generates the different.
-/

section TightFrameExists

open Finset ComplexConjugate NumberField

namespace New

/-- Taking each vector of a tight frame `k` times as often multiplies its length by `k`. -/
lemma IsTightFrame.mul_left {E I : Type} [Field E] [CMType E] [WeilData E] [Fintype I] {w : I → E}
    {m : I → ℕ} {M : ℕ} (h_frame : IsTightFrame w m M) (k : ℕ) :
    IsTightFrame w (fun i : I ↦ k * m i) (k * M) := by
  refine ⟨h_frame.finiteImage_mem, fun σ τ ↦ ?_⟩
  simp only [Nat.cast_mul, mul_assoc, ← mul_sum, h_frame.sum_mul_conj, mul_ite, mul_zero]

namespace Parameters

/-- Let `φ : E →+* ℂ_[p]` be an embedding of the CM field `E = P.E s`, and let `adeleExtension φ` be
its extension to the finite adeles. There is an element `y` of `𝔞₀⁻¹`, the inverse of the
fractional ideal `𝔞₀` of the idele `α = P.α s`, such that the integral adele `α y` is a unit at the
place of `φ`. -/
lemma exists_norm_adeleExtension_alpha_mul_eq_one {P : Parameters} {s p : ℕ} [Fact p.Prime]
    (φ : P.E s →+* ℂ_[p]) :
    ∃ y : P.E s, (P.α s).val * y ∈ Ô (P.E s) ∧ ‖adeleExtension φ ((P.α s).val * y)‖ = 1 := by
  -- `E` is dense in the finite adeles, so some `y` has `α y - 1 ∈ p Ô`.
  let pInv : 𝔸f (P.E s) := ((p : P.E s)⁻¹ : P.E s)
  have h_open : IsOpen {x : 𝔸f (P.E s) | pInv * ((P.α s).val * x - 1) ∈ Ô (P.E s)} :=
    isOpen_Ô.preimage (by fun_prop)
  obtain ⟨y, hy⟩ : ∃ y : P.E s, pInv * ((P.α s).val * y - 1) ∈ Ô (P.E s) :=
    denseRange_algebraMap_finAdele.exists_mem_open h_open ⟨(P.α s)⁻¹.val, by simp⟩
  have h_decomp : (P.α s).val * y = 1 + p * (pInv * ((P.α s).val * y - 1)) := by
    rw [← mul_assoc, ← map_natCast (algebraMap (P.E s) (𝔸f (P.E s))), ← map_mul,
      mul_inv_cancel₀ (NeZero.ne _), map_one, one_mul, add_sub_cancel]
  have h_small : ‖adeleExtension φ (p * (pInv * ((P.α s).val * y - 1)))‖ < 1 :=
    calc ‖adeleExtension φ (p * (pInv * ((P.α s).val * y - 1)))‖
      _ = ‖(p : ℂ_[p])‖ * ‖adeleExtension φ (pInv * ((P.α s).val * y - 1))‖ := by
        rw [map_mul, map_natCast, norm_mul]
      _ ≤ ‖(p : ℂ_[p])‖ :=
        mul_le_of_le_one_right (norm_nonneg _) (norm_adeleExtension_le_one φ hy)
      _ < 1 := norm_p_lt_one
  have h_int : (P.α s).val * y ∈ Ô (P.E s) := by
    rw [h_decomp]
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ p) hy)
  refine ⟨y, h_int, ?_⟩
  -- In an ultrametric field, `‖1 + x‖ = 1` for `‖x‖ < 1`.
  rw [h_decomp, map_add, map_one, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (norm_one.trans_ne h_small.ne'), norm_one, max_eq_left h_small.le]

variable {P : Parameters} {s p : ℕ} [Fact p.Prime] [ι : PadicPlace p]

/-- The trace of `z` from `E` to `K`, as a complex number, is the sum of its images under the
embeddings of the CM type. -/
lemma coe_trace_eq_sum (z : P.E s) :
    Algebra.trace P.K (P.E s) z = ∑ τ : InfinitePlace (P.E s), Φ τ z := by
  -- Apply `Φ 1`, which fixes `K`, to the trace as a sum over the Galois group.
  rw [← P.phi_algebraMap s 1, trace_eq_sum_automorphisms, map_sum,
    ← (P.galOfPlace s).toEquiv.sum_comp]
  simp [← phi_mul]

/-- The finite image of `x` in `E` is the adele `α⁻¹ x`, with `α = P.α s` the idele of `𝔞₀`. -/
lemma finiteImage_id_eq_inv_alpha_mul (x : P.E s) :
    finiteImage id x = (P.α s)⁻¹.val * algebraMap (P.E s) (𝔸f (P.E s)) x := rfl

/-- If `z P'(ζ)` is integral, where `P'(ζ) = relDifferentGen` generates the different of `E / K`,
then the trace of `z` from `E` to `K` is an integer of `K`. -/
lemma exists_coe_eq_trace_of_isIntegral {z : P.E s}
    (hz : IsIntegral ℤ (z * (P.relDifferentGen s).val)) :
    ∃ c : 𝓞 P.K, (c : P.K) = Algebra.trace P.K (P.E s) z := by
  obtain ⟨-, h_span, -⟩ := relDifferent_spec (isPrimitiveRoot_zetaInt (P := P) (s := s))
  have h_le : differentIdeal (𝓞 P.K) (𝓞 (P.E s)) ≤ Ideal.span {P.relDifferentGen s} := h_span.ge
  have h_bot : Ideal.span {P.relDifferentGen s} ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.2 (mod_cast P.relDifferentGen_ne_zero s)
  have h_mem : z ∈ ((Ideal.span {P.relDifferentGen s} : Ideal (𝓞 (P.E s))) :
      FractionalIdeal (nonZeroDivisors (𝓞 (P.E s))) (P.E s))⁻¹ := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_inv,
      FractionalIdeal.mem_spanSingleton]
    exact ⟨⟨_, hz⟩, mul_inv_cancel_right₀ (P.relDifferentGen_ne_zero s) z⟩
  -- The trace maps the inverse different into `𝓞 K`.
  exact Submodule.mem_one.1
    ((differentialIdeal_le_iff (K := P.K) (L := P.E s) h_bot).1 h_le ⟨z, h_mem, rfl⟩)

/-- Let `x`, `y` in the CM field `E = P.E s` lie in `𝔞₀ = E ∩ α Ô`: the finite adeles
`finiteImage id x = α⁻¹ x` and `finiteImage id y = α⁻¹ y`, with `α = P.α s`, lie in the ring `Ô E`
of integral adeles. Then the hermitian product `∑ τ, Φ τ x * conj (Φ τ y)` lies in `quadInt d`, the
ring of integers of `K` inside `ℂ`. -/
lemma sum_mul_conj_mem_quadInt {x y : P.E s} (hx : finiteImage id x ∈ Ô (P.E s))
    (hy : finiteImage id y ∈ Ô (P.E s)) :
    ∑ τ : InfinitePlace (P.E s), Φ τ x * conj (Φ τ y) ∈ quadInt P.d := by
  -- The number `x ȳ P'(ζ)` is integral: it is `α ᾱ P'(ζ)`, a unit at every finite place, times
  -- `α⁻¹ x` and the conjugate of `α⁻¹ y`.
  have h_gen : (P.α s).val * star (P.α s).val * (P.relDifferentGen s).val ∈ Ô (P.E s) :=
    mem_Ô.2 fun w ↦ (v_alpha_mul_star_mul_relDifferentGen w).le
  have h_factor : algebraMap (P.E s) (𝔸f (P.E s)) (x * star y * (P.relDifferentGen s).val) =
      (P.α s).val * star (P.α s).val * (P.relDifferentGen s).val *
        (finiteImage id x * star (finiteImage id y)) := by
    have h_one : (P.α s).val * (P.α s)⁻¹.val * (star (P.α s).val * star (P.α s)⁻¹.val) = 1 := by
      simp [← star_mul']
    have h_conj : star (algebraMap (P.E s) (𝔸f (P.E s)) y) =
        algebraMap (P.E s) (𝔸f (P.E s)) (star y) := by simp
    simp only [finiteImage_id_eq_inv_alpha_mul, map_mul, star_mul', h_conj]
    linear_combination -(algebraMap (P.E s) (𝔸f (P.E s)) x *
      algebraMap (P.E s) (𝔸f (P.E s)) (star y) * (P.relDifferentGen s).val) * h_one
  have h_int : IsIntegral ℤ (x * star y * (P.relDifferentGen s).val) := by
    rw [← algebraMap_mem_Ô, h_factor]
    exact mul_mem h_gen (mul_mem hx (star_mem_Ô hy))
  obtain ⟨c, hc⟩ := exists_coe_eq_trace_of_isIntegral h_int
  exact ⟨c, show ((c : P.K) : ℂ) = _ by simp [hc, coe_trace_eq_sum]⟩

open scoped Classical in
omit [PadicPlace p] in
/-- The image of the idele `α` of `𝔞₀` under the extension of an embedding `φ : E →+* ℂ_[p]` to the
finite adeles: it is `φ(P'(ζ))⁻¹`, with `P'(ζ) = relDifferentGen`, if the prime of `E` induced by
`φ` divides `betaKInE = (1 + √-d) / 2`, and `1` otherwise. -/
lemma adeleExtension_alpha (φ : P.E s →+* ℂ_[p]) :
    adeleExtension φ (P.α s).val =
      (if P.betaKInE s ∈ (placeOfEmb φ).asIdeal then (φ (P.relDifferentGen s))⁻¹ else 1) := by
  let e : ℂ_[p] := adeleExtension φ (idem {w | P.betaKInE s ∈ w.asIdeal})
  have h_expand : adeleExtension φ (P.α s).val = e * (φ (P.relDifferentGen s))⁻¹ + (1 - e) := by
    simp [α, e]
  rw [h_expand]
  split_ifs with h_mem <;> simp [e, adeleExtension, h_mem]

/-- At a `p`-adic place `ιₚ` of `ℂ`, the absolute value of `vacuumRoot` is inverse to that of the
finite idele `α = P.α s` of the Weil data at the place of `weightEmbedding ιₚ τ : y ↦ ιₚ (τ ȳ)`, for
every `τ` in the CM type. For an embedding `φ : E →+* ℂ_[p]`, the map `adeleExtension φ` takes the
component of an adele at the prime of `E` induced by `φ` and applies the extension of `φ` to the
completion at that prime. -/
lemma norm_iota_vacuumRoot (τ : P.Φ s) :
    ‖ιₚ (P.vacuumRoot s)‖ = ‖adeleExtension (weightEmbedding ιₚ τ) (P.α s).val‖⁻¹ := by
  -- All conjugates of `P'(ζ)` over `K` have the same absolute value under `ιₚ`.
  have h_norm_gen_eq (u : P.Φ s) : ‖ιₚ (conj (Φ u (P.relDifferentGen s).val))‖ =
      ‖ιₚ (conj (Φ 1 (P.relDifferentGen s).val))‖ := by
    let φ : P.E s →+* ℂ_[p] := weightEmbedding ιₚ 1
    have h_norm : ‖φ (galOfPlaceInt u (P.relDifferentGen s)).val‖₊ =
        ‖φ (P.relDifferentGen s).val‖₊ := (isEquiv_placeOfEmb φ).eq_iff.2
      (valuation_map_relDifferentGen (galOfPlaceInt u) (MulAction.injective _) (placeOfEmb φ))
    simpa [φ, NNReal.eq_iff, starRingEnd_apply (R := P.E s), ← phi_mul] using h_norm
  -- So the absolute value of `α` at the place of `y ↦ ιₚ (u ȳ)` does not depend on `u`.
  have h_norm_alpha_eq (u : P.Φ s) : ‖adeleExtension (weightEmbedding ιₚ u) (P.α s).val‖ =
      ‖adeleExtension (weightEmbedding ιₚ τ) (P.α s).val‖ := by
    have h_fixed (v : P.Φ s) : Φ v (P.betaKInE s).val = quadGen P.d := P.phi_algebraMap s v _
    simp [adeleExtension_alpha, apply_ite norm, h_norm_gen_eq, h_fixed,
      starRingEnd_apply (R := P.E s)]
  -- Compare `f`-th powers, `f` the number of infinite places: `‖ιₚ (chiFin α)‖` is the product
  -- of these absolute values over all `u`.
  have h_chi : ‖ιₚ (chiFin (P.α s))‖ =
      ‖adeleExtension (weightEmbedding ιₚ τ) (P.α s).val‖ ^ Fintype.card (P.Φ s) := by
    simp only [WeilData.norm_map_chiFin, h_norm_alpha_eq, prod_const, card_univ]
  have h_pow : ‖ιₚ (P.vacuumRoot s)‖ ^ Fintype.card (P.Φ s) = ‖ιₚ (chiFin (P.α s))‖⁻¹ := by
    rw [← norm_pow, ← map_pow, vacuumRoot_pow_numInfPlaces, map_inv₀, norm_inv]
  rw [h_chi, ← inv_pow] at h_pow
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) Fintype.card_ne_zero).1 h_pow

/-- At a `p`-adic place `ιₚ` of `ℂ` with valuation ring `embValRing`, the number `vacuumRoot`
generates the module spanned by `τ(𝔞̄₀)⁻¹`, the set of the `τ ȳ` with `y` in `𝔞₀⁻¹`. -/
lemma span_vacuumRoot_eq (τ : P.Φ s) :
    Submodule.span embValRing {P.vacuumRoot s} =
      Submodule.span embValRing
        {conj (Φ τ y) | (y : P.E s) (_ : (P.α s).val * y ∈ Ô (P.E s))} := by
  -- With `φ` the embedding `y ↦ ιₚ (τ ȳ)`, extended to the finite adeles, we have
  -- `‖φ y‖ = ‖φ (α y)‖ ‖ιₚ vacuumRoot‖`. So each `τ ȳ` is an integral multiple of `vacuumRoot`,
  -- and a unit multiple if `‖φ (α y)‖ = 1`.
  let φ : P.E s →+* ℂ_[p] := weightEmbedding ιₚ τ
  have h_alpha_ne : adeleExtension φ (P.α s).val ≠ 0 := ((P.α s).isUnit.map _).ne_zero
  have h_root : P.vacuumRoot s ≠ 0 := fun h_zero ↦
    h_alpha_ne (norm_eq_zero.1 (by simpa [h_zero, φ, eq_comm] using norm_iota_vacuumRoot τ))
  have h_ratio (y : P.E s) : ‖ιₚ (conj (Φ τ y) / P.vacuumRoot s)‖ =
      ‖adeleExtension φ ((P.α s).val * y)‖ := by
    simp [φ, norm_iota_vacuumRoot τ, starRingEnd_apply y, mul_comm]
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · obtain ⟨y, h_int, h_one⟩ := exists_norm_adeleExtension_alpha_mul_eq_one φ
    have h_unit : ‖ιₚ (conj (Φ τ y) / P.vacuumRoot s)‖ = 1 := (h_ratio y).trans h_one
    have h_inv_norm_le : ‖ιₚ (P.vacuumRoot s / conj (Φ τ y))‖ ≤ 1 := by
      rw [← inv_div, map_inv₀, norm_inv, h_unit, inv_one]
    have h_ne : conj (Φ τ y) ≠ 0 := fun h_zero ↦ by simp [h_zero] at h_unit
    rw [Submodule.span_singleton_le_iff_mem, ← div_mul_cancel₀ (P.vacuumRoot s) h_ne]
    exact Submodule.smul_mem _ (⟨_, h_inv_norm_le⟩ : embValRing)
      (Submodule.subset_span ⟨y, h_int, rfl⟩)
  · rintro - ⟨y, hy, rfl⟩
    have h_mem : conj (Φ τ y) / P.vacuumRoot s ∈ embValRing :=
      (h_ratio y).trans_le (norm_adeleExtension_le_one φ hy)
    exact Submodule.mem_span_singleton.2 ⟨⟨_, h_mem⟩, div_mul_cancel₀ (conj (Φ τ y)) h_root⟩

/-- At a `p`-adic place `ιₚ` of `ℂ`, the absolute value of `periodFactor` equals that of
`vacuumRoot`. It is the inverse of the absolute value of the idele `P.α s` of the Weil data at the
place of `weightEmbedding ιₚ τ : y ↦ ιₚ (τ ȳ)`. -/
lemma norm_iota_periodFactor (τ : P.Φ s) :
    ‖ιₚ (P.periodFactor s)‖ = ‖adeleExtension (weightEmbedding ιₚ τ) (P.α s).val‖⁻¹ := by
  rw [periodFactor, map_div₀, norm_div, norm_iota_chowlaSelbergUnit, div_one,
    norm_iota_vacuumRoot τ]

/-- For `y` in `𝔞₀` (that is, `α⁻¹ y` is an integral adele) the coefficients
`periodFactor * conj (τ y)` of the linear form `z ↦ periodFactor * y† z` are integral at the
`p`-adic place `ιₚ` of `ℂ`. -/
lemma norm_periodFactor_mul_conj_le_one {y : P.E s} (hy : finiteImage id y ∈ Ô (P.E s))
    (τ : P.Φ s) : ‖ιₚ (P.periodFactor s * conj (Φ τ y))‖ ≤ 1 := by
  -- The left side is the absolute value of `α⁻¹ y` at the place of `weightEmbedding ιₚ τ`.
  simpa [finiteImage_id_eq_inv_alpha_mul, norm_iota_periodFactor τ, starRingEnd_apply y] using
    norm_adeleExtension_le_one (weightEmbedding ιₚ τ) hy

variable (P s) in
/-- If the prime `p` does not divide `q₁ = P.q₁ s`, the order of the roots of unity that generate
`E = P.E s` over `K`, then `periodFactor` is a unit at the `p`-adic place `ιₚ` of `ℂ`. -/
lemma norm_iota_periodFactor_eq_one (hp : ¬p ∣ P.q₁ s) : ‖ιₚ (P.periodFactor s)‖ = 1 := by
  -- With `τ = Φ 1`, the number `vacuumRoot` generates the module spanned by the `τ ȳ` with `y` in
  -- `𝔞₀⁻¹`. As `q₁ 𝔞₀ ⊆ 𝓞 E ⊆ 𝔞₀`, the `τ ȳ` are integral, and one of them is the unit `q₁`.
  have h_span : Submodule.span embValRing {P.vacuumRoot s} = Submodule.span embValRing
      {conj (Φ (1 : P.Φ s) y) | (y : P.E s) (_ : (P.α s).val * y ∈ Ô (P.E s))} :=
    span_vacuumRoot_eq (p := p) 1
  have h_le : ‖ιₚ (P.vacuumRoot s)‖ ≤ 1 := by
    have h_int : Submodule.span embValRing {P.vacuumRoot s} ≤ (1 : Submodule embValRing ℂ) := by
      rw [h_span, Submodule.span_le]
      rintro - ⟨y, hy, rfl⟩
      have h_norm : ‖ιₚ (conj (Φ (1 : P.Φ s) y))‖ ≤ 1 := by
        simpa [starRingEnd_apply y] using
          norm_adeleExtension_le_one (weightEmbedding ιₚ 1) (mul_mem inv_alpha_mem hy)
      exact Submodule.mem_one.2 ⟨⟨_, h_norm⟩, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (h_int (Submodule.mem_span_singleton_self _))
    rw [← hc]
    exact c.prop
  obtain ⟨c, hc⟩ : ∃ c : embValRing, c • P.vacuumRoot s = P.q₁ s := by
    rw [← Submodule.mem_span_singleton, h_span]
    exact Submodule.subset_span ⟨P.q₁ s, by simpa [mul_comm] using q₁_mul_alpha_mem, by simp⟩
  have h_norm_q₁ : ‖(P.q₁ s : ℂ_[p])‖ = 1 :=
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hp).norm_natCast_eq_one ℂ_[p]
  have h_ge : 1 ≤ ‖ιₚ (P.vacuumRoot s)‖ :=
    calc 1 = ‖ιₚ c‖ * ‖ιₚ (P.vacuumRoot s)‖ := by
          rw [← norm_mul, ← map_mul, ← smul_eq_mul, ← Subring.smul_def, hc, map_natCast, h_norm_q₁]
      _ ≤ ‖ιₚ (P.vacuumRoot s)‖ := mul_le_of_le_one_left (norm_nonneg _) c.prop
  rw [periodFactor, map_div₀, norm_div, norm_iota_chowlaSelbergUnit, div_one]
  exact h_le.antisymm h_ge

/-- The integers of `P.E s` have integral finite image: for `a` in the ring of integers `𝓞 (P.E s)`,
the finite adele `α⁻¹ a` (`finiteImage id a`) lies in `Ô (P.E s)`. -/
lemma finiteImage_coe_mem (a : 𝓞 (P.E s)) : finiteImage id (a : P.E s) ∈ Ô (P.E s) := by
  rw [finiteImage_id_eq_inv_alpha_mul]
  exact mul_mem inv_alpha_mem (algebraMap_mem_Ô.2 a.isIntegral_coe)

/-- Two embeddings `Φ σ`, `Φ τ` of the CM type that agree on a primitive `q₁`-th root of unity
belong to the same infinite place. -/
lemma eq_of_phi_eq_of_isPrimitiveRoot {z : P.E s} (hz : IsPrimitiveRoot z (P.q₁ s))
    {σ τ : P.Φ s} (h_phi : Φ σ z = Φ τ z) : σ = τ := by
  -- Both embeddings are `K`-linear, and `z` generates `E` over `K`.
  let lift (v : P.Φ s) : P.E s →ₐ[P.K] ℂ := ⟨Φ v, P.phi_algebraMap s v⟩
  have h_lift : lift σ = lift τ := (hz.powerBasis P.K).algHom_ext h_phi
  exact Function.LeftInverse.injective mk_Φ (congrArg AlgHom.toRingHom h_lift)

/-- Orthogonality of characters: for parameters `P : Parameters`, `s : ℕ` and a primitive `q₁`-th
root of unity `z` of `E = P.E s`, with `q₁ = P.q₁ s`, the powers `z ^ i`, `0 ≤ i < q₁`, are a tight
frame of length `q₁` with all multiplicities `1`. -/
lemma isTightFrame_pow {z : P.E s} (hz : IsPrimitiveRoot z (P.q₁ s)) :
    IsTightFrame (fun i : Fin (P.q₁ s) ↦ z ^ i.val) 1 (P.q₁ s) := by
  refine ⟨fun i ↦ finiteImage_coe_mem (hz.toInteger ^ i.val), fun σ τ ↦ ?_⟩
  have h_prim (v : P.Φ s) : IsPrimitiveRoot (Φ v z) (P.q₁ s) := hz.map_of_injective (Φ v).injective
  have h_ne : Φ τ z ≠ 0 := (h_prim τ).ne_zero (NeZero.ne _)
  have h_conj : conj (Φ τ z) = (Φ τ z)⁻¹ :=
    (Complex.inv_eq_conj ((h_prim τ).norm'_eq_one (NeZero.ne _))).symm
  simp only [Pi.one_apply, Nat.cast_one, one_mul, map_pow, h_conj, ← mul_pow, ← sum_range]
  split_ifs with h_eq
  · simp [h_eq, h_ne]
  · have h_ne_one : Φ σ z * (Φ τ z)⁻¹ ≠ 1 := fun h_one ↦
      h_eq (eq_of_phi_eq_of_isPrimitiveRoot hz ((mul_inv_eq_one₀ h_ne).1 h_one))
    rw [geom_sum_eq h_ne_one]
    simp [mul_pow, (h_prim σ).pow_eq_one, (h_prim τ).pow_eq_one]

variable (P s) in
/-- The powers `ζ ^ i`, `0 ≤ i < q₁`, each taken `k` times, form a tight frame (`IsTightFrame`) with
frame bound `k * q₁`. -/
lemma isTightFrame_zeta_pow (k : ℕ) :
    IsTightFrame (fun i : Fin (P.q₁ s) ↦ P.ζ s ^ i.val) (fun _ : Fin (P.q₁ s) ↦ k)
      (k * P.q₁ s) := by
  simpa only [Pi.one_apply, mul_one] using (isTightFrame_pow isPrimitiveRoot_zeta).mul_left k

end Parameters

end New

end TightFrameExists

/-!
## Jet series as Taylor series along lines

`New.taylorAtZero g` is the Taylor series at `0` of `g : ℂ → ℂ`, and `New.linearSeries μ` is the
linear form `∑ p, μ p * X p`. The space `V.finitePart` is spanned by the translates of the vacuum
under the finite Heisenberg operators.
-/

namespace New.Space

open MvPowerSeries MeasureTheory Fock NormedSpace Finset

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n]
  {V : Space E n 1}

open NumberField (InfinitePlace)

/-- Differentiation under the integral: for `f` in the Schwartz space `𝒮 V` of the hermitian space
`V : Space E n 1` over the CM field `E` and a continuous conjugate-linear form `L`, the `k`-th
derivative at `0` of `t ↦ ∫ exp (t * L w) * g w` is `∫ L w ^ k * g w`. Here `g w` is the Gaussian
`realVac w = exp (-|w|² / 2)` times the value of `f` at `realVec w`. The vector `realVec w` is the
adelic vector with finite part zero whose real part is `w` with its coordinates at `τ` multiplied by
`(2π Im τ(ȷ))^(-1/2)`, where `ȷ` is the element `j` of the Weil data. `normalizedVolume` is Lebesgue
measure divided by `π` to the number of coordinates. -/
lemma iteratedDeriv_integral_exp_mul_realVac (f : 𝒮 V) (L : (InfinitePlace E × n → ℂ) →L⋆[ℂ] ℂ)
    (k : ℕ) :
    iteratedDeriv k (fun t : ℂ ↦ ∫ w : InfinitePlace E × n → ℂ,
        exp (t * L w) * (realVac w * f (realVec w)) ∂normalizedVolume (InfinitePlace E × n)) 0 =
      ∫ w : InfinitePlace E × n → ℂ,
        L w ^ k * (realVac w * f (realVec w)) ∂normalizedVolume (InfinitePlace E × n) := by
  -- Expand the exponential under the integral to get a power series in `t`.
  let g (w : InfinitePlace E × n → ℂ) : ℂ := realVac w * f (realVec w)
  let I (t : ℂ) : ℂ := ∫ w, exp (t * L w) * g w ∂normalizedVolume (InfinitePlace E × n)
  have h_sum (t : ℂ) : HasSum (fun j : ℕ ↦
      ∫ w, (t * L w) ^ j / j.factorial * g w ∂normalizedVolume (InfinitePlace E × n)) (I t) := by
    -- Dominated convergence: the bounds sum to a multiple of `exp (‖t‖ * ‖L‖ * ‖w‖) * ‖realVac w‖`.
    refine hasSum_integral_of_dominated_convergence
      (fun j w ↦ (‖t‖ * (‖L‖ * ‖w‖)) ^ j / j.factorial * (‖realVac w‖ * (‖V.θ‖ * ‖f‖)))
      (by fun_prop [realVac]) (fun j ↦ .of_forall fun w ↦ ?_) ?_ ?_
      (.of_forall fun w ↦ (expSeries_div_hasSum_exp (t * L w)).mul_right (g w))
    · simp only [g, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      grw [L.le_opNorm w, norm_apply_le]
    · simp [Summable.mul_right, expSeries_div_summable]
    · simpa [tsum_mul_right, exp_eq_tsum_div, Real.exp_eq_exp_ℝ, mul_assoc] using
        (integrable_exp_mul_realVac (‖t‖ * ‖L‖)).mul_const (‖V.θ‖ * ‖f‖)
  obtain ⟨r, hr⟩ : HasFPowerSeriesAt I (.ofScalars ℂ fun j : ℕ ↦
      (∫ w, L w ^ j * g w ∂normalizedVolume (InfinitePlace E × n)) / j.factorial) 0 :=
    hasFPowerSeriesAt_iff.2 <| .of_forall fun t ↦ by
      simpa [integral_const_mul, mul_pow, mul_assoc, div_eq_inv_mul, mul_left_comm] using h_sum t
  change iteratedDeriv k I 0 = ∫ w, L w ^ k * g w ∂normalizedVolume (InfinitePlace E × n)
  simpa [iteratedDeriv, mul_div_cancel₀, k.factorial_ne_zero] using (hr.factorial_smul 1 k).symm

variable {f : 𝒮 V}

/-- Let `V` be a hermitian space with all signs `1` and let `f` lie in `V.finitePart`, the span of
the translates of the vacuum under the finite Heisenberg operators. Then the Taylor series at `0` of
`t ↦ entireTheta f (a • t • v)` is obtained by substituting `v p * X` for the variable with index
`p` in `V.jetSeries a f`. Here `entireTheta f` is the function `y ↦ θ(ϱ(y) f) exp(|y|²/2)` of a real
vector `y`, where `ϱ(y) f` is the translate of `f` by `y` and `θ = V.θ` is the theta functional, a
linear form on `𝒮 V`. `V.jetSeries a f` is the series whose coefficient of `z ^ k` is `a ^ |k| / k!`
times the value of `θ` at `f` tensored at the real places with the polynomial `z ^ k`, seen as a
vector of the Fock model (the Fock vector of `z ^ k`). Here `|k| = ∑ p, k p` and
`k! = ∏ p, (k p)!`. -/
lemma taylor_line_eq_subst_jetSeries (hf : f ∈ V.finitePart) (a : ℂ)
    (v : InfinitePlace E × n → ℂ) :
    taylorAtZero (fun t : ℂ ↦ entireTheta f (a • t • v)) =
      (V.jetSeries a f).subst fun p : InfinitePlace E × n ↦ linearSeries fun _ : Unit ↦ v p := by
  -- On the line, `entireTheta f` is `t ↦ ∫ exp (t * L w) * g w` for a conjugate-linear form `L`.
  -- Its derivatives at `0` are `∫ L w ^ k * g w`, and these are jets of `V.jetSeries a f`.
  ext k
  let L : (InfinitePlace E × n → ℂ) →L⋆[ℂ] ℂ := a • ∑ p, innerSLFlip ℂ (v p) ∘SL .proj p
  have hL (w : InfinitePlace E × n → ℂ) : L w = a * ∑ p, v p * star (w p) := by
    simp [L]
  let g (w : InfinitePlace E × n → ℂ) : ℂ := realVac w * f (realVec w)
  have h_line (t : ℂ) : entireTheta f (a • t • v) =
      ∫ w, exp (t * L w) * g w ∂normalizedVolume (InfinitePlace E × n) := by
    rw [entireTheta_eq_integral rfl (projReal_eq_self_of_mem_finitePart hf)]
    simp [hL, g, mul_sum, mul_assoc, mul_left_comm, Complex.exp_eq_exp_ℂ]
  let T : PowerSeries ℂ := (V.jetSeries a f).subst fun p ↦ linearSeries fun _ ↦ v p
  have h_jet : k.factorial * PowerSeries.coeff k T =
      ∫ w, L w ^ k * g w ∂normalizedVolume (InfinitePlace E × n) := calc
    _ = jet ℂ (.X () ^ k) T := by
      simp [MvPolynomial.X_pow_eq_monomial, jet_monomial, PowerSeries.coeff]
    _ = jet ℂ ((∑ p, v p • .X p) ^ k) (V.jetSeries a f) :=
      (jet_subst_linearSeries (.replicateCol Unit v) _ _).trans (by simp [linSubst])
    _ = ∫ w, L w ^ k * g w ∂normalizedVolume (InfinitePlace E × n) := by
      -- The jet along a polynomial `Q` is `∫ Q (a • conj w) * g w`.
      rw [jet_jetSeries_eq_theta, theta_integrated]
      simp [hL, g, holomorphicCoord_eq, mul_sum, mul_assoc, mul_left_comm]
  rw [taylorAtZero, PowerSeries.coeff_mk, funext h_line, iteratedDeriv_integral_exp_mul_realVac,
    ← h_jet, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 k.factorial_ne_zero)]

/-- For `V : Space E n 1` (all signs `1`), `f` in `V.finitePart` and `a ≠ 0`: if `V.jetSeries a f`,
the Taylor series at `0` of `z ↦ V.entireTheta f (a • z)`, vanishes, then `f = 0`. -/
lemma eq_zero_of_jetSeries_eq_zero (hf : f ∈ V.finitePart) {a : ℂ} (ha : a ≠ 0)
    (h_jet : V.jetSeries a f = 0) : f = 0 := by
  -- On each line through `0` the entire function `entireTheta f` has Taylor series `0`, so it
  -- vanishes; and `f` is determined by its values at the vectors `realVec y`.
  refine eq_zero_of_apply_realVec_eq_zero fun y ↦ ?_
  have h_taylor : taylorAtZero (fun t : ℂ ↦ entireTheta f (a • t • y)) = taylorAtZero 0 := by
    rw [taylor_line_eq_subst_jetSeries hf a y, h_jet,
      ← coe_substAlgHom (hasSubst_of_constantCoeff_zero (by simp [linearSeries])), map_zero]
    exact PowerSeries.ext fun k ↦ by simp [taylorAtZero]
  have h_line : (fun t : ℂ ↦ entireTheta f (a • t • y)) = 0 :=
    eq_of_taylorAtZero_eq (by fun_prop (disch := simp [hf])) differentiable_zero h_taylor
  -- The point `a⁻¹` of the line is `y`.
  simpa [ha, entireTheta, realVac] using congrFun h_line a⁻¹

/-- The Taylor series at `0` of a finite product of entire functions `x ↦ G i (c i * x)` is the
product of the Taylor series of the `G i`, with `c i • X` substituted for the variable. -/
lemma _root_.New.taylorAtZero_prod_comp_mul {I : Type*} {G : I → ℂ → ℂ}
    (hG : ∀ i : I, Differentiable ℂ (G i)) (c : I → ℂ) (t : Finset I) :
    taylorAtZero (fun x : ℂ ↦ ∏ i ∈ t, G i (c i * x)) =
      ∏ i ∈ t, (taylorAtZero (G i)).subst (c i • (PowerSeries.X : PowerSeries ℂ)) := by
  induction t using cons_induction with
  | empty => simp
  | cons j t hj ih =>
    simp (disch := fun_prop) [ih, taylorAtZero_comp_mul, PowerSeries.rescale_eq_subst]

/-- Two power series over `ℂ` in finitely many variables are equal if their restrictions
`rename (fun _ ↦ ()) (rescale v S)` to the line spanned by `v` agree for every vector `v`. -/
lemma _root_.New.mvPowerSeries_eq_of_forall_line {σ : Type*} [Fintype σ] {S T : MvPowerSeries σ ℂ}
    (h_line : ∀ v : σ → ℂ, rename (fun _ : σ ↦ ()) (rescale v S) =
      rename (fun _ : σ ↦ ()) (rescale v T)) : S = T := by
  -- The homogeneous component of degree `|α|`, evaluated at `v`, is a coefficient of the
  -- restriction to the line; a polynomial over `ℂ` is determined by its values.
  classical
  ext α
  let deg : (σ →₀ ℕ) → Unit →₀ ℕ := Finsupp.mapDomain fun _ ↦ ()
  -- The exponents of the same total degree as `α`.
  let A : Finset (σ →₀ ℕ) :=
    (Filter.TendstoCofinite.finite_preimage_singleton deg (deg α)).toFinset
  have hα : α ∈ A := by simp [A]
  have h_eval (v : σ → ℂ) (U : MvPowerSeries σ ℂ) : (U.truncFinset ℂ A).eval v =
      (rename (fun _ : σ ↦ ()) (rescale v U)).coeff (deg α) := by
    simp [A, deg, truncFinset, coeff_rename, MvPolynomial.eval_monomial, mul_comm]
  have h_trunc : S.truncFinset ℂ A = T.truncFinset ℂ A :=
    MvPolynomial.funext fun v ↦ by rw [h_eval, h_eval, h_line]
  rw [← coeff_truncFinset_of_mem S hα, ← coeff_truncFinset_of_mem T hα, h_trunc]

lemma entireTheta_zero {ε : n → ℤˣ} {V : Space E n ε} (f : 𝒮 V) : entireTheta f 0 = V.θ f := by
  simp [entireTheta, realVac]

/-- If `entireTheta f (c • z) = ∏ i, G i (μ i ⬝ᵥ z)` for all `z`, then the theta functional of `f`
is `∏ i, G i 0`. -/
lemma theta_eq_prod_of_entireTheta_smul {ε : n → ℤˣ} {V : Space E n ε} {f : 𝒮 V} {I : Type*}
    [Fintype I] {G : I → ℂ → ℂ} {c : ℂ} {μ : I → InfinitePlace E × n → ℂ}
    (h_prod : ∀ z : InfinitePlace E × n → ℂ, entireTheta f (c • z) = ∏ i : I, G i (μ i ⬝ᵥ z)) :
    V.θ f = ∏ i : I, G i 0 := by
  simpa only [smul_zero, entireTheta_zero, dotProduct_zero] using h_prod 0

/-- Let `V` have all signs `1`, so that `xᴴJx` is the identity at the infinite places. Let `f` lie
in `V.finitePart`, the span of the translates of the vacuum under the finite Heisenberg operators.
Suppose that `entireTheta f (c • z) = ∏ i, G i (μ i ⬝ᵥ z)` for all `z`, with every `G i` entire.
Then `V.jetSeries c f` is the product of the Taylor series of the `G i`, evaluated at the linear
forms `linearSeries (μ i) = ∑ p, μ i p * X p`. -/
lemma jetSeries_eq_prod_of_entireTheta_smul (hf : f ∈ V.finitePart) {I : Type*} [Fintype I]
    {G : I → ℂ → ℂ} {c : ℂ} {μ : I → InfinitePlace E × n → ℂ}
    (hG : ∀ i : I, Differentiable ℂ (G i))
    (h_prod : ∀ z : InfinitePlace E × n → ℂ, entireTheta f (c • z) = ∏ i : I, G i (μ i ⬝ᵥ z)) :
    V.jetSeries c f = ∏ i : I, (taylorAtZero (G i)).subst (linearSeries (μ i)) := by
  -- Two series agree if their restrictions to all lines through `0` agree. On the line spanned
  -- by `v` both sides are the Taylor series of `x ↦ ∏ i, G i (μ i ⬝ᵥ v * x)`.
  refine mvPowerSeries_eq_of_forall_line fun v ↦ ?_
  let line : MvPowerSeries (InfinitePlace E × n) ℂ →+* PowerSeries ℂ :=
    (rename fun _ ↦ ()).toRingHom.comp (rescale v)
  have h_line (U : MvPowerSeries (InfinitePlace E × n) ℂ) :
      line U = U.subst fun p ↦ v p • (PowerSeries.X : PowerSeries ℂ) := by
    simp [line, PowerSeries.X, subst_comp_subst_apply, rename_eq_subst, rescale_eq_subst,
      subst_smul, subst_X, hasSubst_of_constantCoeff_zero]
  -- Restricting to the line turns the linear form `μ i` into `(μ i ⬝ᵥ v) • X`.
  have h_factor (i : I) : line ((taylorAtZero (G i)).subst (linearSeries (μ i))) =
      (taylorAtZero (G i)).subst ((μ i ⬝ᵥ v) • (PowerSeries.X : PowerSeries ℂ)) := by
    have h_form : line (linearSeries (μ i)) = (μ i ⬝ᵥ v) • PowerSeries.X := by
      simp [line, linearSeries, rescale_eq_subst, ← coe_substAlgHom,
        hasSubst_of_constantCoeff_zero, smul_smul, ← sum_smul, dotProduct, PowerSeries.X]
    rw [← h_form, h_line, h_line]
    exact subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (by simp [linearSeries]))
      (hasSubst_of_constantCoeff_zero (by simp [PowerSeries.X])) _
  calc line (V.jetSeries c f)
    _ = taylorAtZero fun t : ℂ ↦ entireTheta f (c • t • v) := by
      simp [taylor_line_eq_subst_jetSeries hf, h_line, linearSeries, PowerSeries.X]
    _ = taylorAtZero fun x : ℂ ↦ ∏ i, G i (μ i ⬝ᵥ v * x) := by
      simp only [h_prod, dotProduct_smul, smul_eq_mul, mul_comm]
    _ = line (∏ i, (taylorAtZero (G i)).subst (linearSeries (μ i))) := by
      rw [taylorAtZero_prod_comp_mul hG, map_prod]
      simp only [h_factor]

/-- Let `V` have all signs `1`, let `f` lie in its finite part, and suppose that
`entireTheta f (c • z) = ∏ i, G i (μ c i ⬝ᵥ z)` for all `c` and `z`, with every `G i` entire. Then
the theta functional of `f` is `∏ i, G i 0`, and for every `c` the series `V.jetSeries c f` is the
product of the Taylor series of the `G i`, evaluated at the linear forms with coefficients
`μ c i`. -/
lemma jetSeries_eq_prod (hf : f ∈ V.finitePart) {I : Type*} [Fintype I] {G : I → ℂ → ℂ}
    {μ : ℂ → I → InfinitePlace E × n → ℂ} (hG : ∀ i : I, Differentiable ℂ (G i))
    (h_prod : ∀ (c : ℂ) (z : InfinitePlace E × n → ℂ),
      entireTheta f (c • z) = ∏ i : I, G i (μ c i ⬝ᵥ z)) :
    V.θ f = ∏ i : I, G i 0 ∧
    ∀ c : ℂ, V.jetSeries c f = ∏ i : I, (taylorAtZero (G i)).subst (linearSeries (μ c i)) :=
  ⟨theta_eq_prod_of_entireTheta_smul (h_prod 0),
    fun c ↦ jetSeries_eq_prod_of_entireTheta_smul hf hG (h_prod c)⟩

end New.Space

/-!
## Vectors built from sections along a tight frame

Fourier inversion turns a product of monomial sections into the theta function of a vector.
-/

namespace New.Parameters

open NumberField Complex Finset Space CMLattice ComplexConjugate Fintype stdLattice QuadField
  WeilData Pointwise

variable {P : Parameters} {s : ℕ} {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ}

/-- The period `cmPeriod` lies in the lattice `cmPeriod 𝓞_K` of the curve `cmCurve`. -/
lemma cmPeriod_mem_cmCurve_lattice : (P.cmPeriod : ℂ) ∈ P.cmCurve.Λ :=
  latticeModule_cmCurve.ge (mem_scaledIdeal.2 ⟨1, by simp⟩)

/-- The values of the character `selfDualAddChar` of the finite adeles have finite order, so their
images under a multiplicative map `ι` to a normed field have norm one. -/
@[simp] lemma norm_map_selfDualAddChar {F R : Type*} [NormedField R] [FunLike F ℂ R]
    [MonoidHomClass F ℂ R] (ι : F) (z : 𝔸f (P.E s)) : ‖ι (selfDualAddChar (P.E s) z)‖ = 1 :=
  ((ι : ℂ →* R).isOfFinOrder (isOfFinOrder_ψf _)).norm_eq_one

section FrameProduct

variable {V : Space (P.E s) n ε} {I : Type}

/-- The point `-b ⟨γ k, w j⟩` of `ℂ` for `i = (j, k)`, where
`⟨x, y⟩ = ∑ τ, Φ τ x * conj (Φ τ y)` is the sum over the CM type. -/
def resolutionShift (b : ℂ) (w : I → P.E s) (γ : n → P.E s) (i : I × n) : ℂ :=
  b * -∑ τ : InfinitePlace (P.E s), Φ τ (γ i.2) * conj (Φ τ (w i.1))

/-- The coefficients of the linear form `z ↦ a * ∑ τ, conj (Φ τ (w j)) * z (τ, k)` for
`i = (j, k)`. -/
def resolutionFormCoeff (a : ℂ) (w : I → P.E s) (i : I × n) (y : InfinitePlace (P.E s) × n) : ℂ :=
  if y.2 = i.2 then a * conj (Φ y.1 (w i.1)) else 0

/-- The linear form `z ↦ a * ∑ τ, conj (Φ τ (w j)) * z (τ, k)` for `i = (j, k)`. -/
def resolutionLinearForm (a : ℂ) (w : I → P.E s) (i : I × n) :
    (InfinitePlace (P.E s) × n → ℂ) →L[ℂ] ℂ :=
  ∑ τ : InfinitePlace (P.E s), (a * conj (Φ τ (w i.1))) • .proj (τ, i.2)

lemma resolutionLinearForm_apply_eq_dotProduct (a : ℂ) (w : I → P.E s) (i : I × n)
    (z : InfinitePlace (P.E s) × n → ℂ) :
      resolutionLinearForm a w i z = resolutionFormCoeff a w i ⬝ᵥ z := by
  simp [resolutionLinearForm, resolutionFormCoeff, dotProduct, sum_prod_type]

/-- For `i = (j, k)` the linear form `resolutionLinearForm a w i` is
`z ↦ a * ∑ τ, conj (Φ τ (w j)) * z (τ, k)`. The vector `realImage γ` is the image of `γ` at the
infinite places in Fock coordinates; its entry at `(τ, k)` is `P.areaScale * Φ τ (γ k)`, with
`P.areaScale = √(2π / √d)`. At this vector the form with `a = b / P.areaScale` takes the value
`b * ∑ τ, Φ τ (γ k) * conj (Φ τ (w j))`. -/
lemma resolutionLinearForm_realImage {P : Parameters} {s : ℕ} {n I : Type} (b : ℂ) (w : I → P.E s)
    (γ : n → P.E s) (i : I × n) :
    resolutionLinearForm (b / P.areaScale) w i (realImage γ) =
      b * ∑ τ : InfinitePlace (P.E s), Φ τ (γ i.2) * conj (Φ τ (w i.1)) := by
  have h_coord (τ : InfinitePlace (P.E s)) : realImage γ (τ, i.2) = P.areaScale * Φ τ (γ i.2) := by
    simp [realImage_apply, val_scaleIdele_fst, Real.sqrt_div_self, areaScale, j, field]
  simp only [resolutionLinearForm, _root_.sum_apply, mul_sum]
  refine sum_congr rfl fun τ _ ↦ ?_
  simp [h_coord, field]

/-- Let `x`, `y` in `P.E s` have integral finite images `α⁻¹ x`, `α⁻¹ y` (`finiteImage id`). Then
multiplying `a ∈ C.Λ` by `x† y = ∑ τ, Φ τ y * conj (Φ τ x)` gives an element of the CM lattice
`C.Λ`. -/
lemma mul_sum_mul_conj_mem_lattice {C : CMLattice P.d} {a : ℂ} {x y : P.E s} (ha : a ∈ C.Λ)
    (hy : finiteImage id y ∈ Ô (P.E s)) (hx : finiteImage id x ∈ Ô (P.E s)) :
    a * ∑ τ : InfinitePlace (P.E s), Φ τ y * conj (Φ τ x) ∈ C.Λ := by
  rw [mul_comm]
  exact C.mul_mem_of_quadInt (sum_mul_conj_mem_quadInt hy hx) ha

/-- `F` is the product of the functions `f i` along the vectors `w` at scale `b`: for a rational
vector `γ`, the theta function of `V.ϱ (finVec (finiteImage γ)) F`, the translate of `F` by the
finite image of `γ`, is the product of the twisted translates of the `f i`, each evaluated at a
linear form. The factor `i = (j, k)` is translated by `resolutionShift b w γ i` in degree `m j`:
`C.twistedTranslate m l g` is `z ↦ g (z + l)` times a Gaussian factor. -/
structure IsResolutionProduct [Fintype I] (V : Space (P.E s) n ε) (C : CMLattice P.d) (b : ℂ)
    (w : I → P.E s) (m : I → ℕ) (f : I × n → ℂ → ℂ) (F : 𝒮 V) : Prop where
  /-- `F` lies in the finite part of `V`. -/
  mem_finitePart : F ∈ V.finitePart
  /-- The factors are entire. -/
  differentiable (i : I × n) : Differentiable ℂ (f i)
  /-- The product formula; `P.areaScale = √(2π / √d)`. -/
  entireTheta_translate (γ : n → P.E s) (z : InfinitePlace (P.E s) × n → ℂ) :
    entireTheta (V.ϱ (finVec (finiteImage γ)) F) z =
      ∏ i : I × n, C.twistedTranslate (m i.1) (resolutionShift b w γ i) (f i)
        (resolutionLinearForm (b / P.areaScale) w i z)

variable [Fintype I]

/-- The theta value of the translate of a resolution product `F` by the finite image of a rational
vector `γ` is the product of the values at `0` of the translated factors. -/
lemma IsResolutionProduct.theta_translate {C : CMLattice P.d} {b : ℂ} {w : I → P.E s} {m : I → ℕ}
    {f : I × n → ℂ → ℂ} {F : 𝒮 V} (hF : IsResolutionProduct V C b w m f F) (γ : n → P.E s) :
    V.θ (V.ϱ (finVec (finiteImage γ)) F) =
      ∏ i : I × n, C.twistedTranslate (m i.1) (resolutionShift b w γ i) (f i) 0 := by
  simpa only [entireTheta_zero, map_zero] using hF.entireTheta_translate γ 0

/-- Let `V` be a standard space, `C` a lattice in `ℂ` with complex multiplication by the integers of
`K`, and `F` the resolution product of the entire functions `f i`: for every rational vector `γ`,
the function `entireTheta F'` of the translate `F' = V.ϱ (finVec (finiteImage γ)) F` is the product
over `i = (j, k)` of the functions `C.twistedTranslate (m j) l (f i)`, with
`l = -b * ∑ τ, Φ τ (γ k) * conj (Φ τ (w j))`, each at the linear form `z ↦ b / P.areaScale * ∑ τ,
conj (Φ τ (w j)) * z (τ, k)`. Here `C.twistedTranslate n l g` is `z ↦ exp (-n * π * (z * conj
l + |l|² / 2) / C.area) * g (z + l)`. Then `V.jetSeries c F'`, the Taylor series at `0` of
`z ↦ entireTheta F' (c • z)`, is the product of the Taylor series of these translated functions,
each evaluated at the linear form `b / P.areaScale * c * ∑ τ, conj (Φ τ (w j)) * X (τ, k)`. -/
lemma IsResolutionProduct.jetSeries_translate {C : CMLattice P.d} {b : ℂ} {w : I → P.E s}
    {m : I → ℕ} {f : I × n → ℂ → ℂ} {F : 𝒮 V} [hV : V.IsStd]
    (hF : IsResolutionProduct V C b w m f F) (γ : n → P.E s) (c : ℂ) :
    V.jetSeries c (V.ϱ (finVec (finiteImage γ)) F) =
      ∏ i : I × n, (taylorAtZero (C.twistedTranslate (m i.1) (resolutionShift b w γ i) (f i))).subst
        (linearSeries (resolutionFormCoeff (b / P.areaScale * c) w i)) := by
  obtain rfl : ε = 1 := hV.signs_eq_one
  have h_prod (z : InfinitePlace (P.E s) × n → ℂ) :
      entireTheta (V.ϱ (finVec (finiteImage γ)) F) (c • z) =
        ∏ i : I × n, C.twistedTranslate (m i.1) (resolutionShift b w γ i) (f i)
          (resolutionFormCoeff (b / P.areaScale * c) w i ⬝ᵥ z) := by
    simp [hF.entireTheta_translate, resolutionLinearForm_apply_eq_dotProduct, resolutionFormCoeff,
      dotProduct, mul_sum, mul_assoc, mul_left_comm]
  have hf : ∀ i : I × n, Differentiable ℂ (f i) := hF.differentiable
  exact jetSeries_eq_prod_of_entireTheta_smul (rho_finVec_mem_finitePart _ hF.mem_finitePart)
    (fun i ↦ by fun_prop) h_prod

/-- Let `δ δ̄ = N ≠ 0` for an integer `δ` of `K`, and let `b δ̄` lie in the lattice `C.Λ`. Let each
finite adele `finiteImage w j = α⁻¹ w j`, with `α = P.α s`, lie in the ring `Ô E` of integral adeles
of `E = P.E s`; that is, `w j` lies in `𝔞₀ = E ∩ α Ô`. Suppose that `F` is the resolution product of
the monomial sections `θ ^ r * (σ ^ 2) ^ t * G ^ u` of `C` with exponents `x i = (r, t, u)`, of
degree `r + 2 t + 3 u = m i.1`: the theta function of each rational translate of `F` is the product
of twisted translates of these sections, evaluated at linear forms. Here `θ` is the theta function
and `σ` the sigma function of `C`, and `G = translatedYThetaCube` is the entire function that equals
`C.translatedY * θ ^ 3` away from the poles of `C.translatedY`. Then the value of `F` at `finVec y`,
the adelic vector with finite part `α y` and real part zero, is integral at the `p`-adic place
`ιₚ : ℂ →+* ℂ_[p]`. -/
lemma IsResolutionProduct.norm_iota_apply_le_one {C : CMLattice P.d} {b : ℂ} {w : I → P.E s}
    {m : I → ℕ} {F : 𝒮 V} {x : I × n → ℕ × ℕ × ℕ} {δ : 𝓞 P.K} {N : ℕ}
    (hF : IsResolutionProduct V C b w m (fun i : I × n ↦ C.monomialSection (x i)) F) (hN_ne : N ≠ 0)
    (hN : δ * conj (δ : ℂ) = N) (hw : ∀ j : I, finiteImage w j ∈ Ô (P.E s))
    (hx : ∀ i : I × n, CMLattice.monomialDeg (x i) = m i.1) (hbδ_mem : b * conj (δ : ℂ) ∈ C.Λ)
    {p : ℕ} [Fact p.Prime] [PadicPlace p] (y : n → 𝔸f (P.E s)) : ‖ιₚ (F (finVec y))‖ ≤ 1 := by
  -- The value of `F` at `y` is the theta value of a translate, and `y` acts on `F` as the finite
  -- image of some rational `γ` does.
  obtain ⟨γ, -, hγ : V.ϱ (finVec (finiteImage γ)) F = V.ϱ (finVec y) F⟩ :=
    exists_finiteImage_approx hF.mem_finitePart y
  have h_value : F (finVec y) = ∏ i : I × n,
      C.twistedTranslate (m i.1) (resolutionShift b w γ i) (C.monomialSection (x i)) 0 := by
    rw [← theta_rho, ← hγ, hF.theta_translate γ]
  rw [h_value, map_prod, norm_prod]
  refine prod_le_one₀ (by simp) fun i _ ↦ ?_
  -- The shift is a torsion point: `L * finiteImage γ` is integral for some `L ≠ 0`, so `N * L`
  -- times the shift is a period.
  obtain ⟨L, hL, hLγ⟩ : ∃ L : ℕ, L ≠ 0 ∧ ∀ k : n, L * finiteImage γ k ∈ Ô (P.E s) :=
    exists_forall_mul_mem_Ô (finiteImage γ)
  have h_integral : finiteImage id (L * γ i.2) ∈ Ô (P.E s) := by
    simpa [finiteImage, mul_left_comm] using hLγ i.2
  let t : ℂ := ∑ τ : InfinitePlace (P.E s), Φ τ (L * γ i.2) * conj (Φ τ (w i.1))
  have h_period : b * conj (δ : ℂ) * t ∈ C.Λ :=
    mul_sum_mul_conj_mem_lattice hbδ_mem h_integral (hw i.1)
  have h_torsion : (N * L : ℕ) * resolutionShift b w γ i ∈ C.Λ := by
    rw [show (N * L : ℕ) * resolutionShift b w γ i = δ * -(b * conj (δ : ℂ) * t) by
      simp [t, resolutionShift, ← hN, mul_assoc, mul_left_comm b, ← mul_sum]]
    exact C.mul_mem_of_quadInt ⟨δ, rfl⟩ (neg_mem h_period)
  rw [← hx]
  exact C.hasIntegralValues_monomialSection (x i) _ ⟨N * L, mul_ne_zero hN_ne hL, h_torsion⟩

variable {C : CMLattice P.d} {b : ℂ} {w : I → P.E s} {m : I → ℕ} {f : I × n → ℂ → ℂ}

omit [DecidableEq n] in
/-- Let `w` be a tight frame of length `M` with multiplicities `m`: each `α⁻¹ * w j` is integral,
where `α = P.α s` is the finite idele of the Weil data, and `∑ j, m j * Φ σ (w j) * conj (Φ τ (w
j)) = M δ_{σ τ}`, where `Φ` is the CM type. Let the area `C.area` of a period parallelogram of `C`
be `|b|² M √d / 2`, with `d = P.d`. The forms `m j • C.hermitianForm`, where
`C.hermitianForm l z = (π / C.area) * conj l * z`, pulled back (`pullForm`) along the linear forms
of the frame at scale `b / P.areaScale`, sum to the standard hermitian form. -/
lemma sum_pullForm_resolutionLinearForm_apply {M : ℕ} (hw : IsTightFrame w m M)
    (h_area : C.area = ‖b‖ ^ 2 * M * √P.d / 2) (u v : InfinitePlace (P.E s) × n → ℂ) :
    (∑ i : I × n, pullForm (resolutionLinearForm (b / P.areaScale) w i) (m i.1 • C.hermitianForm)) u
      v =
      star u ⬝ᵥ v := by
  obtain ⟨hb, hM, hd⟩ : b ≠ 0 ∧ M ≠ 0 ∧ P.d ≠ 0 := by
    simpa [h_area, and_assoc] using (area_pos C.periodPair).ne'
  -- The area of `C` fixes the scale: the pull-back of `C.hermitianForm` carries the factor `1 / M`.
  have h_scale : Real.pi / C.area * (b / P.areaScale * conj (b / P.areaScale)) = (M : ℂ)⁻¹ := by
    simpa [h_area, ← mul_conj', areaScale, ← ofReal_pow √_, field, Real.pi_nonneg] using ⟨hb, hd⟩
  have h_term (j : I) (k : n) :
      pullForm (resolutionLinearForm (b / P.areaScale) w (j, k)) (m j • C.hermitianForm) u v =
        ∑ σ, ∑ τ, conj (u (τ, k)) * v (σ, k) / M * (m j * (Φ τ (w j) * conj (Φ σ (w j)))) := by
    simp only [div_eq_mul_inv _ (M : ℂ), ← h_scale]
    simp [resolutionLinearForm, mul_assoc, mul_comm, mul_left_comm]
  -- Multiply the frame identity at `(τ, σ)` by `conj (u (τ, k)) * v (σ, k) / M` and sum.
  calc (∑ i : I × n,
      pullForm (resolutionLinearForm (b / P.areaScale) w i) (m i.1 • C.hermitianForm)) u v
    _ = ∑ k, ∑ σ, ∑ τ, conj (u (τ, k)) * v (σ, k) / M *
        ∑ j, m j * (Φ τ (w j) * conj (Φ σ (w j))) := by
      simp [sum_prod_type_right, h_term, mul_sum, sum_comm (s := (univ : Finset I))]
    _ = star u ⬝ᵥ v := by simp [hw.sum_mul_conj, hM, dotProduct, sum_prod_type_right]

omit [DecidableEq n] in
/-- Let each `f i` be a section of degree `m i.1` of `C`: twisted translation
`C.twistedTranslate (m i.1) l` by a period `l` multiplies it by `C.multiplier l ^ m i.1`. Suppose
that the linear forms `A i` take `u` to periods, and let `B` be the sum of the pull-backs
(`pullForm`) of the forms `m i.1 • C.hermitianForm` along the `A i`. Then the normalized translation
by `u` fixes the product of the `f i ∘ A i`. -/
lemma normalizedShift_prod_comp_of_mem_lattice
    (hf : ∀ (i : I × n), ∀ l ∈ C.Λ, C.twistedTranslate (m i.1) l (f i) =
      C.multiplier l ^ m i.1 • f i)
    (A : I × n → (InfinitePlace (P.E s) × n → ℂ) →L[ℂ] ℂ) {u : InfinitePlace (P.E s) × n → ℂ}
    (hu : ∀ i : I × n, A i u ∈ C.Λ) :
    ThetaTori.normalizedShift (∑ i : I × n, pullForm (A i) (m i.1 • C.hermitianForm))
      (conj (quadGen P.d) • 1) u (∏ i : I × n, f i ∘ A i) = ∏ i : I × n, f i ∘ A i := by
  let B : RealComplexForm (InfinitePlace (P.E s) × n → ℂ) :=
    ∑ i, pullForm (A i) (m i.1 • C.hermitianForm)
  let χ : ℂ := ThetaTori.canonicalMultiplier B (conj (quadGen P.d) • 1) u
  -- The multipliers of the factors multiply to the canonical multiplier of `B`.
  have hχ : ∏ i, C.multiplier (A i u) ^ m i.1 = χ := by
    simp [χ, B, hu, multiplier_eq_canonicalMultiplier, ThetaTori.canonicalMultiplier,
      riemannForm_pullForm, ← exp_nsmul, ← exp_sum, mul_sum, mul_left_comm]
  have h_shift : B.thetaShift u (∏ i, f i ∘ A i) = χ • ∏ i, f i ∘ A i := by
    ext z
    simp [B, thetaShift_prod, hf, hu, ← hχ, prod_mul_distrib]
  change χ⁻¹ • B.thetaShift u (∏ i, f i ∘ A i) = _
  rw [h_shift, inv_smul_smul₀ (show χ ≠ 0 from exp_ne_zero _)]

end FrameProduct

/-- Let `V` be a standard space (signs `1`, point the identity). Let `δ δ̄ = N ≠ 0` for an integer
`δ` of `K`, and let `w` be a tight frame of length `M` with multiplicities `m`. Let
`x i = (r, t, u)` be exponents of degree `r + 2 t + 3 u = m i.1` (`monomialDeg`). Let `C` be a CM
lattice of area `|a|² M √d / (2 N)` that contains `a`. The monomial section of `x i` is
`θ ^ r * (σ ^ 2) ^ t * G ^ u`, with `θ` the theta function and `σ` the sigma function of `C`. Here
`G = translatedYThetaCube` is the entire function equal to `C.translatedY * θ ^ 3` away from poles.

There is a vector `F` that is the resolution product of these sections along `w` at scale `a / δ̄`.
That is, for every rational vector `γ`, the theta function of the translate of `F` by the finite
image of `γ` is the product of twisted translates of the sections, evaluated at the linear forms of
the frame. The values of `F` at finite adelic vectors are integral at every `p`-adic place `ιₚ` of
`ℂ`. Let `entireTheta F` be the theta function of `F`, as an entire function on `ℂ^(Φ × n)`. It is a
theta function for the lattice `δ̄ 𝔞₀ⁿ`. That is, it is entire and fixed by the translations
`signedShift γ` (the translation by `γ` times its sign `± 1`) along the lattice. -/
lemma exists_isResolutionProduct_of_isTightFrame (V : Space (P.E s) n ε) [hV : V.IsStd] {M N : ℕ}
    {I : Type} [Fintype I] {w : I → P.E s} {m : I → ℕ} (δ : 𝓞 P.K) (hN_ne : N ≠ 0)
    (hN : δ * conj (δ : ℂ) = N) (hw : IsTightFrame w m M) (x : I × n → ℕ × ℕ × ℕ)
    (hx : ∀ i : I × n, CMLattice.monomialDeg (x i) = m i.1)
    ⦃C : CMLattice P.d⦄ ⦃a : ℂ⦄ (ha : a ∈ C.Λ) (h_area : C.area = ‖a‖ ^ 2 / N * M * √P.d / 2) :
    ∃ F : 𝒮 V,
      IsResolutionProduct V C (a / conj (δ : ℂ)) w m (fun i : I × n ↦ C.monomialSection (x i)) F ∧
      (∀ (p : ℕ) [Fact p.Prime] [PadicPlace p] (y : n → 𝔸f (P.E s)), ‖ιₚ (F (finVec y))‖ ≤ 1) ∧
      IsThetaFunction (star (algebraMap P.K (P.E s) δ) • idealLattice (P.E s) n)
        (entireTheta F) := by
  -- The product `S` of the monomial sections, pulled back along the linear forms `A i`, is fixed
  -- by the signed translations along `δ̄ 𝔞₀ⁿ`, so by Fourier inversion it is `entireTheta F` for a
  -- vector `F`. Values of `F` are products of torsion values of monomials, which are integral.
  generalize hb : a / conj (δ : ℂ) = b
  have hδ : conj (δ : ℂ) ≠ 0 := right_ne_zero_of_mul (hN.trans_ne (Nat.cast_ne_zero.2 hN_ne))
  obtain rfl : a = b * conj (δ : ℂ) := (div_eq_iff hδ).1 hb
  obtain rfl : ε = 1 := hV.signs_eq_one
  let A (i : I × n) : (InfinitePlace (P.E s) × n → ℂ) →L[ℂ] ℂ :=
    resolutionLinearForm (b / P.areaScale) w i
  let B : RealComplexForm (InfinitePlace (P.E s) × n → ℂ) :=
    ∑ i, pullForm (A i) (m i.1 • C.hermitianForm)
  -- Isometry: the frame is tight of length `M`, and the area of `C` fixes the scale.
  have hB (u v : InfinitePlace (P.E s) × n → ℂ) : B u v = star u ⬝ᵥ v := by
    have h_norm : ‖(δ : ℂ)‖ ^ 2 = N := by exact_mod_cast (mul_conj' (δ : ℂ)).symm.trans hN
    refine sum_pullForm_resolutionLinearForm_apply hw ?_ u v
    rw [h_area, norm_mul, norm_conj, mul_pow, h_norm, mul_div_cancel_right₀ _ (mod_cast hN_ne)]
  let S : (InfinitePlace (P.E s) × n → ℂ) → ℂ := ∏ i, C.monomialSection (x i) ∘ A i
  have h_shift (i : I × n) (l : ℂ) (hl : l ∈ C.Λ) :
      C.twistedTranslate (m i.1) l (C.monomialSection (x i)) =
        C.multiplier l ^ m i.1 • C.monomialSection (x i) := by
    rw [← hx]
    exact thetaShift_of_mem (C.monomialSection_mem (x i)) hl
  have hS_diff : Differentiable ℂ S := by
    have hS : S = fun z ↦ ∏ i, C.monomialSection (x i) (A i z) := by
      ext z
      simp [S]
    rw [hS]
    fun_prop
  -- The forms `A i` take the real image of `δ̄ 𝔞₀ⁿ` to periods.
  have h_period (γ : n → P.E s) (hγ : γ ∈ idealLattice (P.E s) n) (i : I × n) :
      A i (realImage (star (algebraMap P.K (P.E s) δ) • γ)) ∈ C.Λ := by
    simpa [A, resolutionLinearForm_realImage, mul_assoc, ← mul_sum] using
      mul_sum_mul_conj_mem_lattice ha (hγ i.2) (hw.finiteImage_mem i.1)
  have hS_theta :
      IsThetaFunction (star (algebraMap P.K (P.E s) δ) • idealLattice (P.E s) n) S := by
    have h_form : fockForm (InfinitePlace (P.E s) × n) = B :=
      ContinuousLinearMap.ext fun u ↦ ContinuousLinearMap.ext fun v ↦ (hB u v).symm
    refine ⟨hS_diff, ?_⟩
    rintro - ⟨γ, hγ, rfl⟩
    have h_traceOne (v : P.Φ s) : Φ v (WeilData.traceOne : P.E s) = quadGen P.d := by
      rw [P.traceOne_eq_betaKInE]
      exact P.phi_algebraMap s v _
    rw [← normalizedShift_realImage (b := conj (quadGen P.d) • 1) (by simp [h_traceOne]), h_form]
    exact normalizedShift_prod_comp_of_mem_lattice h_shift A (h_period γ hγ)
  have hN_E : algebraMap P.K (P.E s) δ * star (algebraMap P.K (P.E s) δ) = N :=
    (Φ 1).injective (by simpa using hN)
  obtain ⟨F, hF, hΘ⟩ : ∃ F ∈ V.finitePart, entireTheta F = S :=
    V.exists_entireTheta_eq_of_isThetaFunction (coe_mem_Ô (algebraMap _ _ δ)) hN_ne hN_E hS_theta
  -- Translation by the finite image of `γ` shifts the factor `i` of `entireTheta F` by
  -- `-A i (realImage γ)`.
  have h_prod : IsResolutionProduct V C b w m (fun i ↦ C.monomialSection (x i)) F := by
    refine ⟨hF, fun i ↦ C.differentiable_monomialSection (x i), fun γ z ↦ ?_⟩
    rw [entireTheta_translate_finiteImage γ V hB, hΘ, thetaShift_prod]
    simp [A, resolutionLinearForm_realImage, resolutionShift]
  have h_int (p : ℕ) [Fact p.Prime] [PadicPlace p] (y : n → 𝔸f (P.E s)) :
      ‖ιₚ (F (finVec y))‖ ≤ 1 :=
    h_prod.norm_iota_apply_le_one hN_ne hN hw.finiteImage_mem hx ha y
  refine ⟨F, h_prod, h_int, ?_⟩
  rw [hΘ]
  exact hS_theta

end New.Parameters

end
