import Lib.CM.FiniteLattices
import Lib.Weil.Construction.CanonicalTheta
import New.Derivatives.Vacuum.TightFrames

/-!
# The integral vacuum θ°: integrality and bounds of its values, standard data at p

Fix the parameters `P`, the field `E = P.E s` and a hermitian space `V` of rank `n` over it. The
integral vacuum θ° = `New.Parameters.intVacuum` is the vacuum scaled by `vacuumScale ^ n`. The
factor `New.Parameters.vacuumScale` is provided by
`New.Parameters.exists_mul_vacElem_integral_bounded` for the standard space of rank one. To obtain
it, a multiple of the vacuum is written as a sum of translates of one vector. For a standard space,
the values of θ° at the points `New.finVec x` are integral at every prime, have bounded conjugates,
and are not all zero. A vector `f` is read as the function `f y = θ(ϱ(y) f)` of adelic vectors `y`.

## Main definitions and results

* `New.Parameters.IsThetaProduct`, `New.Parameters.exists_isThetaProduct`: a vector whose theta
  function is the product of theta functions of a CM lattice along the resolution of powers of `ζ`,
  that is, along the vectors `ζᵏ / q₁`, `k < q₁`, which form a tight frame of `E` over `K`.
* `New.Parameters.standardData V δ`: the module of standard data at a prime `p`. Its scalars are the
  complex numbers that the `p`-adic place sends to integers, and it is spanned by the translates
  `V.finHeisenbergOp x θ°`, for the `x` with `δ x` integral above `p`.
* `New.Parameters.norm_intVacuum_le_one`: the values of θ° at the points `New.finVec x` are integral
  at every prime.
* `New.Parameters.norm_ringEquiv_intVacuum_le`: their conjugates under the automorphisms of `ℂ` are
  bounded; `New.Parameters.norm_gal_intVacuum_le` is the case of automorphisms over `K`.
* `New.Parameters.norm_dataInner_self_le`: a bound for `f` at these points bounds its squared norm
  `New.Space.dataInner f f`, the mean of `|f y| ^ 2` over adelic vectors modulo rational ones.
* `New.Parameters.exists_isJetConjugate_translates`: the conjugates of the jets of the translates of
  one vector that generates the finite part.

Notions from other files:
* `New.Parameters`: The fixed parameters: a multiple `q₀` of `18480 = 16 · 3 · 5 · 7 · 11` and a
  prime `d` with `d ≡ q₀/2 - 1 mod q₀`.
* `New.Parameters.E`: The field E = K(ζ) obtained from K = ℚ(√-d) by adjoining a primitive root of
  unity ζ of order `P.q₁ s`.
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.Space.vacElem`: The vacuum: the product of the Gaussian and a twisted indicator of a lattice,
  as an element of 𝒮(V).
* `New.Space.IsStd`: The space `V` is standard: all its signs are `+1` and its point is the identity
  matrix.
-/

noncomputable section

namespace New.Parameters

/-! ## The integral vacuum in rank one -/

section RankOne

open Real NeZero Space CMLattice Finset Submodule MvPowerSeries Fintype Set Notation Pointwise

/-- The theta function `θ` of the CM lattice `cmCurve` (the lattice `Ω₀ 𝓞_K`, `Ω₀ = cmPeriod`) is
the translate of its sigma function by a point of order two, normalised to `θ 0 = 1`. The twisted
translate `twistedTranslate 1 u θ`, of degree one, is `z ↦ exp (-π (z ū + |u|² / 2) / A) θ (z + u)`,
with `A` the area of the lattice. For the torsion points `u = x Ω₀`, `x ∈ K`, the conjugates over
`K` of its values at `z = 0` are bounded. -/
lemma exists_norm_gal_torsion_value_le (P : Parameters) : ∃ M : ℝ, ∀ (σ : Gal(ℂ/K P)) (x : K P),
    ‖σ (P.cmCurve.twistedTranslate 1 (x * P.cmPeriod) P.cmCurve.θ 0)‖ ≤ M := by
  -- By complex multiplication they are torsion values for the conjugate lattices.
  obtain ⟨M, hM⟩ := exists_norm_twistedTranslate_theta_le P.d
  refine ⟨M, fun σ x ↦ ?_⟩
  obtain ⟨Ω, -, β, -, -, -, -, hβ⟩ := complex_multiplication_theta P.cmCurve σ latticeModule_cmCurve
  -- For `x'` near `β x`, `σ` maps the Taylor series of the translate by `x cmPeriod` to that of the
  -- translate by `x' Ω`; compare the constant terms.
  obtain ⟨U, hU, h_translate⟩ := hβ x
  obtain ⟨x', hx'⟩ := denseRange_algebraMap_finAdele.mem_nhds hU
  have h_value : σ (P.cmCurve.twistedTranslate 1 (x * P.cmPeriod) P.cmCurve.θ 0) =
      (P.cmCurve.galConjugate σ).twistedTranslate 1 (x' * Ω) (P.cmCurve.galConjugate σ).θ 0 := by
    simpa using congrArg PowerSeries.constantCoeff (h_translate x' hx')
  grw [h_value, hM]

/-- Let `E` be a CM field with Weil data (the element `ȷ`, the idele `α` and the splitting character
that define the Weil representation), let `V` be standard and let `δ` be integral (in the finite
adelic integers `Ô E`) with `δ δ̄ = N ≠ 0`. Suppose that the theta functional `V.θ` takes the value
`1` at `F` and that `entireTheta F` is a theta function for `δ̄ 𝔞₀ⁿ`, that is, an entire function
fixed by the signed translations along `δ̄ 𝔞₀ⁿ`. Here `idealLattice E n = 𝔞₀ⁿ` is the lattice of
the rational vectors `γ` with `α⁻¹ γ` integral at all finite places. Then a nonzero multiple of the
vacuum is a sum of `N ^ (f n)` translates `finHeisenbergOp (a j) (ϱ(finVec b) F)`. Here `f` is the
number of infinite places, `n` the rank, `ϱ` the action of adelic vectors, and `finHeisenbergOp x`
is `ϱ(finVec x)` times the scalar `stdLattice.semichar x`. -/
lemma exists_smul_vac_eq_sum {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n]
    [DecidableEq n] {ε : n → ℤˣ} {V : Space E n ε} [V.IsStd] {δ : E} {N : ℕ}
    (hδ : ↑δ ∈ Ô E) (hN_ne : N ≠ 0) (hN : δ * star δ = N) {F : 𝒮 V}
    (hF : IsThetaFunction (star δ • idealLattice E n) (entireTheta F)) (hθ : V.θ F = 1) :
    ∃ c ≠ (0 : ℂ), ∃ (Γ : Type) (_ : Fintype Γ) (a : Γ → n → 𝔸f E) (b : n → 𝔸f E),
      card Γ = N ^ card (NumberField.InfinitePlace E × n) ∧
      c • V.vacElem = ∑ j : Γ, V.finHeisenbergOp (a j) (V.ϱ (finVec b) F) := by
  obtain ⟨Y, Γ, _, _, y, γ, c, -, -, h_card, h_average, h_inversion⟩ :=
    V.exists_fourier_coefficients hδ hN_ne hN hF
  -- `h_average`: each `c i • vacElem` is a sum of translates of `F`; `h_inversion`: `F` times a
  -- power of `N` is the combination of translates of the vacuum with the coefficients `c i`.
  -- As `θ F = 1`, some Fourier coefficient is nonzero.
  obtain ⟨i, hi⟩ : ∃ i : Y, c i ≠ 0 := by
    by_contra! h_zero
    simpa [h_zero, hθ, hN_ne] using (congrArg V.θ h_inversion).symm
  exact ⟨c i, hi, Γ, inferInstance, _, _, h_card, h_average i⟩

/-- The coordinate `-u† y ∈ K` of `y ∈ E` along the vector `u = ζᵏ / q₁` of the frame of powers of
`ζ`, that is minus the trace from `E` to `K` of `y * star ζᵏ`, divided by `q₁`. -/
noncomputable def zetaCoord (P : Parameters) (s : ℕ) (k : Fin (P.q₁ s)) (y : P.E s) : K P :=
  -Algebra.trace P.K (P.E s) (y * star (P.ζ s ^ k.val)) / P.q₁ s

/-- The coordinate along a vector of the frame commutes with multiplication by elements of `K`. -/
lemma zetaCoord_smul {P : Parameters} {s : ℕ} (k : Fin (P.q₁ s)) (a : K P) (y : P.E s) :
    P.zetaCoord s k (a • y) = a * P.zetaCoord s k y := by
  simp [zetaCoord, mul_div_assoc']

section ThetaProduct

variable {P : Parameters} {s : ℕ} {n : Type} [Fintype n] {ε : n → ℤˣ}

/-- The twisted translate of the theta function of the CM lattice `C` by `Ω` times the coordinate
of `y ∈ E` along the vector `ζᵏ / q₁` of the frame of powers of `ζ`. -/
def zetaCoordThetaTranslate (C : CMLattice P.d) (Ω : ℂˣ) (k : Fin (P.q₁ s)) (y : P.E s) : ℂ → ℂ :=
  C.twistedTranslate 1 (P.zetaCoord s k y * Ω) C.θ

/-- The linear form along the frame vector `ζᵏ / q₁` in the coordinate `j`, for the period `Ω` and
the scale `c`: the power series `Ω / q₁ / areaScale * c * ∑ w, conj (Φ w ζᵏ) * z (w, j)` in
variables `z` indexed by infinite places of `E` and coordinates. Here `areaScale = √(2π / √d)`,
`Φ w` is the complex embedding chosen at the place `w`, and `linearSeries a` is `∑ y, a y * z y`. -/
def zetaLinearSeries [DecidableEq n] (Ω : ℂˣ) (c : ℂ) (k : Fin (P.q₁ s)) (j : n) :
    MvPowerSeries (NumberField.InfinitePlace (P.E s) × n) ℂ :=
  linearSeries fun y : NumberField.InfinitePlace (P.E s) × n ↦ if y.2 = j then
    Ω.val / P.q₁ s / P.areaScale * c * starRingEnd ℂ (Φ y.1 (P.ζ s ^ k.val)) else 0

/-- The vector `F` is the product of copies of the theta function of `C` along the frame of the
`ζᵏ / q₁`, each taken `q₁` times, in every coordinate. The period `Ω` scales the coordinates along
the frame to complex numbers, and the level `e` gives the lattice `q₁ e 𝔞₀ⁿ` of periods, where
`𝔞₀ⁿ = idealLattice E n` consists of the rational vectors `γ` with `α⁻¹ γ` integral, `α` being the
idele of the Weil data and `q₁` the order of `ζ`. -/
structure IsThetaProduct [DecidableEq n] (V : Space (P.E s) n ε) (C : CMLattice P.d) (Ω : ℂˣ)
    (e : ℕ+) (F : 𝒮 V) : Prop where
  /-- The vector lies in the finite part, the span of the translates of the vacuum by the operators
  `finHeisenbergOp`. -/
  mem_finitePart : F ∈ V.finitePart
  /-- The theta value of the translate by a rational vector `γ` is a product of values at `0` of
  twisted translates of the theta function of `C`. Here `finiteImage γ` is the finite adelic vector
  `α⁻¹ γ`, with `α` the idele of the Weil data. -/
  theta_translate (γ : n → P.E s) : V.θ (V.ϱ (finVec (finiteImage γ)) F) =
    ∏ k : Fin (P.q₁ s), ∏ j : n, zetaCoordThetaTranslate C Ω k (γ j) 0 ^ P.q₁ s
  /-- The series of jets `jetSeries c` of that translate (for a standard space, the Taylor series at
  `0` of its theta function at the scale `c`) is a product of Taylor series `taylorAtZero` at `0` of
  functions of one variable, each composed with a linear form. -/
  jetSeries_translate (γ : n → P.E s) (c : ℂ) :
    V.jetSeries c (V.ϱ (finVec (finiteImage γ)) F) = ∏ k : Fin (P.q₁ s), ∏ j : n,
      (taylorAtZero (zetaCoordThetaTranslate C Ω k (γ j))).subst (zetaLinearSeries Ω c k j) ^ P.q₁ s
  /-- The values at finite points are integral at every prime `p`, for every `p`-adic place of `ℂ`
  (a ring homomorphism `ιₚ` from `ℂ` to `ℂ_[p]`). -/
  norm_le_one (p : ℕ) [Fact p.Prime] [PadicPlace p] (x : n → 𝔸f (P.E s)) : ‖ιₚ (F (finVec x))‖ ≤ 1
  /-- The theta function of the vector is a theta function for `q₁ e 𝔞₀ⁿ`. -/
  isThetaFunction :
    IsThetaFunction (star (P.q₁ s * e : P.E s) • idealLattice (P.E s) n) (entireTheta F)

/-- The theta functional takes the value `1` at a theta product. -/
lemma IsThetaProduct.theta_eq_one [DecidableEq n] {V : Space (P.E s) n ε} {C : CMLattice P.d}
    {Ω : ℂˣ} {e : ℕ+} {F : 𝒮 V} (hF : IsThetaProduct V C Ω e F) : V.θ F = 1 := by
  simpa [zetaCoordThetaTranslate, zetaCoord] using hF.theta_translate 0

/-- Let `V` be standard and let `C` be a CM lattice of area `|Ω|² √d / 2` that contains a multiple
`Ω e`. Then `V` has a theta product for `C`, `Ω` and `e`. -/
lemma exists_isThetaProduct [DecidableEq n] (V : Space (P.E s) n ε) [V.IsStd] {C : CMLattice P.d}
    {Ω : ℂˣ} {e : ℕ+} (he : Ω.val * e ∈ C.Λ) (h_area : C.area = ‖Ω.val‖ ^ 2 * √P.d / 2) :
    ∃ F : 𝒮 V, IsThetaProduct V C Ω e F := by
  -- Apply `exists_isResolutionProduct_of_isTightFrame` to `δ = q₁ e`, the frame of the repeated
  -- powers of `ζ` and the monomial `θ` of degree one.
  let δ : NumberField.RingOfIntegers P.K := P.q₁ s * e
  obtain ⟨F, hF, h_int, h_periods⟩ := exists_isResolutionProduct_of_isTightFrame V δ
    (ne ((P.q₁ s * e) ^ 2)) (by simp [δ, sq]) (P.isTightFrame_zeta_pow s (P.q₁ s)).repeat_vectors
    (fun _ ↦ (1, 0, 0)) (by simp) he (by simp [h_area, field, ne])
  have h_scale : Ω.val * e / starRingEnd ℂ δ = Ω.val / P.q₁ s := by simp [δ, field]
  have h_coord (k : Fin (P.q₁ s)) (y : P.E s) :
      Ω.val / P.q₁ s * -∑ τ, Φ τ y * starRingEnd ℂ (Φ τ (P.ζ s ^ k.val)) =
        P.zetaCoord s k y * Ω := by
    simp [zetaCoord, coe_trace_eq_sum, starRingEnd_apply, ← map_star_complex, field]
  -- With these two identities the values and series of `hF` are those of a theta product; the
  -- repeated frame vectors give the powers.
  refine ⟨F, hF.mem_finitePart, fun γ ↦ ?_, fun γ c ↦ ?_, h_int, by simpa [δ] using h_periods⟩
  · simp [hF.theta_translate, h_scale, ← h_coord, resolutionShift, monomialSection,
      Fintype.prod_prod_type, Fintype.prod_sigma, Finset.prod_pow, zetaCoordThetaTranslate]
  · simp +unfoldPartialApp [hF.jetSeries_translate, h_scale, ← h_coord, resolutionShift,
      monomialSection, resolutionFormCoeff, Fintype.prod_prod_type, Fintype.prod_sigma,
      Finset.prod_pow, zetaCoordThetaTranslate, zetaLinearSeries]

/-- A standard space has a theta product of level one for the lattice `cmPeriod 𝓞_K` of
`cmCurve`. -/
lemma exists_isThetaProduct_cmCurve [DecidableEq n] (V : Space (P.E s) n ε) [V.IsStd] :
    ∃ F : 𝒮 V, IsThetaProduct V P.cmCurve P.cmPeriod 1 F :=
  exists_isThetaProduct V (by simpa using cmPeriod_mem_cmCurve_lattice)
    (by simp [QuadField.area_eq_of_eq_scaledIdeal latticeModule_cmCurve])

/-- A theta product of level one for `C` and `Ω` is a vector `F` of the finite part whose theta
values and jets at rational translates are those of products of the theta function of `C` along the
vectors `ζᵏ / q₁`, with `q₁` the order of `ζ`, and whose theta function is a theta function for
`q₁ 𝔞₀ⁿ`. In a standard space of rank `n`, a nonzero multiple of the vacuum is then a sum of
`(q₁ ^ 2) ^ (f n)` vectors `finHeisenbergOp (a j) (ϱ(finVec b) F)`, with `f` the number of infinite
places: each is `F` translated by the common finite vector `b`, then by `a j`, and multiplied by the
scalar `stdLattice.semichar (a j)`. -/
lemma IsThetaProduct.exists_smul_vacElem_eq_sum [DecidableEq n] {V : Space (P.E s) n ε} [V.IsStd]
    {C : CMLattice P.d} {Ω : ℂˣ} {F : 𝒮 V} (hF : IsThetaProduct V C Ω 1 F) :
    ∃ c ≠ (0 : ℂ), ∃ (Γ : Type) (_ : Fintype Γ) (a : Γ → n → 𝔸f (P.E s)) (b : n → 𝔸f (P.E s)),
      card Γ = (P.q₁ s ^ 2) ^ card (NumberField.InfinitePlace (P.E s) × n) ∧
      c • V.vacElem = ∑ j : Γ, V.finHeisenbergOp (a j) (V.ϱ (finVec b) F) :=
  exists_smul_vac_eq_sum (δ := (P.q₁ s * (1 : ℕ+) : P.E s)) (by simp [mul_mem])
    (ne (P.q₁ s ^ 2)) (by simp [sq]) hF.isThetaFunction hF.theta_eq_one

end ThetaProduct

/-- With `f` the number of infinite places of `E = P.E s` and `q₁ = P.q₁ s`, one has
`(q₁ ^ 2) ^ f ≤ exp (q₁) ^ (2 * q₁)`. -/
lemma sq_q₁_pow_card_infinitePlace_le (P : Parameters) (s : ℕ) :
    (((P.q₁ s ^ 2) ^ card (NumberField.InfinitePlace (P.E s) × Unit) : ℕ) : ℝ) ≤
      rexp (P.q₁ s) ^ (2 * P.q₁ s) := by
  -- The number of infinite places is at most `q₁`, and `q₁ ≤ exp q₁`.
  have hf : card (NumberField.InfinitePlace (P.E s) × Unit) ≤ P.q₁ s := by
    grw [card_prod, card_unit, mul_one, ← Core.numInfPlaces, numInfPlaces_E, Nat.totient_le,
      mul_comm]
  have h_exp : (P.q₁ s : ℝ) ≤ rexp (P.q₁ s) := by linarith [add_one_le_exp (P.q₁ s : ℝ)]
  grw [hf, ← pow_mul, Nat.cast_pow, h_exp]
  exact one_le_pow₀ NeZero.one_le

/-- The integral vacuum in rank one: a nonzero multiple of the vacuum has values at the finite
points `finVec x` that are integral (`ιₚ` is the map to the `p`-adic complex numbers) and whose
conjugates over `K` have modulus at most `exp (C q₁²)`, with `C` independent of `s`. -/
lemma exists_mul_vacElem_integral_bounded (P : Parameters) : ∃ C : ℕ, ∀ s : ℕ, ∃ c ≠ (0 : ℂ),
    -- (a) the values are integral
    (∀ (p : ℕ) [Fact p.Prime] [PadicPlace p] (x : Unit → 𝔸f (P.E s)),
      ‖ιₚ (c * (stdSpace (P.E s) Unit).vacElem (finVec x))‖ ≤ 1) ∧
    -- (b) their conjugates are bounded
    ∀ (σ : Gal(ℂ/K P)) (x : Unit → 𝔸f (P.E s)),
      ‖σ (c * (stdSpace (P.E s) Unit).vacElem (finVec x))‖ ≤ rexp (C * P.q₁ s ^ 2) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ (σ : Gal(ℂ/K P)) (x : K P),
      ‖σ (P.cmCurve.twistedTranslate 1 (x * P.cmPeriod) P.cmCurve.θ 0)‖ ≤ M :=
    exists_norm_gal_torsion_value_le P
  refine ⟨⌈M⌉₊ + 2, fun s ↦ ?_⟩
  set N : ℕ := P.q₁ s
  let V : Space (P.E s) Unit 1 := stdSpace (P.E s) Unit
  -- The vector `F` is the theta product for the lattice of `cmCurve` with the period `cmPeriod`.
  obtain ⟨F, hF : IsThetaProduct V P.cmCurve P.cmPeriod 1 F⟩ := exists_isThetaProduct_cmCurve V
  obtain ⟨c, hc_ne, Γ, _, a, b, h_card, hc⟩ := hF.exists_smul_vacElem_eq_sum
  -- A value of `c • vacElem` is a sum of `card Γ` values of `F` times roots of unity.
  have h_sum (x : Unit → 𝔸f (P.E s)) :
      ∃ (w : Γ → 𝔸f (P.E s)) (y : Γ → Unit → 𝔸f (P.E s)), c * V.vacElem (finVec x) =
        ∑ k, stdLattice.selfDualAddChar (P.E s) (w k) * F (finVec (y k)) := by
    simpa only [← hc, V.smul_apply] using V.exists_sum_finHeisenbergOp_apply_eq a b x F
  choose w y h_sum using h_sum
  -- A value of `F` is a product of `N²` torsion values of `θ`.
  have h_value (σ : Gal(ℂ/K P)) (z : Unit → 𝔸f (P.E s)) :
      ‖σ (F (finVec z))‖ ≤ rexp M ^ (N * N) := by
    obtain ⟨γ, hγ⟩ : ∃ γ : Unit → P.E s, ratShift γ (entireTheta F) 0 = F (finVec z) :=
      (V.range_apply_finVec_eq_range_ratShift_entireTheta hF.mem_finitePart).le ⟨z, rfl⟩
    have h_theta : F (finVec z) = V.θ (V.ϱ (finVec (finiteImage (-γ))) F) := by
      rw [← entireTheta_zero, V.entireTheta_rho, neg_neg, hγ]
    calc ‖σ (F (finVec z))‖
      _ = ∏ k : Fin N, ‖σ (zetaCoordThetaTranslate P.cmCurve P.cmPeriod k (-γ ()) 0)‖ ^ N := by
        rw [h_theta, hF.theta_translate]
        simp [N]
      _ ≤ ∏ _k : Fin N, rexp M ^ N := by
        gcongr
        exact (hM σ _).trans (by linarith [add_one_le_exp M])
      _ = rexp M ^ (N * N) := by simp [pow_mul]
  refine ⟨c, hc_ne, fun p _ _ x ↦ ?_, fun σ x ↦ ?_⟩
  · exact V.norm_mul_vacElem_le_one_of_eq_sum (hF.norm_le_one p) hc x
  · calc ‖σ (c * V.vacElem (finVec x))‖
      _ ≤ ∑ k : Γ, ‖σ (F (finVec (y x k)))‖ := by
        grw [h_sum, map_sum, norm_sum_le]
        simp [norm_map_selfDualAddChar]
      _ ≤ card Γ * rexp M ^ (N * N) := (sum_le_sum fun k _ ↦ h_value σ _).trans_eq (by simp)
      _ ≤ rexp N ^ (2 * N) * rexp ⌈M⌉₊ ^ (N * N) := by
        grw [h_card, sq_q₁_pow_card_infinitePlace_le P s, ← Nat.le_ceil M]
      _ = rexp ((⌈M⌉₊ + 2 : ℕ) * N ^ 2) := by
        simp only [← exp_nat_mul, ← exp_add]
        grind

/-- The constant `C` in the bound `exp (C q₁²)` for the conjugates of the values of the integral
vacuum of rank one, chosen from `exists_mul_vacElem_integral_bounded`; see `IsVacuumScale`. -/
def vacuumBoundConst (P : Parameters) : ℕ := P.exists_mul_vacElem_integral_bounded.choose

end RankOne

/-!
## The integral vacuum θ° and the module of standard data at p

These are the data to which the integrality of jets (`New.Parameters.norm_jet_jetSeries_le_one`)
applies.
-/

section StandardDataDefs

open NumberField Valued Submodule Fintype

/-- The scalar `c` normalises the vacuum of the standard space of rank one: it is nonzero, and the
values of `c • vacElem` at finite points are integral with bounded conjugates. -/
structure IsVacuumScale (P : Parameters) (s : ℕ) (c : ℂ) : Prop where
  /-- The scalar is nonzero. -/
  ne_zero : c ≠ 0
  /-- The values of `c • vacElem` are integral at every prime. -/
  norm_le_one (p : ℕ) [Fact p.Prime] [PadicPlace p] (x : Unit → 𝔸f (P.E s)) :
    ‖ιₚ (c * (stdSpace (P.E s) Unit).vacElem (finVec x))‖ ≤ 1
  /-- Their conjugates over `K` have norm at most `exp (C * q₁ ^ 2)`, where `C` is
  `vacuumBoundConst`. -/
  norm_gal_le (σ : Gal(ℂ/P.K)) (x : Unit → 𝔸f (P.E s)) :
    ‖σ (c * (stdSpace (P.E s) Unit).vacElem (finVec x))‖ ≤
      Real.exp (P.vacuumBoundConst * P.q₁ s ^ 2)

/-- The nonzero number by which the vacuum of rank one is multiplied to have integral values with
bounded conjugates, chosen from `exists_mul_vacElem_integral_bounded`. -/
def vacuumScale (P : Parameters) (s : ℕ) : ℂ :=
  (P.exists_mul_vacElem_integral_bounded.choose_spec s).choose

theorem isVacuumScale_vacuumScale (P : Parameters) (s : ℕ) :
    P.IsVacuumScale s (P.vacuumScale s) := by
  obtain ⟨h_ne, h_int, h_conj⟩ := (P.exists_mul_vacElem_integral_bounded.choose_spec s).choose_spec
  exact ⟨h_ne, h_int, h_conj⟩

variable {P : Parameters} {s : ℕ} {n : Type*} [Fintype n] [DecidableEq n] {ε : n → ℤˣ}
  (V : Space (P.E s) n ε)

/-- The integral vacuum: the vacuum of a space of rank `n` times `vacuumScale ^ n`. -/
def intVacuum : 𝒮 V := P.vacuumScale s ^ card n • V.vacElem

/-- The additive subgroup of vectors `x` of finite adeles that are integral after multiplication by
`δ`: all coordinates of `δ x` are integral at the places of `E` in `S`. Here `evalAt w` is the
component at the place `w`, and `v` is the valuation of the completion at `w`. -/
def integralAfter (δ : 𝓞 P.K) (S : FinPlace (P.E s) → Prop) : AddSubgroup (n → 𝔸f (P.E s)) where
  carrier := {x : n → 𝔸f (P.E s) | ∀ (i : n) (w : FinPlace (P.E s)), S w →
    v (evalAt w (algebraMap P.K (P.E s) δ * x i)) ≤ 1}
  zero_mem' := by simp
  add_mem' hx hy i w hw := by simpa [mul_add] using v.map_add_le (hx i w hw) (hy i w hw)
  neg_mem' hx i w hw := by simpa using hx i w hw

/-- Standard data at `p`: the span over the ring `embValRing` (the complex numbers that the
`p`-adic place sends to integers) of the translates of the integral vacuum by the points that `δ`
makes integral above `p`. -/
def standardData {p : ℕ} [Fact p.Prime] [PadicPlace p] (δ : 𝓞 P.K) : Submodule embValRing (𝒮 V) :=
  span embValRing {V.finHeisenbergOp x (intVacuum V) | x ∈ integralAfter δ fun w ↦ ↑p ∈ w.asIdeal}

end StandardDataDefs

/-!
## Integrality, bounds and nonvanishing of the values of θ°

The point `New.finVec x` has finite part a fixed multiple of `x` and archimedean part zero.

`Gal(ℂ/K)` is the group of automorphisms of `ℂ` over `K = ℚ(√-d)`.
-/

section IntegralVacuum

open Fintype Space

@[simp] lemma vacuumScale_ne_zero (P : Parameters) (s : ℕ) : vacuumScale P s ≠ 0 :=
  (P.isVacuumScale_vacuumScale s).ne_zero

variable {P : Parameters} {s : ℕ} {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ}
  {V : Space (P.E s) n ε} [V.IsStd]

/-- At a finite point `finVec x`, the integral vacuum of a standard space is the product over the
coordinates `x i` of the values of the scaled vacuum of rank one. -/
lemma intVacuum_finVec_eq_prod {x : n → 𝔸f (P.E s)} : intVacuum V (finVec x) =
    ∏ i : n, P.vacuumScale s * (stdSpace (P.E s) Unit).vacElem (finVec fun _ : Unit ↦ x i) := by
  simp [intVacuum, vacElem_apply_eq_prod_lineTheta, IsStd.signs_eq_one V, IsStd.point_eq_one,
    finVec, signedSpace, vecAtPoint, Finset.prod_mul_distrib]

/-- The values of the integral vacuum of rank `n` at the points `finVec x`, with archimedean part
zero, are integral at every prime. -/
lemma norm_intVacuum_le_one {x : n → 𝔸f (P.E s)} {p : ℕ} [Fact p.Prime] [PadicPlace p] :
    ‖ιₚ (intVacuum V (finVec x))‖ ≤ 1 := by
  rw [intVacuum_finVec_eq_prod, map_prod, norm_prod]
  exact Finset.prod_le_one₀ (by simp) fun _ _ ↦ (P.isVacuumScale_vacuumScale s).norm_le_one p _

/-- The conjugates over `K` of the values of the integral vacuum of rank `n` have modulus at most
`exp (C q₁² n)`, with the constant `C = vacuumBoundConst` of the case of rank one. -/
lemma norm_gal_intVacuum_le {x : n → 𝔸f (P.E s)} (σ : Gal(ℂ/K P)) :
    ‖σ (intVacuum V (finVec x))‖ ≤ Real.exp (P.vacuumBoundConst * P.q₁ s ^ 2) ^ card n := by
  rw [intVacuum_finVec_eq_prod, map_prod, norm_prod, ← Finset.card_univ, ← Finset.prod_const]
  gcongr with i
  exact (P.isVacuumScale_vacuumScale s).norm_gal_le σ _

open NumberField InfinitePlace in
/-- Every automorphism of `ℂ` has the same absolute values as some automorphism over the
imaginary quadratic field `K`. -/
lemma exists_algEquiv_norm_eq (P : Parameters) (σ : ℂ ≃+* ℂ) :
    ∃ σ' : Gal(ℂ/P.K), ∀ z : ℂ, ‖σ z‖ = ‖σ' z‖ := by
  -- The field `P.K` has one infinite place: on it, `σ` or its complex conjugate is the inclusion.
  let φ : P.K →+* ℂ := RingHom.domRestrict (σ : ℂ →+* ℂ) P.K
  obtain h_fix | h_conj : φ = P.K.subtype ∨ ComplexEmbedding.conjugate φ = P.K.subtype :=
    mk_eq_iff.1 (Subsingleton.elim _ _)
  · exact ⟨.ofRingEquiv (f := σ) (RingHom.congr_fun h_fix), fun _ ↦ rfl⟩
  · exact ⟨.ofRingEquiv (f := σ.trans starRingAut) (RingHom.congr_fun h_conj),
      fun z ↦ (norm_star (σ z)).symm⟩

/-- All conjugates `σ (intVacuum V (finVec x))` under automorphisms `σ` of `ℂ` of the values at
`finVec x` of the integral vacuum of the standard space `V` of rank `card n` have modulus at most
`exp (C q₁²) ^ card n`. Here `q₁ = P.q₁ s` and `C = vacuumBoundConst` is the constant of the case of
rank one. -/
lemma norm_ringEquiv_intVacuum_le {x : n → 𝔸f (P.E s)} (σ : ℂ ≃+* ℂ) :
    ‖σ (intVacuum V (finVec x))‖ ≤ Real.exp (P.vacuumBoundConst * P.q₁ s ^ 2) ^ card n := by
  obtain ⟨σ', hσ'⟩ := P.exists_algEquiv_norm_eq σ
  exact (hσ' _).trans_le (norm_gal_intVacuum_le σ')

/-- Let a vector `f` of a standard space be read as the function `f y = θ(ϱ(y) f)` of an adelic
vector `y`, with `θ` the theta functional. If `|f|` is at most `M` at all points `finVec x`, whose
archimedean part is zero, then `dataInner f f`, the mean of `|f|²`, has modulus at most `M ^ 2`. -/
lemma norm_dataInner_self_le {f : 𝒮 V} {M : ℝ}
    (h_bound : ∀ x : n → 𝔸f (P.E s), ‖f (finVec x)‖ ≤ M) :
    ‖V.dataInner f f‖ ≤ M ^ 2 := by
  -- `dataInner f f` is the mean of `|f| ^ 2`. By continuity it is enough to bound `f` at points
  -- whose archimedean part is rational. Translating by a rational vector changes `f` by a factor
  -- of norm one (`apply_vecAtPoint_add`) and moves such a point to one with archimedean part zero.
  suffices h_pointwise : ∀ y : n → 𝔸 (P.E s), ‖f y * starRingEnd ℂ (f y)‖ ≤ M ^ 2 by
    rw [V.dataInner_eq_quotMean]
    exact norm_quotMean_le _ h_pointwise
  refine isClosed_property (.piMap fun _ ↦ denseRange_Φ.prodMap denseRange_id)
    (isClosed_le (by fun_prop) continuous_const) fun (p : n → P.E s × 𝔸f (P.E s)) ↦ ?_
  let γ (i : n) : P.E s := -(p i).1
  let x : n → 𝔸f (P.E s) := finCoord fun i ↦ (0, (γ i : 𝔸f (P.E s)) + (p i).2)
  have h_point : V.vecAtPoint γ + Pi.map (fun _ ↦ Prod.map (RingHom.pi Φ) id) p = finVec x := by
    simp [γ, x, vecAtPoint, IsStd.point_eq_one, finVec.eq_unfold, funext_iff, Prod.add_def]
  rw [← V.apply_vecAtPoint_add _ γ, h_point]
  simpa [sq, Heisenberg.norm_eq_one] using pow_le_pow_left₀ (norm_nonneg _) (h_bound x) 2

/-- For a standard space `V`, there is a finite adelic vector `x` such that the integral vacuum
`intVacuum V` is nonzero at the point `finVec x`. -/
lemma exists_intVacuum_ne_zero : ∃ x : n → 𝔸f (P.E s), intVacuum V (finVec x) ≠ 0 := by
  -- Otherwise the vacuum vanishes at all points `finVec x`, and `norm_dataInner_self_le` with
  -- `M = 0` contradicts its norm being `1`.
  by_contra! h_zero
  have h_le : ‖V.dataInner V.vacElem V.vacElem‖ ≤ 0 ^ 2 :=
    norm_dataInner_self_le fun x ↦ by simpa [intVacuum] using h_zero x
  norm_num [V.dataInner_vacElem_vacElem] at h_le

end IntegralVacuum

/-!
## Conjugates of the jets of the translates of one vector

The product of copies of the theta function along the vectors `ζᵏ / q₁` (the resolution of powers
of `ζ`) also serves to compute the action of the automorphisms of `ℂ` over `K` on jets.
-/

section ConjugateTranslates

open Real NeZero Space CMLattice Finset Submodule MvPowerSeries Fintype Set Notation Pointwise

/-- The number `bigOmega P s`, which is `exp (chowlaSelbergConst d) * 2π / rootDiscr E`, is
positive. Here `chowlaSelbergConst d` is `γ - Re L'/L(1, χ_K)`, with `γ` Euler's constant. -/
lemma bigOmega_pos {P : Parameters} {s : ℕ} : 0 < bigOmega P s := by
  simp [bigOmega, rootDiscr_pos, pi_pos, exp_pos]

/-- The scale `jetScale = periodFactor * areaScale / cmPeriod`, at which the Taylor series of theta
functions are taken, is nonzero. -/
@[simp] lemma jetScale_ne_zero {P : Parameters} {s : ℕ} : jetScale P s ≠ 0 := by
  -- `periodFactor` is the quotient of `vacuumRoot` by the unit `chowlaSelbergUnit` of the formula
  -- of Chowla and Selberg, and both are nonzero by their norms.
  have h_root : P.vacuumRoot s ≠ 0 := fun h_zero ↦ by
    simpa [h_zero, ne_of_gt, rootDiscr_pos, ne] using (P.norm_gal_vacuumRoot s 1).symm
  have h_unit : P.chowlaSelbergUnit ≠ 0 := fun h_zero ↦ by
    simpa [h_zero, pi_ne_zero, ne] using P.area_mul_norm_chowlaSelbergUnit_sq 1
  simp [jetScale, periodFactor, h_root, h_unit]

/-- Let `cmCurve` be the CM lattice `cmPeriod 𝓞_K` and `galConjugate σ` its conjugate by `σ`, with
`E = P.E s`, `K = K P` and `d = P.d`. If the period parallelogram of the conjugate lattice has the
area `|Ω|² √d / 2`, then the scale `σ periodFactor / Ω * areaScale` has the squared norm
`(bigOmega P s)⁻¹`. Here `bigOmega P s` is `exp (γ - Re L'/L(1, χ_K)) * 2π / rootDiscr E`, with `γ`
Euler's constant and `rootDiscr E` the root discriminant of `E`. Here `areaScale` is `√(2π / √d)`
and `periodFactor` is `vacuumRoot / chowlaSelbergUnit`. The denominator is the number chosen in the
formula of Chowla and Selberg for `cmCurve`. -/
lemma norm_gal_periodFactor_div_mul_areaScale_sq (P : Parameters) (s : ℕ) {σ : Gal(ℂ/K P)} {Ω : ℂˣ}
    (h_area : (P.cmCurve.galConjugate σ).area = ‖Ω.val‖ ^ 2 * √P.d / 2) :
    ‖σ (P.periodFactor s) / Ω * P.areaScale‖ ^ 2 = (P.bigOmega s)⁻¹ := by
  -- Divide `‖σ vacuumRoot‖ ^ 2 * π = rootDiscr E / √d * π` by the formula of Chowla and Selberg.
  calc ‖σ (P.periodFactor s) / Ω * P.areaScale‖ ^ 2
    _ = ‖σ (P.vacuumRoot s)‖ ^ 2 * π /
          ((P.cmCurve.galConjugate σ).area * ‖σ P.chowlaSelbergUnit‖ ^ 2) := by
      simp [h_area, periodFactor, areaScale, pi_nonneg, field]
    _ = NumberField.rootDiscr (P.E s) / √P.d * π /
          (π * rexp (chowlaSelbergConst P.d) * (2 * π / √P.d)) := by
      rw [P.norm_gal_vacuumRoot s σ, P.area_mul_norm_chowlaSelbergUnit_sq σ]
    _ = (P.bigOmega s)⁻¹ := by
      rw [bigOmega]
      field [ne]

section FixedSpace

variable {P : Parameters} {s : ℕ} {n : Type} [Fintype n] {ε : n → ℤˣ} [DecidableEq n]

/-- Let `V` be a space and `F` a vector of `𝒮 V`. Suppose `c • vacElem`, with `c ≠ 0`, is a sum of
translates `finHeisenbergOp (a j) (ϱ(finVec b) F)`. Then the finite part `finitePart` (the span of
the vectors `finHeisenbergOp z vacElem`) is contained in the span of the translates `ϱ(finVec x) F`
over all finite adelic vectors `x`. -/
lemma finitePart_le_span_translates {V : Space (P.E s) n ε} {F : 𝒮 V} {c : ℂ} (hc_ne : c ≠ 0)
    {Γ : Type} [Fintype Γ] {a : Γ → n → 𝔸f (P.E s)} {b : n → 𝔸f (P.E s)}
    (hc : c • V.vacElem = ∑ j : Γ, V.finHeisenbergOp (a j) (V.ϱ (finVec b) F)) :
    V.finitePart ≤ span ℂ (Set.range fun x : n → 𝔸f (P.E s) ↦ V.ϱ (finVec x) F) := by
  rw [finitePart, span_le, range_subset_iff]
  intro z
  rw [(eq_inv_smul_iff₀ hc_ne).2 hc, map_smul, map_sum]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ ↦ ?_)
  simp only [finHeisenbergOp, _root_.smul_apply, map_smul, rho_finVec_rho_finVec,
    smul_smul]
  exact Submodule.smul_mem _ _ (subset_span (mem_range_self _))

/-- The series `zetaLinearSeries Ω c k j` is the linear form `Ω / q₁ / areaScale * c * ∑ w, conj (Φ
w ζᵏ) * z (w, j)` in the variables `z`, the sum being over the infinite places `w` of `E = P.E s`.
Here `ζ` is the root of unity that generates `E` over `K`, and `Φ w` is the complex embedding chosen
at `w`. An automorphism `σ` of `ℂ` over `K`, applied to the coefficients, takes this form for the
period `cmPeriod` and the scale `jetScale` to that for the period `Ω` and the scale
`σ periodFactor / Ω * areaScale`, up to the permutation `placePerm s σ` of the infinite places
induced by `σ`. Here `q₁` is the order of `ζ`, `areaScale = √(2π / √d)`,
`periodFactor = vacuumRoot / chowlaSelbergUnit` and
`jetScale = periodFactor * areaScale / cmPeriod`. -/
lemma map_zetaLinearSeries (σ : Gal(ℂ/K P)) (Ω : ℂˣ) (k : Fin (P.q₁ s)) (j : n) :
    (zetaLinearSeries P.cmPeriod (P.jetScale s) k j).map (σ : ℂ →+* ℂ) =
      (zetaLinearSeries Ω (σ (P.periodFactor s) / Ω * P.areaScale) k j).rename
        (Prod.map (placePerm s σ).symm id) := by
  -- The constant factors are `periodFactor / q₁` and its image under `σ`, and `σ` permutes the
  -- embeddings `Φ`.
  have h_left :
      P.cmPeriod.val / P.q₁ s / P.areaScale * P.jetScale s = P.periodFactor s / P.q₁ s := by
    simp [jetScale, field]
  have h_right : Ω.val / P.q₁ s / P.areaScale * (σ (P.periodFactor s) / Ω * P.areaScale) =
      σ (P.periodFactor s) / P.q₁ s := by simp [field]
  simp only [zetaLinearSeries, h_left, h_right, linearSeries, map_sum, smul_eq_C_mul, map_mul,
    map_C, map_X, rename_C, rename_X]
  exact Fintype.sum_equiv ((placePerm s σ).prodCongr 1) _ _ fun ⟨w, i⟩ ↦ by
    simp [← map_star_complex, apply_Phi_eq_Phi_placePerm, apply_ite σ, starRingEnd_apply]

/-- Let `F` be a vector of the finite part, `β` a finite adele of `K` and, for each `x ∈ K`, `U x` a
neighbourhood of `β x`. For a rational vector `γ` there is `a ∈ K` such that the translates of `F`
by `β γ` and `a γ` agree and `a x` lies in `U x` for each coordinate `x = zetaCoord s k (γ i) ∈ K`
of `γ i` along a resolution vector `ζᵏ / q₁`. -/
lemma exists_rational_translate_eq {V : Space (P.E s) n ε} {F : 𝒮 V} (hF_mem : F ∈ V.finitePart)
    {β : 𝔸f P.K} {U : P.K → Set (𝔸f P.K)}
    (hU : ∀ x : P.K, U x ∈ nhds (β * algebraMap P.K (𝔸f P.K) x)) (γ : n → P.E s) :
    ∃ a : P.K, V.ϱ (finVec (finAdeleIncl P.K (P.E s) β • finiteImage γ)) F =
        V.ϱ (finVec (finiteImage (a • γ))) F ∧
      ∀ (k : Fin (P.q₁ s)) (i : n),
        algebraMap P.K (𝔸f P.K) (a * P.zetaCoord s k (γ i)) ∈ U (P.zetaCoord s k (γ i)) := by
  -- Both conditions hold on a neighbourhood of `β`, and `K` is dense in its finite adeles.
  have h_lc : IsLocallyConstant
      fun β' : 𝔸f P.K ↦ V.ϱ (finVec (finAdeleIncl P.K (P.E s) β' • finiteImage γ)) F :=
    (isLocallyConstant_rho_finVec hF_mem).comp_continuous (by fun_prop)
  have h_coord : ∀ᶠ β' in nhds β, ∀ (k : Fin (P.q₁ s)) (i : n),
      β' * algebraMap P.K (𝔸f P.K) (P.zetaCoord s k (γ i)) ∈ U (P.zetaCoord s k (γ i)) :=
    Filter.eventually_all.2 fun k ↦ Filter.eventually_all.2 fun i ↦
      (continuous_mul_const _).continuousAt.preimage_mem_nhds (hU _)
  obtain ⟨a, ha_translate, ha_coord⟩ :=
    denseRange_algebraMap_finAdele.mem_nhds ((h_lc.eventually_eq β).and h_coord)
  refine ⟨a, ?_, by simpa only [map_mul] using ha_coord⟩
  rw [← ha_translate, adeleMap_algebraMap, algebraMap_smul, ← map_smul, algebraMap_smul]

/-- Let `F` be a theta product for `cmCurve` with period `cmPeriod` and level `e`, and `F'` one for
the conjugate curve by `σ` with period `Ω` and level `e'`. The factors of a theta product at a
rational vector `γ` are the functions `zetaCoordThetaTranslate C Ω k (γ j)`, the twisted translates
of the theta function of `C` by `Ω` times the coordinate of `γ j` along `ζᵏ / q₁`. If `σ` takes the
Taylor series of the factors of `F` at `γ` to those of the factors of `F'` at `γ'`, then it takes
the jets of the translate of `F` by `γ` at the scale
`jetScale = periodFactor * areaScale / cmPeriod` to those of the translate of `F'` by `γ'` at the
scale `σ periodFactor / Ω * areaScale`, with the infinite places permuted by `σ`. -/
lemma IsThetaProduct.isJetConjugate_of_map_taylorAtZero_eq {V : Space (P.E s) n ε}
    {σ : Gal(ℂ/K P)} {Ω : ℂˣ} {e e' : ℕ+} {F F' : 𝒮 V}
    (hF : IsThetaProduct V P.cmCurve P.cmPeriod e F)
    (hF' : IsThetaProduct V (P.cmCurve.galConjugate σ) Ω e' F') {γ γ' : n → P.E s}
    (h_series : ∀ (k : Fin (P.q₁ s)) (j : n),
      MvPowerSeries.map (σ : ℂ →+* ℂ) (taylorAtZero
        (zetaCoordThetaTranslate P.cmCurve P.cmPeriod k (γ j))) =
        taylorAtZero (zetaCoordThetaTranslate (P.cmCurve.galConjugate σ) Ω k (γ' j))) :
    IsJetConjugate σ (placePerm s σ) (P.jetScale s) (σ (P.periodFactor s) / Ω * P.areaScale)
      (V.ϱ (finVec (finiteImage γ)) F) (V.ϱ (finVec (finiteImage γ')) F') := by
  -- Both series are products over the resolution of series in one variable composed with linear
  -- forms; compare factor by factor.
  simp only [IsJetConjugate, hF.jetSeries_translate, hF'.jetSeries_translate, map_prod, map_pow]
  refine prod_congr rfl fun k _ ↦ prod_congr rfl fun j _ ↦ congrArg (· ^ P.q₁ s) ?_
  have h_subst (Ω' : ℂˣ) (c : ℂ) : HasSubst fun _ : Unit ↦ zetaLinearSeries (s := s) Ω' c k j :=
    hasSubst_of_constantCoeff_zero fun _ ↦ by simp [zetaLinearSeries]
  rw [PowerSeries.subst, PowerSeries.subst, map_subst (h_subst _ _), h_series]
  -- The linear forms agree, up to the permutation of the places.
  simp only [map_zetaLinearSeries σ Ω k j, rename_eq_subst]
  rw [subst_comp_subst_apply (h_subst _ _) (hasSubst_of_constantCoeff_zero fun _ ↦ by simp)]

end FixedSpace

/-- For each automorphism `σ` of `ℂ` over `K` there is a finite adele `B σ` of `E` such that every
standard space `V` has a vector `F` of the finite part with `θ F = 1`, whose translates
`ϱ(finVec x) F` span the finite part, and, for each `σ`, a vector `F'` of the finite part and a
scale `t` with `|t|² = 1 / bigOmega` such that `σ` takes the jets of the translate of `F` by `x`, at
the scale `jetScale`, to those of the translate of `F'` by `B σ • x` at the scale `t`, with the
infinite places permuted by `σ`. Here `θ` is the theta functional of `V`, `finVec x` is the adelic
vector with finite part a fixed multiple of `x` and archimedean part zero, and `jetScale` and
`bigOmega` are the scale and the period constant attached to `P` and `s`. -/
lemma exists_isJetConjugate_translates (P : Parameters) (s : ℕ) :
    ∃ B : Gal(ℂ/K P) → 𝔸f (P.E s),
    ∀ {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} (V : Space (P.E s) n ε) [V.IsStd],
      ∃ F ∈ V.finitePart, V.θ F = 1 ∧
        V.finitePart ≤ span ℂ (Set.range fun x : n → 𝔸f (P.E s) ↦ V.ϱ (finVec x) F) ∧
        ∀ σ : Gal(ℂ/K P), ∃ t : ℂ, ∃ F' ∈ V.finitePart, ‖t‖ ^ 2 = (P.bigOmega s)⁻¹ ∧
          ∀ x : n → 𝔸f (P.E s), IsJetConjugate σ (placePerm s σ) (P.jetScale s) t
            (V.ϱ (finVec x) F) (V.ϱ (finVec (B σ • x)) F') := by
  -- Complex multiplication gives, for each `σ`, a number `Ω σ` with a multiple `Ω σ * e` in the
  -- conjugate lattice and an adele `β σ`: for `x'` in a neighbourhood `U σ x` of `β σ * x`, `σ`
  -- maps the Taylor series of `θ` translated by `x cmPeriod` to that of its conjugate translated by
  -- `x' * Ω σ`. The vectors `F`, `F'` are the theta products for the two lattices.
  let C (σ : Gal(ℂ/K P)) : CMLattice P.d := P.cmCurve.galConjugate σ
  have h_cm (σ : Gal(ℂ/K P)) : ∃ (Ω : ℂˣ) (β : 𝔸f P.K),
      (C σ).area = ‖Ω.val‖ ^ 2 * √P.d / 2 ∧ (∃ e : ℕ+, Ω.val * e ∈ (C σ).latticeModule) ∧
      ∀ x : P.K, ∃ U ∈ nhds (β * x), ∀ x' : P.K, ↑x' ∈ U →
        taylorVia σ (P.cmCurve.twistedTranslate 1 (x * P.cmPeriod) P.cmCurve.θ) =
          taylorAtZero ((C σ).twistedTranslate 1 (x' * Ω) (C σ).θ) := by
    obtain ⟨Ω, -, β, -, -, h_area, h_multiple, h_translate⟩ :=
      complex_multiplication_theta P.cmCurve σ latticeModule_cmCurve
    exact ⟨Ω, β, h_area, h_multiple, h_translate⟩
  choose Ω β h_area h_multiple U hU h_translate using h_cm
  refine ⟨fun σ ↦ finAdeleIncl P.K (P.E s) (β σ), fun {n _ _ ε} V _ ↦ ?_⟩
  obtain ⟨F, hF⟩ : ∃ F : 𝒮 V, IsThetaProduct V P.cmCurve P.cmPeriod 1 F :=
    exists_isThetaProduct_cmCurve V
  refine ⟨F, hF.mem_finitePart, hF.theta_eq_one, ?_, fun σ ↦ ?_⟩
  · -- The vacuum is a combination of translates of `F`, and so are its translates.
    obtain ⟨c, hc_ne, Γ, _, a, b, -, hc⟩ := hF.exists_smul_vacElem_eq_sum
    exact finitePart_le_span_translates hc_ne hc
  obtain ⟨e, he⟩ := h_multiple σ
  obtain ⟨F', hF'⟩ : ∃ F' : 𝒮 V, IsThetaProduct V (C σ) (Ω σ) e F' :=
    exists_isThetaProduct V he (h_area σ)
  let B : 𝔸f (P.E s) := finAdeleIncl P.K (P.E s) (β σ)
  let t : ℂ := σ (P.periodFactor s) / Ω σ * P.areaScale
  refine ⟨t, F', hF'.mem_finitePart, P.norm_gal_periodFactor_div_mul_areaScale_sq s (h_area σ),
    fun y ↦ ?_⟩
  -- Both sides are locally constant in `y` and the rational points are dense, so let `y` be a
  -- rational point `γ`.
  have h_lc : IsLocallyConstant
      fun y : n → 𝔸f (P.E s) ↦ (V.ϱ (finVec y) F, V.ϱ (finVec (B • y)) F') :=
    (isLocallyConstant_rho_finVec hF.mem_finitePart).prodMk
      ((isLocallyConstant_rho_finVec hF'.mem_finitePart).comp_continuous (by fun_prop))
  refine denseRange_finiteImage.induction_on y
    ⟨h_lc {f | ¬IsJetConjugate σ (placePerm s σ) (P.jetScale s) t f.1 f.2}⟩ fun γ ↦ ?_
  -- Take `x₀ ∈ K` so near to `β σ` that translating `F'` by `B γ` or by `x₀ γ` is the same, and
  -- that `x₀ * x` lies in `U σ x` for each coordinate `x` of `γ`.
  obtain ⟨x₀, h_rational, h_coord⟩ : ∃ x₀ : P.K,
      V.ϱ (finVec (B • finiteImage γ)) F' = V.ϱ (finVec (finiteImage (x₀ • γ))) F' ∧
      ∀ (k : Fin (P.q₁ s)) (i : n), ↑(x₀ * P.zetaCoord s k (γ i)) ∈ U σ (P.zetaCoord s k (γ i)) :=
    exists_rational_translate_eq hF'.mem_finitePart (hU σ) γ
  -- Both translates are now rational, and their factors correspond by complex multiplication.
  suffices IsJetConjugate σ (placePerm s σ) (P.jetScale s) t (V.ϱ (finVec (finiteImage γ)) F)
    (V.ϱ (finVec (finiteImage (x₀ • γ))) F') by rwa [h_rational]
  refine hF.isJetConjugate_of_map_taylorAtZero_eq hF' fun k j ↦ ?_
  rw [zetaCoordThetaTranslate, zetaCoordThetaTranslate, Pi.smul_apply, zetaCoord_smul]
  exact h_translate σ _ _ (h_coord k j)

end ConjugateTranslates

end New.Parameters

end
