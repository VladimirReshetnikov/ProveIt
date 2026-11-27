import Lib.ClassField.HeckeCharacter.SplitTameCharacters
import Lib.Weil.CompactLift.ThetaKernelDefs
import Lib.Weil.DualPair.GaloisLaw
import New.Derivatives.Vacuum.ShortVectors
import New.UpperBound.Seesaw.AdmissibleCombinations

/-!
# Galois conjugates of jets of theta functions and archimedean bounds for jets

An automorphism `σ` of `ℂ` over `K = ℚ(√-d)` acts on the jets of theta functions. This action is
realized as a `σ`-semilinear map `L` on `𝒮 V`, whose laws hold on `V.finitePart`. We then prove
archimedean bounds for the conjugates of the jets of admissible combinations of the operators
`New.Space.finHeisenbergOp` applied to the integral vacuum, moved by finite points of a pair of
groups.

## Main definitions and results

* `New.Parameters.exists_isJetConjugation`: existence of `L`;
  `New.Parameters.IsJetConjugation.exists_map_schrodingerOp`: its action on the vacuum `vacElem` and
  on the data `Ψ ⊗ vacElem` for Schwartz–Bruhat functions `Ψ`;
  `New.Parameters.IsJetConjugation.norm_map_intVacuum_le`: a bound, with constant `P.constantBound`,
  for the images of the translates of `ω g (intVacuum V)`; it rests on
  `New.Parameters.norm_omega_vac_le`.
* `New.Parameters.norm_jet_le_of_isVacuumCombination` and
  `New.Parameters.sqrt_weylNormSq_schurJet_le_of_isVacuumCombination`: archimedean bounds for the
  conjugates by `σ ∈ Aut ℂ` of the jets, and for their Schur matrices;
  `New.Parameters.isVacuumCombination_of_isAdmissibleCombination` makes them apply to admissible
  combinations.

Notions from other files:
* `New.Parameters.E`: The field `P.E s = K(ζ)`, for a primitive root of unity `ζ` of order
  `P.q₁ s`; `P.Φ s` is the set of its infinite places, a group isomorphic to `Gal(E/K)`.
* `New.Parameters.jetScale`: A nonzero complex number, the period factor times the area scale over
  the period `Ω₀`, at which Taylor series of theta functions are scaled.
* `New.Parameters.bigOmega`: The real number Ω = exp(γ − Re L′/L(1, χ_K))·2π/rd_E, with γ Euler's
  constant and rd_E the root discriminant of E.
* `New.Parameters.intVacuum`: The vacuum of rank n multiplied by the n-th power of a fixed number
  that makes its values at finite vectors integral.
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.𝒮`: For a space V of rank n, a Banach space of integrable functions on 𝔸^n on which the
  Heisenberg and Weil representations act. Applied to an adelic vector, `f : 𝒮 V` gives the value
  of its theta function.

## Relation to the literature

Related work: Bannai–Kobayashi, Algebraic theta functions and the p-adic interpolation of
Eisenstein–Kronecker numbers, 2010; Kings–Sprang, Eisenstein–Kronecker classes and integrality of
critical values, 2019; Katz, p-adic L-functions for CM fields, 1978.

The Galois action on theta functions with complex multiplication and on the finite Weil
representation is known; see `Lib.Weil.DualPair.KernelLaws` for sources.
-/

/-!
## Galois conjugation of jets as a semilinear map

`New.Space.IsJetConjugate σ π t t' f f'` says that `σ` applied to the Taylor series of `f` at scale
`t` is that of `f'` at scale `t'`, with places renamed by `π⁻¹`. `New.Space.finitePart` is spanned
by the finite Heisenberg translates of the vacuum `vacElem`. `V.ϱ` and `V.ω` are the Heisenberg and
Weil representations, and `finVec x` is the adelic vector with finite part `α x` and zero
archimedean part, for the idele `α` of the Weil data.
-/

section ConjugatesOfJets

open Real Fintype MvPowerSeries New.Space New.stdLattice LinearMap Function Subtype NeZero
  New.WeilData

/-- `L` conjugates jets by `σ`, an automorphism of `ℂ` over `K`, at a scale `t` with `|t|² = 1/Ω`:
it is a `σ`-semilinear map on `𝒮 V` that on the finite part scales finite translations by the
finite adele `b`, `σ` acts on the character `selfDualAddChar` as multiplication by `b b̄` does, and
for `f` in the finite part the jets of `L f` at the scale `t` are the conjugates of the jets of `f`.
Here `V` is a space over `E P s = K(ζ)`, with `ζ` a root of unity of order `P.q₁ s`; `𝒮 V` is the
Banach space of functions on adelic vectors on which the Heisenberg and Weil representations act;
and `placePerm s σ` is the permutation of the infinite places of `E P s` induced by `σ`.
The law for the Weil operators is `New.Space.ScalesTranslations.map_omega`. -/
structure New.Parameters.IsJetConjugation {P : Parameters} {s : ℕ} {n : Type} [Fintype n]
    [DecidableEq n] {ε : n → ℤˣ} (V : Space (E P s) n ε) (σ : Gal(ℂ/K P))
    (t : ℂ) (b : 𝔸f (E P s)) (L : 𝒮 V →ₛₗ[(σ : ℂ →+* ℂ)] 𝒮 V) : Prop where
  /-- The scale `t` has `|t|² = 1/Ω`. -/
  norm_scale_sq : ‖t‖ ^ 2 = (P.bigOmega s)⁻¹
  /-- `L` keeps `V.finitePart` and turns the translation by a finite `x` into that by `b x` there,
  and `σ (selfDualAddChar z) = selfDualAddChar (b b̄ z)`. -/
  scalesTranslations : V.ScalesTranslations σ b L
  /-- For `f ∈ V.finitePart`, the jets of `L f` at scale `t` are the conjugates by `σ` of the
  jets of `f` at scale `P.jetScale s`. -/
  isJetConjugate : ∀ f ∈ V.finitePart, IsJetConjugate σ (placePerm s σ) (P.jetScale s) t f (L f)

/-- The Galois law of the additive character `selfDualAddChar` of the finite adeles, from the
standard space `V = stdSpace E Unit` of rank one. The translate of `F` by a finite adele `x` is
`V.ϱ (finVec x) F`.

Let `F` and `F'` lie in `V.finitePart`, with `F ≠ 0` and `t ≠ 0`. Suppose that for all `x` the ring
homomorphism `σ` takes the jets at scale `t` of the translate of `F` by `x` to the jets at scale
`t'` of the translate of `F'` by `b • x`, up to the permutation `e` of the infinite places. Then `σ`
takes `selfDualAddChar z` to `selfDualAddChar (b * star b * z)`. -/
lemma New.Space.map_selfDualAddChar_of_isJetConjugate {E : Type} [Field E] [CMType E] [WeilData E]
    {σ : ℂ →+* ℂ} {e : Equiv.Perm (NumberField.InfinitePlace E)} {t t' : ℂ} {b : 𝔸f E}
    {F F' : 𝒮 (stdSpace E Unit)} (hF : F ∈ (stdSpace E Unit).finitePart)
    (hF' : F' ∈ (stdSpace E Unit).finitePart) (hF_ne : F ≠ 0) (ht : t ≠ 0)
    (h_conj : ∀ x : Unit → 𝔸f E, IsJetConjugate σ e t t'
      ((stdSpace E Unit).ϱ (finVec x) F) ((stdSpace E Unit).ϱ (finVec (b • x)) F'))
    (z : 𝔸f E) : σ (selfDualAddChar E z) = selfDualAddChar E (b * star b * z) := by
  -- Take `N ≠ 0` such that translation by `N` fixes `F` and translation by `N • b` fixes `F'`,
  -- write `z = N * x`, and compare the jets at `2x` and at `2x + N` by the Heisenberg relation.
  let V : Space E Unit 1 := stdSpace E Unit
  have h_lc : IsLocallyConstant fun x : Unit → 𝔸f E ↦ (V.ϱ (finVec x) F, V.ϱ (finVec x) F') :=
    (isLocallyConstant_rho_finVec hF).prodMk (isLocallyConstant_rho_finVec hF')
  obtain ⟨N, hN, h_fix⟩ := exists_natCast_smul_mem_of_isCompact E
    (Set.toFinite {1, b • 1}).isCompact (h_lc.eventually_eq 0)
  have h_fixF : V.ϱ (finVec ((N : 𝔸f E) • 1)) F = F := by
    simpa using congrArg Prod.fst (h_fix 1 (.inl rfl))
  have h_fixF' : V.ϱ (finVec ((N : 𝔸f E) • b • 1)) F' = F' := by
    simpa using congrArg Prod.snd (h_fix (b • 1) (.inr rfl))
  obtain ⟨x, rfl⟩ : (N : 𝔸f E) ∣ z := (isUnit_natCast_finAdele hN).dvd
  have h_jet : IsJetConjugate σ e t t' (V.ϱ (finVec (x • 2)) (V.ϱ (finVec ((N : 𝔸f E) • 1)) F))
      (V.ϱ (finVec (b • x • 2)) (V.ϱ (finVec ((N : 𝔸f E) • b • 1)) F')) := by
    simpa only [h_fixF, h_fixF'] using h_conj (x • 2)
  -- The jets of a translate of `F` do not vanish, so they cancel in the comparison.
  have h_jet_ne : V.jetSeries t (V.ϱ (finVec (x • 2 + (N : 𝔸f E) • 1)) F) ≠ 0 :=
    fun h_zero ↦ hF_ne <| by
      rw [← norm_eq_zero, ← V.heisenbergRep.norm_map,
        eq_zero_of_jetSeries_eq_zero (rho_finVec_mem_finitePart _ hF) ht h_zero, norm_zero]
  have h_cmp : σ (selfDualAddChar E (half * (x * ((N : 𝔸f E) * 2)))) =
      selfDualAddChar E (half * (b * (x * (star b * ((N : 𝔸f E) * 2))))) := by
    -- By the Heisenberg relation both sides are scalars times jets at `x • 2 + N`, which cancel.
    have h_sum := h_conj (x • 2 + (N : 𝔸f E) • 1)
    rw [rho_finVec_rho_finVec, rho_finVec_rho_finVec, smul_comm _ b, ← smul_add] at h_jet
    simpa [V, IsJetConjugate, smul_eq_C_mul, -smul_add, ← h_sum, h_jet_ne] using h_jet
  have h_left : half * (x * ((N : 𝔸f E) * 2)) = (N : 𝔸f E) * x := by
    linear_combination (N : 𝔸f E) * x * two_mul_half (E := E)
  have h_right : half * (b * (x * (star b * ((N : 𝔸f E) * 2)))) =
      b * star b * ((N : 𝔸f E) * x) := by
    linear_combination b * star b * ((N : 𝔸f E) * x) * two_mul_half (E := E)
  rwa [h_left, h_right] at h_cmp

/-- Galois conjugates of jets. Let `V` be a hermitian space over `E P s` that is standard: its signs
`ε` at the infinite places are `+1` and its point, an adelic basis that diagonalizes the form, is
the identity matrix.

Let `σ` be an automorphism of `ℂ` over `K`. Then there are a scale `t`, a finite adele `b` and a
`σ`-semilinear map `L` with the laws of `New.Parameters.IsJetConjugation`. First, `|t|² = 1/Ω` for
`Ω = P.bigOmega s = exp (γ - Re L'/L(1, χ_K)) * 2π / rd_E`, with `γ` Euler's constant, `χ_K` the
quadratic character of `K` and `rd_E` the root discriminant of `E`. Next, `L` keeps the span
`V.finitePart` of the finite translates of the vacuum; there it takes translation by `x` to
translation by `b x`, and the jets of `L f` at scale `t` are the `σ`-conjugates of those of `f` at
scale `P.jetScale s`. Finally `σ (selfDualAddChar z) = selfDualAddChar (b b̄ z)`. -/
theorem New.Parameters.exists_isJetConjugation {P : Parameters} {s : ℕ} {n : Type}
    [Fintype n] [DecidableEq n] {ε : n → ℤˣ} (V : Space (E P s) n ε) [hV : V.IsStd]
    (σ : Gal(ℂ/K P)) :
    ∃ (t : ℂ) (b : 𝔸f (E P s)) (L : 𝒮 V →ₛₗ[(σ : ℂ →+* ℂ)] 𝒮 V), IsJetConjugation V σ t b L := by
  obtain rfl : ε = 1 := hV.signs_eq_one
  -- `exists_isJetConjugate_translates` gives `F`, whose translates span `V.finitePart`, an adele
  -- `B σ` and `F'` such that `ϱ x F` and `ϱ (B σ • x) F'` have conjugate jets. The map `L` sends
  -- `f ∈ V.finitePart` to the vector whose jets are the conjugates of those of `f`.
  obtain ⟨B, hB⟩ := P.exists_isJetConjugate_translates s
  obtain ⟨F, -, -, h_span, hσ⟩ := hB V
  obtain ⟨t, F', hF', ht, hJ⟩ : ∃ t : ℂ, ∃ F' ∈ V.finitePart, ‖t‖ ^ 2 = (P.bigOmega s)⁻¹ ∧
      ∀ x : n → 𝔸f (E P s), IsJetConjugate σ (placePerm s σ) (P.jetScale s) t
        (V.ϱ (finVec x) F) (V.ϱ (finVec (B σ • x)) F') := hσ σ
  let renamedJet : V.finitePart →ₗ[ℂ] MvPowerSeries (P.Φ s × n) ℂ := domRestrict
    ((rename ((placePerm s σ).symm.prodCongr (.refl n))).toLinearMap ∘ₗ V.jetSeries t) V.finitePart
  let conjJet : 𝒮 V →ₛₗ[(σ : ℂ →+* ℂ)] MvPowerSeries (P.Φ s × n) ℂ :=
    { toFun := fun f ↦ MvPowerSeries.map σ (V.jetSeries (P.jetScale s) f)
      map_add' := by simp
      map_smul' := by simp [smul_eq_C_mul] }
  let L : 𝒮 V →ₛₗ[(σ : ℂ →+* ℂ)] V.finitePart := renamedJet.leftInverse ∘ₛₗ conjJet
  -- A vector of `V.finitePart` is determined by its jets, since `t ≠ 0`.
  have ht_ne : t ≠ 0 := fun h_zero ↦ by simpa [h_zero, bigOmega_pos.ne'] using ht.symm
  have h_inj : ker renamedJet = ⊥ := by
    refine ker_eq_bot'.2 fun f hf ↦ Subtype.ext ?_
    have h_series : V.jetSeries t f = 0 := (renameEquiv ..).map_eq_zero_iff.1 hf
    exact eq_zero_of_jetSeries_eq_zero f.2 ht_ne h_series
  have hL (x : n → 𝔸f (E P s)) : L (V.ϱ (finVec x) F) = V.ϱ (finVec (B σ • x)) F' := by
    have h_jet : conjJet (V.ϱ (finVec x) F) =
        renamedJet ⟨_, rho_finVec_mem_finitePart (B σ • x) hF'⟩ := by
      simpa [conjJet, renamedJet, IsJetConjugate] using hJ x
    simp [L, h_jet, leftInverse_apply_of_inj h_inj]
  -- The law for `selfDualAddChar` comes from the generator in rank one.
  have hχ (z : 𝔸f (E P s)) : σ (selfDualAddChar _ z) = selfDualAddChar _
    (B σ * star (B σ) * z) := by
    obtain ⟨F₁, hF₁, hθ, -, hσ₁⟩ := hB (stdSpace _ Unit)
    obtain ⟨t₁, F₁', hF₁', -, hJ₁⟩ := hσ₁ σ
    have hF₁_ne : F₁ ≠ 0 := fun h_zero ↦ by simp [h_zero] at hθ
    exact map_selfDualAddChar_of_isJetConjugate hF₁ hF₁' hF₁_ne jetScale_ne_zero hJ₁ z
  -- The next two laws hold on translates of `F`, hence on their span.
  have hϱ (f : 𝒮 V) (hf : f ∈ V.finitePart) :
      ∀ x, L (V.ϱ (finVec x) f) = V.ϱ (finVec (B σ • x)) (L f) := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (h_span hf)
    · rintro _ ⟨w, rfl⟩ x
      simp [hL, hχ, rho_finVec_rho_finVec, mul_left_comm stdLattice.half, mul_assoc]
    · simp
    · simp +contextual
    · simp +contextual
  have hJC (f : 𝒮 V) (hf : f ∈ V.finitePart) :
      IsJetConjugate σ (placePerm s σ) (P.jetScale s) t f (L f) := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ (h_span hf)
    · rintro _ ⟨w, rfl⟩
      simpa [hL] using hJ w
    · simp [IsJetConjugate]
    · simp +contextual [IsJetConjugate]
    · simp +contextual [IsJetConjugate, smul_eq_C_mul]
  have h_scale : V.ScalesTranslations σ (B σ) (V.finitePart.subtype ∘ₛₗ L) :=
    { map_selfDualAddChar := hχ, map_mem {f} _ := (L f).property, map_rho {f} hf := hϱ f hf }
  exact ⟨t, B σ, V.finitePart.subtype ∘ₛₗ L, ht, h_scale, hJC⟩

/-- For an automorphism `σ` of `ℂ` over `K` and a finite unitary matrix `g`, the number
`multiplierRatio σ g = σ (Δ g) / Δ g` has modulus `1`. Here `Δ = New.finMultiplier` is the finite
part of the multiplier of the Weil representation. -/
lemma New.Parameters.norm_multiplierRatio {P : Parameters} {s : ℕ} {n : Type} [Fintype n]
    [DecidableEq n] (σ : Gal(ℂ/K P)) (g : Gf (E P s) n) : ‖multiplierRatio σ g‖ = 1 := by
  -- Its square is a quotient of two numbers of modulus `1`.
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← norm_pow, multiplierRatio_sq]
  simp [upsilonU1_hasWeight.norm_map_eq_one, funext_iff, Circle.norm_coe]

namespace New.Parameters.IsJetConjugation

/-- On a standard space `V` (all signs `+1`, the point the identity matrix), a map `L` that
conjugates jets is injective on `V.finitePart`, the span of the finite translates of the vacuum. -/
lemma eq_zero_of_map_eq_zero {P : Parameters} {s : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    {ε : n → ℤˣ} {V : Space (E P s) n ε} {σ : Gal(ℂ/K P)} {t : ℂ} {b : 𝔸f (E P s)}
    {L : 𝒮 V →ₛₗ[(σ : ℂ →+* ℂ)] 𝒮 V} (hL : IsJetConjugation V σ t b L) [hV : V.IsStd] {f : 𝒮 V}
    (hf : f ∈ V.finitePart) (h_zero : L f = 0) : f = 0 := by
  -- The conjugates of the jets of `f` vanish, and the jets determine `f`.
  obtain rfl : ε = 1 := hV.signs_eq_one
  have h_series : V.jetSeries (P.jetScale s) f = 0 := MvPowerSeries.ext fun m ↦ by
    simpa [h_zero] using congrArg (coeff m) (hL.isJetConjugate f hf)
  exact eq_zero_of_jetSeries_eq_zero hf jetScale_ne_zero h_series

/-- Let `V` be a hermitian space over `E P s`, a cyclotomic extension of `K P = ℚ(√-d)`, and let
`𝒮 V` be the Banach space of functions on adelic vectors on which the Heisenberg group acts. Let the
`σ`-semilinear map `L` on `𝒮 V` conjugate jets by the automorphism `σ` of `ℂ` over `K P` at the
scale `t`, scaling finite translations by the finite adele `b`. Let `f` lie in `V.finitePart`, the
span of the finite Heisenberg translates of the vacuum. Then `σ` takes the value of the theta
function of `f` at `finVec x` to that of `L f` at `finVec (b • x)`. Here `finVec x` is the adelic
vector with archimedean part zero and finite part `α x`, for the idele `α` of the Weil data. -/
lemma map_apply_finVec {P : Parameters} {s : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    {ε : n → ℤˣ} {V : Space (E P s) n ε} {σ : Gal(ℂ/K P)} {t : ℂ} {b : 𝔸f (E P s)}
    {L : 𝒮 V →ₛₗ[(σ : ℂ →+* ℂ)] 𝒮 V} (hL : IsJetConjugation V σ t b L) {f : 𝒮 V}
    (hf : f ∈ V.finitePart) (x : n → 𝔸f (E P s)) :
    σ (f (finVec x)) = L f (finVec (b • x)) := by
  -- These values are the constant terms of the jets of `ϱ(x) f` and of `L (ϱ(x) f) = ϱ(b x) (L f)`.
  have h_jet : IsJetConjugate σ (placePerm s σ) (P.jetScale s) t (V.ϱ (finVec x) f)
      (V.ϱ (finVec (b • x)) (L f)) := by
    rw [← hL.scalesTranslations.map_rho hf]
    exact hL.isJetConjugate _ (rho_finVec_mem_finitePart x hf)
  simpa [constantCoeff_jetSeries, rho_finVec_mem_finitePart, hf,
    hL.scalesTranslations.map_mem hf] using congrArg constantCoeff h_jet

/-- Let `V` be a standard hermitian space over `E P s`, a cyclotomic extension of `K P = ℚ(√-d)`.
Let the `σ`-semilinear map `L` conjugate jets on the space `𝒮 V` of the Weil representation `V.ω`,
and let `R` be a set of finite places (`FinPlace`) of `E P s` disjoint from its complex conjugate.
There are a number `c ≠ 0` and a finite adele `u` with `u ū = 1` such that
`L vacElem = c ω(u) vacElem` and `L (Ψ ⊗ vacElem) = c ω(u) ((σ ∘ Ψ) ⊗ vacElem)` for all `Ψ`
Schwartz–Bruhat above `R`. Here `ω(u)` is `V.ω` at the point with archimedean part `1` and finite
part the scalar matrix `scalarFin n u`, `vacElem` is the vacuum, and `Ψ ⊗` is `V.schrodingerOp R Ψ`,
the combination of finite translations attached to `Ψ`. -/
theorem exists_map_schrodingerOp {P : Parameters} {s : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    {ε : n → ℤˣ} {V : Space (E P s) n ε} {σ : Gal(ℂ/K P)} {t : ℂ} {b : 𝔸f (E P s)}
    {L : 𝒮 V →ₛₗ[(σ : ℂ →+* ℂ)] 𝒮 V} (hL : IsJetConjugation V σ t b L) [V.IsStd]
    {R : Set (FinPlace (E P s))} (hR : R.IsConjDisjoint) :
    ∃ c ≠ (0 : ℂ), ∃ u : unitary (𝔸f (E P s)),
      L V.vacElem = c • V.ω (1, scalarFin n u) V.vacElem ∧
      ∀ Ψ : (n → 𝔸f (E P s)) → ℂ, IsSchwartzBruhat R Ψ →
        L (V.schrodingerOp R Ψ V.vacElem) = c • V.ω (1, scalarFin n u)
          (V.schrodingerOp R (σ ∘ Ψ) V.vacElem) := by
  obtain ⟨c, u, h_vac, h_schrodinger⟩ := hL.scalesTranslations.exists_map_schrodingerOp hR
  refine ⟨c, fun hc ↦ ?_, u, h_vac, h_schrodinger⟩
  -- `L` is injective on the finite part, and the vacuum is a unit vector.
  have h_zero : V.vacElem = 0 :=
    hL.eq_zero_of_map_eq_zero vacElem_mem_finitePart (by rw [h_vac, hc, zero_smul])
  simpa [h_zero] using V.dataInner_vacElem_vacElem

end New.Parameters.IsJetConjugation

/-!
### Bounds for the values of the vacuum and of its conjugates

These bounds are uniform in the lattice. They enter Cauchy's estimate for the jets below.
-/

/-- At `W.vecAtPoint γ`, the coordinates of a rational vector `γ` at the point of a definite space,
the vacuum function `vacuumFn` (a Gaussian times a phase supported on a lattice) is bounded by
`exp (-π ‖γ‖² / √d)`. Here `‖γ‖ = ‖W.archCoords γ‖` is the length of the archimedean
coordinates. -/
lemma New.Parameters.norm_vacuumFn_vecAtPoint_le {P : Parameters} {s : ℕ} {n : Type} [Fintype n]
    [DecidableEq n] (W : Space (E P s) n 1) (γ : n → P.E s) :
    ‖vacuumFn (W.vecAtPoint γ)‖ ≤ exp (-(π / √P.d * ‖W.archCoords γ‖ ^ 2)) := by
  have h_exponent : ∑ i : n, ∑ w : P.Φ s, π * (Φ w j).im * ‖(W.vecAtPoint γ i).1 w‖ ^ 2 =
      π / √P.d * ‖W.archCoords γ‖ ^ 2 := by
    have h_im (w : P.Φ s) : (Φ w j).im = 1 / √P.d := by simp [j, sqrt_div_self]
    rw [EuclideanSpace.norm_sq_eq, sum_prod_type_right, Finset.mul_sum]
    simp [h_im, Finset.mul_sum, archCoords, div_eq_mul_inv π]
  rw [vacuumFn, h_exponent, norm_mul, Complex.norm_real, norm_of_nonneg (exp_nonneg _)]
  exact mul_le_of_le_one_right (exp_nonneg _) (by split_ifs <;> simp [Circle.norm_coe])

/-- Let `W` be a definite hermitian space over `E` (all signs `+1`), given by a matrix `J` over `E`
and a point `x ∈ GL_n(𝔸)` with `xᴴ J x = 1`. For `γ ∈ E^n`, `W.vecAtPoint γ = x⁻¹ γ`, and
`W.archCoords γ` is the vector of its components at all infinite places, in a Euclidean space.
Suppose that the finite parts of the coordinates of `x⁻¹ γ`, divided by the idele `α`, lie in the
ring `Ô` of finite adeles integral at every finite place. Then the squared length of
`W.archCoords γ` is an integer. Here `α = P.α s` is the inverse of a generator of the different of
`E / K` at the places dividing `(1 + √-d) / 2`, and `1` at the other finite places. -/
lemma New.Parameters.exists_intCast_eq_norm_archCoords_sq {P : Parameters} {s : ℕ} {n : Type}
    [Fintype n] [DecidableEq n] (W : Space (E P s) n 1) {γ : n → P.E s}
    (hγ : ∀ i : n, finCoord (W.vecAtPoint γ) i ∈ Ô (P.E s)) :
    ∃ m : ℤ, (m : ℝ) = ‖W.archCoords γ‖ ^ 2 := by
  -- The squared length is the trace to `K` of the value `h` of the hermitian form. This value lies
  -- in the ideal of `α ᾱ`, which is the inverse different of `E / K` (`relDifferentGen` generates
  -- the different). So the trace is an integer of `K`, and it is real.
  let h : P.E s := star γ ⬝ᵥ W.J.mulVec γ
  have h_fin : (toAdele h).2 = ∑ i : n, star (W.vecAtPoint γ i).2 * (W.vecAtPoint γ i).2 := by
    rw [← W.stdForm_vecAtPoint]
    simp [dotProduct, stdForm, Matrix.mulVec_diagonal, Prod.snd_sum]
  have h_gen : (P.α s).val * star (P.α s).val * (P.relDifferentGen s).val ∈ Ô (P.E s) :=
    mem_Ô.2 fun w ↦ (v_alpha_mul_star_mul_relDifferentGen w).le
  have h_factor (x : 𝔸f (P.E s)) : star x * x * (P.relDifferentGen s).val =
      (P.α s).val * star (P.α s).val * (P.relDifferentGen s).val *
        (star ((P.α s)⁻¹.val * x) * ((P.α s)⁻¹.val * x)) := by
    have h_star : star (P.α s).val * star (P.α s)⁻¹.val = 1 := by simp [← star_mul']
    grind [star_mul', Units.mul_inv]
  have h_int : IsIntegral ℤ (h * (P.relDifferentGen s).val) := by
    rw [← algebraMap_mem_Ô, map_mul, ← toAdele_apply_snd h, h_fin, Finset.sum_mul]
    refine sum_mem fun i _ ↦ ?_
    rw [h_factor]
    exact mul_mem h_gen (mul_mem (star_mem_Ô (hγ i)) (hγ i))
  obtain ⟨c, hc⟩ : ∃ c : NumberField.RingOfIntegers P.K,
      (c : P.K) = Algebra.trace P.K (P.E s) h := exists_coe_eq_trace_of_isIntegral h_int
  have h_trace : ((c : P.K) : ℂ) = (‖W.archCoords γ‖ ^ 2 : ℝ) := by
    have h_place (w : P.Φ s) : Φ w h = ∑ i : n, (‖(W.vecAtPoint γ i).1 w‖ ^ 2 : ℝ) := by
      rw [← toAdele_apply_fst, ← W.stdForm_vecAtPoint]
      simp [dotProduct, stdForm, Matrix.mulVec_diagonal, Prod.fst_sum, Complex.conj_mul']
    rw [hc, coe_trace_eq_sum, EuclideanSpace.norm_sq_eq, sum_prod_type]
    simp [h_place, archCoords]
  obtain ⟨m, hm⟩ := exists_eq_intCast_of_mem_quadInt_of_conj_eq ⟨c, h_trace⟩ (Complex.conj_ofReal _)
  exact ⟨m, mod_cast hm.symm⟩

/-- Let `W` be a definite hermitian space (all signs `+1`) over `E = P.E s`, a cyclotomic extension
of `ℚ(√-d)`, given by a matrix `J` over `E` and a point `x ∈ GL_n(𝔸)` with `xᴴ J x = 1`. Let
`γ ≠ δ`, and let the finite parts of the coordinates of `x⁻¹ γ` and `x⁻¹ δ` become integral (lie in
`Ô`) after division by the idele `α` of the Weil data. Then `W.archCoords γ` and `W.archCoords δ`
have distance at least `1`. -/
lemma New.Parameters.one_le_norm_archCoords_sub {P : Parameters} {s : ℕ} {n : Type}
    [Fintype n] [DecidableEq n] (W : Space (E P s) n 1) {γ δ : n → P.E s}
    (hγ : ∀ i : n, finCoord (W.vecAtPoint γ) i ∈ Ô (P.E s))
    (hδ : ∀ i : n, finCoord (W.vecAtPoint δ) i ∈ Ô (P.E s)) (h_ne : γ ≠ δ) :
    1 ≤ ‖W.archCoords γ - W.archCoords δ‖ := by
  -- The squared distance is a positive integer.
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (m : ℝ) = ‖W.archCoords (γ - δ)‖ ^ 2 :=
    exists_intCast_eq_norm_archCoords_sq W fun i ↦ by
      simpa [finCoord, mul_sub] using sub_mem (hγ i) (hδ i)
  have h_pos : 0 < ‖W.archCoords (γ - δ)‖ := by
    obtain ⟨w⟩ : Nonempty (P.Φ s) := inferInstance
    exact norm_pos_iff.2 fun h_zero ↦ sub_ne_zero.2 h_ne <|
      W.eq_zero_of_vecAtPoint_fst_eq_zero (w := w)
      (funext fun i ↦ congrArg (fun z : EuclideanSpace ℂ _ ↦ z (w, i)) h_zero)
  rw [← map_sub, ← one_le_sq_iff₀ h_pos.le, ← hm]
  exact_mod_cast (pow_pos h_pos 2).trans_eq hm.symm

/-- Completing the square: `t D ≤ π t² / a + a D²` for `a > 0`, in exponential form. -/
lemma New.exp_neg_pi_div_mul_sq_le {a : ℝ} (ha : 0 < a) (t D : ℝ) :
    exp (-(π / a * t ^ 2)) ≤ exp (a * D ^ 2) * exp t ^ (-D) := by
  rw [← exp_mul, ← exp_add, exp_le_exp, ← sub_nonneg]
  have h_pi : 0 ≤ π - 1 / 4 := by linarith [two_le_pi]
  calc 0 ≤ ((π - 1 / 4) * t ^ 2 + (t / 2 - a * D) ^ 2) / a := by positivity
    _ = a * D ^ 2 + t * -D - -(π / a * t ^ 2) := by field

/-- If `δ ≤ 2 M`, then `√d (δ + 1)² + 3 δ ≤ 2 (2 d + 6) (M + 1)²`: the comparison of exponents in
`New.Parameters.norm_omega_vac_le`. -/
lemma New.sqrt_mul_sq_add_le_of_le {d M δ : ℕ} (hδ : δ ≤ 2 * M) :
    √d * (δ + 1) ^ 2 + (δ * 2 + δ) ≤ (2 : ℕ) * ((2 * d + 6) * (M + 1) ^ 2) := by
  have h_sqrt : √d ≤ (d : ℝ) :=
    sqrt_le_iff.2 ⟨d.cast_nonneg, mod_cast Nat.le_self_pow two_ne_zero d⟩
  -- The difference expands to nonnegative terms.
  grw [hδ, h_sqrt, ← sub_nonneg]
  push_cast
  ring_nf
  positivity

/-- In a definite space, given by a hermitian matrix and a point, the values of the vacuum moved
by the Weil operator `ω g` are bounded by `exp ((2 d + 6) (q₁ n + 1)²)`, uniformly in `g` and
in the argument. Here `n` is the rank, `g` is a point of the adelic unitary group for the signs
`+1`, `K = ℚ(√-d)`, and `q₁ = P.q₁ s` is the order of the root of unity that generates `P.E s`
over `K`. -/
lemma New.Parameters.norm_omega_vac_le {P : Parameters} {s : ℕ} {n : Type} [Fintype n]
    [DecidableEq n] (V : Space (E P s) n 1) (g : G (P.E s) (1 : n → ℤˣ)) (y : n → 𝔸 (P.E s)) :
    ‖V.ω g V.vacElem y‖ ≤ exp ((2 * P.d + 6) * (P.q₁ s * card n + 1) ^ 2) := by
  -- The squared modulus of the value is a theta series of matrix coefficients of the vacuum. These
  -- are Gaussians supported on a lattice of rational vectors whose squared lengths are integers,
  -- so a packing bound estimates the series.
  let W : Space (E P s) n 1 := V.move g
  let supp : Set (n → P.E s) := {γ | ∀ i : n, finCoord (W.vecAtPoint γ) i ∈ Ô (P.E s)}
  let dim : ℕ := Module.finrank ℝ (EuclideanSpace ℂ (P.Φ s × n))
  let D : ℝ := dim + 1
  have h_sep : Pairwise fun γ δ : supp ↦ 1 ≤ ‖W.archCoords γ - W.archCoords δ‖ :=
    fun γ δ h_ne ↦ one_le_norm_archCoords_sub W γ.2 δ.2 (coe_injective.ne h_ne)
  -- The packing bound in real dimension `dim`, with exponent `dim + 1`.
  obtain ⟨h_summable, h_pack⟩ : Summable (fun γ : supp ↦ exp ‖W.archCoords γ‖ ^ (-D)) ∧
      ∑' γ : supp, exp ‖W.archCoords γ‖ ^ (-D) ≤ (1 + 2 * 1 / 1) ^ dim * exp dim :=
    tsum_le_of_separated one_pos zero_le_one h_sep (fun _ ↦ one_le_exp (norm_nonneg _))
      (fun γ ↦ by linarith [add_one_le_exp ‖W.archCoords γ‖]) (lt_add_one _)
      (by simpa [D, dim] using add_one_le_exp _)
  -- The value at `y` is `θ f`. The matrix coefficients of `f` have the moduli of values of the
  -- vacuum.
  let f : 𝒮 V := V.ϱ y (V.ω g V.vacElem)
  have h_coeff (γ : n → P.E s) : ‖V.dataInner f (V.ϱ (V.vecAtPoint γ) f)‖ ≤
      extend val (fun γ : supp ↦ exp (√P.d * D ^ 2) * exp ‖W.archCoords γ‖ ^ (-D)) 0 γ := by
    have h_move : ‖V.dataInner f (V.ϱ (V.vecAtPoint γ) f)‖ = ‖vacuumFn (W.vecAtPoint γ)‖ := by
      -- The right side is a coefficient of `ω g vacElem`; translation by `y` only gives a phase.
      rw [vecAtPoint_move, ← V.dataInner_omega_vacElem_rho]
      simp [f, rho_swap _ _ y, Heisenberg.norm_eq_one]
    by_cases hγ : γ ∈ supp
    · grw [h_move, extend_val_apply hγ, norm_vacuumFn_vecAtPoint_le,
        exp_neg_pi_div_mul_sq_le (sqrt_pos.2 (Nat.cast_pos.2 (pos P.d))) _ D]
    · rw [h_move, extend_val_apply' hγ, Pi.zero_apply, norm_le_zero_iff, vacuumFn]
      exact mul_eq_zero_of_right _ (ite_eq_right hγ)
  have h_series : HasSum (fun γ : n → P.E s ↦ V.dataInner f (V.ϱ (V.vecAtPoint γ) f))
      (V.θ f * starRingEnd ℂ (V.θ f)) := hasSum_dataInner ..
  have h_theta : ‖V.θ f‖ ^ 2 ≤ exp (√P.d * D ^ 2) * (exp 2 ^ dim * exp dim) :=
    calc ‖V.θ f‖ ^ 2 = ‖V.θ f * starRingEnd ℂ (V.θ f)‖ := by simp [sq]
      _ ≤ exp (√P.d * D ^ 2) * ∑' γ : supp, exp ‖W.archCoords γ‖ ^ (-D) :=
        h_series.norm_le_of_bounded
          ((hasSum_extend_zero val_injective).2 (h_summable.hasSum.mul_left _)) h_coeff
      _ ≤ _ := by grw [h_pack, div_one, mul_one, add_comm 1, add_one_le_exp]
  -- Compare exponents: `dim` is `2 n` times the number of infinite places, which is at most
  -- `P.q₁ s`.
  have h_dim : dim ≤ 2 * (P.q₁ s * card n) := by
    simp only [dim, finrank_real_of_complex, finrank_euclideanSpace, card_prod]
    grw [← Core.numInfPlaces, numInfPlaces_E, Nat.totient_le, mul_comm (towerDeg s)]
  rw [show V.ω g V.vacElem y = V.θ f from (theta_rho ..).symm]
  refine le_of_sq_le_sq (h_theta.trans ?_) (exp_nonneg _)
  rw [← exp_nat_mul, ← exp_add, ← exp_add, ← exp_nat_mul, exp_le_exp]
  simpa [D] using sqrt_mul_sq_add_le_of_le (d := P.d) h_dim

namespace New.Parameters.IsJetConjugation

/-- Let `V` be a standard space of rank `n` (all signs `+1`, the point the identity matrix), and
let the `σ`-semilinear map `L` conjugate jets by `σ` at the scale `t`, scaling finite translations
by `b`. Then every value of `L ϱ(x) ω(g) (intVacuum V)`, for finite `x` and `g`, has norm at most
`exp (c (q₁ n + 1)²)`. Here `intVacuum V` is the integral multiple of the vacuum and `q₁ = P.q₁ s`
is the order of the root of unity that generates `E P s` over `K = ℚ(√-d)`. The real number
`c = P.constantBound` depends only on `P`: it is the sum of `P.vacuumBoundConst` (the constant in
the bound for the conjugates of the values of the integral vacuum), `2 d + 6` and a nonnegative
term. -/
theorem norm_map_intVacuum_le {P : Parameters} {s : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    {ε : n → ℤˣ} {V : Space (E P s) n ε} {σ : Gal(ℂ/K P)} {t : ℂ}
    {b : 𝔸f (E P s)} {L : 𝒮 V →ₛₗ[(σ : ℂ →+* ℂ)] 𝒮 V}
    (hL : IsJetConjugation V σ t b L) [hV : V.IsStd]
    (x : n → 𝔸f (E P s)) (g : Gf (E P s) n) (y : n → 𝔸 (E P s)) :
    ‖L (V.ϱ (finVec x) (V.ω (1, g) (intVacuum V))) y‖ ≤
      exp (P.constantBound * (P.q₁ s * card n + 1) ^ 2) := by
  -- `L (intVacuum V)` is `a` times a unit vacuum. So `‖a‖²` is its squared norm, which its values
  -- at finite points bound, and the values of unit vacua are bounded by `norm_omega_vac_le`.
  obtain ⟨c, u, h_vac⟩ : ∃ (c : ℂ) (u : unitary (𝔸f (E P s))),
      L V.vacElem = c • V.ω (1, scalarFin n u) V.vacElem := by
    obtain ⟨c, -, u, h_vac, -⟩ := hL.exists_map_schrodingerOp (R := ∅) disjoint_bot_left
    exact ⟨c, u, h_vac⟩
  obtain rfl : ε = 1 := hV.signs_eq_one
  let a : ℂ := σ (P.vacuumScale s ^ card n) * c
  -- `C` is a summand of `P.constantBound`.
  let C : ℕ := P.vacuumBoundConst
  have h_mem : intVacuum V ∈ V.finitePart := V.finitePart.smul_mem _ V.vacElem_mem_finitePart
  have h_image : L (intVacuum V) = a • V.ω (1, scalarFin n u) V.vacElem := by
    simp [a, intVacuum, h_vac, smul_smul]
  have h_value (w : n → 𝔸f (E P s)) :
      ‖L (intVacuum V) (finVec w)‖ ≤ exp (C * P.q₁ s ^ 2) ^ card n := by
    obtain ⟨w', rfl⟩ := hL.scalesTranslations.isUnit.smul_bijective.surjective w
    simpa only [← hL.map_apply_finVec h_mem] using norm_gal_intVacuum_le σ
  have ha : ‖a‖ ≤ exp (C * P.q₁ s ^ 2) ^ card n := by
    have h_norm : ‖V.dataInner (L (intVacuum V)) (L (intVacuum V))‖ ≤
        (exp (C * P.q₁ s ^ 2) ^ card n) ^ 2 := norm_dataInner_self_le h_value
    exact (sq_le_sq₀ (norm_nonneg a) (by positivity)).1 (by simpa [h_image, sq] using h_norm)
  have h_rank : (card n * P.q₁ s ^ 2 : ℝ) ≤ (P.q₁ s * card n + 1) ^ 2 := by
    have h_sq : (card n : ℝ) ≤ card n ^ 2 := mod_cast Nat.le_self_pow two_ne_zero _
    calc (card n * P.q₁ s ^ 2 : ℝ) ≤ (P.q₁ s * card n) ^ 2 := by grw [mul_pow, ← h_sq, mul_comm]
      _ ≤ (P.q₁ s * card n + 1) ^ 2 := by grw [← le_add_of_nonneg_right zero_le_one]
  calc _ = ‖a‖ * ‖V.ω (1, g * scalarFin n u) V.vacElem (y + finVec (b • x))‖ := by
        rw [hL.scalesTranslations.map_rho (omega_mem_finitePart g h_mem),
          hL.scalesTranslations.map_omega g h_mem, h_image]
        simp [norm_multiplierRatio, rep_apply_apply, Heisenberg.norm_eq_one]
    _ ≤ exp (C * P.q₁ s ^ 2) ^ card n * exp ((2 * P.d + 6) * (P.q₁ s * card n + 1) ^ 2) := by
        grw [ha, norm_omega_vac_le]
    _ ≤ exp ((C + (2 * P.d + 6)) * (P.q₁ s * card n + 1) ^ 2) := by
        grw [← exp_nat_mul, ← exp_add, add_mul (C : ℝ), mul_left_comm, h_rank]
    _ ≤ exp (P.constantBound * (P.q₁ s * card n + 1) ^ 2) := by
        gcongr
        -- the remaining summand of `P.constantBound` is nonnegative
        exact le_add_of_nonneg_right (by positivity)

end New.Parameters.IsJetConjugation

end ConjugatesOfJets

/-!
## Archimedean bounds for jets

`New.Space.jetSeries V c f` is the Taylor series of the theta function of `f` at scale `c`.
`New.jet ℂ Q` applies the differential operator `Q(∂)` at `0`.
-/

namespace New

open Matrix Fintype Finset Real MvPolynomial MeasureTheory Space Fock NumberField InfinitePlace
  Seesaw

/-- Let `κ τ h` count the columns of height `h` at the place `τ`. If `κ` fits the ranks `card n` and
`card n'` (`New.FitsRanks`: no column has height strictly between them), then the row lengths
`diagramWeight` of the diagram formed by the columns of height below `card n'`, summed over all
places and the first `card n` rows, add up to the number of boxes of that diagram. -/
lemma FitsRanks.sum_diagramWeight_eq_boxes {n n' Φ : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] [Fintype Φ] {κ : Φ → ℕ → ℕ}
    (hκ : FitsRanks (fun _ : Φ ↦ n) (fun _ : Φ ↦ n') κ) :
    ∑ x : Φ × Fin (Fintype.card n), diagramWeight (rankAt fun _ : Φ ↦ n') κ (x.1, x.2) =
      boxes κ (Fintype.card n') := by
  simp only [sum_prod_type, diagramWeight_apply]
  refine sum_congr rfl fun τ _ ↦ ?_
  -- Exchange the sums: a column of height `k` meets the rows `i < k`, and there are `k` of them
  -- in `Fin (card n)` unless `κ τ k = 0`.
  calc ∑ i : Fin (card n), ∑ k ∈ Ioo (i : ℕ) (card n'), κ τ k
    _ = ∑ k ∈ range (card n'), ∑ _i ∈ {i : Fin (card n) | i < k}, κ τ k := sum_comm' (by grind)
    _ = ∑ k ∈ range (card n'), k * κ τ k := by
        refine sum_congr rfl fun k hk ↦ ?_
        have h_height : k ≤ card n ∨ κ τ k = 0 := by grind [FitsRanks]
        simpa [Fin.card_filter_val_lt] using h_height

variable (P : Parameters) {s : ℕ} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n']

/-- `HasConjugateGrowth σ Q T L w A` says that the values of `Q`, conjugated by `σ`, grow at most
exponentially: `‖σ Q(z)‖ ≤ A * exp (w + L R)` whenever `∑ ‖σ z_i‖ ^ 2 ≤ T (2 L + 2) R`. For an
automorphism `σ`, `Q` homogeneous of degree `L`, `T > 0` and `A ≥ 0` it says that `A * exp w` bounds
`T ^ (L / 2) * ‖(σ Q)(y)‖ * exp (-L |y|² / (2 L + 2))` for all `y`: put `σ z = √T y`. -/
def HasConjugateGrowth {ι : Type*} [Fintype ι] (σ : ℂ → ℂ) (Q : MvPolynomial ι ℂ) (T : ℝ) (L : ℕ)
    (w A : ℝ) : Prop :=
  ∀ (z : ι → ℂ) (R : ℝ),
    ∑ i : ι, ‖σ (z i)‖ ^ 2 ≤ T * (2 * L + 2) * R → ‖σ (eval z Q)‖ ≤ A * exp (w + L * R)

/-- Against `normalizedVolume ι`, which is Lebesgue measure on `ι → ℂ` divided by `π ^ card ι`, the
Gaussian `exp (-|y|² / a)` has integral `a ^ card ι`. -/
lemma integral_exp_neg_inv_mul_normalizedVolume {ι : Type} [Fintype ι] [DecidableEq ι] {a : ℝ}
    (ha : 0 < a) :
    ∫ y : ι → ℂ, exp (-a⁻¹ * ∑ i : ι, ‖y i‖ ^ 2) ∂normalizedVolume ι = a ^ card ι := by
  rw [normalizedVolume, integral_smul_nnreal_measure,
    HasGaussianIntegral.integral_exp_eq (by positivity)]
  simp [NNReal.smul_def, mul_pow, pi_ne_zero]

/-- A function on `ι → ℂ` bounded by `C * exp (-|y|² / a)` has integral of norm at most
`C * a ^ card ι` against `normalizedVolume ι`, for `a > 0`. This measure is Lebesgue measure
divided by `π ^ card ι`, so that `exp (-|y|²)` has integral `1`. -/
lemma norm_integral_normalizedVolume_le {ι : Type} [Fintype ι] [DecidableEq ι] {a C : ℝ}
    (ha : 0 < a) {f : (ι → ℂ) → ℂ} (hf : ∀ y : ι → ℂ, ‖f y‖ ≤ C * exp (-a⁻¹ * ∑ i : ι, ‖y i‖ ^ 2)) :
    ‖∫ y : ι → ℂ, f y ∂normalizedVolume ι‖ ≤ C * a ^ card ι := by
  rw [← integral_exp_neg_inv_mul_normalizedVolume ha, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (.const_mul ?_ C) (.of_forall hf)
  -- The Gaussian is integrable because its integral is not zero.
  exact .of_integral_ne_zero ((integral_exp_neg_inv_mul_normalizedVolume ha).trans_ne
    (by positivity))

/-- The vacuum `realVac y` has modulus `exp (-|y|² / 2)`. -/
lemma norm_realVac {ι : Type} [Fintype ι] [DecidableEq ι] (y : ι → ℂ) :
    ‖realVac y‖ = exp (-(∑ i : ι, ‖y i‖ ^ 2) / 2) := by
  rw [realVac, star_dotProduct_self_eq_sum, Complex.norm_exp]
  norm_cast

/-- A factor `c` in the scale of the Taylor series can be moved into the differential operator: the
jet along `Q` at scale `c * a` is the jet along `Q (c z)` at scale `a`. Here the jet `jet ℂ Q G` of
a power series `G` along a polynomial `Q` is `Q(∂) G` at `0`, and `V.jetSeries a F` is the Taylor
series at scale `a` of the theta function of `F`, a vector of the space `𝒮 V` on which the Weil
representation acts. -/
lemma Parameters.jet_jetSeries_mul (V : Space (P.E s) (n' × n) (homSigns 1 1)) (c a : ℂ)
    (Q : MvPolynomial (P.Φ s × n' × n) ℂ) (F : 𝒮 V) :
    jet ℂ Q (V.jetSeries (c * a) F) = jet ℂ (aeval (c • X) Q) (V.jetSeries a F) := by
  have h_scale : bind₁ (fun i ↦ (c * a) • X i) Q = bind₁ (fun i ↦ a • X i) (aeval (c • X) Q) := by
    rw [Q.as_sum]
    simp [monomial_eq, ← C_mul', mul_assoc]
  rw [jet_jetSeries_eq_theta, jet_jetSeries_eq_theta, aeval_eq_bind₁, aeval_eq_bind₁, h_scale]

/-- Conjugates of jets as Gaussian integrals, on a space `V` whose signs `homSigns 1 1` are all
`+1`. Suppose that `σ` takes the Taylor series of `F` at scale `P.jetScale s` to that of `F'` at
scale `t`, up to the permutation `placePerm s σ` that `σ` induces on the infinite places `P.Φ s` of
`P.E s`. Then the conjugate of the jet of `F` along `Q` is the integral, for Lebesgue measure
divided by `π` in each complex coordinate, of the values of `F'` at `realVec y` against the vacuum
`realVac y = exp (-|y|² / 2)` and the polynomial `Q`, with conjugated coefficients and permuted
places, evaluated at `t ȳ`. -/
lemma Parameters.map_jet_eq_integral {V : Space (P.E s) (n' × n) (homSigns 1 1)} {σ : Gal(ℂ/P.K)}
    {t : ℂ} {F F' : 𝒮 V} (h_conj : IsJetConjugate σ (placePerm s σ) (P.jetScale s) t F F')
    (Q : MvPolynomial (P.Φ s × n' × n) ℂ) :
    σ (jet ℂ Q (V.jetSeries (P.jetScale s) F)) =
      ∫ y : P.Φ s × n' × n → ℂ,
        eval (t • star y) (rename (Prod.map (placePerm s σ) id) (Q.map (σ : ℂ →+* ℂ))) *
          realVac y * F' (realVec y) ∂normalizedVolume (P.Φ s × n' × n) := by
  set Q' := rename (Prod.map (placePerm s σ) id) (Q.map (σ : ℂ →+* ℂ))
  have h_rename : rename (Prod.map (placePerm s σ).symm id) Q' = Q.map (σ : ℂ →+* ℂ) := by
    simp [Q', Prod.map_comp_map]
  have h_jet : σ (jet ℂ Q (V.jetSeries (P.jetScale s) F)) = jet ℂ Q' (V.jetSeries t F') :=
    calc _ = jet ℂ (Q.map (σ : ℂ →+* ℂ))
            ((V.jetSeries t F').rename (Prod.map (placePerm s σ).symm id)) := by
          rw [← h_conj]
          exact map_jet (σ : ℂ →+* ℂ) _ _
      _ = jet ℂ Q' (V.jetSeries t F') :=
          jet_rename ((placePerm s σ).symm.prodCongr 1).toEmbedding h_rename _
  -- The jet is `θ` of an integrated operator, and the integrands agree monomial by monomial.
  rw [h_jet, jet_jetSeries_eq_theta, theta_integrated]
  congr! 2 with y
  rw [polyVector_apply, Q'.as_sum]
  simp [monomial_eq, ← C_mul', holomorphicCoord_eq, realSigns, pairSign]

/-- Cauchy's estimate for the jets of one finite translate `ϱ(x) ω(g) (intVacuum V)` of the integral
vacuum `intVacuum V` of a standard space `V` (all signs `+1`, the point the identity matrix), at
scale `c * P.jetScale s`. If `0 ≤ A`, `‖σ c‖ ^ 2 / P.bigOmega s ≤ T`, and
`‖σ Q(z)‖ ≤ A * exp (w + L R)` whenever `∑ ‖σ z_i‖ ^ 2 ≤ T (2 L + 2) R`, then the conjugate by `σ`
of the jet along `Q` has norm at most `exp (P.constantBound * (P.q₁ s * card (n' × n) + 1) ^ 2 +
w) * (2 L + 2) ^ card (P.Φ s × n' × n)` times `A`. -/
lemma Parameters.norm_jet_translate_le (V : Space (P.E s) (n' × n) (homSigns 1 1)) [V.IsStd]
    (σ : Gal(ℂ/P.K)) {c : ℂ} {Q : MvPolynomial (P.Φ s × n' × n) ℂ} {L : ℕ} {w A T : ℝ}
    (_hA : 0 ≤ A) (hT : ‖σ c‖ ^ 2 / P.bigOmega s ≤ T) (hQ : HasConjugateGrowth σ Q T L w A)
    (x : n' × n → 𝔸f (P.E s)) (g : Gf (P.E s) (n' × n)) :
    ‖σ (jet ℂ Q (V.jetSeries (c * P.jetScale s) (V.ϱ (finVec x) (V.ω (1, g) (intVacuum V)))))‖ ≤
      exp (P.constantBound * (P.q₁ s * card (n' × n) + 1) ^ 2 + w) *
        (2 * L + 2) ^ card (P.Φ s × n' × n) * A := by
  -- The conjugate jet is a Gaussian integral of a conjugate of `Q` against a bounded function.
  set F : 𝒮 V := V.ϱ (finVec x) (V.ω (1, g) (intVacuum V))
  set M : ℝ := P.constantBound * (P.q₁ s * card (n' × n) + 1) ^ 2
  have hF : F ∈ V.finitePart := rho_finVec_mem_finitePart x
    (omega_mem_finitePart g (Submodule.smul_mem _ _ vacElem_mem_finitePart))
  -- The `σ`-semilinear map `Λ` conjugates jets, and `Λ F` is bounded by `exp M`.
  obtain ⟨t, b, Λ, hΛ⟩ := exists_isJetConjugation V σ
  let Q' : MvPolynomial (P.Φ s × n' × n) ℂ :=
    rename (Prod.map (placePerm s σ) id) (MvPolynomial.map (σ : ℂ →+* ℂ) (aeval (c • X) Q))
  -- The integrand is bounded by a Gaussian: with `R = |y|² / (2 L + 2)` the growth `exp (L R)` of
  -- the polynomial and the vacuum `exp (-|y|² / 2)` multiply to `exp (-R)`.
  have h_integrand (y : P.Φ s × n' × n → ℂ) :
      ‖eval (t • star y) Q' * realVac y * Λ F (realVec y)‖ ≤
        A * exp (M + w) * exp (-(2 * L + 2 : ℝ)⁻¹ * ∑ i, ‖y i‖ ^ 2) := by
    let e : P.Φ s × n' × n ≃ P.Φ s × n' × n := (placePerm s σ).prodCongr 1
    let z : P.Φ s × n' × n → ℂ := c • σ.symm ∘ (t • star y) ∘ e
    set N : ℝ := ∑ i, ‖y i‖ ^ 2
    have h_eval : eval (t • star y) Q' = σ (eval z Q) := by
      unfold Q'
      rw [Q.as_sum]
      simp [z, e, monomial_eq, ← C_mul']
    have hz : ∑ i, ‖σ (z i)‖ ^ 2 ≤ T * (2 * L + 2) * (N / (2 * L + 2)) :=
      calc ∑ i, ‖σ (z i)‖ ^ 2 = ‖σ c‖ ^ 2 / P.bigOmega s * ∑ i, ‖y (e i)‖ ^ 2 := by
            simp [z, mul_sum, mul_pow, hΛ.norm_scale_sq, div_eq_mul_inv, mul_assoc]
        _ ≤ T * N := by grw [e.sum_comp fun i ↦ ‖y i‖ ^ 2, hT]
        _ = T * (2 * L + 2) * (N / (2 * L + 2)) := by field
    calc ‖eval (t • star y) Q' * realVac y * Λ F (realVec y)‖
      _ ≤ A * exp (w + L * (N / (2 * L + 2))) * exp (-N / 2) * exp M := by
          grw [norm_mul₃_le, hΛ.norm_map_intVacuum_le x g, h_eval, hQ z _ hz, norm_realVac]
      _ = A * exp (M + w) * exp (-(2 * L + 2 : ℝ)⁻¹ * N) := by
          simp only [mul_assoc, ← exp_add]
          congr 2
          field
  calc ‖σ (jet ℂ Q (V.jetSeries (c * P.jetScale s) F))‖
    _ = ‖∫ y : P.Φ s × n' × n → ℂ, eval (t • star y) Q' * realVac y * Λ F (realVec y)
          ∂normalizedVolume (P.Φ s × n' × n)‖ := by
        rw [P.jet_jetSeries_mul, P.map_jet_eq_integral (hΛ.isJetConjugate F hF)]
    _ ≤ A * exp (M + w) * (2 * L + 2) ^ card (P.Φ s × n' × n) :=
        norm_integral_normalizedVolume_le (by positivity) h_integrand
    _ = exp (M + w) * (2 * L + 2) ^ card (P.Φ s × n' × n) * A := by ring

/-- `P.IsVacuumCombination V B f` says that `f = ∑ r x • V.finHeisenbergOp x (intVacuum V)` is a
finite combination of Heisenberg translates of the integral vacuum by finite adelic vectors `x`,
with `∑ ‖σ (r x)‖ ≤ B` for every field automorphism `σ` of `ℂ`. The operator
`V.finHeisenbergOp x` is `V.ϱ (finVec x)` times the root of unity `stdLattice.semichar x`. -/
def Parameters.IsVacuumCombination {n : Type*} [Fintype n] [DecidableEq n] {ε : n → ℤˣ}
    (V : Space (P.E s) n ε) (B : ℝ) (f : 𝒮 V) : Prop :=
  ∃ r : (n → 𝔸f (P.E s)) →₀ ℂ, (∀ σ : ℂ ≃+* ℂ, ∑ x ∈ r.support, ‖σ (r x)‖ ≤ B) ∧
    f = ∑ x ∈ r.support, r x • V.finHeisenbergOp x (intVacuum V)

/-- An admissible combination `f = ∑ r x • V.finHeisenbergOp x (intVacuum V)` of size `B` is a
vacuum combination of size `B`. Admissible means that `r` has support in `A`, that each `d * r x` is
integral at the primes not dividing `q`, and, since the argument `True` turns this condition on,
that `∑ ‖σ (r x)‖ ≤ B` for every automorphism `σ` of `ℂ`. Only the last condition is kept. -/
lemma Parameters.isVacuumCombination_of_isAdmissibleCombination {n : Type*} [Fintype n]
    [DecidableEq n] {ε : n → ℤˣ} {V : Space (P.E s) n ε} {A : Set (n → 𝔸f (P.E s))} {q d : ℕ}
    {B : ℝ} {f : 𝒮 V}
    (hf : IsAdmissibleCombination (fun x : n → 𝔸f (P.E s) ↦ V.finHeisenbergOp x (intVacuum V)) A q d
      True B f) :
    P.IsVacuumCombination V B f :=
  let ⟨r, hr, h_expand⟩ := hf
  ⟨r, hr.sum_norm_le trivial, h_expand⟩

/-- A single Heisenberg translate `V.finHeisenbergOp x (intVacuum V)` of the integral vacuum is a
vacuum combination with coefficient bound `1`. -/
lemma Parameters.isVacuumCombination_finHeisenbergOp {n : Type*} [Fintype n] [DecidableEq n]
    {ε : n → ℤˣ} (V : Space (P.E s) n ε) (x : n → 𝔸f (P.E s)) :
    P.IsVacuumCombination V 1 (V.finHeisenbergOp x (intVacuum V)) :=
  ⟨.single x 1, by simp, by simp⟩

/-- The factor in the size bounds for the jets of a combination of translates of the integral vacuum
whose coefficients have total size `B`, for a growth rate `L` and an extra exponent `w`. It equals
`B * exp (P.constantBound * (P.q₁ s * card (n' × n) + 1) ^ 2) * exp w` times
`(2 L + 2) ^ card (P.Φ s × n' × n)`. -/
noncomputable def Parameters.jetSizeBound (s : ℕ) (n n' : Type*) [Fintype n] [Fintype n'] (B : ℝ)
    (L : ℕ) (w : ℝ) : ℝ :=
  B * exp (P.constantBound * (P.q₁ s * card (n' × n) + 1) ^ 2 +
    card (P.Φ s × n' × n) * log (2 * L + 2) + w)

omit [DecidableEq n] [DecidableEq n'] in
/-- The factor `P.jetSizeBound s n n' B L w` in closed form: it is `B * (exp (P.constantBound *
(P.q₁ s * card (n' × n) + 1) ^ 2 + w) * (2 * L + 2) ^ card (P.Φ s × n' × n))`. -/
lemma Parameters.jetSizeBound_eq (B : ℝ) (L : ℕ) (w : ℝ) :
    P.jetSizeBound s n n' B L w =
      B * (exp (P.constantBound * (P.q₁ s * card (n' × n) + 1) ^ 2 + w) *
        (2 * L + 2) ^ card (P.Φ s × n' × n)) := by
  simp only [jetSizeBound, exp_add, exp_nat_mul, exp_log (show 0 < (2 * L + 2 : ℝ) by positivity)]
  ring

/-- Let `a` and `b` be automorphic characters of the norm-one adeles that have a weight: on points
`u` with integral finite part, `a u = ∏ u_v ^ ea v * ∏ ψ w (u mod w)`, over the infinite places `v`
and the finite places `w`, and the same for `b` with `eb` and `ψ'`. Then the conjugates over `P.K`
of the value `a(det h) b(det g)⁻¹` of `pairChar a b` at finite points `g` and `h` have norm one. -/
lemma Parameters.norm_map_pairChar {ea eb : P.Φ s → ℤ} {a b : AutChar (P.E s)}
    {ψ ψ' : (w : FinPlace (P.E s)) → MulChar (ResField w) ℂ}
    [AutChar.HasWeight a ea ψ] [AutChar.HasWeight b eb ψ']
    (σ : Gal(ℂ/P.K)) (g : Gf (P.E s) n) (h : Gf (P.E s) n') :
    ‖σ (pairChar a b (((1, g), (1, h)) : G (P.E s) 1 × G (P.E s) 1))‖ = 1 := by
  simp [pairChar_apply, AutChar.HasWeight.norm_map_eq_one, funext_iff]

/-- Size of jets. Let `f = ∑ r x • (translate by x of the integral vacuum)` be a finite combination,
on the space of maps between the standard hermitian spaces of ranks `n` and `n'` over `P.E s`, with
`∑ ‖τ (r x)‖ ≤ B` for every automorphism `τ` of `ℂ`. Move it by the points `g` and `h` of the finite
adelic unitary groups under the Weil representation `pairWeil` of the dual pair, twisted by
automorphic characters `a` and `b`, and take the Taylor series of its theta function at scale
`c * P.jetScale s`. The jet along `Q` is `Q(∂)` of this series at `0`. If `0 ≤ A`,
`‖σ c‖ ^ 2 / P.bigOmega s ≤ T`, and `‖σ Q(z)‖ ≤ A * exp (w + L R)` whenever
`∑ ‖σ z_i‖ ^ 2 ≤ T (2 L + 2) R`, then the conjugate by `σ` of the jet has norm at most
`P.jetSizeBound s n n' B L w * A`. -/
lemma Parameters.norm_jet_le_of_isVacuumCombination
    {ea eb : P.Φ s → ℤ} {a b : AutChar (P.E s)}
    {ψ ψ' : (w : FinPlace (P.E s)) → MulChar (ResField w) ℂ}
    [AutChar.HasWeight a ea ψ] [hb : AutChar.HasWeight b eb ψ']
    {B : ℝ} {f : 𝒮 ((stdSpace (P.E s) n).hom (stdSpace (P.E s) n'))}
    (hf : P.IsVacuumCombination ((stdSpace (P.E s) n).hom (stdSpace (P.E s) n')) B f)
    {σ : ℂ ≃+* ℂ} {c : ℂ} (g : Gf (P.E s) n) (h : Gf (P.E s) n')
    {Q : MvPolynomial (P.Φ s × n' × n) ℂ} {L : ℕ} {w A T : ℝ}
    (hA : 0 ≤ A) (hT : ‖σ c‖ ^ 2 / P.bigOmega s ≤ T) (hQ : HasConjugateGrowth σ Q T L w A) :
    ‖σ (jet ℂ Q (jetSeries ((stdSpace (P.E s) n).hom (stdSpace (P.E s) n')) (c * P.jetScale s)
        (pairWeil (stdSpace (P.E s) n) (stdSpace (P.E s) n') a b ((1, g), 1, h) f)))‖ ≤
      P.jetSizeBound s n n' B L w * A := by
  -- Expand `f` as a sum of translates of the integral vacuum and bound each one, replacing `σ` by
  -- an automorphism `σ'` over `P.K` that gives the same norms.
  obtain ⟨σ', hσ'⟩ := P.exists_algEquiv_norm_eq σ
  obtain ⟨r, h_size, rfl⟩ := hf
  set V : Space (P.E s) (n' × n) (homSigns 1 1) := (stdSpace (P.E s) n).hom (stdSpace (P.E s) n')
  set p : G (P.E s) (1 : n → ℤˣ) × G (P.E s) (1 : n' → ℤˣ) := ((1, g), 1, h) with hp
  set W : 𝒮 V →L[ℂ] 𝒮 V := pairWeil (stdSpace (P.E s) n) (stdSpace (P.E s) n') a b p with hW
  let C : ℝ := exp (P.constantBound * (P.q₁ s * card (n' × n) + 1) ^ 2 + w) *
    (2 * L + 2) ^ card (P.Φ s × n' × n)
  have hT' : ‖σ' c‖ ^ 2 / P.bigOmega s ≤ T := by rwa [← hσ' c]
  have hQ' : HasConjugateGrowth σ' Q T L w A := by simpa only [HasConjugateGrowth, hσ'] using hQ
  have h_term (x : n' × n → 𝔸f (P.E s)) :
      ‖σ (jet ℂ Q (V.jetSeries (c * P.jetScale s) (W (V.finHeisenbergOp x (intVacuum V)))))‖ ≤
        C * A := by
    -- `W` is a scalar times `ω` at a finite point `k`, and `ω(k)` moves past the translation.
    -- The conjugates of the scalars have norm one.
    let k : Gf (P.E s) (n' × n) := (G.onHom p).2
    obtain ⟨ζ, hζ, h_fin⟩ := V.exists_isOfFinOrder_finHeisenbergOp_eq_smul_rho (k.val.val *ᵥ x)
    have h_move : W (V.finHeisenbergOp x (intVacuum V)) =
        (pairChar a b p * ζ) • V.ϱ (finVec (k.val.val *ᵥ x)) (V.ω (1, k) (intVacuum V)) := by
      rw [hW, pairWeil_apply, hp, G.onHom_fin, omega_finHeisenbergOp, h_fin, mul_smul]
      rfl
    have h_unit : ‖σ' (pairChar a b p * ζ)‖ = 1 := by
      rw [map_mul, norm_mul, P.norm_map_pairChar σ' g h, one_mul]
      exact (MonoidHom.isOfFinOrder (σ' : ℂ →* ℂ) hζ).norm_eq_one
    rw [hσ', h_move, map_smul, map_smul, smul_eq_mul, map_mul, norm_mul, h_unit, one_mul]
    exact P.norm_jet_translate_le V σ' hA hT' hQ' _ k
  calc _ = ‖∑ x ∈ r.support, σ (r x) *
          σ (jet ℂ Q (V.jetSeries (c * P.jetScale s)
            (W (V.finHeisenbergOp x (intVacuum V)))))‖ := by
        simp only [map_sum, map_smul, smul_eq_mul, map_mul]
    _ ≤ ∑ x ∈ r.support, ‖σ (r x)‖ * (C * A) :=
        norm_sum_le_of_le _ fun x _ ↦ by grw [norm_mul, h_term]
    _ ≤ B * (C * A) := by grw [← sum_mul, h_size σ]
    _ = P.jetSizeBound s n n' B L w * A := by rw [jetSizeBound_eq, mul_assoc B]

/-- Let `L > 0`, `u` and `R` be real numbers, and let `(τ, i)` run over `Φ × I` for a finite type
`Φ` and a finite set `I` of natural numbers. If the nonnegative numbers `ρ τ i` have sum at most
`exp u * (2 L + 2) * R`, then for all exponents `l (τ, i) : ℕ` the square root of the monomial
`∏ ρ ^ l` is at most `exp (w + L R)`, where `2 w = ∑ (l / L + log l! + l * u)`. -/
lemma sqrt_prod_pow_le_exp {Φ : Type*} [Fintype Φ] (I : Finset ℕ) (ρ : Φ → ℕ → NNReal)
    (l : Φ × ℕ → ℕ) {L u R : ℝ} (hL : 0 < L)
    (h_sum : ∑ τ : Φ, ∑ i ∈ I, (ρ τ i : ℝ) ≤ exp u * (2 * L + 2) * R) :
    √(∏ τ : Φ, ∏ i ∈ I, (ρ τ i : ℝ) ^ l (τ, i)) ≤
      exp ((∑ τ : Φ, ∑ i ∈ I, (l (τ, i) / L + log (l (τ, i)).factorial + l (τ, i) * u)) / 2 +
        L * R) := by
  -- Bound `ρ ^ l` by `l! exp (l v + ρ exp (-v))` with `v = u + 1 / L`. The terms `ρ exp (-v)` add
  -- up to at most `(2 L + 2) R / (1 / L + 1) = 2 L R`, as `exp (1 / L) ≥ 1 / L + 1`.
  set S : ℝ := ∑ τ : Φ, ∑ i ∈ I, (ρ τ i : ℝ) with hS
  have h_tail : S / exp (u + L⁻¹) ≤ 2 * (L * R) :=
    calc _ ≤ exp u * (2 * L + 2) * R / (exp u * (L⁻¹ + 1)) := by
          grw [exp_add, ← add_one_le_exp L⁻¹, h_sum]
      _ = 2 * (L * R) := by field
  set w : ℝ := ∑ τ : Φ, ∑ i ∈ I, (l (τ, i) / L + log (l (τ, i)).factorial + l (τ, i) * u) with hw
  have h_prod : ∏ τ : Φ, ∏ i ∈ I, (ρ τ i : ℝ) ^ l (τ, i) ≤ exp (w + S / exp (u + L⁻¹)) :=
    calc _ ≤ ∏ τ : Φ, ∏ i ∈ I,
            exp (log (l (τ, i)).factorial + l (τ, i) * (u + L⁻¹) + ρ τ i / exp (u + L⁻¹)) := by
          gcongr with τ _ i _
          exact pow_le_exp_log_factorial_add _ _ _
      _ = exp (w + S / exp (u + L⁻¹)) := by
          simp only [hw, hS, ← exp_sum, sum_div, ← sum_add_distrib]
          congr! 3
          ring
  grw [h_prod, h_tail, ← exp_half, add_div, mul_div_cancel_left₀ _ two_ne_zero]

/-- The exponent `∑ (l / L + log l! + l * u) / 2` in the growth bound for Schur matrices. Here
`κ τ h` counts the columns of height `h` at the place `τ`, and `l` runs over the lengths of the
first `card n` rows, at all places, of the diagram formed by the columns of height below
`card n'`. The bound `rankAt (fun _ ↦ n')` is `card n'` at every place, so the length of row `i` at
`τ`, a value of `diagramWeight`, is the sum of `κ τ h` over `i < h < card n'`. -/
noncomputable def schurGrowthExponent (n n' : Type) [Fintype n] [Fintype n'] {Φ : Type} [Fintype Φ]
    (κ : Φ → ℕ → ℕ) (L : ℕ) (u : ℝ) : ℝ :=
  (∑ τ : Φ, ∑ i ∈ range (card n),
    (diagramWeight (rankAt fun _ : Φ ↦ n') κ (τ, i) / L +
      log (diagramWeight (rankAt fun _ : Φ ↦ n') κ (τ, i)).factorial +
      diagramWeight (rankAt fun _ : Φ ↦ n') κ (τ, i) * u)) / 2

/-- Growth of the matrix coefficients `z ↦ y ⬝ᵥ schur κ z *ᵥ ξ` of the Schur matrix of a lift weight
`κ`. If the conjugate by `σ` of the covector `y` has dual norm at most one for the Gram norm
`√(weylNormSq ·)`, the conjugated values are at most that norm of the conjugate of `ξ` times
`exp (w + L R)` whenever `∑ ‖σ z_i‖ ^ 2 ≤ exp u * (2 L + 2) * R`, where
`w = schurGrowthExponent n n' κ L u` is half the sum of `l / L + log l! + l * u` over the row
lengths `l`. Here `κ τ h` counts the columns of height `h` at the place `τ`, and
`IsLiftWeight n n' κ eb e` says that `card n < card n'`, that no column has height strictly between
these ranks, and that `e τ = eb τ + κ τ (card n)`. -/
lemma Parameters.hasConjugateGrowth_schurCoeffPoly {κ : P.Φ s → ℕ → ℕ} {eb e : P.Φ s → ℤ}
    (hκ : IsLiftWeight n n' κ eb e) {σ : ℂ ≃+* ℂ} {y : WeylIndex n' κ → ℂ}
    (hy : ∀ η : WeylIndex n' κ → ℂ, ‖σ (y ⬝ᵥ η)‖ ≤ √(weylNormSq (σ ∘ η)))
    (ξ : WeylIndex n κ → ℂ) (L : ℕ+) (u : ℝ) :
    HasConjugateGrowth σ (schurCoeffPoly y ξ) (exp u) L (schurGrowthExponent n n' κ L u)
      √(weylNormSq (σ ∘ ξ)) := by
  intro z R hz
  have h_fits : FitsRanks (fun _ : P.Φ s ↦ n) (fun _ : P.Φ s ↦ n') κ := hκ.1
  set l : P.Φ s × ℕ →₀ ℕ := diagramWeight (rankAt fun _ : P.Φ s ↦ n') κ
  let Z : P.Φ s → Matrix n' n ℂ := fun τ ↦ of fun j i ↦ z (τ, j, i)
  -- The Schur matrix of `σ z` has squared norm at most `∏ ρ ^ l` with `∑ ρ ≤ ∑ ‖σ (z i)‖ ^ 2`.
  obtain ⟨ρ, h_row, h_op⟩ : ∃ ρ : P.Φ s → ℕ → NNReal,
      (∀ τ : P.Φ s, ∑ i ∈ range (card n), (ρ τ i : ℝ) ≤ ∑ j : n', ∑ i : n, ‖σ (z (τ, j, i))‖ ^ 2) ∧
      ∀ η : WeylIndex n κ → ℂ, weylNormSq (schur κ (fun τ ↦ (Z τ).map σ) *ᵥ η) ≤
        (∏ τ : P.Φ s, ∏ i ∈ range (card n), (ρ τ i : ℝ) ^ l (τ, i)) * weylNormSq η := by
    simpa [Z] using weylNormSq_schur_le h_fits fun τ ↦ (Z τ).map σ
  have h_sum : ∑ τ : P.Φ s, ∑ i ∈ range (card n), (ρ τ i : ℝ) ≤ exp u * (2 * L + 2) * R :=
    (Finset.sum_le_sum fun τ _ ↦ h_row τ).trans (by simpa [sum_prod_type] using hz)
  have h_map : σ ∘ (schur κ Z *ᵥ ξ) = schur κ (fun τ ↦ (Z τ).map σ) *ᵥ (σ ∘ ξ) := by
    rw [schur_map h_fits]
    exact funext ((σ : ℂ →+* ℂ).map_mulVec _ ξ)
  calc ‖σ (eval z (schurCoeffPoly y ξ))‖
    _ ≤ √(weylNormSq (schur κ (fun τ ↦ (Z τ).map σ) *ᵥ (σ ∘ ξ))) := by
        grw [eval_schurCoeffPoly hκ, hy, h_map]
    _ ≤ √(weylNormSq (σ ∘ ξ)) * exp (schurGrowthExponent n n' κ L u + L * R) := by
        grw [h_op, sqrt_mul (by positivity),
          sqrt_prod_pow_le_exp _ ρ l (Nat.cast_pos.2 L.pos) h_sum, mul_comm, schurGrowthExponent]

/-- Size of Schur jets. Let `f = ∑ r x • (translate by x of the integral vacuum)` be a finite
combination with `∑ ‖τ (r x)‖ ≤ B` for every automorphism `τ` of `ℂ`. It lies in the space `𝒮` of
the Weil representation `pairWeil` of the dual pair of the standard hermitian spaces `stdSpace`
(form and point the identity matrix) of ranks `n` and `n'` over `E = P.E s`. This representation is
twisted by automorphic characters `a` and `b` of weights `ea`, `eb` (an exponent for each infinite
place) and tame parts `ψ`, `ψ'` (a character of each residue field). Move `f` by the points `g` and
`h` of the finite adelic unitary groups `Gf`, and let `F` be the Taylor series of its theta function
at scale `c * P.jetScale s`, where `P.jetScale s = P.periodFactor s * √(2π / √d) / Ω₀` is a nonzero
number and `Ω₀` is the period of `K = ℚ(√-d)`. Let `κ` be a lift weight and `t = ‖σ c‖ ^ 2 / Ω`,
where `Ω = P.bigOmega s = exp (γ - Re L'/L(1, χ_K)) * 2π / rd_E`, with `γ` Euler's constant, `χ_K`
the quadratic character of `K` and `rd_E` the root discriminant of `E`.

Let `schurJet κ F` be the matrix whose entries are `Q(∂) F` at `0`, for `Q` the polynomial entries
of the Schur matrix `schur κ z`. For every positive integer `L`, it multiplies the Gram norm
`√(weylNormSq ·)` of the conjugate of `ξ` by at most `P.jetSizeBound s n n' B L w`, where
`w = schurGrowthExponent n n' κ L (log t)` is half the sum of `l / L + log l! + l * log t` over the
row lengths `l`. This factor is `B * exp w` times `(2 L + 2) ^ card (P.Φ s × n' × n)` times a
constant that depends only on `P`, `s` and the ranks (`jetSizeBound_eq`). A lift weight
(`IsLiftWeight`) has `card n < card n'`, no column of height strictly between the ranks, and
determinant exponent `e τ = eb τ + κ τ (card n)`. -/
lemma Parameters.sqrt_weylNormSq_schurJet_le_of_isVacuumCombination
    {ea eb : P.Φ s → ℤ} {a b : AutChar (P.E s)}
    {ψ ψ' : (w : FinPlace (P.E s)) → MulChar (ResField w) ℂ}
    [AutChar.HasWeight a ea ψ] [hb : AutChar.HasWeight b eb ψ']
    {B : ℝ} {f : 𝒮 ((stdSpace (P.E s) n).hom (stdSpace (P.E s) n'))}
    (hf : P.IsVacuumCombination ((stdSpace (P.E s) n).hom (stdSpace (P.E s) n')) B f)
    {σ : ℂ ≃+* ℂ} {c : ℂ} (g : Gf (P.E s) n) (h : Gf (P.E s) n') (L : ℕ+)
    {κ : P.Φ s → ℕ → ℕ} {e : P.Φ s → ℤ} (hκ : IsLiftWeight n n' κ eb e) (ξ : WeylIndex n κ → ℂ) :
    √(weylNormSq (σ ∘ (schurJet κ
        (jetSeries ((stdSpace (P.E s) n).hom (stdSpace (P.E s) n')) (c * P.jetScale s)
          (pairWeil (stdSpace (P.E s) n) (stdSpace (P.E s) n') a b ((1, g), 1, h) f)) *ᵥ ξ))) ≤
      P.jetSizeBound s n n' B L (schurGrowthExponent n n' κ L (log (‖σ c‖ ^ 2 / P.bigOmega s))) *
        √(weylNormSq (σ ∘ ξ)) := by
  -- By duality, apply the bound for jets to the polynomials `schurCoeffPoly y ξ`, where the
  -- conjugate of the covector `y` has norm at most one.
  refine sqrt_weylNormSq_le_of_dual σ fun y hy ↦ ?_
  rw [dotProduct_schurJet_mulVec]
  exact P.norm_jet_le_of_isVacuumCombination hf g h (sqrt_nonneg _) (le_exp_log _)
    (P.hasConjugateGrowth_schurCoeffPoly hκ hy ξ L _)

end New
