import New.Reduction.IntegralTargetForms
import New.Spanning.SecondMoment.SpanningTheorem
import New.UpperBound.Divisibility.LocalDivisibility
import New.UpperBound.Seesaw.SeesawIdentity
import New.UpperBound.Size.ArchimedeanSize

/-!
# Theorem A (short forms) and Theorem B (enough forms)

The source is the space `ramifiedSourceForms` of ramified source forms. It lies in the space
`SourceForm` of all source forms, whose dimension is written `D_X`. The target is the space
`targetForms`, whose dimension `D.targetDim` is written `d_T`. We define the translates `s 𝔭` of the
map `𝔭` from the source to the target and prove Theorems A and B: the source is spanned by integral
forms `φ` whose images `s 𝔭 φ` have short lifts `Θ₁ s 𝔭 φ`, these images have small index, and the
images of few translates span almost all of the target.

Notions from other files:
* `D.poincare` is the Poincaré map `𝒫` from source forms to the forms on `Y₀`, without the factor
  `poincareScale`, which the number `c_ss` (`D.seesawConst`, entering as its inverse in
  `D.scaledInclusion`) absorbs. `D.chosenGL` is the finite group `Ḡ` acting on the forms on `Y₀`,
  with the central projection `e₀` to the good part.
* `D.Θ ϑ` is the chain of lifts `Θ_ϑ` of target forms for the twist `ϑ`.
* `D.targetLattice` records which target forms are integral at each `ι`, and its `IndexLe y δ` says
  that at every `ι ∣ l` the family `y` becomes integral with loss `δ_l`, where `∑ δ_l log l ≤ δ`.
* `D.gain l` is the divisibility asked of the chain at `l`; `D.errorUnit` is `f a log³ b`, with
  `D.logB` standing for `log b`.
-/

noncomputable section

namespace New.Data

open Submodule Module Real Finset LevelPlaces.LevelForm Parameters

variable {P : Parameters} (D : Data P)

/-! ### The errors in the divisibility of the composite lift -/

/-- A choice of the numbers `err_l` in the theorem on the divisibility of the composite lift,
`New.Data.exists_err_gaugeLe_compositeLift`. -/
def divisibilityError : ℕ → ℝ := D.exists_err_gaugeLe_compositeLift.choose

lemma divisibilityError_nonneg (l : ℕ) : 0 ≤ D.divisibilityError l :=
  D.exists_err_gaugeLe_compositeLift.choose_spec.1 l

/-- The error `err_l` is zero if `l ≠ N` and either `l` splits in `K` (that is, the value at `l` of
the character `chiK P.d` of the imaginary quadratic field `K = ℚ(√-d)` is `1`) or `l` is at least
the cut-off `x₁`. -/
lemma divisibilityError_eq_zero {l : ℕ} (hN : l ≠ D.N) (hl : chiK P.d l = 1 ∨ D.x₁ ≤ l) :
    D.divisibilityError l = 0 := by
  obtain ⟨-, h_zero, -⟩ := D.exists_err_gaugeLe_compositeLift.choose_spec
  exact h_zero l hN hl

/-- For every finite set `U` of natural numbers, the sum over `l ∈ U` of `err_l log l`, with
`err_l = D.divisibilityError l`, is at most the unit of loss `D.errorUnit = f a log³ b`. -/
lemma sum_divisibilityError_mul_log_le (U : Finset ℕ) :
    ∑ l ∈ U, D.divisibilityError l * log l ≤ D.errorUnit := by
  obtain ⟨-, -, h_sum, -⟩ := D.exists_err_gaugeLe_compositeLift.choose_spec
  exact h_sum U

/-- Fix a prime `l` and an `l`-adic place of `ℂ`, with valuation ring `𝒪 = embValRing`. Let
`gain_l = D.gain l` be the divisibility asked of the chain of lifts at `l`, and
`err_l = D.divisibilityError l` the error allowed in it. There are `j ≤ err_l · dim_ℂ D.SourceForm`
and an `𝒪`-module `S` of source forms with two properties.
* Every finite family of integral ramified source forms is carried into `S` by a square matrix over
  `𝒪` whose determinant divides `l ^ j` (`ColengthDvd`).
* For `φ ∈ S`, the form `B_ϑ φ = compositeLift ϑ Ψ φ` has valuation at least `gain_l - err_l`: the
  `l`-adic gauge at `g` of its value at each finite adelic point `g` is at most
  `l ^ (err_l - gain_l)`.

Here `ϑ` runs over the twists whose level `ϑ.normQ` is prime to `l`, and `Ψ` over their chain data
(`IsChainDatum`), which are finitely supported coefficient functions on `D.Translations`, the tuples
of translations that define a chain of lifts. -/
lemma exists_colengthDvd_gaugeLe_divisibilityError (l : ℕ) [Fact l.Prime] [PadicPlace l] :
    ∃ (j : ℕ) (S : Submodule embValRing D.SourceForm),
      j ≤ D.divisibilityError l * finrank ℂ D.SourceForm ∧
      ColengthDvd (D.integralSourceForms ⊓ D.ramifiedSourceForms.restrictScalars embValRing) S
        (l ^ j) ∧
      ∀ (ϑ : D.Twist) (Ψ : D.Translations →₀ ℂ), IsChainDatum ϑ Ψ → l.Coprime ϑ.normQ →
        ∀ φ ∈ S, GaugeLe 1 (l ^ (D.divisibilityError l - D.gain l)) (compositeLift ϑ Ψ φ) := by
  obtain ⟨-, -, -, h_local⟩ := D.exists_err_gaugeLe_compositeLift.choose_spec
  obtain ⟨j, S, hj, -, h_index, h_gauge⟩ := h_local l
  exact ⟨j, S, hj, h_index, h_gauge⟩

/-! ### The map from source forms to target forms -/

/-- The integer `g_l = ⌊gain_l - err_l⌋`. For a prime `l` it vanishes unless `l` is non-split and
below `x₁` or `l = N`. -/
def gainExponent (l : ℕ) : ℤ := ⌊D.gain l - D.divisibilityError l⌋

/-- The positive rational number `c_B = ∏ l ^ (-g_l)`, the product taken over the non-split primes
below `x₁` and the level `N`. -/
def invGainFactor : ℚ := ∏ l ∈ D.smallNonsplitPrimes ∪ {D.N}, (l : ℚ) ^ (-D.gainExponent l)

/-- Every `l` in `D.smallNonsplitPrimes ∪ {D.N}`, the set of primes indexing the product
`c_B = D.invGainFactor`, is prime. The non-split primes below `x₁` are prime by definition, and the
level `N` is prime. -/
lemma prime_of_mem_smallNonsplitPrimes_union {l : ℕ} (hl : l ∈ D.smallNonsplitPrimes ∪ {D.N}) :
    l.Prime := by
  rcases mem_union.1 hl with h_nonsplit | hN
  · obtain ⟨-, h_prime, -⟩ := mem_filter.1 h_nonsplit
    exact h_prime
  · rw [mem_singleton.1 hN]
    exact D.N_prime

lemma invGainFactor_pos : 0 < D.invGainFactor :=
  prod_pos fun _ hl ↦ zpow_pos (mod_cast (D.prime_of_mem_smallNonsplitPrimes_union hl).pos) _

/-- The sum of `log l` over the non-split primes `l` below `x₁` and `l = N` is at most the
weight `b = D.b`, which is `exp D.logB`. It bounds the loss from rounding the exponents `g_l` down
to integers. -/
lemma sum_log_smallNonsplitPrimes_union_le : ∑ l ∈ D.smallNonsplitPrimes ∪ {D.N}, log l ≤ D.b := by
  have h_term : ∀ l ∈ D.smallNonsplitPrimes, log l ≤ D.x₁ := by
    intro l hl
    have h_lt : l < ⌈D.x₁⌉₊ := mem_range.1 (mem_of_mem_filter l hl)
    exact (log_le_self l.cast_nonneg).trans (Nat.lt_ceil.1 h_lt).le
  have h_card : #D.smallNonsplitPrimes ≤ ⌈D.x₁⌉₊ := (card_filter_le _ _).trans_eq (card_range _)
  calc ∑ l ∈ D.smallNonsplitPrimes ∪ {D.N}, log l
      ≤ ∑ l ∈ D.smallNonsplitPrimes, log l + log D.N := by
        rw [← sum_singleton (fun l : ℕ ↦ log l) D.N, ← sum_union_inter]
        exact le_add_of_nonneg_right (sum_nonneg fun l _ ↦ log_natCast_nonneg l)
    _ ≤ ⌈D.x₁⌉₊ * D.x₁ + log D.N := by grw [sum_le_card_nsmul _ _ _ h_term, nsmul_eq_mul, h_card]
    _ ≤ D.b := D.le_of_hasLogBound

/-- The number `c_B = D.invGainFactor` satisfies `log c_B ≤ -∑ gain_l log l + f a log³ b + b`, the
sum taken over the non-split primes `l` below the cut-off `x₁ = D.x₁`. -/
lemma log_invGainFactor_le :
    log D.invGainFactor ≤ -∑ l ∈ D.smallNonsplitPrimes, D.gain l * log l + D.errorUnit + D.b := by
  have h_ne : ∀ l ∈ D.smallNonsplitPrimes ∪ {D.N}, (l : ℝ) ^ (-D.gainExponent l) ≠ 0 := fun l hl ↦
    zpow_ne_zero _ (mod_cast (D.prime_of_mem_smallNonsplitPrimes_union hl).ne_zero)
  -- The level `N` is at least `x₁`, so it has no gain.
  have h_gain : ∑ l ∈ D.smallNonsplitPrimes, D.gain l * log l =
      ∑ l ∈ D.smallNonsplitPrimes ∪ {D.N}, D.gain l * log l := by
    refine sum_subset subset_union_left fun l hl hl_notMem ↦ ?_
    rw [mem_singleton.1 ((mem_union.1 hl).resolve_left hl_notMem),
      D.gain_eq_zero (.inr D.le_of_hasLogBound), zero_mul]
  calc log D.invGainFactor = ∑ l ∈ D.smallNonsplitPrimes ∪ {D.N}, -D.gainExponent l * log l := by
        push_cast [invGainFactor, log_prod h_ne, log_zpow]
        rfl
    _ ≤ ∑ l ∈ D.smallNonsplitPrimes ∪ {D.N}, (-D.gain l + D.divisibilityError l + 1) * log l := by
        gcongr with l
        grw [gainExponent, ← Int.sub_one_lt_floor]
        linarith
    _ = -∑ l ∈ D.smallNonsplitPrimes, D.gain l * log l +
          ∑ l ∈ D.smallNonsplitPrimes ∪ {D.N}, D.divisibilityError l * log l +
          ∑ l ∈ D.smallNonsplitPrimes ∪ {D.N}, log l := by
        simp only [h_gain, add_mul, neg_mul, one_mul, sum_add_distrib, sum_neg_distrib]
    _ ≤ -∑ l ∈ D.smallNonsplitPrimes, D.gain l * log l + D.errorUnit + D.b := by
        grw [sum_divisibilityError_mul_log_le, sum_log_smallNonsplitPrimes_union_le]

/-- For a prime `l`, the absolute value in `ℂ_l` of `c_B = D.invGainFactor` is that of
`l ^ (-g_l)`. -/
lemma norm_invGainFactor (l : ℕ) [hl : Fact l.Prime] :
    ‖(D.invGainFactor : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ (-D.gainExponent l) := by
  push_cast [invGainFactor]
  rw [norm_prod, prod_eq_single l, norm_zpow]
  · intro p hp hpl
    have h_coprime : l.Coprime p :=
      (Nat.coprime_primes hl.out (D.prime_of_mem_smallNonsplitPrimes_union hp)).2 hpl.symm
    rw [norm_zpow, h_coprime.norm_natCast_eq_one, one_zpow]
  · -- If `l` is not in the product, then `g_l = 0`.
    rw [notMem_union, notMem_singleton]
    rintro ⟨h_notMem, hN⟩
    have h_cases : chiK P.d l = 1 ∨ D.x₁ ≤ l :=
      chiK_eq_one_or_le_of_notMem_smallNonsplitPrimes h_notMem
    simp [gainExponent, D.gain_eq_zero h_cases, D.divisibilityError_eq_zero hN h_cases]

/-- A non-zero constant `c_ss` for which the seesaw identity `New.Data.seesaw_identity` holds with
the linear form `D.besselForm` and the archimedean point `D.besselPoint`. -/
def seesawConst : ℂˣ := (D.seesaw_identity D.besselForm D.besselPoint).choose

/-- The inclusion of the ramified source forms, times the number `c_ss⁻¹` of the seesaw
identity. -/
def scaledInclusion : D.ramifiedSourceForms →ₗ[ℂ] D.SourceForm :=
  (D.seesawConst⁻¹ : ℂˣ).val • D.ramifiedSourceForms.subtype

/-- The map `φ ↦ y = #Ḡ · e₀ s z`, with `z = c_ss⁻¹ 𝒫 φ`, from the source to the target. Here
`𝒫` is the Poincaré map, `Ḡ` the finite group `D.chosenGL` and `e₀` the projection to the good
part. -/
abbrev projectedPoincare (s : D.chosenGL) : D.ramifiedSourceForms →ₗ[ℂ] D.targetForms :=
  D.goodPoincare s ∘ₗ D.scaledInclusion

/-- The map `φ ↦ c_B y`, with `y = #Ḡ · e₀ s c_ss⁻¹ 𝒫 φ`. It is the translate `s 𝔭` of
`𝔭 = c_B c_ss⁻¹ #Ḡ · e₀ 𝒫` (`coe_normalizedPoincare`). -/
def normalizedPoincare (s : D.chosenGL) : D.ramifiedSourceForms →ₗ[ℂ] D.targetForms :=
  (D.invGainFactor : ℂ) • D.projectedPoincare s

/-- The map `normalizedPoincare s = c_B c_ss⁻¹ #Ḡ · e₀ s 𝒫` is the translate by `s` of
`𝔭 = normalizedPoincare 1`, in the representation `D.principalRep` of the finite group
`Ḡ = D.chosenGL` on the forms on `Y₀`. -/
lemma coe_normalizedPoincare (s : D.chosenGL) (φ : D.ramifiedSourceForms) :
    (D.normalizedPoincare s φ : D.principalForms (D.spaceY 0)) =
      D.principalRep (D.spaceY 0) s (D.normalizedPoincare 1 φ) := by
  have h_comm : Commute (D.principalRep (D.spaceY 0) s)
      ((D.principalRep (D.spaceY 0)).asAlgebraHom D.e₀) := by
    simpa using (D.isCentralProj_e₀.2.commute (.of ℂ D.chosenGL s)).map
      (D.principalRep (D.spaceY 0)).asAlgebraHom
  have h_translate (z : D.principalForms (D.spaceY 0)) :
      (D.goodProjTranslate s z : D.principalForms (D.spaceY 0)) =
        D.principalRep (D.spaceY 0) s (D.goodProjTranslate 1 z) := by
    -- Both sides are `#Ḡ` times the two sides of `h_comm` at `z`.
    simpa using congrArg ((Nat.card D.chosenGL : ℂ) • ·) (LinearMap.congr_fun h_comm.eq z).symm
  simp only [normalizedPoincare, LinearMap.smul_apply, Submodule.coe_smul, map_smul]
  exact congrArg _ (h_translate (D.poincare (D.scaledInclusion φ)))

/-- The ramified source forms that are integral at every `ι`, where `ι` runs over the pairs of a
prime `l` and an `l`-adic place of `ℂ` (`PrimePadicIso`). -/
def integralRamified : Set D.ramifiedSourceForms :=
  {φ : D.ramifiedSourceForms |
    ∀ ι : PrimePadicIso, letI := ι.place; (φ : D.SourceForm) ∈ D.integralSourceForms}

/-- The seesaw identity for `z = c_ss⁻¹ 𝒫 φ = D.poincare (D.scaledInclusion φ)`. Each twist `ϑ` has
a chain datum `Ψ` (the data of the upper chain of lifts `B_ϑ = compositeLift ϑ Ψ`) with
`ι_ϑ z = B_ϑ φ` for all ramified `φ`. Here `ι_ϑ = D.lowerChain ϑ.toTameChar` is the lower chain of
lifts, from forms on `Y₀` to forms on `Y_m`, taken for the tame character `ϑ.toTameChar` underlying
the twist. -/
lemma exists_lowerChain_poincare_eq (ϑ : D.Twist) :
    ∃ Ψ : D.Translations →₀ ℂ, IsChainDatum ϑ Ψ ∧ ∀ φ : D.ramifiedSourceForms,
      D.lowerChain ϑ.toTameChar (D.poincare (D.scaledInclusion φ)) =
        compositeLift ϑ.toTameChar Ψ φ := by
  obtain ⟨Ψ, hΨ, h_eq⟩ : ∃ Ψ : D.Translations →₀ ℂ, IsChainDatum ϑ Ψ ∧ ∀ φ : D.ramifiedSourceForms,
      D.lowerChain ϑ.toTameChar (D.poincare φ) =
        (D.seesawConst : ℂ) • compositeLift ϑ.toTameChar Ψ φ :=
    (D.seesaw_identity D.besselForm D.besselPoint).choose_spec ϑ
  exact ⟨Ψ, hΨ, fun φ ↦ by simp [scaledInclusion, h_eq]⟩

/-- The map `D.normalizedPoincare s` is `c_B = D.invGainFactor` times `D.projectedPoincare s`, the
map `#Ḡ · e₀ s c_ss⁻¹ 𝒫` from ramified source forms to target forms. The positive rational factor
`c_B` multiplies the squared norm `‖Θ₁ ·‖_σ²` by `exp (2 log c_B)`, for every automorphism `σ` of
`ℂ`. -/
lemma normSqAt_normalizedPoincare (s : D.chosenGL) (φ : D.ramifiedSourceForms) (σ : ℂ ≃+* ℂ) :
    (D.Θ 1 (D.normalizedPoincare s φ)).normSqAt σ =
      exp (2 * log D.invGainFactor) * (D.Θ 1 (D.projectedPoincare s φ)).normSqAt σ := by
  have h_norm : ‖σ D.invGainFactor‖ ^ 2 = exp (2 * log D.invGainFactor) := by
    rw [two_mul, exp_add, exp_log (mod_cast D.invGainFactor_pos), ← sq]
    simp
  simp only [normalizedPoincare, LinearMap.smul_apply, map_smul, normSqAt, mul_classSum, ← h_norm]
  exact congrArg _ (funext fun g ↦ weylNormSq_comp_smul _ σ _)

/-! ### Theorem A -/

/-- **Theorem A (a).** The source is spanned by the forms `φ` that are integral at every prime `l`
and `l`-adic place of `ℂ` and satisfy `‖Θ₁ s 𝔭 φ‖_σ² ≤ exp (main - m rem + f a log⁴ b)` for all `s`
in the finite group `D.chosenGL` and all automorphisms `σ` of `ℂ`. Here
`s 𝔭 = D.normalizedPoincare s` maps the source to the target, `Θ₁ = D.Θ 1` is the chain of `m = D.m`
lifts for the trivial twist, and `‖·‖_σ²` is the squared norm of the conjugate form. In the bound:
* `main = D.mainAmount` is `m k ∑_τ (s_∞(κ(τ)) - s_fin(κ(τ), τ))`, summed over all infinite places
  `τ`, where `k = D.k` is the rank of the source, `κ` the weight, `s_∞ = D.jetSize` the size of a
  derivative of given order and `s_fin = D.primeSum` the prime sum for its divisibility;
* `rem = D.totalRemainder` is `∑ (s_fin(a, τ) - s_main)`, summed over the `a`-places `τ`, with the
  main part `s_main = D.mainPrimeSum`;
* `f = D.f` is the number of infinite places, `a = D.a` is the long order `x b`, and
  `log b = D.logB` is the logarithm of the weight `b`. -/
theorem span_short_integralRamified_eq_top :
    span ℂ {φ ∈ D.integralRamified | ∀ (s : D.chosenGL) (σ : ℂ ≃+* ℂ),
      (D.Θ 1 (D.normalizedPoincare s φ)).normSqAt σ ≤
        exp (D.mainAmount - D.m * D.totalRemainder + D.f * D.a * D.logB ^ 4)} = ⊤ := by
  -- The short forms span the source, so it suffices to bound the lifts for a short form `φ`.
  refine eq_top_mono (span_mono ?_) D.span_isShort_ramifiedSourceForms_eq_top
  rintro φ ⟨h_integral, h_size⟩
  refine ⟨fun ι ↦ ?_, fun s σ ↦ ?_⟩
  · -- A short form is integral at every `ι`.
    let : PadicPlace ι.1 := ι.place
    exact ⟨φ.val.prop, h_integral ι.1⟩
  obtain ⟨Ψ, hΨ, h_seesaw⟩ : ∃ Ψ : D.Translations →₀ ℂ,
      IsChainDatum (1 : D.MFoldTwist).toTwist Ψ ∧ ∀ φ : D.ramifiedSourceForms,
        D.lowerChain .one (D.poincare (D.scaledInclusion φ)) = compositeLift .one Ψ φ :=
    D.exists_lowerChain_poincare_eq 1
  set β : ℝ := D.mainAmount - D.m * D.totalRemainder +
    2 * ∑ l ∈ D.smallNonsplitPrimes, D.gain l * log l + D.errorUnit with β_def
  -- The values of `ι₁ z = B₁ φ`, for `z = c_ss⁻¹ 𝒫 φ`, are bounded by the sizes of `φ` and the
  -- chain.
  have h_chain (g : Gf D.E (D.Y D.m)) :
      weylNormSq (σ ∘ (D.lowerChain .one (D.poincare (D.scaledInclusion φ))).val g) ≤
        exp (D.errorUnit + β) := by
    rw [h_seesaw φ]
    exact weylNormSq_compositeLift_le hΨ (h_size σ) g
  -- The passage from `z` to the target form `y = #Ḡ · e₀ s z` adds `x ^ 99`.
  have h_target :
      (D.Θ 1 (D.projectedPoincare s φ)).normSqAt σ ≤ exp (D.x ^ 99 + (D.errorUnit + β)) :=
    normSqAt_goodProjTranslate_le h_chain
  have h_error : D.x ^ 99 + 4 * D.errorUnit + 2 * D.b ≤ D.f * D.a * D.logB ^ 4 :=
    D.le_of_hasLogBound
  -- The positive rational number `c_B` adds `2 log c_B`, and the gains cancel.
  grw [D.normSqAt_normalizedPoincare, h_target, ← exp_add, exp_le_exp, β_def]
  linarith [D.log_invGainFactor_le]

/-- The ramified source forms `D.ramifiedSourceForms` have at least half the dimension over `ℂ` of
all source forms `D.SourceForm`: `finrank ℂ D.SourceForm ≤ 2 * finrank ℂ D.ramifiedSourceForms`. -/
lemma finrank_sourceForm_le_two_mul :
    finrank ℂ D.SourceForm ≤ 2 * finrank ℂ D.ramifiedSourceForms := by
  have h_small : D.f / (D.N - 1 : ℝ) ≤ 2⁻¹ := D.f_div_N_sub_one_le.trans D.le_of_hasLogBound
  have h_half : (1 - 2⁻¹ : ℝ) * finrank ℂ D.SourceForm ≤ finrank ℂ D.ramifiedSourceForms := by
    grw [← h_small, D.le_finrank_ramifiedSourceForms]
  rify
  linarith

/-- Let `l = ι.1` be the prime below `ι`, let `gain_l = D.gain l` be the divisibility asked of the
chain of lifts at `l` and `err_l = D.divisibilityError l` the error allowed in it. Suppose that
`B_ϑ φ = compositeLift ϑ Ψ φ` has valuation at least `gain_l - err_l` at `ι`, for every twist `ϑ`
whose level `ϑ.normQ` is prime to `l` and every chain datum `Ψ` of `ϑ`. Then the target form
`y = s 𝔭 φ = D.normalizedPoincare s φ` is integral at `ι`: its lift `Θ_ϑ y` is integral at `ι` for
every `m`-fold twist `ϑ` of level prime to `l`. -/
lemma normalizedPoincare_mem_integralVectors {ι : PrimePadicIso} (s : D.chosenGL)
    {φ : D.ramifiedSourceForms}
    (hφ : ∀ (ϑ : D.Twist) (Ψ : D.Translations →₀ ℂ), IsChainDatum ϑ Ψ →
      Nat.Coprime ι.1 ϑ.normQ → letI := ι.place
      GaugeLe 1 (((ι.1 : ℕ) : ℝ) ^ (D.divisibilityError ι.1 - D.gain ι.1)) (compositeLift ϑ Ψ φ)) :
    D.normalizedPoincare s φ ∈ D.targetLattice.integralVectors ι := by
  let : PadicPlace ι.1 := ι.place
  refine mem_integralVectors_targetLattice.2 fun ϑ hϑ ↦ ?_
  obtain ⟨Ψ, hΨ, h_seesaw⟩ : ∃ Ψ : D.Translations →₀ ℂ, IsChainDatum ϑ.toTwist Ψ ∧
      ∀ φ : D.ramifiedSourceForms, D.lowerChain ϑ.toTameChar (D.poincare (D.scaledInclusion φ)) =
        compositeLift ϑ.toTameChar Ψ φ :=
    D.exists_lowerChain_poincare_eq ϑ
  -- As `g_l ≤ gain_l - err_l`, the form `B_ϑ φ` is `l ^ g_l` times an integral form.
  have h_gauge : GaugeLe 1 1
      (((ι.1 : ℕ) : ℂ) ^ (-D.gainExponent ι.1) • compositeLift ϑ.toTameChar Ψ φ) :=
    (hφ ϑ Ψ hΨ hϑ).zpow_neg_smul ((Int.floor_le _).trans_eq (neg_sub _ _).symm)
  have h_norm : ‖ιₚ (D.invGainFactor : ℂ)‖ = ‖ιₚ (((ι.1 : ℕ) : ℂ) ^ (-D.gainExponent ι.1))‖ := by
    simp [norm_invGainFactor]
  -- With `z = c_ss⁻¹ 𝒫 φ`, the form `c_B ι_ϑ z = c_B B_ϑ φ` is integral at `ι`, as
  -- `v_ι(c_B) = -g_l`.
  have h_lift_mem :
      (D.invGainFactor : ℂ) • D.lowerChainAtLevel ϑ (D.poincare (D.scaledInclusion φ)) ∈
        integralForms ι.place := fun g ↦ by
    show weylGauge D.columnsY (D.lastEntry D.m) g ((D.invGainFactor : ℂ) •
      (D.lowerChain ϑ.toTameChar (D.poincare (D.scaledInclusion φ))).val g) ≤ 1
    rw [h_seesaw φ, weylGauge_smul, h_norm, ← weylGauge_smul]
    simpa using h_gauge g
  -- So is `Θ_ϑ s 𝔭 φ`, which is `c_B Θ_ϑ` of `#Ḡ` times the good part of a translate of `z`.
  have h_smul : D.Θ ϑ (D.normalizedPoincare s φ) =
      (D.invGainFactor : ℂ) • D.Θ ϑ (D.projectedPoincare s φ) :=
    (D.Θ ϑ).map_smul _ _
  rw [h_smul]
  exact goodProjTranslate_mem_integralForms ι.place h_lift_mem s

/-- Fix `s` in the finite group `D.chosenGL`. A finite family `y` of target forms
`s 𝔭 φ = D.normalizedPoincare s φ`, with each `φ` a ramified source form integral at every `ι`, has
logarithmic index at most `δ = dim src · 2 · D.errorUnit` in `D.targetLattice`. Here `src` is the
space `D.ramifiedSourceForms`, and `D.errorUnit` is the unit of loss `D.f * D.a * D.logB ^ 3`. -/
lemma indexLe_of_mem_image_normalizedPoincare (s : D.chosenGL) {n : ℕ} {y : Fin n → D.targetForms}
    (hy : ∀ i : Fin n, y i ∈ D.normalizedPoincare s '' D.integralRamified) :
    D.targetLattice.IndexLe y (finrank ℂ D.ramifiedSourceForms * (2 * D.errorUnit)) := by
  -- At `ι ∣ l` the map `s 𝔭` takes a submodule of colength `j ≤ err_l D_X` to integral target
  -- forms, `D_X` being the dimension of the space of all source forms. So `e l = D_X err_l` serves,
  -- and `D_X ≤ 2 dim src`.
  refine TwistedLattice.indexLe_of_colengthDvd
    (e := fun l ↦ finrank ℂ D.SourceForm * D.divisibilityError l)
    (fun l ↦ mul_nonneg (by positivity) (D.divisibilityError_nonneg l)) (fun U _ ↦ ?_) fun ι ↦ ?_
  · have h_errorUnit_nonneg : 0 ≤ D.errorUnit := (HasLogBound.pos D).le
    simp only [mul_assoc _ (D.divisibilityError _), ← mul_sum]
    grw [sum_divisibilityError_mul_log_le, finrank_sourceForm_le_two_mul]
    push_cast
    exact le_of_eq (by ring)
  let : PadicPlace ι.1 := ι.place
  -- On `S` the chain has valuation at least `gain_l - err_l`, for all twists prime to `l`.
  obtain ⟨j, S, hj, h_index, h_gauge⟩ := D.exists_colengthDvd_gaugeLe_divisibilityError ι.1
  let A : D.ramifiedSourceForms →ₗ[ι.integers] D.targetForms :=
    (D.normalizedPoincare s).restrictScalars _
  let M : Submodule ι.integers D.ramifiedSourceForms :=
    D.integralSourceForms.comap (D.ramifiedSourceForms.subtype.restrictScalars _)
  have h_source : ColengthDvd M ((D.targetLattice.integralVectors ι).comap A) (ι.1 ^ j) :=
    h_index.comap _ (fun φ hφ ↦ ⟨hφ, φ.prop⟩) fun φ _ hφ ↦
      D.normalizedPoincare_mem_integralVectors s fun ϑ Ψ hΨ hϑ ↦ h_gauge ϑ Ψ hΨ hϑ φ hφ
  have h_subset : D.integralRamified ⊆ M := fun φ hφ ↦ hφ ι
  exact ⟨j, M.map A, hj.trans_eq (mul_comm _ _), fun i ↦ Set.image_mono h_subset (hy i),
    h_source.map A le_sup_left (map_comap_le A _)⟩

/-- **Theorem A (b).** A finite family `y` of target forms `s 𝔭 φ = D.normalizedPoincare s φ`, with
`s` in a set `t` of translates and `φ` in the source `src = D.ramifiedSourceForms` integral at every
`ι`, has logarithmic index at most `δ = #t · dim src · 2 f a log³ b` in the target lattice. -/
theorem indexLe_normalizedPoincare (t : Finset D.chosenGL) {n : ℕ} {y : Fin n → D.targetForms}
    (hy : ∀ i : Fin n, ∃ s ∈ t, y i ∈ D.normalizedPoincare s '' D.integralRamified) :
    D.targetLattice.IndexLe y (#t * finrank ℂ D.ramifiedSourceForms * (2 * D.errorUnit)) := by
  -- Sort the family by translates; indices add over a union of families.
  rw [mul_assoc]
  exact TwistedLattice.indexLe_card_mul t
    (fun s _ n z ↦ D.indexLe_of_mem_image_normalizedPoincare s) hy

/-! ### Theorem B -/

/-- The range of `D.normalizedPoincare s` (the map `s 𝔭`) is the image of the ramified source forms
`D.ramifiedSourceForms` under `D.goodPoincare s = #Ḡ · e₀ s 𝒫`, as the scalars `c_B` and `c_ss⁻¹` in
`𝔭` do not vanish. -/
lemma range_normalizedPoincare (s : D.chosenGL) :
    (D.normalizedPoincare s).range = D.ramifiedSourceForms.map (D.goodPoincare s) := by
  simp [normalizedPoincare, scaledInclusion, LinearMap.range_smul, LinearMap.range_comp,
    D.invGainFactor_pos.ne']

/-- The factor `(5/2) (1 + log (1 / (16 ε)))` in the number of translates is at most
`5 log (1 + 2 b²)` for `ε = b⁻² / 8`. -/
lemma five_halves_mul_one_add_log_le :
    5 / 2 * (1 + log (16 * (8 * D.b ^ 2)⁻¹)⁻¹) ≤ 5 * log (1 + 2 * D.b ^ 2) := by
  have hb : 2 ≤ D.b ^ 2 := D.le_of_hasLogBound
  have h_one : 1 ≤ log (1 + 2 * D.b ^ 2) :=
    (le_log_iff_exp_le (by positivity)).2 (by linarith [exp_one_lt_three])
  have h_le : (16 * (8 * D.b ^ 2)⁻¹)⁻¹ ≤ 1 + 2 * D.b ^ 2 := by
    rw [mul_inv, inv_inv]
    linarith
  linarith [log_le_log (by positivity) h_le]

lemma targetDim_pos : 0 < D.targetDim := D.finrank_targetForms_ne_zero.pos

/-- There is a set `t` of elements of the finite group `D.chosenGL = ∏ GL_r(𝔽_w)` (product over the
chosen places `w` above the two level primes) with `#t · dim src ≤ 5 d_T log (1 + 2 b²)` such that
the spaces `s 𝔭 src`, `s ∈ t`, span at least `(1 - 4 / b²) d_T` dimensions. Here
`d_T = D.targetDim` is the dimension of the target, `b = D.b = exp D.logB` is the weight at the
`b`-places, `src` is the space of ramified source forms and `s 𝔭` is `D.normalizedPoincare s`. -/
theorem exists_le_finrank_iSup_range_normalizedPoincare :
    ∃ t : Finset D.chosenGL,
      #t * finrank ℂ D.ramifiedSourceForms ≤ 5 * D.targetDim * log (1 + 2 * D.b ^ 2) ∧
      (1 - 4 / D.b ^ 2) * D.targetDim ≤ finrank ℂ ↥(⨆ s ∈ t, (D.normalizedPoincare s).range) := by
  have : Nontrivial D.SourceForm := D.sourceFormCoords.nontrivial
  -- For `ε = (8 b²)⁻¹ < 1 / 16`, few translates of the image of all source forms span all but the
  -- share `16 ε = 2 / b²` of the target.
  obtain ⟨t, h_count, h_span⟩ : ∃ t : Finset D.chosenGL,
      #t * finrank ℂ D.SourceForm ≤ 5 / 2 * (1 + log (16 * (8 * D.b ^ 2)⁻¹)⁻¹) * D.targetDim ∧
      (1 - 16 * (8 * D.b ^ 2)⁻¹ : ℝ) * D.targetDim ≤
        finrank ℂ ↥(⨆ s ∈ t, (D.goodPoincare s).range) :=
    D.isSpread_goodPoincare.exists_few_le_finrank_iSup_range D.targetDim_pos (HasLogBound.pos D)
      D.lt_of_hasLogBound
  have h_few : #t * finrank ℂ D.SourceForm ≤ 5 * D.targetDim * log (1 + 2 * D.b ^ 2) := by
    grw [h_count, D.five_halves_mul_one_add_log_le, mul_right_comm]
  refine ⟨t, by grw [D.ramifiedSourceForms.finrank_le, h_few], ?_⟩
  -- Passing to the ramified forms loses at most their codimension for each translate.
  have h_codim : (finrank ℂ D.SourceForm - finrank ℂ D.ramifiedSourceForms : ℝ) ≤
      D.f / (D.N - 1) * finrank ℂ D.SourceForm := by linarith [D.le_finrank_ramifiedSourceForms]
  have h_small : (D.b ^ 8)⁻¹ * (5 * log (1 + 2 * D.b ^ 2)) ≤ 2 / D.b ^ 2 := D.le_of_hasLogBound
  have h_loss : #t * (finrank ℂ D.SourceForm - finrank ℂ D.ramifiedSourceForms : ℝ) ≤
      2 / D.b ^ 2 * D.targetDim :=
    calc #t * (finrank ℂ D.SourceForm - finrank ℂ D.ramifiedSourceForms : ℝ)
        ≤ #t * ((D.b ^ 8)⁻¹ * finrank ℂ D.SourceForm) := by grw [h_codim, D.f_div_N_sub_one_le]
      _ ≤ (D.b ^ 8)⁻¹ * (5 * D.targetDim * log (1 + 2 * D.b ^ 2)) := by grw [mul_left_comm, h_few]
      _ = (D.b ^ 8)⁻¹ * (5 * log (1 + 2 * D.b ^ 2)) * D.targetDim := by ring
      _ ≤ 2 / D.b ^ 2 * D.targetDim := by grw [h_small]
  rw [iSup_congr fun s ↦ iSup_congr fun _ ↦ D.range_normalizedPoincare s]
  calc (1 - 4 / D.b ^ 2) * D.targetDim
      = (1 - 16 * (8 * D.b ^ 2)⁻¹) * D.targetDim - 2 / D.b ^ 2 * D.targetDim := by ring
    _ ≤ (finrank ℂ ↥(⨆ s ∈ t, D.ramifiedSourceForms.map (D.goodPoincare s)) : ℝ) := by
        linarith [finrank_biSup_range_le D.goodPoincare t D.ramifiedSourceForms, h_span, h_loss]

/-- **Theorem B**, the bound on the dimension spanned by few translates. The target has dimension
`d_T = D.targetDim ≥ 1`, and there is a set `t` of elements of the finite group `D.chosenGL` with
`#t · dim src ≤ 5 d_T log (1 + 2 b²)` such that the spaces `s 𝔭 src`, `s ∈ t`, span at least
`(1 - 4 / b²) d_T` dimensions. Here `b = D.b = exp D.logB` is the weight at the `b`-places, `src`
is the space of ramified source forms and `s 𝔭` is `D.normalizedPoincare s`. -/
theorem enough_forms :
    0 < D.targetDim ∧
    ∃ t : Finset D.chosenGL,
      #t * finrank ℂ D.ramifiedSourceForms ≤ 5 * D.targetDim * log (1 + 2 * D.b ^ 2) ∧
      (1 - 4 / D.b ^ 2) * D.targetDim ≤ finrank ℂ ↥(⨆ s ∈ t, (D.normalizedPoincare s).range) :=
  ⟨D.targetDim_pos, D.exists_le_finrank_iSup_range_normalizedPoincare⟩

end New.Data

end
