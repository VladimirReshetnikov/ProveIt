import New.Congruences.GaloisRepresentations.SelmerHypotheses
import New.Congruences.Selmer.AuxiliaryPrimes
import New.OneLift.ComparisonOperator.ThreeExchanges
import New.OneLift.HeckeValues.AlgebraicPartIntegrality
import New.OneLift.HeckeValues.PeriodAtOne
import New.OneLift.HeckeValues.TwistedRatio

/-!
# L-values of a pair as integral measures, and avatars of tame characters

For a pair `p` (`New.Data.CriticalPair`: a character `ν` of U(1) and a point `z`) ramified at the
chosen places, ratios of the values `L(z, (ν ϑ)⁻¹)`, as `ϑ` runs over tame characters
(`New.Data.TameChar`), are interpolated over `ℂ` by integral measures. The `ℓ`-adic form is in
`New.Congruences.Selmer.LValueSystems`.

* `New.Data.CriticalPair.exists_isTwistMeasure`: a function `F` of `ϑ` that is an integral measure
  at every modulus (`New.Data.TameChar.IsIntegralMeasure`) and gives a power of the ratio of
  `L`-values `New.Data.CriticalPair.ratio` on twists (`New.Data.CriticalPair.IsTwistMeasure`); the
  cases `z ≥ 2` and `z = 1` are `New.Data.CriticalPair.isTwistMeasure_integralAlgebraicPart` and
  `New.Data.CriticalPair.exists_isTwistMeasure_of_z_eq_one`.
* `New.Selmer.exists_tameChar_invAvatar_eq`: an anticyclotomic Galois character of auxiliary
  modulus that is trivial above `ℓ` is the `ℓ`-adic avatar of the inverse of a tame character
  (`New.Data.TameChar.invAvatar`).

Notions from other files:
* `New.IsAuxiliary S I`: The places of `I` have prime norm, neither they nor their conjugates lie in
  the set `S` of places, and their conjugates lie outside `I`.
* `New.Data.CriticalPair`: A character `p.character` of U(1) of weight `-p.negWeight` with tame part
  `p.tamePart`, and an integer `p.z` with `1 ≤ z ≤ c` at every infinite place.
* `New.Data.TameChar`: A character of U(1) of weight 0, with modulus a finite set `Q` of places and
  tame part `ψ` supported on `Q`; `New.Data.Twist` is the type of those that are twists of `D`.
* `New.Data.IsChosen`: The places dividing a fixed element `D.piM` of `E`; they carry the
  tame part of a pair.
* `New.Data.CriticalPair.ratio`: The absolute value of `L(z, (ν ϑ)⁻¹) / L(z, ν⁻¹)`, without the
  Euler factors at the chosen places, in the numerator also at the modulus of `ϑ`, and their
  conjugates.
* `New.Data.CriticalPair.IsRamified`: The tame part of the pair is nontrivial exactly at the chosen
  places.

## Relation to the literature
Known result: Integral group-ring elements interpolating twisted Hecke L-values, with norm
relations. The form proved here concerns tame anticyclotomic twists of a fixed modulus, and the
elements are integral at every prime away from it at once. At integers from 2 on, the element is the
squared norm of a theta lift from U(1); at 1 it is a theta period on U(2) times its conjugate and
gives the squared value. Adding a place multiplies the element by Euler factors. Source: N. Katz,
p-adic L-functions for CM fields, Invent. Math. 49 (1978); construction as theta elements:
Bertolini, Darmon, Invent. Math. 126 (1996), adelic form Chida, Hsieh, J. reine angew. Math. 741
(2018); Euler factor: Tamagawa, Ann. of Math. 77 (1963).
-/

open New Matrix Finset Complex Rows WeilData HeckeChar Data AlgHeckeChar AutChar HasWeight Unitary

namespace New.Data.CriticalPair

variable {P : Parameters} {D : Data P}

open scoped Classical in
/-- The properties of a family `F` of values, one for each tame character, by which it interpolates
ratios of twisted and untwisted `L`-values (`p.ratio`). The set `I` holds the exponents of the
inverse Euler factors that a new place in the modulus contributes. At a twist the ratio occurs to
the power `m + 1`, times the `m`-th power of the norm of the modulus. -/
structure IsTwistMeasure (p : D.CriticalPair) (I : Finset ℕ) (m : ℕ) (F : D.TameChar → ℂ) :
  Prop where
  /-- The value at the trivial character is not zero. -/
  apply_one_ne_zero : F TameChar.one ≠ 0
  /-- At each modulus, `F` is evaluation on one combination of points whose coefficients are
  integral at every prime that does not divide the norm of the modulus. -/
  isIntegralMeasure : ∀ ϑ : D.TameChar, ϑ.IsIntegralMeasure F
  /-- Adding a place `v` to the modulus multiplies `F` by the inverse Euler factors at `v` with
  the exponents in `I`. -/
  apply_insert : ∀ (ϑ ϑ' : D.TameChar) (v : FinPlace D.E), v ∉ ϑ.Q → ϑ'.Q = insert v ϑ.Q →
    ϑ'.toAutChar = ϑ.toAutChar → ϑ'.tamePart = ϑ.tamePart →
    F ϑ' = F ϑ * ∏ l ∈ I, ∏ ε : ℤˣ,
      (1 - (p.character * ϑ.toAutChar).baseChange.atUniformizer v ^ ε.val / v.q ^ l)
  /-- At a twist, `F` is its value at the trivial character times the `m`-th power of the norm of
  the modulus and the `(m + 1)`-th power of the ratio. -/
  apply_twist : ∀ ϑ : D.Twist, F ϑ = F TameChar.one * (ϑ.normQ ^ m * p.ratio ϑ ^ (m + 1))

/-- For a critical pair `p` and a tame character `ϑ`, the product of their tame parts is trivial at
every place off the modulus `D.twistModulus ϑ 2`, whose places are the chosen places (the places
dividing `D.piM`) and those of `ϑ.Q`. -/
lemma tamePart_mul_tamePart_apply_eq_one_of_notMem (p : D.CriticalPair) (ϑ : D.TameChar) :
    ∀ w ∉ (D.twistModulus ϑ 2).places, (p.tamePart * ϑ.tamePart) w = 1 := by
  simp_all [places_twistModulus, p.tamePart_eq_one, ϑ.tamePart_eq_one]

open scoped Classical in
/-- For a critical pair `p = (ν, z)`, with `ν = p.character`, let `H` say that `n` has `2 z`
elements and `z ≥ 2`. Let `ϑ` and `ϑ'` be the same tame character, with moduli `Q` and `Q ∪ {v}`.
Then `integralAlgebraicPart H`, a fixed multiple of `L(z, (ν ϑ)⁻¹)` without the chosen places, the
modulus and their conjugates, is multiplied by `(1 - a / q ^ z) * (1 - a⁻¹ / q ^ z)`, with `q` the
norm of `v` and `a` the value of the base change `x ↦ (ν ϑ)(x / x̄)` at a uniformizer at `v`. -/
lemma integralAlgebraicPart_insert {p : D.CriticalPair} {n : Type} [Fintype n] [DecidableEq n]
    (H : p.HasLiftRank n) {ϑ ϑ' : D.TameChar} {v : FinPlace D.E}
    (hv : v ∉ ϑ.Q) (hQ : ϑ'.Q = insert v ϑ.Q) (hχ : ϑ'.toAutChar = ϑ.toAutChar) :
    integralAlgebraicPart H ϑ' = integralAlgebraicPart H ϑ * ∏ ε : ℤˣ,
      (1 - (p.character * ϑ.toAutChar).baseChange.atUniformizer v ^ ε.val / v.q ^ p.z) := by
  obtain ⟨A, -, hA⟩ : ∃ A ≠ (0 : ℂ), ∀ ϑ : D.TameChar, integralAlgebraicPart H ϑ =
      A * (p.character * ϑ.toAutChar)⁻¹.L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) p.z :=
    exists_integralAlgebraicPart_eq_mul_L H
  obtain ⟨hv_star', hv_chosen, hv_star_chosen⟩ :
      star v ∉ ϑ'.Q ∧ ¬D.IsChosen v ∧ ¬D.IsChosen (star v) := by
    -- `↓` rewrites `star v ∉ ϑ'.Q` before `hQ` changes the set.
    simp [IsChosen, D.normQ_mem_and_notMem_of_mem_Q ϑ', ↓ϑ'.star_notMem, hQ]
  have at_star :
      (p.character * ϑ.toAutChar).baseChange.atUniformizer (star v) =
        ((p.character * ϑ.toAutChar).baseChange.atUniformizer v)⁻¹ := by
    apply (p.hasWeight.mul ϑ.hasWeight).atUniformizer_star
    · exact p.tamePart_mul_tamePart_apply_eq_one_of_notMem ϑ v
        (by simp [places_twistModulus, hv, hv_chosen])
    · have hv_star : star v ∉ ϑ.Q := fun h_mem ↦ hv_star' (by simp [hQ, h_mem])
      exact p.tamePart_mul_tamePart_apply_eq_one_of_notMem ϑ (star v)
        (by simp [places_twistModulus, hv_star, hv_star_chosen])
  let φ := (p.character * ϑ.toAutChar)⁻¹.baseChange.finPart
  let S (Q : Finset (FinPlace D.E)) : Set (FinPlace D.E) :=
    ({w : FinPlace D.E | D.IsChosen w} ∪ ↑Q).conjClosure
  simp_rw [hA, hχ, mul_assoc, AutChar.L]
  congr 1
  -- Setting the coefficients at `{v, star v}` to zero multiplies the Euler product by the two
  -- inverse Euler factors.
  obtain ⟨-, -, h_erase⟩ := eulerProd_erase
    (p.hasWeight.mul ϑ.hasWeight).inv.isHeckeOfType.norm_heckeCoeff_le {v, star v}
  have h_coeff : heckeCoeff φ (S ϑ'.Q) = Set.indicator {v, star v}ᶜ (heckeCoeff φ (S ϑ.Q)) := by
    -- The places removed for `ϑ'` are those for `ϑ` together with `v` and `star v`.
    simp [φ, S, funext_iff, heckeCoeff, Set.indicator, hQ]
    grind [star_star]
  have h_factors :
      ∏ w ∈ {v, star v}, (1 - heckeCoeff φ (S ϑ.Q) w * (w.q : ℂ) ^ (-(p.z : ℂ))) =
        ∏ ε : ℤˣ, (1 - (p.character * ϑ.toAutChar).baseChange.atUniformizer v ^ ε.val / v.q ^
          p.z) := by
    simp_all [φ, S, HeckeChar.atUniformizer, heckeCoeff, cpow_neg, Ne.symm]
    grind
  rw [h_coeff, ← h_factors]
  simpa [φ, S] using h_erase p.z (mod_cast H.2)

/-- For a critical pair `p = (ν, z)`, let `H` say that `n` has `2 z` elements and `z ≥ 2`. Then
`integralAlgebraicPart H`, an integral multiple of the algebraic part of the twisted `L`-value at
`z`, has the properties of `IsTwistMeasure {z} 0`: it is nonzero at the trivial character; at each
modulus it is evaluation on finitely many points with coefficients integral away from that modulus
(an integral measure); it is multiplied by the inverse Euler factors with exponent `z` when a place
is added; and at a twist it is its value at the trivial character times `p.ratio`, the absolute
value of the ratio of the twisted to the untwisted `L`-value. -/
theorem isTwistMeasure_integralAlgebraicPart {p : D.CriticalPair} {n : Type} [Fintype n]
    [DecidableEq n] (H : p.HasLiftRank n) :
    p.IsTwistMeasure {p.z} 0 (integralAlgebraicPart H) := by
  refine ⟨integralAlgebraicPart_ne_zero H TameChar.one, isIntegralMeasure_integralAlgebraicPart H,
    fun ϑ ϑ' v hv hQ hχ _ ↦ by simpa using integralAlgebraicPart_insert H hv hQ hχ, fun ϑ ↦ ?_⟩
  simp [ratio_eq_integralAlgebraicPart_div H ϑ,
    mul_div_cancel₀ _ (integralAlgebraicPart_ne_zero H TameChar.one)]

/-- For `p = (ν, z)` a critical pair with `ν = p.character` of weight `-c`, where `c = p.negWeight`,
and `ϑ` a tame character, `ν ϑ υ` has weight `-(c - 1)` and the product of the tame parts of `ν`
and `ϑ` as tame part. Here `υ = upsilonU1` is the restriction to the norm-one ideles of the fixed
splitting Hecke character of `E`. -/
lemma hasWeight_mul_upsilonU1 (p : D.CriticalPair) (ϑ : D.TameChar) :
    (p.character * ϑ.toAutChar * upsilonU1 ^ 1).HasWeight
      (fun τ : D.Φ ↦ -((p.negWeight τ - 1 : ℕ) : ℤ)) (p.tamePart * ϑ.tamePart) := by
  have h_one_le (τ : D.Φ) : 1 ≤ p.negWeight τ := p.z_mem.1.trans (p.le_negWeight τ)
  exact ((p.hasWeight.mul ϑ.hasWeight).mul_upsilonU1_pow 1).of_weight_eq (by grind [add_zero])

/-- Let `p = (ν, z)` be a critical pair with `ν = p.character` of weight `-c`, whose tame part is
nontrivial exactly at the chosen places, those dividing `D.piM` (`IsRamified`). For a twist `ϑ`, a
tame character whose tame part is nontrivial at each place of its modulus `Q`, let `Λ` be the period
(`detPeriod`) on the rank-two unitary group of the character `ν ϑ υ`, in weight `c - 1`, with the
modulus `D.twistModulus ϑ 2` and the product of the tame parts of `ν` and `ϑ`. Here `υ = upsilonU1`
is the restriction to the norm-one ideles of the fixed splitting Hecke character. Then there is a
constant `C`, independent of `ϑ`, such that `Λ ≠ 0`, `C ≠ 0` and `C * ‖Λ‖ ^ 2` is
`Exchange.lValueProd`: the norms of the places in `S = {w | D.IsChosen w} ∪ Q` multiplied together,
times `|L(1, (ν ϑ)⁻¹)| ^ 2` without the Euler factors at `S` and its conjugate. -/
lemma exists_mul_norm_sq_detPeriod_eq {p : D.CriticalPair} (h_ram : p.IsRamified) :
    ∃ C : ℝ, ∀ ϑ : D.Twist,
      detPeriod (Fin 2) (p.character * ϑ.toAutChar * upsilonU1 ^ 1)
        (fun τ : D.Φ ↦ p.negWeight τ - 1)
          (D.twistModulus ϑ.toTameChar 2) (p.tamePart * ϑ.tamePart) ≠ 0 ∧
        C ≠ 0 ∧
        C * ‖detPeriod (Fin 2) (p.character * ϑ.toAutChar * upsilonU1 ^ 1)
          (fun τ : D.Φ ↦ p.negWeight τ - 1)
            (D.twistModulus ϑ.toTameChar 2) (p.tamePart * ϑ.tamePart)‖ ^ 2 =
          Exchange.lValueProd ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q)
            (p.character * ϑ.toAutChar)⁻¹ 1 := by
  -- `exists_mul_stdClassSum_modKernelStdSpace_eq_one` gives `γ` with `γ * Λ = 1` and
  -- `‖γ‖ ^ 2 = C / lValueProd`.
  obtain ⟨C, exists_period_inv⟩ := exists_mul_stdClassSum_modKernelStdSpace_eq_one _ even_two
    (fun τ : D.Φ ↦ p.negWeight τ - 1)
  refine ⟨C, fun ϑ ↦ ?_⟩
  set Λ : ℂ := detPeriod (Fin 2) (p.character * ϑ.toAutChar * upsilonU1 ^ 1)
    (fun τ : D.Φ ↦ p.negWeight τ - 1) (D.twistModulus ϑ.1 2) (p.tamePart * ϑ.tamePart)
  obtain ⟨γ, norm_γ, eq_γ⟩ :=
    exists_period_inv (isTameFor_of_hasWeight (c := 2) ϑ (hasWeight_mul_upsilonU1 p ϑ.1) h_ram)
  have h_norm : ‖γ‖ * ‖Λ‖ = 1 := by rw [← norm_mul, show γ * Λ = 1 from eq_γ 1, norm_one]
  have h_sq : ‖γ‖ ^ 2 =
      C / Exchange.lValueProd ({w | D.IsChosen w} ∪ ϑ.Q) (p.character * ϑ.toAutChar)⁻¹ 1 := by
    simpa [places_twistModulus, inv_mul_cancel_comm] using norm_γ
  grind [norm_zero]

open scoped Classical in
/-- Let `p = (ν, z)` be a critical pair with `ν = p.character` of weight `-c`. Let `ϑ'` be the tame
character `ϑ` (same `toAutChar` and `tamePart`) with modulus `Q ∪ {v}` instead of `Q`, where
`v ∉ Q`. Let `υ = upsilonU1` be the restriction to the norm-one ideles of the fixed splitting Hecke
character. Replacing `ϑ` by `ϑ'` multiplies by `(1 - X) * (1 - q * X)` the period `detPeriod` of
`ν ϑ υ` on the rank-two unitary group, in weight `c - 1`, with the tame part of `ν` times that of
`ϑ`, at the modulus `D.twistModulus ϑ 2` (the chosen places to the exponent `2`, times `Q`). Here
`q` is the norm of `v`, and `X⁻¹` is `AutChar.frobValue` in rank two:
`q * (ν ϑ υ)(ϖ / ϖ̄) / υ(ϖ) ^ 2` for a uniformizer `ϖ` at `v`, where `υ(ϖ)` is the value of the
Hecke character itself. -/
lemma detPeriod_mul_upsilonU1_insert {p : D.CriticalPair} {ϑ ϑ' : D.TameChar} {v : FinPlace D.E}
    (hv : v ∉ ϑ.Q) (hQ : ϑ'.Q = insert v ϑ.Q) (hχ : ϑ'.toAutChar = ϑ.toAutChar)
    (hψ : ϑ'.tamePart = ϑ.tamePart) :
    detPeriod (Fin 2) (p.character * ϑ'.toAutChar * upsilonU1 ^ 1) (fun τ : D.Φ ↦ p.negWeight τ - 1)
        (D.twistModulus ϑ' 2) (p.tamePart * ϑ'.tamePart) =
      SiegelWeil.qPochhammer v.q 2
          ((p.character * ϑ.toAutChar * upsilonU1 ^ 1).frobValue (Fin 2) v)⁻¹ *
        detPeriod (Fin 2) (p.character * ϑ.toAutChar * upsilonU1 ^ 1)
          (fun τ : D.Φ ↦ p.negWeight τ - 1)
          (D.twistModulus ϑ 2) (p.tamePart * ϑ.tamePart) := by
  have h_off : ∀ w ∉ (D.twistModulus ϑ 2).places, (p.tamePart * ϑ'.tamePart) w = 1 := by
    simpa [hψ] using p.tamePart_mul_tamePart_apply_eq_one_of_notMem ϑ
  have h_notMem : v ∉ (D.twistModulus ϑ 2).places := by
    simp [places_twistModulus, IsChosen, hv, hQ, D.normQ_mem_and_notMem_of_mem_Q ϑ']
  have h_places : (D.twistModulus ϑ' 2).places = insert v (D.twistModulus ϑ 2).places := by
    simp [places_twistModulus, hQ]
  simpa [hχ, hψ] using
    detPeriod_insert (n := Fin 2) (h := hasWeight_mul_upsilonU1 p ϑ') h_off v h_notMem h_places

/-- For a critical pair `p = (ν, z)` with `ν = p.character` of weight `-c` and `υ = upsilonU1`,
there is `N ≠ 0` such that `F ϑ' = ‖D.chosenGroupOrder * N * Λ ϑ'‖ ^ 2` is an integral measure at
the modulus of every tame character `ϑ`: on the characters `ϑ'` with `ϑ'.Q = ϑ.Q` it is a sum
`∑ a, c_a * ϑ'(u_a)`, with fixed norm-one ideles `u_a` and coefficients `c_a` integral at every
prime not dividing the norm of `ϑ.Q`. Here `Λ ϑ'` is the period `detPeriod` of `ν ϑ' υ` on the
rank-two unitary group, a sum over classes at the standard level, in weight `c - 1`, with tame part
that of `ν ϑ'` and modulus `D.twistModulus ϑ' 2`, the chosen places to the exponent `2` times
`ϑ'.Q`. -/
lemma exists_isIntegralMeasure_norm_sq_detPeriod (p : D.CriticalPair) :
    ∃ N ≠ (0 : ℂ), ∀ ϑ : D.TameChar, ϑ.IsIntegralMeasure fun ϑ' : D.TameChar ↦
      ‖D.chosenGroupOrder * N *
        detPeriod (Fin 2) (p.character * ϑ'.toAutChar * upsilonU1 ^ 1)
          (fun τ : D.Φ ↦ p.negWeight τ - 1)
          (D.twistModulus ϑ' 2) (p.tamePart * ϑ'.tamePart)‖ ^ 2 := by
  classical
  -- The period is a weighted sum of kernel values at points `g x` that depend only on the modulus,
  -- and `N` times such a value is integral once `g x` is moved to an integral point.
  let c (τ : D.Φ) : ℕ := p.negWeight τ - 1
  have weight (ϑ : D.TameChar) :
      (p.character * ϑ.toAutChar * upsilonU1 ^ 1).HasWeight (-c ·) (p.tamePart * ϑ.tamePart) :=
    hasWeight_mul_upsilonU1 p ϑ
  -- The polynomial `∏ τ, det ^ c τ` of the kernel is homogeneous of degree `2 * ∑ c`.
  have h_homog : (∏ τ, (variableMinor τ id id : MvPolynomial (D.Φ × Fin 2 × Fin 2) ℂ) ^ c τ)
      |>.IsHomogeneous (univ.sum c * 2) := by
    rw [isHomogeneous_iff_aeval_smul_X]
    simp [variableMinor, det_apply', prod_pow_eq_pow_sum, prod_smul, ← smul_sum, smul_pow, pow_mul,
      sq, mul_smul]
  obtain ⟨N, hN, ker_int⟩ := exists_ne_zero_isModKernelScale (Fin 2) (Fin 2) D (univ.sum c * 2)
  refine ⟨N, hN, fun ϑ ↦ ?_⟩
  let g (x : StdClasses (stdLevel D.E (Fin 2)) × GL (Fin 2) (D.twistModulus ϑ 2).ResidueRing) :
    Gf D.E (Fin 2) :=
    x.1.out * (Rows.liftMod x.2).1
  let θ : Gf D.E (Fin 2) → ℂ :=
    detKernel (Fin 2) (p.character * TameChar.one.toAutChar * upsilonU1 ^ 1) c (D.twistModulus ϑ 2)
      (Pi.single 1 1)
  -- The point of the measure at `x` is `det (g x)`; its coefficient is `chosenGroupOrder` over
  -- the order of the automorphism group of the class, times `N * θ`.
  let coeff (x : StdClasses (stdLevel D.E (Fin 2)) × GL (Fin 2) (D.twistModulus ϑ 2).ResidueRing) :
    ℂ :=
    D.chosenGroupOrder / Nat.card (classAut stdRatPoints (stdLevel _ (Fin 2)) x.1.out) *
      (N * θ (g x))
  have h_coeff : ∀ x, coeff x ∈ Seesaw.integralAway ϑ.normQ := by
    refine fun x ↦ mul_mem ?_ fun l _ hl j ↦ ?_
    · -- Minkowski's lemma: `chosenGroupOrder` over the order of the group is an integer.
      exact Seesaw.div_mem_integralAway
        ((D.card_classAut_dvd_chosenGroupOrder (by simpa using D.nat_le_of_hasLogBound) le_rfl
          x.1.out).mul_right (_ ^ 0))
    -- Move `g x` by a rational point until it is integral at `l`.
    obtain ⟨r, hr, -⟩ := exists_mul_mem_integralAbove l (g x) 1
    simp_rw [θ, ← detKernel_stdEmbFin_mul _ r (g x)]
    let _ : PadicPlace l := ⟨j⟩
    refine ker_int.norm_le_one (weight .one) (weight .one) D.normQ_mul_M_pow_mem_modulus
      (by simp [ite_mem, Pi.single_apply]) h_homog hl (by simp) hr
      ⟨∏ τ, det (of (.X ⟨τ, ·, ·⟩)) ^ c τ, ?_⟩
    simp [variableMinor, det_apply]
  have h_twist (μ : AutChar D.E) (x : Gf D.E (Fin 2)) :
      detKernel (Fin 2) (p.character * μ * upsilonU1 ^ 1) c (D.twistModulus ϑ 2) (Pi.single 1 1) x =
        μ.1 (detFin 1 x) * θ x := by
    simp [θ, detKernel, modKernel_twist]
    ac_rfl
  -- So the period at a character of modulus `ϑ.Q` is a sum of multiples of its values.
  have h_period (ϑ' : D.TameChar) (hQ : ϑ'.Q = ϑ.Q) :
      detPeriod (Fin 2) (p.character * ϑ'.toAutChar * upsilonU1 ^ 1) c (D.twistModulus ϑ' 2)
        (p.tamePart * ϑ'.tamePart) =
        stdClassSum (stdLevel D.E (Fin 2)) fun x ↦ ∑ y :
          GL (Fin 2) (D.twistModulus ϑ 2).ResidueRing,
          ϑ'.toAutChar.1 (detFin 1 (x * (liftMod y).1)) * θ (x * (liftMod y).1) := by
    have h_weight : (p.character * ϑ'.toAutChar * upsilonU1 ^ 1).HasWeight (-c ·)
      (p.tamePart * ϑ'.tamePart) := weight ϑ'
    obtain ⟨μ, Q, ψ⟩ := ϑ'
    subst hQ
    simp_rw [← h_twist]
    exact detPeriod_eq_stdClassSum_sum (p.tamePart_mul_tamePart_apply_eq_one_of_notMem _)
  refine .norm_sq _ ⟨_, inferInstance, fun x ↦ detFin 1 (g x), coeff, h_coeff, fun ϑ' hQ ↦ ?_⟩
  simp [↓h_period ϑ' hQ, coeff, g, c, classSum, mul_sum, Fintype.sum_prod_type, Rat.smul_def,
    division_def, ↓finsum_eq_sum_of_fintype]
  ac_rfl

open scoped Classical in
/-- Let `p = (ν, 1)` be a critical pair, that is, a character `ν` of U(1) with the point `1`, whose
tame part is nontrivial exactly at the chosen places, those dividing `D.piM` (`IsRamified`). There
is a function `F` of tame characters with the properties of `IsTwistMeasure {0, 1} 1`: it is nonzero
at the trivial character; at each modulus it is evaluation on finitely many points with coefficients
integral away from that modulus (an integral measure); adding a place of norm `q` multiplies it by
the inverse Euler factors with denominators `q ^ 0` and `q ^ 1`; and at a twist `ϑ` it is
`F 1 * normQ ϑ * r ^ 2`, where `r = p.ratio ϑ` is the ratio of the absolute values of the twisted
and untwisted `L`-values at `1`. -/
theorem exists_isTwistMeasure_of_z_eq_one {p : D.CriticalPair} (h_ram : p.IsRamified)
    (hz : p.z = 1) :
    ∃ F : D.TameChar → ℂ, p.IsTwistMeasure {0, 1} 1 F := by
  -- Take the squared absolute value of a fixed multiple of the period `detPeriod` in rank two of
  -- `ν ϑ υ`.
  let Λ (ϑ : D.TameChar) : ℂ :=
    detPeriod (Fin 2) (p.character * ϑ.toAutChar * upsilonU1 ^ 1) (fun τ : D.Φ ↦ p.negWeight τ - 1)
      (D.twistModulus ϑ 2) (p.tamePart * ϑ.tamePart)
  -- `D.chosenGroupOrder * N` clears the denominators of the period; `C` relates its size at a
  -- twist to `L`-values.
  obtain ⟨N, hN, h_measure⟩ := exists_isIntegralMeasure_norm_sq_detPeriod p
  obtain ⟨C, Λ_twist⟩ : ∃ C : ℝ, ∀ ϑ : D.Twist, Λ ϑ.1 ≠ 0 ∧ C ≠ 0 ∧
      C * ‖Λ ϑ.1‖ ^ 2 =
        Exchange.lValueProd ({w | D.IsChosen w} ∪ ϑ.Q) (p.character * ϑ.toAutChar)⁻¹ 1 :=
    exists_mul_norm_sq_detPeriod_eq h_ram
  refine ⟨fun ϑ ↦ ‖D.chosenGroupOrder * N * Λ ϑ‖ ^ 2,
    ⟨?_, h_measure, fun ϑ ϑ' v hv hQ hχ hψ ↦ ?_,
      fun ϑ ↦ ?_⟩⟩
  · obtain ⟨h_ne_zero, -, -⟩ := Λ_twist 1
    simp [NeZero.ne, hN, h_ne_zero]
  · -- The squared norm of `(1 - X) * (1 - v.q * X)` is the stated product of inverse Euler factors.
    have h_period : Λ ϑ' = SiegelWeil.qPochhammer v.q 2
        ((p.character * ϑ.toAutChar * upsilonU1 ^ 1).frobValue (Fin 2) v)⁻¹ * Λ ϑ :=
      detPeriod_mul_upsilonU1_insert hv hQ hχ hψ
    simp [h_period, ↓← mul_conj', AutChar.frobValue, AutChar.spaceChar, ← ofReal_pow,
      prod_range, inv_eq_conj, prod_mul_distrib]
    ring
  · -- Compare `Λ_twist` at `ϑ` and at `1`: the two values of `lValueProd` differ by the factor
    -- in `lValueProd_eq_mul_prod_ratio_sq`, and `C ≠ 0` cancels.
    have h_sq : (‖Λ ϑ.1‖ : ℂ) ^ 2 =
        ‖Λ TameChar.one‖ ^ 2 * (ϑ.normQ * p.ratio ϑ ^ 2) := by
      have h_ratio : Exchange.lValueProd ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q)
          (p.character * ϑ.toAutChar ^ (1 : ℤˣ).val)⁻¹ p.z = ϑ.normQ ^ p.z ^ 2 *
            (Exchange.lValueProd {w : FinPlace D.E | D.IsChosen w} p.character⁻¹ p.z *
              ∏ k ∈ Icc 1 p.z, (p.lowerPoint k).ratio ϑ.1 1 ^ 2) :=
        p.lValueProd_eq_mul_prod_ratio_sq 1 ϑ.1
      obtain ⟨-, hC, h_one⟩ := Λ_twist 1
      obtain ⟨-, -, h_ϑ⟩ := Λ_twist ϑ
      -- With `z = 1` the product has one factor, the square of the ratio; divide by `C` after
      -- casting the identities for `ϑ` and `1` to `ℝ`.
      simp [ratio, lowerPoint, hz,
        toAutChar_one_and_toTwist_one_and_Q_one] at h_ratio h_one h_ϑ ⊢
      norm_cast at *
      grind
    simp only [norm_mul, mul_pow, ofReal_mul, pow_one, h_sq]
    ring

/-- Let `p = (ν, z)` be a critical pair, that is, a character `ν` of U(1) with an integer
`1 ≤ z ≤ c`, `-c` its weight, whose tame part is nontrivial exactly at the chosen places, those
dividing `D.piM` (`IsRamified`). Some function `F` of tame characters has the properties of
`IsTwistMeasure I m`: it is nonzero at the trivial character; at each modulus it is evaluation on
finitely many points with coefficients integral away from that modulus (an integral measure); adding
a place of norm `q` multiplies it by the inverse Euler factors with denominators `q ^ l`, `l ∈ I`;
and at a twist `ϑ` it is `F 1 * normQ ϑ ^ m * r ^ (m + 1)`, where `r = p.ratio ϑ` is the ratio of
twisted and untwisted `L`-values at `z` in absolute value. For `z ≥ 2`, which is what
`HasLiftRank` asks besides `2 z` indices, `I = {z}`, `m = 0` and `F` is `integralAlgebraicPart`, an
integral multiple of the algebraic part of the `L`-value. For `z = 1`, `I = {0, 1}` and `m = 1`, so
that the square of the ratio occurs. -/
theorem exists_isTwistMeasure {p : D.CriticalPair} (h_ram : p.IsRamified) :
    ∃ F : D.TameChar → ℂ,
      (∀ H : p.HasLiftRank (Fin (2 * p.z)), F = integralAlgebraicPart H) ∧
      p.IsTwistMeasure (if p.z = 1 then {0, 1} else {p.z}) (if p.z = 1 then 1 else 0) F := by
  obtain ⟨hz_pos, -⟩ := p.z_mem
  obtain hz | hz := hz_pos.lt_or_eq'
  · have H : p.HasLiftRank (Fin (2 * p.z)) := ⟨card_fin _, hz⟩
    exact ⟨integralAlgebraicPart H, fun _ ↦ rfl, by
      simpa [hz.ne'] using isTwistMeasure_integralAlgebraicPart H⟩
  · obtain ⟨F, hF⟩ := exists_isTwistMeasure_of_z_eq_one h_ram hz
    exact ⟨F, fun H ↦ absurd H.2 (by omega), by simpa [hz] using hF⟩

end New.Data.CriticalPair

namespace New.Selmer

variable {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]

/-- If `I` is an auxiliary set of places avoiding `badPlaces D ℓ`, the places dividing `ℓ M N` (with
`M = D.M` and `N = D.N` the level), then the product of the norms of the places of `I` is prime to
`ℓ` and to `M N`. -/
lemma coprime_prod_q_of_isAuxiliary {I : Finset (FinPlace D.E)}
    (hI : IsAuxiliary (badPlaces D ℓ) I) :
    ℓ.Coprime (∏ w ∈ I, w.q) ∧ (D.M * D.N).Coprime (∏ w ∈ I, w.q) := by
  -- If the prime `w.q` divided `ℓ * (D.M * D.N)`, then `w`, which contains `w.q`, would lie in
  -- `badPlaces D ℓ`.
  have h_coprime : ∀ w ∈ I, w.q.Coprime (ℓ * (D.M * D.N)) := by
    intro w hw
    obtain ⟨h_notMem, h_prime, -⟩ := hI w hw
    refine h_prime.coprime_iff_not_dvd.2 fun h_dvd ↦ h_notMem ?_
    simpa [badPlaces] using w.asIdeal.mem_of_dvd h_dvd.natCast w.asIdeal.absNorm_mem
  exact Nat.coprime_mul_iff_left.1 (Nat.Coprime.prod_left h_coprime).symm

/-- The tame character of modulus `I` given by a member `χ = (μ, ψ)` of `tameChars I`, that is, a
character `μ` of U(1)(𝔸) of weight `0` whose tame part `ψ` is trivial outside `I`; here `I` is an
auxiliary set avoiding `badPlaces D ℓ`, the places dividing `ℓ`, `D.M` or `D.N`. -/
@[simp]
noncomputable def tameCharOfAuxiliary (I : Finset (FinPlace D.E))
    (hI : IsAuxiliary (badPlaces D ℓ) I) (χ : tameChars I) :
    D.TameChar where
  toAutChar := χ.1.1
  Q := I
  tamePart := χ.1.2
  hasWeight := χ.2.1
  tamePart_eq_one := χ.2.2
  star_notMem := by grind
  coprime := (coprime_prod_q_of_isAuxiliary hI).2

variable [PadicIso ℓ]

/-- If a finite idele `x` of `E` has the Artin symbol `g` in the absolute Galois group `AbsGal D`,
then `τ.invAvatar`, the `ℓ`-adic avatar of the inverse of a tame character `τ`, takes at `g` the
value `ιℓ (b⁻¹)`, with `b` the value at `x` of the base change of `τ` and `ιℓ` the fixed
isomorphism of `ℂ` with the algebraic closure of the `ℓ`-adic numbers. -/
lemma invAvatar_eq_of_artinMap_eq {τ : D.TameChar} {x : (𝔸f D.E)ˣ} {g : AbsGal D}
    (hx : artinMap (AbsGal D) x = g) :
    τ.invAvatar g = ιℓ (τ.toAutChar.baseChange.finPart x)⁻¹ := by
  -- The formula for the avatar; the type is `0`, so the product over the embeddings is `1`.
  refine (AlgHeckeChar.avatar_apply_of_artinMap_eq _ hx).trans ?_
  simp [toAlgebraic, IsHeckeOfType.toAlgebraic, AlgHeckeChar.character, AlgHeckeChar.infinityType]

/-- Let `ℓ` be the fixed prime, `E = D.E` the CM field of the data `D`, `Ω` the algebraic closure of
`ℚ`, and `I` a finite set of places of `E` that is auxiliary for `badPlaces D ℓ`, the places
dividing `ℓ * D.M * D.N`: the places of `I` have prime norm, their conjugates are outside `I`, and
neither they nor their conjugates are bad. Let `ψ : Gal(Ω/E) → ℚ̄_ℓ` be a locally constant character
with `ψ(Art x) = η(x / x̄)` for an idele class character `η` of modulus `I` that is trivial on the
local components at the places over `ℓ` (`IsFromU1`). Then `ψ = τ.invAvatar` for some `τ` with
modulus `I` in `D.TameChar`, the weight-zero tamely ramified characters of U(1)(𝔸) of `E`. -/
lemma exists_tameChar_invAvatar_eq {I : Finset (FinPlace D.E)} (hI : IsAuxiliary (badPlaces D ℓ) I)
    {ψ : Gal(Ω/D.E) →* PadicAlgCl ℓ} (hψ : IsFromU1 (placesDividing D.E ℓ) I ψ) :
    ∃ τ : D.TameChar, τ.Q = I ∧ ψ = τ.invAvatar := by
  -- `ψ (Art x) = η (x / star x)` for a character `η` of the finite ideles that kills the
  -- principal ones. Restricted to U(1), `η` factors through the class group of tame level `I`, so
  -- it comes from a tame character `μ`; then `ψ` is `TameChar.invAvatar` of `μ⁻¹`.
  obtain ⟨η, η_rat, η_int, η_art⟩ : ∃ η : (𝔸f D.E)ˣ →* PadicAlgCl ℓ,
      (∀ y : D.Eˣ, η (principalIdele y) = 1) ∧
      (∀ a ∈ idelesUnitOff (placesDividing D.E ℓ).conjClosure,
        (∀ w ∈ ↑I \ (placesDividing D.E ℓ).conjClosure,
          Valued.v ((ideleAt w a : LocField w) - 1) < 1) → η a = 1) ∧
      ∀ (x : (𝔸f D.E)ˣ) (g : Gal(Ω/D.E)), artinMap Gal(Ω/D.E) x = g → ψ g = η (x / star x) :=
    hψ.exists_ideleChar
  let toFinIdele : unitary (𝔸 D.E) →* (𝔸f D.E)ˣ :=
    (Units.map (MonoidHom.snd (NumberField.InfinitePlace D.E → ℂ) (𝔸f D.E))).comp Unitary.toUnits
  let η' : unitary (𝔸 D.E) →* PadicAlgCl ℓ := η.comp toFinIdele
  -- `η'` is trivial on rational points and on integral points that are `1` modulo `I`.
  have rat_le : rationalU1 ≤ η'.ker := by
    intro u hu
    obtain ⟨y, hy⟩ := exists_unitary_of_mem_rationalU1 hu
    have h_principal : toFinIdele u = principalIdele (Unitary.toUnits y) :=
      Units.ext (by simp [toFinIdele, ← hy])
    simp [η', h_principal, η_rat]
  have int_le : integralU1 I ≤ η'.ker := fun u ⟨hu, hu_red⟩ ↦
    η_int _ (idelesUnitOff_mono bot_le (idelesUnitOff_empty.ge ⟨hu, star_mem_Ô hu⟩))
      fun w hw ↦ residue_eq_iff_valuation_sub_lt_one.1 (hu_red w hw.1)
  let χ : unitary (𝔸 D.E) ⧸ (rationalU1 ⊔ integralU1 I) →* ℂ :=
    MonoidHom.comp ιℓ.symm (QuotientGroup.lift _ η' (sup_le rat_le int_le))
  -- The character `χ` is that of a member `μ` of `tameChars I`.
  obtain ⟨μ, hμ⟩ := AutChar.exists_mem_tameChars χ
  refine ⟨tameCharOfAuxiliary I hI μ⁻¹, rfl, MonoidHom.ext fun g ↦ ?_⟩
  obtain ⟨x, hx⟩ := artinMap_surjective (AbsGal D) g
  let u : unitary (𝔸 D.E) := divStar (finIdeleIncl x)
  have h_baseChange : (μ.val.1.baseChange.finPart x : ℂ) = μ.val.1.val u := rfl
  calc ψ g = η (x / star x) := η_art x g hx
    _ = η' u := congrArg η (Units.ext rfl)
    _ = ιℓ (μ.val.1.val u) := ιℓ.symm_apply_eq.1 (hμ u).symm
    _ = (tameCharOfAuxiliary I hI μ⁻¹).invAvatar g := by
      simp [invAvatar_eq_of_artinMap_eq hx, h_baseChange, -map_inv₀]

end New.Selmer
