import New.OneLift.HeckeValues.AlgebraicPartIntegrality
import New.OneLift.HeckeValues.TwistedRatio

/-!
# Archimedean bounds and heights of squared norms of rank-one theta lifts

This file bounds the absolute values of the conjugates under `Aut(ℂ/K)` of the squared norm `‖φ‖²`
of the lift `φ = New.Data.CriticalPair.trivialLift` of a critical pair for the trivial twist. It
also bounds the conjugates of `New.Data.CriticalPair.integralAlgebraicPart` for flat pairs
(`New.Data.CriticalPair.HasEmptyRow`, `c = z`). A conjugate of the squared norm is a multiple of the
squared norm of the lift for the conjugate character, and this is an `L`-value times explicit
factors. The file shows that flat pairs exist over a given character of weight zero and bounds the
range of the jet degrees of a main pair (`New.Data.CriticalPair.IsMainPair`). It bounds the height
(`New.HeightLe`) of the squared norm of the untwisted lift of a main pair.

## Main definitions and results

* `New.Data.heightLe_norm_trivialLift_sq`: for a main pair, a bound for the height of the squared
  norm of the untwisted lift.
* `New.Data.CriticalPair.norm_map_integralAlgebraicPart_le`: for a flat pair, every conjugate under
  `Aut ℂ` of `integralAlgebraicPart` at the trivial twist has absolute value at most
  `exp (x ^ 34)`.

Notions from other files:
* `New.Data.CriticalPair`: An integer 1 ≤ z ≤ t and a character ν of U(1)(𝔸) of weight −c, z ≤ c(v)
  ≤ 4b, with tame part supported on the chosen places.
* `New.Data.CriticalPair.integralAlgebraicPart`: The product of
  `n_L = chosenGroupOrder * denomBound ^ 2` and the algebraic part `‖φ‖² / N(Q) ^ (2 z - 1)`
  (`New.Data.CriticalPair.algPart`); the first factor of `n_L` clears the orders of automorphism
  groups, the second the denominators of `φ`.

## Relation to the literature

Critical Hecke L-values of CM fields as squared norms of theta lifts from U(1). See
`Lib.SiegelWeil.RallisInner.SharpData` for sources.
-/

noncomputable section

/-! ## Archimedean bounds for the algebraic part of flat pairs -/

section AlgebraicPartSize

open New Fintype Real LValueData Ideal LevelPlaces «GL» DescentPair

/-- Archimedean bound for one value of the theta kernel of a flat pair `p = (ν, z)`. For
`σ ∈ Aut ℂ`, the Gram norm of the conjugate under `σ` of `pointKernel` at the trivial twist and any
point of `U(1) × U(n)` has a bound that depends on `D` and `card n` only. -/
lemma New.Data.CriticalPair.sqrt_weylNormSq_pointKernel_le {P : Parameters} {D : Data P}
    {p : D.CriticalPair}
    {n : Type} [Fintype n] [DecidableEq n] (hp : p.HasEmptyRow n) (σ : ℂ ≃+* ℂ) (u : Gf D.E Unit)
    (g : Gf D.E n) :
    √(weylNormSq (σ ∘ pointKernel hp.2 TameChar.one u g)) ≤
      (D.M ^ D.f : ℝ) ^ card n *
        exp (P.constantBound * (P.q₁ D.towerExp * card n + 1) ^ 2 + D.f * card n * log 4) := by
  -- The weight is `0`, the test vector has norm `1`, and the datum is that of
  -- `identityBlockIndicator`, a function modulo an ideal of norm `M ^ f` with values `0` and `1`.
  let L : LValueData D.E n := lValueData hp.2 .one
  have h_weight : L.descentPair.columnCount = 0 := by aesop
  have h_vec : weylNormSq (σ ∘ (1 : WeylIndexFamily (fun _ : D.Φ ↦ Unit) 0 → ℂ)) = 1 := by
    refine (congrArg weylNormSq ?_).trans (weylNormSq_weylEval_permArray (rowEquivFin _))
    simp [funext_iff, weylEval, Exchange.nablaBasis_eq_one]
  have h_card : card ((D.levelPlaces .one).levelModulus 1).ResidueRing = D.M ^ D.f := by
    have h_twist : IsEmpty (D.levelPlaces .one).TwistIndex := ⟨nofun⟩
    rw [card_levelModulus_residueRing, pow_one, prod_empty (ι := TwistIndex _), mul_one]
    exact prod_q_chosenPlace
  have h_values (σ : ℂ ≃+* ℂ) (y : Matrix n Unit (L.descentPair.levelModulus 1).ResidueRing) :
      ‖σ (L.descentPair.identityBlockIndicator y)‖ ≤ 1 := by
    grind [identityBlockIndicator, norm_one, norm_zero]
  grw (transparency := default) [P.sqrt_weylNormSq_schurJet_le_of_isVacuumCombination
      (hb := L.charV_hasWeight)
      (P.isVacuumCombination_of_isAdmissibleCombination
        (P.isAdmissibleCombination_vacuumDatum 1 h_values)) u g 1
      L.isLiftWeight,
    card_fun, h_card, h_weight, h_vec]
  simp [Parameters.jetSizeBound, schurGrowthExponent, diagramWeight,
    show (2 + 2 : ℝ) = 4 by norm_num]

/-- Let `p = (ν, z)` be a critical pair of the data `D`, let `n` have `2 z ≥ 4` elements, let
`φ = trivialLift h_rank .one` be the normalised lift of `ν` to `U(n)` at the trivial twist, and let
`σ ∈ Aut ℂ`. Suppose all `σ`-conjugates of kernel values have norm at most `C`. Then `normSqAt σ`,
the sum over the classes of `U(n)` at the level of `φ` of the squared norms of the `σ`-conjugates of
the values of `φ`, each divided by the order of its stabiliser, is at most
`exp (x ^ 30) * (exp (x ^ 30) * C) ^ 2`, where `x = D.x` is the length of the prime sum. -/
lemma New.Data.CriticalPair.normSqAt_trivialLift_le {P : Parameters} {D : Data P}
    {p : D.CriticalPair} {n : Type}
    [Fintype n] [DecidableEq n] (h_rank : p.HasLiftRank n) (σ : ℂ ≃+* ℂ) {C : ℝ}
    (h_ker : ∀ (u : Gf D.E Unit) (g : Gf D.E n),
      √(weylNormSq (σ ∘ pointKernel h_rank TameChar.one u g)) ≤ C) :
    (trivialLift h_rank TameChar.one).normSqAt σ ≤ exp (D.x ^ 30) * (exp (D.x ^ 30) * C) ^ 2 := by
  have hC : 0 ≤ C := (sqrt_nonneg _).trans (h_ker 1 1)
  -- Both class numbers, of `U(1)` and of `U(n)`, are at most `exp (x ^ 30)`.
  have h_classes_one : Nat.card (StdClasses (n := Unit) D.chosenLevel) ≤ exp (D.x ^ 30) :=
    D.card_stdClasses_le_exp (D.principalLevel_le_chosenLevel (dvd_mul_right ..))
      (by simpa using D.nat_le_of_hasLogBound)
  have h_level :
      principalLevel n (D.piM * D.piN) ≤ (lValueData h_rank .one).descentPair.levelGroup := by
    refine principalLevel_le_levelOf ?_
    rintro (⟨i, w, hw⟩ | w)
    exacts [mul_mem_right _ _ hw.1, nomatch w]
  have h_classes : Nat.card (StdClasses (lValueData h_rank .one).descentPair.levelGroup) ≤ exp
    (D.x ^ 30) :=
    D.card_stdClasses_le_exp h_level (h_rank.1.trans_le D.nat_le_of_hasLogBound)
  -- A value of `φ` is a sum of kernel values over the classes of `U(1)` and the units at the
  -- twist places, of which there are none.
  have h_twist : IsEmpty (D.levelPlaces .one).TwistIndex := ⟨nofun⟩
  have h_value (g : Gf D.E n) : √(weylNormSq (σ ∘ trivialLift h_rank .one g)) ≤
      Nat.card (StdClasses (n := Unit) D.chosenLevel) * C := by
    grw (transparency := default) [trivialLift_apply, sqrt_weylNormSq_sum_le, h_ker]
    simp [← Nat.card_eq_fintype_card, Nat.card_prod,
      (Nat.card_unique : Nat.card (TwistGL (D.levelPlaces .one) Unit) = 1)]
  calc (trivialLift h_rank .one).normSqAt σ
      ≤ Nat.card (StdClasses (lValueData h_rank .one).descentPair.levelGroup) *
          (Nat.card (StdClasses (n := Unit) D.chosenLevel) * C) ^ 2 :=
        classSum_le_card_mul_sq h_value
    _ ≤ exp (D.x ^ 30) * (exp (D.x ^ 30) * C) ^ 2 := by gcongr

/-- For a flat pair `p = (ν, z)` (`HasEmptyRow`: `ν` has weight `-z` at every infinite place), the
integer `D.chosenGroupOrder * p.denomBound ^ 2`, by which `integralAlgebraicPart` multiplies the
algebraic part `algPart`, is at most `exp (x ^ 33)`, where `x = D.x` is the length of the prime sum.
-/
lemma New.Data.CriticalPair.chosenGroupOrder_mul_denomBound_sq_le {P : Parameters} {D : Data P}
    {p : D.CriticalPair} {n : Type} [Fintype n] (hp : p.HasEmptyRow n) :
    (D.chosenGroupOrder * p.denomBound ^ 2 : ℝ) ≤ exp (D.x ^ 33) := by
  -- The rows are empty, so `p.denomBound = D.M ^ (4 f z)`.
  have h_log : log (D.chosenGroupOrder * p.denomBound ^ 2) =
      log D.chosenGroupOrder + 8 * D.f * p.z * log D.M := by
    simp [denomBound, hp, log_mul, NeZero.ne]
    ring
  exact le_exp_of_log_le (h_log.trans_le D.le_of_hasLogBound)

/-- Archimedean bound for a flat pair. Let `p = (ν, z)` with `ν` of weight `-z` at every infinite
place, let `n` have `2 z ≥ 4` elements (`HasEmptyRow`), and let `φ` be the normalised lift of `ν` to
`U(n)`. At the trivial twist `integralAlgebraicPart` is `‖φ‖²` times the integer
`chosenGroupOrder * denomBound ^ 2`, which clears the orders of stabilisers and the denominators of
`φ`. Every conjugate of it under `Aut ℂ` has absolute value at most `exp (x ^ 34)`, where `x = D.x`
is the length of the prime sum. -/
lemma New.Data.CriticalPair.norm_map_integralAlgebraicPart_le {P : Parameters} {D : Data P}
    {p : D.CriticalPair} {n : Type}
    [Fintype n] [DecidableEq n] (hp : p.HasEmptyRow n) (σ : ℂ ≃+* ℂ) :
    ‖σ (integralAlgebraicPart hp.2 TameChar.one)‖ ≤ exp (D.x ^ 34) := by
  -- Cauchy–Schwarz bounds the conjugates of `‖φ‖²` by the class sums `φ.normSqAt`, and these are
  -- bounded through the bound `C` for one kernel value.
  let φ : (lValueData hp.2 .one).descentPair.FormV := trivialLift hp.2 .one
  let C : ℝ := (D.M ^ D.f : ℝ) ^ card n *
    exp (P.constantBound * (P.q₁ D.towerExp * card n + 1) ^ 2 + D.f * card n * log 4)
  have h_normSq (σ : ℂ ≃+* ℂ) : φ.normSqAt σ ≤ exp (D.x ^ 30) * (exp (D.x ^ 30) * C) ^ 2 :=
    normSqAt_trivialLift_le hp.2 σ (sqrt_weylNormSq_pointKernel_le hp σ)
  have h_inner : ‖σ (inner ℂ φ φ)‖ ≤ exp (D.x ^ 30) * (exp (D.x ^ 30) * C) ^ 2 := by
    grw [φ.norm_map_inner_le φ, h_normSq, h_normSq, mul_self_sqrt (by positivity)]
  -- Every term of the logarithm is small against `x ^ 34`.
  have h_log : log (exp (D.x ^ 33) * (exp (D.x ^ 30) * (exp (D.x ^ 30) * C) ^ 2)) ≤ D.x ^ 34 := by
    simpa [C, hp, log_mul, NeZero.ne] using D.le_of_hasLogBound
  calc ‖σ (integralAlgebraicPart hp.2 .one)‖
      = D.chosenGroupOrder * p.denomBound ^ 2 * ‖σ (inner ℂ φ φ)‖ := by
        simp [integralAlgebraicPart, toAutChar_one_and_toTwist_one_and_Q_one, φ]
    _ ≤ exp (D.x ^ 33) * (exp (D.x ^ 30) * (exp (D.x ^ 30) * C) ^ 2) := by
        grw [h_inner, chosenGroupOrder_mul_denomBound_sq_le hp]
    _ ≤ exp (D.x ^ 34) := le_exp_of_log_le h_log

end AlgebraicPartSize

/-!
## Galois conjugates of the squared norm of the lift

`New.Data.CriticalPair.exists_log_norm_map_norm_sq_trivialLift_eq_add_sum_jetSize` estimates the
absolute values of the conjugates under `Aut(ℂ/K)` of the squared norm of the lift for the trivial
twist. A conjugate of the squared norm is a multiple of the squared norm of the lift for the
conjugate character, and this is an `L`-value times explicit factors.
-/

section AlgebraicPartConjugates

open Real Fintype New Parameters LValueData

/-- For `σ ∈ Aut(ℂ/K)` the map `star ∘ σ ∘ star` lies in `Aut(ℂ/K)`, and it permutes the infinite
places of `P.E s`, the CM field of index `s` in the tower over `K`, as `σ` does (`placePerm`). -/
lemma New.Parameters.exists_eq_star_map_star_and_placePerm_eq {P : Parameters} (s : ℕ)
    (σ : Gal(ℂ/K P)) :
    ∃ σ' : Gal(ℂ/K P), (∀ x : ℂ, σ' x = star (σ (star x))) ∧ placePerm s σ' = placePerm s σ := by
  have h_comm (x : K P) : star (σ (star (x : ℂ))) = x := by
    simpa using congrArg star (σ.commutes (star x))
  let σ' : Gal(ℂ/K P) := { starRingAut * σ.toRingEquiv * starRingAut with commutes' := h_comm }
  have h_emb : (σ' : ℂ →+* ℂ).comp (Φ (1 : P.Φ s)) = (σ : ℂ →+* ℂ).comp (Φ (1 : P.Φ s)) :=
    RingHom.ext fun x ↦ by simp [σ', ← map_star_complex, apply_Phi_eq_Phi_placePerm]
  exact ⟨σ', fun _ ↦ rfl, by rw [placePerm, placePerm, h_emb]⟩

/-- Let `p = (ν, z)` be a critical pair with `card n = 2 z ≥ 4` and `ν` of weight `-p.negWeight`,
let `ϑ` be a tame character and `J = p.rowLengthSum = ∑ τ, (p.negWeight τ - z)`. Let `A` be
`jetScale ^ J` times the lift of `ν ϑ` to `U(n)` without scaling. The normalised lift
`φ = trivialLift H ϑ` is `vacuumScale ^ card n * (star piMBar) ^ J` times `A`, where `piMBar` is an
integer of `K` of norm `M = D.M`. Hence `‖φ‖² = ‖vacuumScale ^ card n‖² * M ^ J * ⟪A, A⟫`. -/
lemma New.Data.CriticalPair.norm_trivialLift_sq_eq_mul_inner {P : Parameters} {D : Data P}
    {p : D.CriticalPair}
    {n : Type} [Fintype n] [DecidableEq n] (H : p.HasLiftRank n) (ϑ : D.TameChar) :
    let A : (lValueData H ϑ).descentPair.FormV :=
      P.jetScale D.towerExp ^ p.rowLengthSum • (lValueData H ϑ).trivialLift
    (‖trivialLift H ϑ‖ ^ 2 : ℂ) =
      (‖P.vacuumScale D.towerExp ^ card n‖ ^ 2 : ℝ) * D.M ^ p.rowLengthSum * inner ℂ A A := by
  intro A
  have h_smul :
      trivialLift H ϑ = (P.vacuumScale D.towerExp ^ card n * star (D.piMBar : ℂ) ^ p.rowLengthSum) •
        A := by
    rw [trivialLift, mul_pow, ← mul_assoc, mul_smul]
  have h_norm : ‖trivialLift H ϑ‖ ^ 2 =
      ‖P.vacuumScale D.towerExp ^ card n‖ ^ 2 * D.M ^ p.rowLengthSum * ‖A‖ ^ 2 := by
    rw [h_smul, norm_smul, norm_mul, norm_pow (star _), mul_pow, mul_pow, pow_right_comm,
      show ‖star (D.piMBar : ℂ)‖ ^ 2 = D.M from D.norm_map_star_piMBar_sq 1]
  rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, h_norm]
  simp

/-- Let `σ` be an automorphism of `ℂ` over the imaginary quadratic field `K = ℚ(i√d)` of the
parameters `P`. There is a constant `a > 0` with the following property. Let `p = (ν, z)` be a pair
with `card n = 2 z ≥ 4` and `ν` of weight `-p.negWeight`, and let
`J = p.rowLengthSum = ∑ τ, (p.negWeight τ - z)`. Let `A` be `jetScale ^ J` times the lift for the
data of `p` at the trivial twist. Then there are lift data `Y` on the same places, with the row
lengths `p.negWeight τ - z` permuted by `σ` (`placePerm`), such that `‖σ ⟪A, A⟫‖` is `Ω ^ (-J) * a`
times the squared norm of the lift for `Y`. Here `Ω = P.bigOmega D.towerExp = exp (γ - Re L'/L(1,
χ_K)) 2π / rd_E`, with Euler's constant `γ` and the root discriminant `rd_E` of `D.E`. -/
lemma New.Data.CriticalPair.exists_norm_map_inner_trivialLift_eq_mul {P : Parameters} (D : Data P)
    (n : Type) [Fintype n] [DecidableEq n] (σ : Gal(ℂ/K P)) :
    ∃ a : ℝ, 0 < a ∧ ∀ (p : D.CriticalPair) (H : p.HasLiftRank n),
      let A : (lValueData H TameChar.one).descentPair.FormV :=
        P.jetScale D.towerExp ^ p.rowLengthSum • (lValueData H TameChar.one).trivialLift
      ∃ Y : LValueData D.E n,
        Y.toLevelPlaces = D.levelPlaces TameChar.one ∧
        (∀ τ : D.Φ, Y.rowLength (placePerm D.towerExp σ τ) = p.negWeight τ - p.z) ∧
        ‖σ (inner ℂ A A)‖ = (√(P.bigOmega D.towerExp))⁻¹ ^ (2 * p.rowLengthSum) * a *
          ‖inner ℂ Y.trivialLift Y.trivialLift‖ := by
  -- Both `σ` and `σ' = star ∘ σ ∘ star` carry `A` to a constant times `multiplierRatio` times the
  -- lift for the conjugate character `ν` (`LValueData.map_trivialLift`).
  obtain ⟨σ', hσ' : ∀ x : ℂ, σ' x = star (σ (star x)),
    h_perm : placePerm D.towerExp σ' = placePerm D.towerExp σ⟩ :=
      exists_eq_star_map_star_and_placePerm_eq D.towerExp σ
  obtain ⟨t, c, u, ht : ‖t‖ = (√(P.bigOmega D.towerExp))⁻¹, hc : c ≠ 0, h_law⟩ :=
    map_trivialLift n (D.levelPlaces .one) ⟨nofun⟩ σ
  obtain ⟨t', c', u', ht' : ‖t'‖ = (√(P.bigOmega D.towerExp))⁻¹, hc' : c' ≠ 0, h_law'⟩ :=
    map_trivialLift n (D.levelPlaces .one) ⟨nofun⟩ σ'
  refine ⟨‖c'‖ * ‖c‖, by positivity, fun p H ↦ ?_⟩
  intro A
  let X : LValueData D.E n := lValueData H .one
  obtain ⟨ν, hν_weight, hν : ∀ v : unitary (𝔸 D.E), v.val.1 = 1 → ν.val v = σ (X.u1Char.val v)⟩ :=
    X.hasWeight.exists_conj (σ := σ) apply_Phi_eq_Phi_placePerm
  have hν' (v : unitary (𝔸 D.E)) (hv : v.val.1 = 1) : ν.val v = σ' (X.u1Char.val v) := by
    simp [hσ', ← Circle.coe_inv_eq_conj, ← hν, hv]
  let Y : LValueData D.E n :=
    { toLevelPlaces := X.toLevelPlaces
      rowLength τ := X.rowLength ((placePerm D.towerExp σ).symm τ)
      u1Char := ν
      tamePart w := (X.tamePart w).ringHomComp σ
      hasWeight := hν_weight
      one_lt_card := X.one_lt_card
      unramified w hw := by simp [X.unramified w hw] }
  let toPair (h : Gf D.E n) : Gf D.E (n × Unit) :=
    (G.onHom (s := X.descentPair.signs) (s' := 1) (1, 1, h)).2
  have h_map (h : Gf D.E n) (i : WeylIndex n X.descentPair.columnCount) :
      σ (A h i) = t ^ p.rowLengthSum * (c * Y.descentPair.charV.val u) *
        multiplierRatio σ (toPair h) *
        Y.trivialLift h fun τ ↦ i ((placePerm D.towerExp σ).symm τ) :=
    h_law hν_weight Y.unramified rfl H.1 rfl hν h i
  have h_map' (h : Gf D.E n) (i : WeylIndex n X.descentPair.columnCount) :
      star (σ (star (A h i))) =
        t' ^ p.rowLengthSum * (c' * Y.descentPair.charV.val u') * multiplierRatio σ' (toPair h) *
          Y.trivialLift h fun τ ↦ i ((placePerm D.towerExp σ).symm τ) :=
    (hσ' _).symm.trans (h_law' hν_weight Y.unramified rfl H.1 h_perm hν' h i)
  -- The factors `multiplierRatio` for `σ` and `σ'` cancel in the inner product.
  have h_cancel (h : Gf D.E n) :
      multiplierRatio σ (toPair h) * star (multiplierRatio σ' (toPair h)) = 1 := by
    simpa [hσ', multiplierRatio, div_mul_div_comm, div_eq_one_iff_eq, finMultiplier_ne_zero] using
      map_finMultiplier_mul_conj σ (toPair h)
  have h_inner : σ (inner ℂ A A) = star (t' ^ p.rowLengthSum * (c' * Y.descentPair.charV.val u')) *
      (t ^ p.rowLengthSum * (c * Y.descentPair.charV.val u)) * inner ℂ Y.trivialLift
        Y.trivialLift :=
    LevelPlaces.map_inner_self_eq σ A h_map h_map' h_cancel
  refine ⟨Y, rfl, fun τ ↦ by simp [Y, X], ?_⟩
  simp only [h_inner, norm_mul, norm_star, norm_pow, ht, ht', Circle.norm_coe]
  ring

/-- Size of the squared norm of a lift without twist. Let `S` be level places of `D.E` without twist
places. There is a constant `c` such that for all data `Y` on `S` of a theta lift from `U(1)` to
`U(n)`, with `card n = 2 k ≥ 4`, the lift `φ = Y.trivialLift` has `⟪φ, φ⟫ ≠ 0` and
`log ‖⟪φ, φ⟫‖ = c + r + ∑ τ, log (Y.rowLength τ)!` with `-4 f ≤ r`, and `r ≤ 4 f` if all row lengths
vanish. Here `f` is the number of infinite places `τ`. -/
lemma New.Data.exists_log_norm_inner_trivialLift_eq {P : Parameters} (D : Data P) (n : Type)
    [Fintype n] [DecidableEq n] (S : LevelPlaces D.E) (hS : IsEmpty S.TwistIndex) :
    ∃ c : ℝ, ∀ (Y : LValueData D.E n) (k : ℕ), Y.toLevelPlaces = S → card n = 2 * k → 2 ≤ k →
      inner ℂ Y.trivialLift Y.trivialLift ≠ 0 ∧
      ∃ r : ℝ,
        -(4 * D.f) ≤ r ∧
        ((∀ τ : D.Φ, Y.rowLength τ = 0) → r ≤ 4 * D.f) ∧
        log ‖inner ℂ Y.trivialLift Y.trivialLift‖ =
          c + r + ∑ τ : D.Φ, log (Y.rowLength τ).factorial := by
  -- In `LValueData.inner_trivialLift_self_eq_L` the factors `C` and `unitsCard` depend on `n` and
  -- `S` only, and `r` is the logarithm of the dimension `d` times the `L`-value `ℓ`.
  let C : ℂ :=
    (stdSpace D.E n).quotMeasure.real ⊤ * (stdSpace D.E Unit).quotMeasure.real ⊤ /
      eulerProd (K := D.E) placeSign (card n / 2 : ℕ)
  let unitsCard : ℕ := ∏ i : S.ChosenIndex, ((S.chosenPlace i).q - 1)
  refine ⟨log ‖C‖ + log unitsCard, ?_⟩
  rintro Y k rfl h_card hk
  let ℓ : ℂ := Y.u1Char⁻¹.L Y.places k
  let d : ℕ := card (WeylIndex n Y.descentPair.columnCount)
  have h_unitsCard_pos : 0 < unitsCard := by simp [unitsCard]
  have hd_pos : 0 < d := NeZero.pos _
  obtain ⟨hC_ne, h_inner⟩ : C ≠ 0 ∧ inner ℂ Y.trivialLift Y.trivialLift =
      C * unitsCard * hookNumber Y.descentPair.columnCount (rankAt fun _ ↦ n) * d * ℓ *
        (∏ i : Y.TwistIndex, (Y.twistPlace i).q : ℕ) ^ (card n - 1) :=
    Y.inner_trivialLift_self_eq_L h_card.symm hk
  -- The `L`-value is taken at `k ≥ 2`, where the Euler product is bounded.
  obtain ⟨hℓ_ne : ℓ ≠ 0, h_log⟩ :=
    eulerProd_ne_zero_and_abs_log_norm_le Y.hasWeight.inv.isHeckeOfType.norm_heckeCoeff_le le_rfl
      (mod_cast hk : (2 : ℝ) ≤ k)
  obtain ⟨h_log_ge, h_log_le⟩ : -(4 * D.f) ≤ log ‖ℓ‖ ∧ log ‖ℓ‖ ≤ 4 * D.f :=
    abs_le.1 <| h_log.trans_eq <| by
      norm_num [finrank_eq_two_mul_card_infinitePlace, ← mul_assoc]
  have h_norm : ‖inner ℂ Y.trivialLift Y.trivialLift‖ =
      ‖C‖ * unitsCard * (∏ τ : D.Φ, (Y.rowLength τ).factorial : ℝ) * d * ‖ℓ‖ := by
    rw [h_inner, hookNumber_eq_prod_factorial, prod_empty fun i ↦ (Y.twistPlace i).q]
    simp
  refine ⟨norm_pos_iff.1 (by rw [h_norm]; positivity), log d + log ‖ℓ‖,
    by linarith [log_natCast_nonneg d], fun h_zero ↦ ?_, ?_⟩
  · -- In degree zero all basis polynomials are `1`, so the weight has dimension one.
    have hd_le : d ≤ 1 := card_le_one_iff.2 fun _ _ ↦
      linearIndependent_nablaBasis (R := ℂ).injective (by simp [Exchange.nablaBasis_eq_one, h_zero])
    simpa [hd_le.antisymm hd_pos] using h_log_le
  · rw [h_norm, ← log_prod (fun _ _ ↦ by positivity)]
    simp (disch := positivity) only [log_mul]
    ring

/-- Size of the conjugates of `‖φ‖²`, where `φ = trivialLift H .one` is the normalised theta lift to
the definite `U(n)` of the character `ν` of a pair `p = (ν, z)`, without twist. Let `K P = ℚ(i√d)`
be the imaginary quadratic field of the parameters. For `σ ∈ Aut(ℂ/K)` there is a constant `c` such
that for every critical pair `p` with `card n = 2 z ≥ 4` and `ν` of weight `-p.negWeight` there is a
real `r` with (a) `-4 f ≤ r`, (b) `r ≤ 4 f` if `p.negWeight τ = z` for all `τ` (`HasEmptyRow`), and
(c) `log ‖σ ‖φ‖²‖ = c + r + ∑ τ, jetSize (p.negWeight τ - z)`. Here
`jetSize j = log j! + j log (M / Ω)` with `M = D.M` and `Ω = P.bigOmega D.towerExp`, and `f` is the
number of infinite places `τ`. -/
lemma New.Data.CriticalPair.exists_log_norm_map_norm_sq_trivialLift_eq_add_sum_jetSize
    {P : Parameters} (D : Data P) (n : Type)
    [Fintype n] [DecidableEq n] (σ : Gal(ℂ/K P)) :
    ∃ c : ℝ, ∀ (p : D.CriticalPair) (H : p.HasLiftRank n), ∃ r : ℝ,
      -(4 * D.f) ≤ r ∧
      (p.HasEmptyRow n → r ≤ 4 * D.f) ∧
      log ‖σ (‖trivialLift H TameChar.one‖ ^ 2)‖ = c + r + ∑ τ : D.Φ,
        D.jetSize (p.negWeight τ - p.z) := by
  -- `‖φ‖²` is an explicit multiple of `⟪A, A⟫`, whose conjugate is a multiple of the squared norm
  -- of the lift for conjugate data `Y`.
  obtain ⟨a, ha_pos : 0 < a, h_conj⟩ := exists_norm_map_inner_trivialLift_eq_mul D n σ
  obtain ⟨c, h_size⟩ := D.exists_log_norm_inner_trivialLift_eq n (D.levelPlaces .one) ⟨nofun⟩
  let vacuumFactor : ℝ := ‖σ (‖P.vacuumScale D.towerExp ^ card n‖ ^ 2 : ℝ)‖
  have h_vacuumFactor_pos : 0 < vacuumFactor := by simp [vacuumFactor]
  refine ⟨log vacuumFactor + log a + c, fun p H ↦ ?_⟩
  obtain ⟨Y, h_places, h_deg : ∀ τ : D.Φ,
    Y.rowLength (placePerm D.towerExp σ τ) = p.negWeight τ - p.z,
    h_inner⟩ :=
    h_conj p H
  let N : ℝ := ‖inner ℂ Y.trivialLift Y.trivialLift‖
  obtain ⟨h_ne, r, hr_ge, hr_le : (∀ τ : D.Φ, Y.rowLength τ = 0) → r ≤ 4 * D.f,
    h_log : log N = c + r + ∑ τ : D.Φ, log (Y.rowLength τ).factorial⟩ :=
    h_size Y p.z h_places H.1 H.2
  have hN_pos : 0 < N := norm_pos_iff.2 h_ne
  refine ⟨r, hr_ge, fun ⟨h_flat, _⟩ ↦ hr_le fun τ ↦ ?_, ?_⟩
  · obtain ⟨τ, rfl⟩ := (placePerm D.towerExp σ).surjective τ
    rw [h_deg, h_flat, Nat.sub_self]
  have h_norm : ‖σ (‖trivialLift H .one‖ ^ 2)‖ =
      vacuumFactor * D.M ^ p.rowLengthSum *
        ((√(P.bigOmega D.towerExp))⁻¹ ^ (2 * p.rowLengthSum) * a * N) := by
    rw [norm_trivialLift_sq_eq_mul_inner, map_mul, norm_mul, h_inner]
    simp [vacuumFactor, N]
  have h_fact : ∑ τ : D.Φ, log (Y.rowLength τ).factorial = ∑ τ : D.Φ,
    log (p.negWeight τ - p.z).factorial := by
    simp only [← h_deg, Equiv.sum_comp (placePerm D.towerExp σ) fun τ ↦
      log (Y.rowLength τ).factorial]
  have hΩ_pos : 0 < P.bigOmega D.towerExp := bigOmega_pos
  have hM_pos : 0 < D.M := NeZero.pos _
  have h_jet : ∑ τ : D.Φ, D.jetSize (p.negWeight τ - p.z) = ∑ τ : D.Φ,
    log (p.negWeight τ - p.z).factorial +
      p.rowLengthSum * (log D.M - log (P.bigOmega D.towerExp)) := by
    simp [jetSize, Finset.sum_add_distrib, Finset.sum_mul, log_div, hΩ_pos.ne', hM_pos.ne']
  rw [h_norm, h_jet]
  simp (disch := positivity) only [log_mul, log_pow, log_inv, log_sqrt, h_log, h_fact]
  push_cast
  ring

end AlgebraicPartConjugates

/-!
## Critical pairs with an empty row and the height of the squared norm of the lift

* `New.Data.exists_hasEmptyRow`: critical pairs with an empty row over a given character of weight
  zero.
* `New.Data.heightLe_norm_trivialLift_sq`: the height of the untwisted value of a main pair.
* `New.Data.CriticalPair.IsMainPair.negWeight_sub_z_mem_Icc`: the range of the jet degrees of a main
  pair.
-/

namespace New.Data

variable {P : Parameters} {D : Data P}

open Fintype Real WeilData CriticalPair AutChar

/-- Let `card n` be even and between `4` and the number `D.t = 5 * D.r` of the data `D`. Let
`χ = (μ, ψ)` be a character `μ` of `U(1)(𝔸)` of weight zero with its tame part `ψ`, which is trivial
off the chosen places. Then some critical pair `p = (ν, z)` has an empty row on `n`, has tame part
`ψ`, and has `ν υ ^ (card n / 2) = μ`, where `υ` is the splitting character on the norm-one ideles
(`New.rankTwist`). -/
lemma exists_hasEmptyRow (n : Type) [Fintype n] (h_four_le : 4 ≤ card n) (h_le_t : card n ≤ D.t)
    (h_even : 2 ∣ card n) (χ : tameChars D.finite_isChosen.toFinset) :
    ∃ p : D.CriticalPair, (rankTwist p.character n = χ.val.1 ∧ p.tamePart = χ.val.2) ∧ p.HasEmptyRow
      n := by
  -- Take `p.character = ν υ ^ (-z)` and the constant `negWeight` `z`, with `z = card n / 2`.
  obtain ⟨⟨ν, ψ⟩, h_weight : ν.HasWeight 0 ψ,
    h_tame : ∀ w ∉ D.finite_isChosen.toFinset, ψ w = 1⟩ := χ
  obtain ⟨z, hz : card n = 2 * z⟩ := h_even
  have h_weight_twist : (ν * (upsilonU1 ^ z)⁻¹).HasWeight (fun _ ↦ -(z : ℤ)) ψ := by
    have h_mul : (ν * (upsilonU1 ^ z)⁻¹).HasWeight (0 + -fun _ ↦ (z : ℤ)) (ψ * 1⁻¹) :=
      h_weight.mul (hasWeight_upsilonU1_pow z).inv
    rwa [zero_add, inv_one, mul_one] at h_mul
  have hz_mem : z ∈ Set.Icc 1 D.t := ⟨by lia, by lia⟩
  have hz_le : (z : ℝ) ≤ 4 * D.b :=
    calc (z : ℝ) ≤ D.t := mod_cast hz_mem.2
      _ ≤ 4 * D.b := D.le_of_hasLogBound
  let p : D.CriticalPair :=
    { character := ν * (upsilonU1 ^ z)⁻¹
      negWeight _ := z
      tamePart := ψ
      z := z
      hasWeight := h_weight_twist
      tamePart_eq_one w hw := h_tame w (by simpa using hw)
      z_mem := hz_mem
      le_negWeight _ := le_rfl
      negWeight_le _ := hz_le }
  have h_twist : rankTwist p.character n = ν := by simp [p, rankTwist, hz]
  have h_rank : p.HasLiftRank n := ⟨hz, show 2 ≤ z by lia⟩
  exact ⟨p, ⟨h_twist, rfl⟩, fun _ ↦ rfl, h_rank⟩

lemma CriticalPair.HasEmptyRow.hasLiftRank {p : D.CriticalPair} {n : Type} [Fintype n]
    (h_flat : p.HasEmptyRow n) :
    p.HasLiftRank n :=
  h_flat.2

/-- Let `p = (ν, z)` be a main pair for `j` (`IsMainPair`: `m < z ≤ r`, tame part `D.chiMLocal ^ j`,
and `w_j + r - t ≤ c ≤ w_j` at every infinite place, for the weight `-c` of `ν` and
`w_j = D.liftWeight j`). At every infinite place `τ`, the row length `c τ - z` lies between the
weight `κ(τ) = D.weight τ` and `κ(τ) + x ^ 42`, where `x = D.x` is the length of the prime sum. -/
lemma CriticalPair.IsMainPair.negWeight_sub_z_mem_Icc {p : D.CriticalPair} {j : ℕ}
    (hp : p.IsMainPair j) (τ : D.Φ) :
    ((p.negWeight τ - p.z : ℕ) : ℝ) ∈ Set.Icc (D.weight τ : ℝ) (D.weight τ + D.x ^ 42) := by
  -- As `z ≤ r`, the degree lies in `[w_j - t, w_j]`; and `κ + t ≤ w_j ≤ κ + x ^ 42`.
  have hz_le : p.z ≤ D.r := hp.z_mem.2
  have hc_le : p.negWeight τ ≤ D.liftWeight j τ := hp.negWeight_le τ
  have hc_ge : D.liftWeight j τ + D.r ≤ p.negWeight τ + D.t := hp.le_negWeight τ
  have h_gap : D.weight τ + D.t ≤ D.liftWeight j τ := by
    rw [D.liftWeight_eq j τ]
    linarith [D.k_add_t_add_one_le_halfGap, Nat.zero_le (j * D.gap), Nat.zero_le D.k]
  exact ⟨Nat.cast_le.2 (by omega),
    (Nat.cast_le.2 (by omega : p.negWeight τ - p.z ≤ D.liftWeight j τ)).trans
      (D.liftWeight_le_weight_add (by linarith [hp.j_mem.2]) τ)⟩

/-- Let `p = (ν, z)` be a main pair for `j`, with `m = D.m` the number of lifts, `r = D.r` the rank
of the target and `t = 5 r`. Take the squared norm `‖φ‖²` of the untwisted lift of `ν` to `U(2 z)`
as a constant family, indexed by the primes `l` with an isomorphism `ℂ ≃ ℚ̄_l`. Then it has height
(`New.HeightLe`) at most `denominatorBudget - ∑ τ, jetSize (κ τ)`. Here
`denominatorBudget = f a log³ b / (m k)`, with `f` the number of infinite places `τ`, `b = D.b` the
weight scale, `a = x b` for the length `x` of the prime sum and `k = r + 1 - m`; further
`κ τ = D.weight τ`, and `jetSize i = log i! + i log (M / Ω)` is the size of a derivative of order
`i`, with `M = D.M` and `Ω = P.bigOmega D.towerExp`. -/
lemma heightLe_norm_trivialLift_sq {j : ℕ} {p : D.CriticalPair} (hp : p.IsMainPair j) :
    HeightLe (D.denominatorBudget - ∑ τ : D.Φ, D.jetSize (D.weight τ)) fun _ : PrimePadicIso ↦
      ‖trivialLift hp.hasLiftRank TameChar.one‖ ^ 2 := by
  -- Compare with the critical pair with an empty row `q = (υ ^ (-z), z)` of the same rank. The
  -- multiplier is `q.integralAlgebraicPart / ‖φ‖²`: its product with `‖φ‖²` is
  -- `q.integralAlgebraicPart`, integral at every prime, and in its conjugates the unknown constant
  -- of `exists_log_norm_map_norm_sq_trivialLift_eq_add_sum_jetSize` cancels.
  obtain ⟨h_card : card (RankOneIndex p.z) = 2 * p.z, hz_two : 2 ≤ p.z⟩ := hp.hasLiftRank
  have h_card_le : card (RankOneIndex p.z) ≤ D.t := by
    have hz_le : p.z ≤ D.r := hp.z_mem.2
    rw [h_card, Data.t]
    lia
  obtain ⟨q, -, h_flat : q.HasEmptyRow (RankOneIndex p.z)⟩ :=
    D.exists_hasEmptyRow (RankOneIndex p.z) (by lia) h_card_le ⟨p.z, h_card⟩ 1
  let normSqP : ℂ := ‖trivialLift hp.hasLiftRank .one‖ ^ 2
  let normSqQ : ℂ := ‖trivialLift h_flat.2 .one‖ ^ 2
  let mult : ℂ := q.integralAlgebraicPart h_flat.2 .one / normSqP
  have h_conj (σ : Gal(ℂ/P.K)) : log ‖σ mult‖ ≤ D.denominatorBudget - ∑ τ,
    D.jetSize (D.weight τ) := by
    obtain ⟨c, hc⟩ := exists_log_norm_map_norm_sq_trivialLift_eq_add_sum_jetSize D
      (RankOneIndex p.z) σ
    obtain ⟨r₀, -, hr₀_le : q.HasEmptyRow (RankOneIndex p.z) → r₀ ≤ 4 * D.f,
      h_log_q : log ‖σ normSqQ‖ = c + r₀ + ∑ τ, D.jetSize (q.negWeight τ - q.z)⟩ := hc q h_flat.2
    obtain ⟨r, hr_ge : -(4 * D.f) ≤ r, -,
      h_log_p : log ‖σ normSqP‖ = c + r + ∑ τ, D.jetSize (p.negWeight τ - p.z)⟩ :=
        hc p hp.hasLiftRank
    have h_size_q : ∑ τ, D.jetSize (q.negWeight τ - q.z) = 0 := by simp [h_flat, jetSize]
    have h_weight (τ : D.Φ) : D.weight τ ≤ p.negWeight τ - p.z :=
      mod_cast (hp.negWeight_sub_z_mem_Icc τ).1
    have h_size_p : ∑ τ, D.jetSize (D.weight τ) ≤ ∑ τ, D.jetSize (p.negWeight τ - p.z) :=
      Finset.sum_le_sum fun τ _ ↦ by simpa using D.jetSize_le_add (e := 0) (h_weight τ)
    have h_log_mult : log ‖σ mult‖ = log (D.chosenGroupOrder * q.denomBound ^ 2) +
        log ‖σ normSqQ‖ - log ‖σ normSqP‖ := by
      simp [mult, normSqP, normSqQ, CriticalPair.integralAlgebraicPart,
        toAutChar_one_and_toTwist_one_and_Q_one,
        denomBound, log_mul, log_div,
        NeZero.ne]
    have h_log_int : log (D.chosenGroupOrder * q.denomBound ^ 2) ≤ D.x ^ 33 :=
      (log_le_iff_le_exp (by simp [h_flat, denomBound, NeZero.pos])).2
        (chosenGroupOrder_mul_denomBound_sq_le h_flat)
    have h_budget : D.x ^ 33 + 8 * D.f ≤ D.denominatorBudget := D.le_of_hasLogBound
    linarith [hr₀_le h_flat]
  -- The multiplier takes the whole bound at infinity, and nothing is lost at the primes.
  refine .of_mul_le (H := mult) (α := D.denominatorBudget - ∑ τ, D.jetSize (D.weight τ)) (e := 0)
    (by simp [mult, normSqP]) (fun σ ↦ ?_) (fun ι ↦ ?_) (by simp)
  · -- `σ` has the same moduli as some `σ'` fixing `K`
    obtain ⟨σ', hσ'⟩ := P.exists_algEquiv_norm_eq σ
    exact (hσ' mult).trans_le (le_exp_of_log_le (h_conj σ'))
  · -- `integralAlgebraicPart` at the trivial character is integral at every prime
    have h_prod : mult * normSqP = q.integralAlgebraicPart h_flat.2 .one :=
      div_mul_cancel₀ _ (by simp [normSqP])
    change ‖ι.2 (mult * normSqP)‖ ≤ exp 0
    simp [h_prod, norm_integralAlgebraicPart_one_le_one]

end New.Data

end
