import New.Congruences.FirstOrder.DenominatorBound
import New.Congruences.GaloisRepresentations.RowsFromEigensystems
import New.Congruences.Selmer.TwistingTheorem
import New.Determinant.Chain.NormOfChain
import New.OneLift.HeckeValues.CentralAction

/-!
# All data have regular families of m-fold twists

This file states the conclusion of the Selmer group argument.

* `New.exists_isRegularFamily`: for all data `D` there is a family of `m`-fold twists, one for each
  prime `ℓ` and isomorphism `ι : ℂ ≃ ℚ̄_ℓ`, that is regular (`New.Data.IsRegularFamily`): for the
  first `m` powers of its members the inverse ratios of `L`-values have height at most `D.x₁`, and
  the logarithms of the denominators of the projections to lifts sum over the primes to at most
  `D.denominatorBudget`.
* `New.Selmer.exists_mFoldTwist_hasDenominatorsLe`: the twist for one prime and one isomorphism.
* `New.Selmer.range_goodLift_le_span_hasLiftHeckePolynomial`: the lifts are spanned by forms that
  lift one of finitely many eigensystems, which do not depend on the twist.

Notions from other files:
* `New.Data.MFoldTwist`: a twist ϑ whose tame part ψ has ψ_wⁿ non-trivial for all places w in its
  set Q and 1 ≤ n ≤ m.
* `New.Data.IsNegligible`: nonnegative reals `e l` with `∑ e l log l ≤ x ^ C` over every finite set
  of primes, where `x = D.x` is the length of the prime sum, the smallest scale of the data.
* `New.Selmer.IsMainSummand`: an `ℓ`-adic Galois representation satisfies the local and global
  conditions `IsMainSummandLike` and, up to a twist and a string of characters, gives the traces of
  the representations attached to the lifts of a Hecke eigensystem, for all twists of a descent
  pair.
* `New.Selmer.DenominatorLe`: an operator `Λ` on a space `Z` of forms, with determinant of norm at
  least `exp (-(dim Z · r · β))` at `ι`, clears the denominators of the orthogonal projection to
  `Z`. Here `r` is the rank of the source of the lift.

## Relation to the literature

For each prime ℓ and each identification of the complex numbers with the algebraic closure of the
ℓ-adic numbers, there is a twist whose first m powers have few congruences. For these twists, the
denominators of projections to theta lifts and the divisibility of ratios of Hecke values sum over
all ℓ to a total that the heights afford. It is known that denominators of projections to lifts give
Selmer classes and that twisting lowers Selmer ranks. Related work: Prasanna, Integrality of a ratio
of Petersson norms, 2006 (after Ribet, 1976; Wiles); Klosin, Congruences among modular forms on
U(2,2) and the Bloch–Kato conjecture, 2009; Mazur–Rubin, Ranks of twists of elliptic curves, 2010.
-/

open New Selmer Submodule Data GaloisRep Polynomial Multiset Finset Real

/-- Let the projection to the space `Z` of lifts have denominator at most `exp β` per dimension of
`Z` and per unit of the rank `r` of the source (`DenominatorLe`). If `β ≤ β'`, then some operator
with determinant of norm at least `exp (-(dim Z · r · β'))` clears this denominator
(`New.Data.ClearsProjection`). -/
lemma New.Selmer.DenominatorLe.clearsProjection {P : Parameters} {D : Data P} {ℓ : ℕ}
    [Fact ℓ.Prime] {ι : ℂ ≃+* PadicAlgCl ℓ} {ϑ : D.Twist} {j : ℕ} {β β' : ℝ}
    (h_denom : DenominatorLe ι (D.descentPair ϑ j) D.e₀ (D.goodLift ϑ j).range β) (hββ' : β ≤ β') :
    D.ClearsProjection ι ϑ j β' := by
  obtain ⟨Λ, h_det, h_int⟩ := h_denom
  refine ⟨Λ, ?_, fun y hy h_test ↦ (h_int y hy h_test).left⟩
  calc exp (-(Module.finrank ℂ (D.goodLift ϑ j).range * (D.r * β')))
      ≤ exp (-(Module.finrank ℂ (D.goodLift ϑ j).range * (Fintype.card D.RowIndex * β))) := by
        rw [D.card_rowIndex]
        gcongr
    _ ≤ ‖ι Λ.det‖ := h_det

/-- Summed over a finite set `T` of primes `l` with weights `log l`, the `l`-adic valuations of a
natural number `a` are at most `log b` for every natural number `b ≥ a`. -/
lemma New.Selmer.sum_padicValNat_mul_log_le (T : Finset ℕ) (hT : ∀ l ∈ T, l.Prime) {a b : ℕ}
    (hab : a ≤ b) : ∑ l ∈ T, (padicValNat l a : ℝ) * log l ≤ log b :=
  calc ∑ l ∈ T, (padicValNat l a : ℝ) * log l = ∑ l ∈ T, a.factorization l * log l :=
      sum_congr rfl fun l hl ↦ by rw [a.factorization_def (hT l hl)]
    _ ≤ ∑ l ∈ T ∪ a.factorization.support, a.factorization l * log l := by
      grw [← T.subset_union_left]
    _ = log a := by
      rw [log_nat_eq_sum_factorization,
        Finsupp.sum_of_support_subset _ subset_union_right _ (by simp)]
    _ ≤ log b := by
      rw [← log_of_nat_eq_posLog, ← log_of_nat_eq_posLog]
      exact posLog_le_posLog (by linarith [a.cast_nonneg (α := ℝ)]) (Nat.cast_le.2 hab)

lemma New.Selmer.sum_half_pow_mul_log_le (T : Finset ℕ) :
    ∑ l ∈ T, (1 / 2 : ℝ) ^ l * log l ≤ 2 :=
  calc ∑ l ∈ T, (1 / 2 : ℝ) ^ l * log l ≤ ∑ l ∈ T, l * (1 / 2 : ℝ) ^ l :=
      sum_le_sum fun l _ ↦ by grw [log_le_self l.cast_nonneg, mul_comm]
    _ ≤ 1 / 2 / (1 - 1 / 2) ^ 2 :=
      sum_le_hasSum T (by simp) (hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num))
    _ = 2 := by norm_num

/-- Let `natB` be the weight `b` of the data `D` as a natural number, and `halfGap = r ^ 8`. The
product of the natural numbers `k` with `natB - 30 halfGap³ < k ≤ natB + 30 halfGap³` (truncated
subtraction), which enters the crystalline loss `crystallineLoss`, is at most
`(natB + 30 halfGap³) ^ (60 halfGap³)`. -/
lemma New.Selmer.prod_Ioc_natB_le_pow {P : Parameters} (D : Data P) :
    ∏ k ∈ Finset.Ioc (D.natB - 30 * D.halfGap ^ 3) (D.natB + 30 * D.halfGap ^ 3), k ≤
      (D.natB + 30 * D.halfGap ^ 3) ^ (60 * D.halfGap ^ 3) := by
  have h_pos : 0 < D.halfGap := Nat.zero_lt_of_lt D.k_add_t_add_one_le_halfGap
  set hCube : ℕ := D.halfGap ^ 3
  have h_card : #(Finset.Ioc (D.natB - 30 * hCube) (D.natB + 30 * hCube)) ≤ 60 * hCube := by
    rw [Nat.card_Ioc]
    omega
  calc _ ≤ (D.natB + 30 * hCube) ^ #(Finset.Ioc (D.natB - 30 * hCube) (D.natB + 30 * hCube)) :=
      prod_le_pow_card _ _ _ fun k hk ↦ (Finset.mem_Ioc.1 hk).2
    _ ≤ (D.natB + 30 * hCube) ^ (60 * hCube) := Nat.pow_le_pow_right (by positivity) h_card

/-- Let `m` be the number of lifts, `r` the rank of the target, `k = r + 1 - m` the rank of the
source, `b = D.natB` the weight as a natural number, `h = D.halfGap = r ^ 8`, and `M = D.M` the
product of the two level primes. The local loss `defectBound D l` is
`10⁶ (m / k) (b v_l(M) + v_l((2 b)! Π ^ h³))`, where `v_l` is the `l`-adic valuation and `Π` is the
product of the positive integers in `(b - 30 h³, b + 30 h³]`. Summed over any finite set `T` of
primes `l` with weights `log l`, these losses are at most
`10⁶ (m / k) (b log M + log ((2 b)! (b + 30 h³) ^ (60 h⁶)))`. -/
lemma New.Selmer.sum_defectBound_mul_log_le {P : Parameters} (D : Data P) (T : Finset ℕ)
    (hT : ∀ l ∈ T, l.Prime) :
    ∑ l ∈ T, (defectBound D l : ℝ) * log l ≤
      10 ^ 6 * ((D.m : ℝ) / D.k) * (D.natB * log D.M +
        log ((2 * D.natB).factorial *
          ((D.natB + 30 * D.halfGap ^ 3) ^ (60 * D.halfGap ^ 3)) ^ D.halfGap ^ 3 : ℕ)) := by
  -- `defectBound` is a combination of two valuations; bound each weighted sum by a logarithm
  set hCube : ℕ := D.halfGap ^ 3
  let N : ℕ := (2 * D.natB).factorial *
    (∏ k ∈ Finset.Ioc (D.natB - 30 * hCube) (D.natB + 30 * hCube), k) ^ hCube
  have hN : N ≤ (2 * D.natB).factorial * ((D.natB + 30 * hCube) ^ (60 * hCube)) ^ hCube :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (prod_Ioc_natB_le_pow D) _)
  calc ∑ l ∈ T, (defectBound D l : ℝ) * log l
      = 10 ^ 6 * ((D.m : ℝ) / D.k) * (D.natB * ∑ l ∈ T, (padicValNat l D.M : ℝ) * log l +
          ∑ l ∈ T, (padicValNat l N : ℝ) * log l) := by
        rw [mul_sum, ← sum_add_distrib, mul_sum]
        refine sum_congr rfl fun l _ ↦ ?_
        push_cast [defectBound, crystallineLoss, N, hCube]
        ring
    _ ≤ _ := by
        gcongr
        exacts [sum_padicValNat_mul_log_le T hT le_rfl, sum_padicValNat_mul_log_le T hT hN]

/-- **Bound for the local loss.** The numbers `localDefectBound D l = 4 f · defectBound D l` have
`∑ localDefectBound D l · log l ≤ 4 · 10⁶ e¹⁸⁰ f (m / k) b log b` over every finite set `T` of
primes. Here `f` is the number of infinite places of `D.E`, `m` the number of lifts, `k = r + 1 - m`
the rank of the source, `b = exp D.logB` the weight, and `defectBound D l` is `10⁶ (m / k)` times a
sum of `l`-adic valuations of integers attached to `D`. -/
lemma New.Selmer.sum_localDefectBound_mul_log_le {P : Parameters} (D : Data P) (T : Finset ℕ)
    (hT : ∀ l ∈ T, l.Prime) :
    ∑ l ∈ T, (localDefectBound D l : ℝ) * log l ≤
      4 * 10 ^ 6 * exp 180 * (D.f * ((D.m : ℝ) / D.k) * D.b * D.logB) := by
  have h_bracket : D.natB * log D.M + log ((2 * D.natB).factorial *
      ((D.natB + 30 * D.halfGap ^ 3) ^ (60 * D.halfGap ^ 3)) ^ D.halfGap ^ 3 : ℕ) ≤
        exp 180 * D.b * D.logB := by
    push_cast
    exact D.le_of_hasLogBound
  calc ∑ l ∈ T, (localDefectBound D l : ℝ) * log l = 4 * D.f * ∑ l ∈ T,
         (defectBound D l : ℝ) * log l := by
        simp [localDefectBound, mul_sum, mul_assoc]
    _ ≤ 4 * D.f * (10 ^ 6 * ((D.m : ℝ) / D.k) * (exp 180 * D.b * D.logB)) := by
        grw [sum_defectBound_mul_log_le D T hT, h_bracket]
    _ = _ := by ring

/-- **The odd classes are few.** The integer `oddClassBound D` is at most `2 ^ (4 (N + t + 3) ^ 27)`
times the class number of `D.E`, for the cyclotomic conductor `N`. Its `l`-adic valuation bounds the
lengths of the groups of odd classes (`shaOdd`), Galois cohomology classes of `D.E` with
coefficients in Tate twists of `O/l^ν`. These valuations are negligible with the exponent `2000`:
with weights `log l` they sum to at most `D.x ^ 2000` over every finite set of primes. -/
lemma New.Selmer.isNegligible_padicValNat_oddClassBound {P : Parameters} (D : Data P) :
    D.IsNegligible 2000 fun l : ℕ ↦ padicValNat l (oddClassBound D) := by
  refine ⟨fun l ↦ Nat.cast_nonneg _, fun T hT ↦ ?_⟩
  calc ∑ l ∈ T, (padicValNat l (oddClassBound D) : ℝ) * log l
      ≤ log (2 ^ (4 * (D.cyclotomicConductor + D.t + 3) ^ 27) * NumberField.classNumber D.E : ℕ) :=
        sum_padicValNat_mul_log_le T hT (oddClassBound_le D)
    _ = 4 * (D.cyclotomicConductor + D.t + 3) ^ 27 * log 2 + log (NumberField.classNumber D.E) := by
        push_cast
        rw [log_mul (by positivity) (mod_cast NumberField.classNumber_ne_zero D.E), log_pow]
        push_cast
        ring
    _ ≤ 4 * (D.cyclotomicConductor + D.t + 3) ^ 27 * log 2 + D.x ^ 30 := by
      grw [D.log_classNumber_le]
    _ ≤ D.x ^ 2000 := D.le_of_hasLogBound

/-- The numbers `twistError l D = (4 f + 3) r v_l(D.chosenGroupOrder) + 2⁻ˡ` are negligible with
the exponent `999`: with weights `log l` they sum to at most `D.x ^ 999` over every finite set of
primes. -/
lemma New.Selmer.isNegligible_twistError {P : Parameters} (D : Data P) :
    D.IsNegligible 999 fun l : ℕ ↦ twistError l D := by
  refine ⟨fun l ↦ NNReal.coe_nonneg _, fun T hT ↦ ?_⟩
  calc ∑ l ∈ T, (twistError l D : ℝ) * log l
      = (4 * D.f + 3) * D.r * ∑ l ∈ T, (padicValNat l D.chosenGroupOrder : ℝ) * log l +
          ∑ l ∈ T, (1 / 2 : ℝ) ^ l * log l := by
        simp [twistError, add_mul, sum_add_distrib, mul_sum, mul_assoc]
    _ ≤ (4 * D.f + 3) * D.r * log D.chosenGroupOrder + 2 := by
        grw [sum_padicValNat_mul_log_le T hT le_rfl, sum_half_pow_mul_log_le T]
    _ ≤ D.x ^ 999 := D.le_of_hasLogBound

/-- The error term `denominatorError D l` of the bound for the denominators of projections to lifts
is finite: it is an explicit combination of the `l`-adic valuations of `oddClassBound D`, the bound
for odd Galois cohomology classes, and `D.chosenGroupOrder`, the order of a product of general
linear groups over residue fields. These terms are negligible with the exponent `4000`: with weights
`log l` they sum to at most `D.x ^ 4000` over every finite set of primes. -/
lemma New.Selmer.isNegligible_denominatorError {P : Parameters} (D : Data P) :
    D.IsNegligible 4000 fun l : ℕ ↦ (denominatorError D l).toReal := by
  refine ⟨fun l ↦ ENNReal.toReal_nonneg, fun T hT ↦ ?_⟩
  -- every term is a multiple of the valuation of `oddClassBound D` or of `D.chosenGroupOrder`
  let c : ℝ := 8 * D.f * D.t + 2 + ((4 * D.t + 1) * D.halfGap ^ 22 + D.halfGap)
  calc ∑ l ∈ T, (denominatorError D l).toReal * log l
      = D.t * ∑ l ∈ T, (padicValNat l (oddClassBound D) : ℝ) * log l +
          c * ∑ l ∈ T, (padicValNat l D.chosenGroupOrder : ℝ) * log l := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun l _ ↦ ?_
        rw [denominatorError_eq_natCast, ENNReal.toReal_natCast]
        push_cast [c]
        ring
    _ ≤ D.t * D.x ^ 2000 + c * log D.chosenGroupOrder := by
        grw [(isNegligible_padicValNat_oddClassBound D).sum_mul_log_le T hT,
          sum_padicValNat_mul_log_le T hT le_rfl]
    _ ≤ D.x ^ 4000 := D.le_of_hasLogBound

/-- The `l`-adic valuations of the class number of `U(1)` at the level `D.chosenLevel` (the number
of double cosets `StdClasses`) are negligible with the exponent `30`: with weights `log l` they sum
to at most `D.x ^ 30` over every finite set of primes. -/
lemma New.Selmer.isNegligible_padicValNat_card_stdClasses {P : Parameters} (D : Data P) :
    D.IsNegligible 30 fun l : ℕ ↦
      padicValNat l (Nat.card (StdClasses (n := Unit) D.chosenLevel)) := by
  refine ⟨fun l ↦ Nat.cast_nonneg _, fun T hT ↦ ?_⟩
  have h_classes : (Nat.card (StdClasses (n := Unit) D.chosenLevel) : ℝ) ≤ exp (D.x ^ 30) :=
    D.card_stdClasses_le_exp (D.principalLevel_le_chosenLevel (dvd_mul_right ..))
      (Fintype.card_unit.trans_le D.nat_le_of_hasLogBound)
  calc ∑ l ∈ T, (padicValNat l (Nat.card (StdClasses (n := Unit) D.chosenLevel)) : ℝ) * log l
      ≤ log (Nat.card (StdClasses (n := Unit) D.chosenLevel)) :=
        sum_padicValNat_mul_log_le T hT le_rfl
    _ ≤ D.x ^ 30 := (log_le_iff_le_exp (Nat.cast_pos.2 Nat.card_pos)).2 h_classes

/-- The number `clearingBound D l` is the bound for the exponent of `l` in the denominator of a
projection to lifts, per dimension and per unit of rank of the source: a sum of the local loss
`localDefectBound D l`, multiples of the twist and error terms, and the valuation of
`D.chosenGroupOrder`. The number of `StdClasses` at the level `D.chosenLevel` is the class number of
`U(1)` there. Summed over a finite set `T` of primes `l` with weights `log l`, the clearing bounds
and the `l`-adic valuations of this class number are at most
`D.denominatorBudget = D.errorUnit / (m k)`, for `m` the number of lifts and `k = r + 1 - m`. -/
lemma New.Selmer.sum_clearingBound_add_padicValNat_le {P : Parameters} (D : Data P) (T : Finset ℕ)
    (hT : ∀ l ∈ T, l.Prime) :
    ∑ l ∈ T, (clearingBound D l * log l +
      padicValNat l (Nat.card (StdClasses (n := Unit) D.chosenLevel)) * log l) ≤
        D.denominatorBudget := by
  -- the terms are the local loss and negligible numbers, and all are small against
  -- `denominatorBudget`
  calc _ = ∑ l ∈ T, (localDefectBound D l : ℝ) * log l +
        (1 + 2 * D.t) * ∑ l ∈ T, (twistError l D : ℝ) * log l +
        ∑ l ∈ T, (denominatorError D l).toReal * log l +
        ∑ l ∈ T, (padicValNat l D.chosenGroupOrder : ℝ) * log l +
        ∑ l ∈ T, (padicValNat l (Nat.card (StdClasses (n := Unit) D.chosenLevel)) : ℝ) * log l := by
        simp only [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun l _ ↦ ?_
        push_cast [clearingBound, ENNReal.coe_toNNReal_eq_toReal]
        ring
    _ ≤ 4 * 10 ^ 6 * exp 180 * (D.f * ((D.m : ℝ) / D.k) * D.b * D.logB) +
        (1 + 2 * D.t) * D.x ^ 999 + D.x ^ 4000 + log D.chosenGroupOrder + D.x ^ 30 := by
        grw [sum_localDefectBound_mul_log_le D T hT,
          (isNegligible_twistError D).sum_mul_log_le T hT,
          (isNegligible_denominatorError D).sum_mul_log_le T hT,
          sum_padicValNat_mul_log_le T hT (a := D.chosenGroupOrder) le_rfl,
          (isNegligible_padicValNat_card_stdClasses D).sum_mul_log_le T hT]
    _ ≤ D.denominatorBudget := D.le_of_hasLogBound

/-- A descent pair `O` consists of the data of a theta lift from a hermitian space `W` to one of
rank `#n`: a finite set of level places, a character of `U(1)` with its weight and tame part, and
the weight of the forms. Here `W` has rank one (index type `Unit`), and `O.ChosenIndex` indexes the
chosen places of `O`. The label of each chosen place, a polynomial over its residue field, is taken
to be `X - 1`. Then the trivial `ℓ`-adic representation of rank one satisfies `IsRepOfType`: it is
conjugate self-dual with the parameter `1`, meets the local conditions of `IsConjSelfDualOfLevel` at
all finite places (the level is `∅`) with the single jump `0` at each embedding of `D.E` in `ℂ`, and
inertia at each chosen place acts through the root of the label. -/
lemma New.Selmer.isRepOfType_one {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] {n : Type} [Fintype n] [DecidableEq n] (O : DescentPair D.E Unit n) :
    IsRepOfType O (Fintype.card Unit) (fun _ : D.E →+* ℂ ↦ {0})
      (fun _ : O.ChosenIndex ↦ Polynomial.X - 1) ∅ (1 : GalRep ℓ D.E Unit) := by
  -- the local clauses are those of the trivial character
  have h_loc (A : ClosurePlace) : IsFiniteTypeAt (1 : GalRep ℓ D.E Unit) A ∧
      HasJumpsAt (1 : GalRep ℓ D.E Unit) A (fun _ : D.E →+* ℂ ↦ {0}) ∧
      ∀ s : AbsGal D, PolyKillsAt (1 : GalRep ℓ D.E Unit) A s (Polynomial.X - 1) := by
    simpa using
      localConditions_char_of_finite_image_inertia (E := D.E) (A := A) (μ := 1) (m := Unit)
        continuous_one (by simp)
  choose h_finite h_jumps h_kills using h_loc
  refine
    { continuous := continuous_one
      nondeg := by simp +contextual [IsTraceNondeg, Matrix.trace, ← Matrix.ext_iff]
      trace_conj := by simp
      local_conditions v _ A _ :=
        ⟨h_finite A, h_jumps A, fun _ ↦ isGoodAt_iff.2 ⟨h_finite A, fun s _ ↦ h_kills A s⟩⟩
      labelled i A s a _ := ?_ }
  -- the only root of the label `X - 1` is `1`
  rw [← C_1, aroots_X_sub_C]
  simpa using h_kills A s

/-- A critical pair `(ν, z)` is a main pair for an index `1 ≤ j ≤ m` if `m < z ≤ r`, the tame part
of `ν` is `D.chiMLocal ^ j`, and the weight `-c` of `ν` has `w + r - t ≤ c ≤ w` at each infinite
place, for `w = D.liftWeight j`. Here `m` is the number of lifts, `r = D.r`, `t = D.t`, and
`D.chiMLocal` is the fixed family of residue characters that is trivial off the chosen places. The
data `lValueData` describe the theta lift of `ν`, untwisted, from `U(1)` to `U(2 z)`. Then there is
an `ℓ`-adic representation `T` of rank one that is a main summand (`IsMainSummand`) for this lift
and the constant system `1` of Hecke eigenvalues: `T` satisfies `IsMainSummandLike`, and for every
twist of the lift the Galois representations attached to lifted eigenforms have, up to
normalisation, the trace of the twisted `T` plus a string of characters. -/
lemma New.Selmer.exists_isMainSummand_mainPair {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    {ι : PadicIso ℓ} (p : {p : D.CriticalPair × D.LiftIndex // p.1.IsMainPair p.2}) :
    ∃ T : GalRep ℓ D.E Unit,
      IsMainSummand (p.val.1.lValueData p.prop.hasLiftRank (1 : D.Twist)).descentPair 1 T := by
  obtain ⟨⟨q, j⟩, hq : q.IsMainPair j⟩ := p
  -- the main summand comes from the trivial representation, whose only jump is `0`
  refine exists_isMainSummand_of_isRepOfType ι (isLiftSetting_mainPair 1 hq) 1 (fun _ ↦ {0}) 1
    (isRepOfType_one _) (by simp) ?_
  -- the shifted jump is that of `isMainSummandWeights_mainPair`
  obtain ⟨h_card, hz_large⟩ : Fintype.card (RankOneIndex q.z) = 2 * q.z ∧ 2 ≤ q.z :=
    hq.hasLiftRank
  have h_weight (v : D.Φ) : q.negWeight v - q.z + 2 * q.z / 2 = q.negWeight v := by
    grind [q.le_negWeight v]
  have h_shift : ((1 : ℕ) - (2 * q.z - 1 : ℕ) : ℤ) / 2 = 1 - q.z := by omega
  have h_jump (s c z : ℤ) : 0 - (1 - z - s * -c) = z - 1 - s * c := by ring
  simpa only [DescentPair.rankDiff, Fintype.card_unit, h_card, h_weight, h_shift,
    Multiset.map_singleton, h_jump] using isMainSummandWeights_mainPair hq

/-- **Splitting, pairs of rank `r`.** Let `ϑ` be a twist and `1 ≤ j ≤ m`. The map `D.goodLift ϑ j`
is the theta lift, for the data `D.descentPair ϑ j`, of the good forms on the rank `r` space
`W_j = D.spaceW j`; good forms have principal level at the chosen places and lie in the image of the
idempotent `D.e₀`. Its range, the space of lifts, is spanned by its forms `y` with two properties.
* There is a tuple `c` of labels, one polynomial over the residue field at each chosen place, that
  satisfies `IsLiftSetting`: each label has degree `r`, some label over each level prime is
  primitive, and no twisted label has the root `1`. The form `y` lies in the image of the idempotent
  of `c` (`typeProjection`), which is contained in that of `D.e₀`.
* There is a system `q (w, i)` of Hecke eigenvalues, one for each finite place `w` and number `i` of
  the Hecke operator, that occurs in a good form on `W_m`, such that at the split places outside the
  level the Hecke polynomial of `y` is that of a lift of `q`. -/
theorem New.Selmer.range_goodLift_le_span_hasLiftHeckePolynomial {P : Parameters} {D : Data P}
    (j : D.LiftIndex) (ϑ : D.Twist) :
    (D.goodLift ϑ j).range ≤ span ℂ {y ∈ (D.goodLift ϑ j).range |
      (∃ c : ∀ i : (D.descentPair ϑ j).ChosenIndex,
        (ResField ((D.descentPair ϑ j).chosenPlace i))[X],
        y ∈ (typeProjection (D.descentPair ϑ j) c).range ∧
        IsLiftSetting (D.descentPair ϑ j) c ϑ ∧
        (typeProjection (D.descentPair ϑ j) c).range ≤
          ((D.descentPair ϑ j).groupAlgAction D.e₀).range) ∧
      ∃ q : FinPlace D.E × ℕ → ℂ,
        D.goodForms (D.spaceW D.m) ⊓ D.eigenPart (D.spaceW D.m) q ≠ ⊥ ∧
        (D.descentPair ϑ j).HasLiftHeckePolynomial y fun (w : FinPlace D.E) (i : ℕ) ↦
          q (w, i)} := by
  -- the space of lifts is spanned by the lifts of good eigenforms `y` on `W_j`
  refine D.range_goodLift_le fun q y hy c hc hy_c ↦ ?_
  obtain rfl | hy_ne := eq_or_ne y 0
  · simp
  -- the eigensystem `q` of `y` also occurs on `W_m`
  let jmax : D.LiftIndex := ⟨D.m, D.nat_le_of_hasLogBound, le_rfl⟩
  have hq : D.goodForms (D.spaceW D.m) ⊓ D.eigenPart (D.spaceW D.m) q ≠ ⊥ := fun h_bot ↦
    hy_ne ((D.goodForms_inf_eigenPart_eq_bot_of_eq_bot (D.spaceW j) (D.spaceW jmax) h_bot).le hy)
  obtain ⟨hy_good : y ∈ D.goodForms (D.spaceW j), hy_eigen : y ∈ D.eigenPart (D.spaceW j) q⟩ := hy
  have h_range : D.singleLift ϑ j y ∈ (D.goodLift ϑ j).range := ⟨⟨y, hy_good⟩, rfl⟩
  have h_lifts : (D.descentPair ϑ j).HasLiftHeckePolynomial (D.singleLift ϑ j y) fun w i ↦
    q (w, i) :=
    D.hasLiftHeckePolynomial_singleLift _ hy_eigen
  exact subset_span ⟨h_range, ⟨c, hy_c, isLiftSetting_descentPair D ϑ j hc,
    D.range_tupleIdem_le hc⟩,
    q, hq, h_lifts⟩

/-- **The twisting theorem for two families of main summands.** Let `ℓ` be a prime,
`ι : ℂ ≃ ℚ̄_ℓ`, and `e = twistError ℓ D = (4 f + 3) r v_ℓ(D.chosenGroupOrder) + 2 ^ (-ℓ)`, where
`f` is the number of infinite places of `D.E` and `D.chosenGroupOrder` the order of a product of
general linear groups over residue fields. Let `R a` and `R₁ b` be finitely many Galois
representations of rank `r` and one, each satisfying the conditions `IsMainSummandLike` on main
summands for some self-duality parameter `t` and some multisets `J` of Hodge–Tate jumps. There is a
twist `τ`, whose tame part has nontrivial powers up to `m` at each place of its modulus
(`MFoldTwist`), such that each power `ϑ = τ ^ j`, `1 ≤ j ≤ m`, has the following properties, where
`ψ = ϑ.invAvatar` is the `ℓ`-adic Galois character of `ϑ⁻¹`.
* The modulus `ϑ.Q` is auxiliary for the places dividing `ℓ p₀ p₁ N`, for the two level primes
  `p₀, p₁` and the level `N` (`badPlaces`): its places have prime norm, avoid these places and
  their conjugates, and no two are conjugate. The character `ψ` comes from the norm-one torus, and
  the valuations of `ψ σ - 1`, for tame generators `σ` at the places of `ϑ.Q`, sum to at most `e`
  (`IsAuxTwist`).
* For each given representation, some Galois element `γ` acts on a lattice in its twist by `ψ` as a
  scalar `ζ`, and the crystalline Selmer group of that lattice with coefficients in `Frac O / O`
  has length at most `e`, normalised so that `O / ℓ` has length one, for all large coefficient
  rings `O` (`HasDivisibleSelmerLengthLe`).
* For each pair `p = (ν, z)` ramified exactly at the chosen places and each sign `s`, the inverse of
  `p.ratio ϑ s = |L(z, (ν ϑ ^ s)⁻¹)| / |L(z, ν⁻¹)|`, a ratio of partial `L`-values, has norm at most
  `ℓ ^ e` at `ι`. -/
lemma New.Selmer.exists_mFoldTwist_selmerLengthLe_inv_ratio_le {P : Parameters} (D : Data P) {ℓ : ℕ}
    [ThePrime ℓ] (ι : PadicIso ℓ) {A B : Type} [Finite A] [Finite B]
    {R : A → GalRep ℓ D.E D.RowIndex} {R₁ : B → GalRep ℓ D.E Unit}
    (hR : ∀ a : A, ∃ (t : ℕ) (J : (D.E →+* ℂ) → Multiset ℤ), IsMainSummandLike D t J (R a))
    (hR₁ : ∀ b : B, ∃ (t : ℕ) (J : (D.E →+* ℂ) → Multiset ℤ), IsMainSummandLike D t J (R₁ b)) :
    ∃ τ : D.MFoldTwist, ∀ j : D.LiftIndex,
      let ϑ : D.Twist := τ.powTwist j
      IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar (twistError ℓ D) ∧
      (∀ a : A, ∃ (γ : AbsGal D) (ζ : intQpBar ℓ),
        HasDivisibleSelmerLengthLe ϑ.invAvatar (R a) ϑ.Q γ ζ (twistError ℓ D)) ∧
      (∀ b : B, ∃ (γ : AbsGal D) (ζ : intQpBar ℓ),
        HasDivisibleSelmerLengthLe ϑ.invAvatar (R₁ b) ϑ.Q γ ζ (twistError ℓ D)) ∧
      ∀ (p : D.CriticalPair) (s : ℤˣ), p.IsRamified →
        ‖ι.ιℓ (p.ratio ϑ s)⁻¹‖ ≤ exp (twistError ℓ D * log ℓ) := by
  -- join the families over `A ⊕ B`; `SummandCoordIndex` is the index type `D.RowIndex` on the left
  -- summand and `Unit` on the right
  let r (i : A ⊕ B) : Type := SummandCoordIndex D.RowIndex (t := 1) (i.getRight?.map 0)
  let S : ∀ i : A ⊕ B, GalRep ℓ D.E (r i)
    | .inl a => R a
    | .inr b => R₁ b
  have hS : ∀ i : A ⊕ B, ∃ (t : ℕ) (J : (D.E →+* ℂ) → Multiset ℤ), IsMainSummandLike D t J (S i) :=
    Sum.forall.2 ⟨hR, hR₁⟩
  obtain ⟨τ, hτ⟩ := exists_mFoldTwist_hasDivisibleSelmerLengthLe D ℓ ι hS
  refine ⟨τ, fun j ↦ ?_⟩
  obtain ⟨h_aux, h_divisible, h_ratio⟩ := hτ j
  exact ⟨h_aux, fun a ↦ h_divisible (.inl a), fun b ↦ h_divisible (.inr b),
    fun p s hp ↦ norm_inv_le_exp_of_ellVal_le (h_ratio p s hp)⟩

/-- **Denominator for the space of lifts.** Let the modulus of the twist `ϑ` be auxiliary and its
ramification at most `twistError ℓ D` (`IsAuxTwist`). Suppose that every Hecke eigensystem `q` of
good forms on `W_m = D.spaceW D.m` has a main summand for the `j`-th descent pair of the trivial
twist `TameChar.one`. That is, there is a Galois representation `R` giving the traces attached to
all twisted lifts of `q` (`IsMainSummand`), and the twist of `R` by `ϑ⁻¹` has a short Selmer group
with divisible coefficients. Let `Z = (D.goodLift ϑ j).range` be the space of lifts for `ϑ` and `j`,
and let `r` be the size of `D.RowIndex`, the rank of `W_m`. Then some operator with determinant of
norm at least `ℓ ^ (-(dim Z · r · clearingBound D ℓ))` clears the denominators of the projection to
`Z` on integral forms orthogonal to the false lifts for the idempotent `D.e₀` of the good forms
(`DenominatorLe`). -/
lemma New.Selmer.denominatorLe_range_goodLift {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    (ι : PadicIso ℓ) {ϑ : D.Twist} (j : D.LiftIndex)
    (h_aux : IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar (twistError ℓ D))
    (h_summand : ∀ q : FinPlace D.E × ℕ → ℂ,
      D.goodForms (D.spaceW D.m) ⊓ D.eigenPart (D.spaceW D.m) q ≠ ⊥ →
      ∃ R : GalRep ℓ D.E D.RowIndex,
        IsMainSummand (D.descentPair TameChar.one j) (fun (w : FinPlace D.E) (i : ℕ) ↦ q (w, i)) R ∧
        ∃ (γ : AbsGal D) (ζ : intQpBar ℓ),
          HasDivisibleSelmerLengthLe ϑ.invAvatar R ϑ.Q γ ζ (twistError ℓ D)) :
    DenominatorLe ι.ιℓ (D.descentPair ϑ j) D.e₀ (D.goodLift ϑ j).range
      (clearingBound D ℓ * log ℓ) := by
  have h_char : (D.descentPair ϑ j).u1Char = (D.descentPair TameChar.one j).u1Char *
    ϑ.toAutChar := by
    simp [descentPair, liftChar, toAutChar_one_and_toTwist_one_and_Q_one]
  refine denominatorLe_clearingBound ι ϑ h_aux
    ((range_goodLift_le_span_hasLiftHeckePolynomial j ϑ).trans (span_mono ?_))
  rintro y ⟨h_mem, h_labels, q, hq, h_lifts⟩
  obtain ⟨R, hR, h_selmer⟩ := h_summand q hq
  -- `y` is a lift generator, with the system `q` and the main summand `R`
  exact ⟨h_mem, h_labels, _, h_lifts, R, D.descentPair TameChar.one j, hR, h_char, h_selmer⟩

/-- **Denominator for the line of a main pair.** Let the modulus of the twist `ϑ` be auxiliary and
its ramification at most `twistError ℓ D` (`IsAuxTwist`). Let `p = (ν, z)` be a main pair for `j`
(`IsMainPair`), with `lValueData` the data of the theta lift of `ν ϑ` from `U(1)` to `U(2 z)` and
`trivialLift` the lifted form. Let `R` be a main summand for the untwisted lift and the trivial
eigensystem whose twist by `ϑ⁻¹` has a short Selmer group with divisible coefficients. Then an
operator with determinant of norm at least `ℓ ^ (-clearingBound D ℓ)` clears the denominators of the
projection to the line of `trivialLift` on integral forms orthogonal to the false lifts for the
idempotent of the labels `X - 1` at the chosen places (`DenominatorLe`). -/
lemma New.Selmer.denominatorLe_span_trivialLift {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    (ι : PadicIso ℓ) {ϑ : D.Twist} {p : D.CriticalPair} {j : ℕ} (hp : p.IsMainPair j)
    (h_aux : IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar (twistError ℓ D)) {R : GalRep ℓ D.E Unit}
    (hR : IsMainSummand (p.lValueData hp.hasLiftRank (1 : D.Twist)).descentPair 1 R)
    (h_selmer : ∃ (γ : AbsGal D) (ζ : intQpBar ℓ),
      HasDivisibleSelmerLengthLe ϑ.invAvatar R ϑ.Q γ ζ (twistError ℓ D)) :
    open scoped Classical in
    DenominatorLe ι.ιℓ (p.lValueData hp.hasLiftRank ϑ).descentPair
      (tupleIdem Unit fun _ : (p.lValueData hp.hasLiftRank ϑ).descentPair.ChosenIndex ↦
        Polynomial.X - 1)
      (ℂ ∙ (p.lValueData hp.hasLiftRank ϑ).trivialLift) (clearingBound D ℓ * log ℓ) := by
  have h_char : (p.lValueData hp.hasLiftRank ϑ).descentPair.u1Char =
      (p.lValueData hp.hasLiftRank (1 : D.Twist)).descentPair.u1Char * ϑ.toAutChar := by
    simp [toAutChar_one_and_toTwist_one_and_Q_one]
  refine denominatorLe_clearingBound ι ϑ h_aux (span_mono (Set.singleton_subset_iff.2 ?_))
  -- `trivialLift` has the labels `X - 1` and lifts the eigensystem `1`
  refine ⟨mem_span_singleton_self _, ⟨fun _ ↦ Polynomial.X - 1, ?_, isLiftSetting_mainPair ϑ hp,
    le_rfl⟩,
    1, LValueData.hasLiftHeckePolynomial_trivialLift _, R, _, hR, h_char, h_selmer⟩
  -- `convert`, as the two `DecidableEq` instances on the index type agree only propositionally
  convert trivialLift_mem_range_typeProjection ϑ hp

/-- **A twist with few congruences at one prime.** For a prime `ℓ` and `ι : ℂ ≃ ℚ̄_ℓ` there is an
`m`-fold twist `τ` (`D.MFoldTwist`) with three properties, where `ϑ = τ ^ j` (`τ.powTwist j`) and
`j : D.LiftIndex`, so `1 ≤ j ≤ m`. The product `τ.normQ` of the norms of the places in the set `Q`
of `τ` is prime to `ℓ`. Take each ramified pair `p = (ν, z)` (`p.IsRamified`: the tame part of `ν`
is nontrivial exactly at the places dividing `D.piM`, of norm `p₀ p₁`) and each sign `s`. The
inverse of `p.ratio ϑ s = |L(z, (ν ϑ ^ s)⁻¹)| / |L(z, ν⁻¹)|` (partial `L`-values) has norm at most
`ℓ ^ e` under `ι.ιℓ`, where `e = twistError ℓ D = (4 f + 3) r v_ℓ(D.chosenGroupOrder) + 2 ^ (-ℓ)`.
For each `j`, `D.HasDenominatorsLe ι.ιℓ ϑ j β` holds, with `exp β` equal to `ℓ ^ clearingBound D ℓ`
times the `ℓ`-part of the number of classes `StdClasses` of `U(1)` at level `D.chosenLevel`. -/
lemma New.Selmer.exists_mFoldTwist_hasDenominatorsLe {P : Parameters} (D : Data P) {ℓ : ℕ}
    [ThePrime ℓ] (ι : PadicIso ℓ) :
    ∃ τ : D.MFoldTwist, ℓ.Coprime τ.normQ ∧
      (∀ (j : D.LiftIndex) (p : D.CriticalPair) (s : ℤˣ), p.IsRamified →
        ‖ι.ιℓ (p.ratio (τ.powTwist j) s)⁻¹‖ ≤ exp (twistError ℓ D * log ℓ)) ∧
      ∀ j : D.LiftIndex, D.HasDenominatorsLe ι.ιℓ (τ.powTwist j) j (clearingBound D ℓ * log ℓ +
        padicValNat ℓ (Nat.card (StdClasses (n := Unit) D.chosenLevel)) * log ℓ) := by
  -- There are finitely many main summands: one for each `j` and each eigensystem of good forms on
  -- `W_m`, one for each main pair. The twisting theorem gives a twist for whose powers all of them
  -- have short Selmer groups, and these bound the denominators.
  let systems : Set (FinPlace D.E × ℕ → ℂ) :=
    {q | D.goodForms (D.spaceW D.m) ⊓ D.eigenPart (D.spaceW D.m) q ≠ ⊥}
  have : Finite systems := D.finite_setOf_inf_eigenPart_ne_bot _ _
  have h_summands (a : D.LiftIndex × systems) : ∃ T : GalRep ℓ D.E D.RowIndex,
      IsMainSummand (D.descentPair TameChar.one a.1) (fun w i ↦ a.2.val (w, i)) T :=
    exists_isMainSummand_descentPair ι a.2.prop a.1
  choose R hR using h_summands
  choose R₁ hR₁ using exists_isMainSummand_mainPair (D := D) (ι := ι)
  obtain ⟨τ, hτ⟩ := exists_mFoldTwist_selmerLengthLe_inv_ratio_le D ι (R := R) (R₁ := R₁)
    (fun a ↦ ⟨_, (hR a).left⟩) fun b ↦ ⟨_, (hR₁ b).left⟩
  -- the powers of `τ`: auxiliary modulus, short Selmer groups for `R` and `R₁`, small ratios
  choose h_aux h_selmer h_selmer₁ h_ratio using hτ
  have h_coprime : ℓ.Coprime τ.normQ := by
    obtain ⟨h_auxiliary, -⟩ := h_aux ⟨1, le_rfl, D.nat_le_of_hasLogBound⟩
    exact (coprime_prod_q_of_isAuxiliary h_auxiliary).left
  have h_lifts (j : D.LiftIndex) : DenominatorLe ι.ιℓ (D.descentPair (τ.powTwist j) j) D.e₀
      (D.goodLift (τ.powTwist j) j).range (clearingBound D ℓ * log ℓ) :=
    denominatorLe_range_goodLift ι j (h_aux j) fun q hq ↦
      ⟨R (j, ⟨q, hq⟩), hR (j, ⟨q, hq⟩), h_selmer j (j, ⟨q, hq⟩)⟩
  have h_free : ∀ g : Gf D.E Unit, classAut stdRatPoints D.chosenLevel g = ⊥ :=
    D.classAut_eq_bot_of_le_chosenLevel le_rfl
      (Fintype.card_unit.trans_le D.nat_le_of_hasLogBound)
  refine ⟨τ, h_coprime, h_ratio, fun j ↦ ⟨?_, fun p hp Ξ Ξ' hΞ hΞ' ↦ ?_⟩⟩
  · exact (h_lifts j).clearsProjection (le_add_of_nonneg_right (by positivity))
  · -- main pairs: the denominator for the line of `trivialLift` bounds the inner product
    have h_line := denominatorLe_span_trivialLift ι hp (h_aux j) (hR₁ ⟨(p, j), hp⟩)
      (h_selmer₁ j ⟨(p, j), hp⟩)
    exact h_line.norm_inner_starProjection_le _ h_free hΞ hΞ'

/-- **Twists with few congruences.** All data `D` have a regular family of `m`-fold twists `θ κ`,
one for each pair `κ` of a prime `ℓ` and an isomorphism `ℂ ≃ ℚ̄_ℓ`. The modulus of `θ κ` is prime to
`ℓ`. -/
lemma New.exists_isRegularFamily {P : Parameters} (D : Data P) :
    ∃ θ : PrimePadicIso → D.MFoldTwist, D.IsRegularFamily θ := by
  have h_twist (κ : PrimePadicIso) : ∃ τ : D.MFoldTwist, Nat.Coprime κ.1 τ.normQ ∧
      (∀ (j : D.LiftIndex) (p : D.CriticalPair) (s : ℤˣ), p.IsRamified →
        ‖κ.2 (p.ratio (τ.powTwist j) s)⁻¹‖ ≤ exp (twistError κ.1 D * log (κ.1 : ℕ))) ∧
      ∀ j : D.LiftIndex, D.HasDenominatorsLe κ.2 (τ.powTwist j) j
        (clearingBound D κ.1 * log (κ.1 : ℕ) +
          padicValNat κ.1 (Nat.card (StdClasses (n := Unit) D.chosenLevel)) * log (κ.1 : ℕ)) :=
    have : ThePrime κ.1 := ⟨⟩
    exists_mFoldTwist_hasDenominatorsLe D ⟨κ.2⟩
  choose θ h_coprime h_ratio h_denominators using h_twist
  -- it remains to sum the bounds over the primes
  have h_error (T : Finset ℕ) (hT : ∀ l ∈ T, l.Prime) : ∑ l ∈ T, twistError l D * log l ≤ D.x₁ :=
    ((isNegligible_twistError D).sum_mul_log_le T hT).trans D.le_of_hasLogBound
  exact ⟨θ,
    { coprime := h_coprime
      height_le j p s hp := HeightLe.of_le h_error fun κ ↦ h_ratio κ j p s hp
      exists_denominator_bound j := ⟨_, sum_clearingBound_add_padicValNat_le D, fun κ ↦
        h_denominators κ j⟩ }⟩
