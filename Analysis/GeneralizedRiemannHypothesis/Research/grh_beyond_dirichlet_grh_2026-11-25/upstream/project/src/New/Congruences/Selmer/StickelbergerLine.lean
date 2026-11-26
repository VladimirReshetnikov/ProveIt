import New.Congruences.Selmer.OneSystem
import New.Congruences.Selmer.StickelbergerSystems

/-!
# Stickelberger systems on a line

Let `P = ψ_X(Θ_J)` be the value of the polynomial character `ψ_X = ∏_j (1 + X_j) ^ h_j` at the
element `Θ_J` of a Stickelberger system, where `J` is a set of tied auxiliary primes, the first
prime `P₀` included. On the line on which all variables but the one of `P₀` vanish, `P` is a
polynomial `P(X, 0)` in one variable. Up to a power of `1 + X` it is congruent to `R₀ R₁` modulo
`(1 + X) ^ ℓ ^ N - 1`. Here `R₀` comes from the element for `{P₀}` and has `v(R₀(0)) ≤ β` if
`ϑ(φ_{P₀})` is close enough to `ϑ(g₀)` and `N` is large, and `R₁` comes from the Euler factors at
the other primes and has small Gauss valuation. If `ρ ≤ 1` and `v_ρ(R₀ R₁) < N ρ`, the congruence
bounds the valuation of `P` at a point where `R₀ R₁` attains its Gauss valuation.

* `New.Selmer.StickelbergerSystem.exists_congruence_lineChar_element`: the congruence.
* `New.Selmer.StickelbergerSystem.exists_point_ellVal_universalChar_le`: an upper bound for the
  valuation of `P` at some point whose coordinates have valuation at least `ρ`.

Notions from other files:
* `New.Selmer.StickelbergerSystem`: elements `Θ_Q` of the group rings of class groups `Cl_Q` with a
  norm relation, a character `ϑ`, a list of integers `e`, and the number `β`.
* `New.Selmer.IsTiedPrimes`: an auxiliary set `J` of primes with places, Frobenius elements `φ`,
  tame generators `γ`, characters `h` to `ℤ / ℓ ^ N` and slopes, and a first prime `P₀ ∈ J`; for
  primes `v, w ≠ P₀` of `J` one has `h_{P₀}(φ_v) = 1` and `h_w(φ_v) = 0`.
* `New.Selmer.groupRingEval`: the value of a function on `Gal(Ω/E)`, read on `Cl_Q` and extended
  linearly, at an element of the group ring of `Cl_Q`.
* `New.ellVal`: the valuation `v` of `ℚ̄_ℓ` with `v(ℓ) = 1`, cut off at `0` from below;
  `New.intQpBar` is its valuation ring.
* `New.Selmer.gaussVal`: the Gauss valuation `v_ρ(g) = min_i (v(y_i) + ρ i)` of `g = ∑ y_i Y ^ i`.
-/

noncomputable section

namespace New.Selmer

open Finset Filter Polynomial

open scoped NNReal ENNReal NNRat

/-- Let `E` be a CM number field embedded in the algebraic closure `Ω` of `ℚ`, let `ζ_j` be `q`-th
roots of unity in `R`, and `h_j` characters of `Gal(Ω/E)` to `ℤ / q`. If each `h_j` with `ζ_j ≠ 1`
comes from the norm-one torus with modulus `I` and is trivial at `S`, then so does the character
`g ↦ ∏ ζ_j ^ h_j(g)` (`pointChar`). -/
lemma isFromU1_pointChar {E σ R : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
    [CommRing R] [Fintype σ] {q : ℕ} [NeZero q] {S I : Set (FinPlace E)}
    {h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)} {ζ : σ → R} (hζ : ∀ j : σ, ζ j ^ q = 1)
    (h_fromU1 : ∀ j : σ, ζ j ≠ 1 → IsFromU1 S I (h j)) : IsFromU1 S I (pointChar h ζ hζ) := by
  let factor (j : σ) : Gal(Ω/E) →* R := (AddChar.zmodChar q (hζ j)).toMonoidHom.comp (h j)
  have h_prod : pointChar h ζ hζ = ∏ j : σ, factor j :=
    MonoidHom.ext fun g ↦ by simp [factor, AddChar.zmodChar_apply]
  rw [h_prod]
  refine prod_induction factor _ (fun _ _ ↦ IsFromU1.mul) IsFromU1.one fun j _ ↦ ?_
  by_cases hj : ζ j = 1
  · rw [show factor j = 1 from MonoidHom.ext fun g ↦ by simp [factor, AddChar.zmodChar_apply, hj]]
    exact IsFromU1.one
  · exact (h_fromU1 j hj).map _

/-- Let `E` be a CM number field embedded in the algebraic closure `Ω` of `ℚ`, let `h_j` be
characters of `Gal(Ω/E)` to `ℤ / q`, and `ζ_j` `q`-th roots of unity in the valuation ring of
`ℚ̄_ℓ`. Let `a` be in the group ring over that valuation ring of `Cl_Q = U1ClassGroup Q`, the finite
ideles `u` with `u ū = 1` modulo those in `Eˣ` and the units that are `≡ 1` at the primes in `Q`.
Then the value of `ψ_X = ∏ (1 + X_j) ^ h_j` (`universalChar`) on `a`, at the point `(ζ_j - 1)_j`, is
the value of the character `∏ ζ_j ^ h_j` (`pointChar`) on `a`. -/
lemma coe_eval_groupRingEval_universalChar {ℓ : ℕ} [ThePrime ℓ] {E σ : Type} [Field E]
    [EmbeddedNumberField E] [NumberField.IsCMField E] [Fintype σ] {q : ℕ} [NeZero q]
    (h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)) {ζ : σ → intQpBar ℓ}
    (hζ : ∀ j : σ, (ζ j : PadicAlgCl ℓ) ^ q = 1) {Q : Finset (FinPlace E)}
    (a : MonoidAlgebra (intQpBar ℓ) (U1ClassGroup Q)) :
    ((MvPolynomial.eval (fun j : σ ↦ ζ j - 1) (groupRingEval (universalChar h) a) : intQpBar ℓ) :
        PadicAlgCl ℓ) =
      groupRingEval (pointChar h (fun j : σ ↦ (ζ j : PadicAlgCl ℓ)) hζ) a := by
  let L : MvPolynomial σ (intQpBar ℓ) →ₐ[intQpBar ℓ] PadicAlgCl ℓ :=
    MvPolynomial.aeval fun j ↦ (ζ j : PadicAlgCl ℓ) - 1
  have hL (P : MvPolynomial σ (intQpBar ℓ)) :
      (MvPolynomial.eval (fun j ↦ ζ j - 1) P : intQpBar ℓ) = L P :=
    (MvPolynomial.aeval_algebraMap_apply (PadicAlgCl ℓ) (fun j ↦ ζ j - 1) P).symm
  have h_char : (fun g ↦ L (universalChar h g)) = pointChar h (fun j ↦ (ζ j : PadicAlgCl ℓ)) hζ :=
    funext (aeval_sub_one_universalChar h hζ)
  rw [hL, ← h_char]
  exact map_groupRingEval L.toLinearMap (universalChar h) a

section Valuation

variable {ℓ : ℕ} [ThePrime ℓ] {a b c : PadicAlgCl ℓ} {M : ℝ≥0∞}

/-- The ultrametric inequality for the valuation `v = ellVal` of `ℚ̄_ℓ`. -/
lemma le_ellVal_add (ha : M ≤ ellVal a) (hb : M ≤ ellVal b) : M ≤ ellVal (a + b) := by
  obtain h | h := le_max_iff.1 (IsUltrametricDist.norm_add_le_max a b)
  · exact ha.trans (ellVal_le_ellVal h)
  · exact hb.trans (ellVal_le_ellVal h)

lemma ellVal_eq_of_lt_ellVal_sub (h_lt : ellVal b < ellVal (a - b)) : ellVal a = ellVal b := by
  have h_norm : ‖a - b‖ < ‖b‖ := lt_of_not_ge fun h_le ↦ h_lt.not_ge (ellVal_le_ellVal h_le)
  refine ellVal_congr_norm ?_
  simpa [max_eq_right h_norm.le] using IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_norm.ne

/-- For units `a` and `b`, the differences `a⁻¹ - b⁻¹` and `a - b` have the same valuation. -/
lemma ellVal_inv_sub_inv (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : ellVal (a⁻¹ - b⁻¹) = ellVal (a - b) := by
  refine ellVal_congr_norm ?_
  rw [inv_sub_inv (norm_ne_zero_iff.1 (by simp [ha])) (norm_ne_zero_iff.1 (by simp [hb])),
    norm_div, norm_mul, ha, hb, mul_one, div_one, norm_sub_rev]

/-- For a unit `a`, the valuation of `a ^ k - 1` is at least that of `a - 1`, for every integer
`k`. -/
lemma ellVal_sub_one_le_ellVal_zpow_sub_one (ha : ‖a‖ = 1) (k : ℤ) :
    ellVal (a - 1) ≤ ellVal (a ^ k - 1) := by
  have h_nat (n : ℕ) : ellVal (a - 1) ≤ ellVal (a ^ n - 1) := by
    simpa using dvd_iff_ellVal_le.1 (sub_one_dvd_pow_sub_one (⟨a, ha.le⟩ : intQpBar ℓ) n)
  obtain ⟨n, rfl | rfl⟩ : ∃ n : ℕ, k = n ∨ k = -n := k.eq_nat_or_neg
  · simpa using h_nat n
  · calc ellVal (a - 1) ≤ ellVal (a ^ n - 1) := h_nat n
      _ = ellVal (a ^ (-n : ℤ) - 1) := by
        simpa using (ellVal_inv_sub_inv (a := a ^ n) (by simp [ha]) norm_one).symm

/-- If `‖a‖ = 1`, and `a ≡ b` and `c ≡ 1` up to valuation `M > v(b - 1)`, where `v = ellVal`, then
`v(1 - a * c) = v(b - 1)`. -/
lemma ellVal_one_sub_mul_eq (ha : ‖a‖ = 1) (hab : M ≤ ellVal (a - b)) (hc : M ≤ ellVal (c - 1))
    (hb : ellVal (b - 1) < M) : ellVal (1 - a * c) = ellVal (b - 1) := by
  have h_congr : M ≤ ellVal (a * c - 1 - (b - 1)) := by
    rw [show a * c - 1 - (b - 1) = a * (c - 1) + (a - b) by ring]
    exact le_ellVal_add (hc.trans_eq (ellVal_congr_norm (by simp [ha]))) hab
  rw [ellVal_congr_norm (norm_sub_rev 1 (a * c)), ellVal_eq_of_lt_ellVal_sub (hb.trans_le h_congr)]

/-- Let `a`, `b` and `q` be `ℓ`-adic units with `a ≡ b` and `q ≡ 1` up to valuation
`M > v(b - 1)`. Then `(1 - a q ^ k) (1 - a⁻¹ q ^ k)` has valuation at most `2 v(b - 1)`, since each
factor has the valuation of `b - 1`. -/
lemma ellVal_one_sub_mul_one_sub_inv_le {q : PadicAlgCl ℓ} (k : ℤ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hq_norm : ‖q‖ = 1) (hab : M ≤ ellVal (a - b)) (hq : M ≤ ellVal (q - 1))
    (hM : ellVal (b - 1) < M) :
    ellVal ((1 - a * q ^ k) * (1 - a⁻¹ * q ^ k)) ≤ 2 * ellVal (b - 1) := by
  have hq_zpow : M ≤ ellVal (q ^ k - 1) :=
    hq.trans (ellVal_sub_one_le_ellVal_zpow_sub_one hq_norm k)
  have hab_inv : M ≤ ellVal (a⁻¹ - b⁻¹) := hab.trans (ellVal_inv_sub_inv ha hb).ge
  have hb_inv : ellVal (b⁻¹ - 1) = ellVal (b - 1) := by
    rw [← ellVal_inv_sub_inv hb norm_one, inv_one]
  calc ellVal ((1 - a * q ^ k) * (1 - a⁻¹ * q ^ k))
      ≤ ellVal (1 - a * q ^ k) + ellVal (1 - a⁻¹ * q ^ k) := ellVal_mul_le
    _ = ellVal (b - 1) + ellVal (b⁻¹ - 1) := by
        rw [ellVal_one_sub_mul_eq ha hab hq_zpow hM,
          ellVal_one_sub_mul_eq (by simp [ha]) hab_inv hq_zpow (hb_inv.trans_lt hM)]
    _ = 2 * ellVal (b - 1) := by rw [hb_inv, two_mul]

/-- Let `a`, `b` and `q` be `ℓ`-adic units with `a ≡ b` and `q ≡ 1` up to valuation `M`, and let
`M > 2 r v(b - 1)`, where `r` is the length of the list `exps`. Then the product
`eulerFactor exps a q` of the factors `1 - a ^ (±1) q ^ (-e)`, `e ∈ exps`, has valuation at most
`2 r v(b - 1)`. -/
lemma ellVal_eulerFactor_le {q : ℕ} (exps : List ℤ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hq_norm : ‖(q : PadicAlgCl ℓ)‖ = 1) (hab : M ≤ ellVal (a - b))
    (hq : M ≤ ellVal (q - 1 : PadicAlgCl ℓ)) (hM : exps.length * (2 * ellVal (b - 1)) < M) :
    ellVal (eulerFactor exps a q) ≤ exps.length * (2 * ellVal (b - 1)) := by
  induction exps with
  | nil => simp [ellVal, eulerFactor_nil]
  | cons e exps ih =>
    rw [List.length_cons, Nat.cast_succ, add_one_mul] at hM ⊢
    have hb_lt : ellVal (b - 1) < M :=
      calc ellVal (b - 1) ≤ 2 * ellVal (b - 1) := le_self_add.trans_eq (two_mul _).symm
        _ < M := le_add_self.trans_lt hM
    have h_tail : ellVal (eulerFactor exps a q) ≤ exps.length * (2 * ellVal (b - 1)) :=
      ih (le_self_add.trans_lt hM)
    have h_head : ellVal ((1 - a * (q : PadicAlgCl ℓ) ^ (-e)) *
        (1 - a⁻¹ * (q : PadicAlgCl ℓ) ^ (-e))) ≤ 2 * ellVal (b - 1) :=
      ellVal_one_sub_mul_one_sub_inv_le (-e) ha hb hq_norm hab hq hb_lt
    rw [eulerFactor_cons, add_comm]
    exact ellVal_mul_le.trans (add_le_add h_head h_tail)

end Valuation

section Congruence

variable {ℓ : ℕ} [ThePrime ℓ]

/-- Let `α` and `c` be `ℓ`-adic units. There is an integral polynomial `R` whose Gauss valuation of
radius `ρ` is at most `2 ρ`, with `R(ζ - 1) = ζ (1 - α ζ c) (1 - (α ζ)⁻¹ c)` for all integral
`ζ ≠ 0`. It is the product of `1 - α c (1 + X)` and `1 + X - α⁻¹ c`. -/
lemma exists_polynomial_one_sub_mul_one_sub_inv (ρ : ℚ≥0) {α c : PadicAlgCl ℓ} (hα : ‖α‖ = 1)
    (hc : ‖c‖ = 1) :
    ∃ R : (intQpBar ℓ)[X], gaussVal ρ R ≤ 2 * (ρ : ℝ≥0) ∧
      ∀ ζ : intQpBar ℓ, ζ ≠ 0 → ((R.eval (ζ - 1) : intQpBar ℓ) : PadicAlgCl ℓ) =
        ζ * ((1 - α * ζ * c) * (1 - (α * ζ)⁻¹ * c)) := by
  let a : intQpBar ℓ := ⟨α * c, by simp [hα, hc, ← NNReal.coe_le_coe]⟩
  let b : intQpBar ℓ := ⟨α⁻¹ * c, by simp [hα, hc, ← NNReal.coe_le_coe]⟩
  have ha_unit : IsUnit a := ellVal_eq_zero_iff_isUnit.1 (by simp [a, ellVal, hα, hc])
  have h_linear (g : (intQpBar ℓ)[X]) (hg : IsUnit (g.coeff 1)) : gaussVal ρ g ≤ (ρ : ℝ≥0) := by
    simpa using gaussVal_le_of_isUnit_coeff (ρ := ρ) hg
  refine ⟨(1 - C a * (1 + X)) * (1 + X - C b), ?_, fun ζ hζ ↦ ?_⟩
  · rw [gaussVal_mul, two_mul]
    exact add_le_add (h_linear _ (by simpa [coeff_one] using ha_unit))
      (h_linear _ (by simp [coeff_one]))
  · have hζ_ne : (ζ : PadicAlgCl ℓ) ≠ 0 := by simpa using hζ
    calc ((((1 - C a * (1 + X)) * (1 + X - C b)).eval (ζ - 1) : intQpBar ℓ) : PadicAlgCl ℓ)
        = (1 - α * c * ζ) * (ζ - α⁻¹ * c) := by simp [a, b]
      _ = ζ * ((1 - α * ζ * c) * (1 - (α * ζ)⁻¹ * c)) := by field_simp

/-- Let `α` and `q` be `ℓ`-adic units and `r` the length of the list `exps`. There is an integral
polynomial `R` whose Gauss valuation of radius `ρ` is at most `2 r ρ`, with `R(ζ - 1) = ζ ^ r ∏_e
∏_± (1 - (α ζ) ^ (±1) q ^ (-e))` for all integral `ζ ≠ 0`. The double product, over `e ∈ exps`, is
`eulerFactor exps (α ζ) q`. -/
lemma exists_polynomial_eulerFactor (ρ : ℚ≥0) (exps : List ℤ) {α : PadicAlgCl ℓ} (hα : ‖α‖ = 1)
    {q : ℕ} (hq : ‖(q : PadicAlgCl ℓ)‖ = 1) :
    ∃ R : (intQpBar ℓ)[X], gaussVal ρ R ≤ exps.length * (2 * (ρ : ℝ≥0)) ∧
      ∀ ζ : intQpBar ℓ, ζ ≠ 0 → ((R.eval (ζ - 1) : intQpBar ℓ) : PadicAlgCl ℓ) =
        (ζ : PadicAlgCl ℓ) ^ exps.length * eulerFactor exps (α * (ζ : PadicAlgCl ℓ)) q := by
  induction exps with
  | nil =>
    refine ⟨1, ?_, fun ζ _ ↦ by simp [eulerFactor_nil]⟩
    simpa using gaussVal_le_of_isUnit_coeff (ρ := ρ) (g := (1 : (intQpBar ℓ)[X])) (d := 0) (by simp)
  | cons e exps ih =>
    obtain ⟨R, hR_le, hR_eval⟩ := ih
    obtain ⟨S, hS_le, hS_eval⟩ :=
      exists_polynomial_one_sub_mul_one_sub_inv ρ hα (c := (q : PadicAlgCl ℓ) ^ (-e)) (by simp [hq])
    refine ⟨R * S, ?_, fun ζ hζ ↦ ?_⟩
    · rw [gaussVal_mul, List.length_cons, Nat.cast_succ, add_one_mul]
      exact add_le_add hR_le hS_le
    · rw [eval_mul, MulMemClass.coe_mul, hR_eval ζ hζ, hS_eval ζ hζ, eulerFactor_cons,
        List.length_cons]
      ring

/-- A polynomial that vanishes at all `ζ - 1` with `ζ ^ q = 1` is divisible by `(1 + X) ^ q - 1`,
since these are the `q` distinct roots of this monic polynomial. -/
lemma one_add_X_pow_sub_one_dvd {q : ℕ} [NeZero q] {D : (intQpBar ℓ)[X]}
    (hD : ∀ ζ : intQpBar ℓ, ζ ^ q = 1 → D.eval (ζ - 1) = 0) : (1 + X) ^ q - 1 ∣ D := by
  obtain ⟨η, hη⟩ : ∃ η : PadicAlgCl ℓ, IsPrimitiveRoot η q := HasEnoughRootsOfUnity.prim
  let ζ : intQpBar ℓ := ⟨η, (hη.isOfFinOrder (NeZero.ne q)).norm_eq_one.le⟩
  have hζ : IsPrimitiveRoot ζ q := IsPrimitiveRoot.coe_submonoidClass_iff.1 hη
  have h_monic : IsMonicOfDegree ((1 + X) ^ q - 1 : (intQpBar ℓ)[X]) q := by
    simpa [add_comm] using ((isMonicOfDegree_X_add_one (1 : intQpBar ℓ)).pow q).sub
      (natDegree_one.trans_lt (by simpa using NeZero.pos q))
  have h_inj : Set.InjOn (fun i : ℕ ↦ ζ ^ i - 1) (range q) :=
    fun i hi j hj h_eq ↦ hζ.injOn_pow hi hj (sub_left_injective h_eq)
  have h_degree : (D %ₘ ((1 + X) ^ q - 1)).degree < #(range q) :=
    (degree_modByMonic_lt D h_monic.monic).trans_eq <| by
      simp [degree_eq_natDegree h_monic.monic.ne_zero, h_monic.natDegree_eq]
  have h_eval (i : ℕ) : (D %ₘ ((1 + X) ^ q - 1)).eval (ζ ^ i - 1) = 0 := by
    have h_root : (ζ ^ i) ^ q = 1 := by rw [pow_right_comm, hζ.pow_eq_one, one_pow]
    simp [modByMonic_eq_sub_mul_div, hD _ h_root, h_root]
  rw [← modByMonic_eq_zero_iff_dvd h_monic.monic]
  exact eq_zero_of_degree_lt_of_eval_index_eq_zero (range q) h_inj h_degree fun i _ ↦ h_eval i

/-- If `v(y) ≥ ρ` for the valuation `v = ellVal`, with `ρ ≤ 1`, then `(1 + y) ^ ℓ ^ N - 1` has
valuation at least `N * ρ`. -/
lemma le_ellVal_one_add_pow_sub_one {ρ : ℚ≥0} (hρ : ρ ≤ 1) {y : intQpBar ℓ}
    (hy : (ρ : ℝ≥0) ≤ ellVal (y : PadicAlgCl ℓ)) (N : ℕ) :
    (N : ℝ≥0∞) * (ρ : ℝ≥0) ≤ ellVal ((1 + y) ^ ℓ ^ N - 1 : intQpBar ℓ).val :=
  calc (N : ℝ≥0∞) * (ρ : ℝ≥0) ≤ ellVal (∑ i ∈ range (ℓ ^ N), (1 + y) ^ i).val :=
      le_ellVal_geom_sum hρ (by rwa [add_sub_cancel_left]) N
    _ ≤ ellVal ((1 + y) ^ ℓ ^ N - 1).val :=
      dvd_iff_ellVal_le.1 (Dvd.intro _ (geom_sum_mul (1 + y) (ℓ ^ N)))

/-- Let `(1 + X) ^ j P ≡ R` modulo `(1 + X) ^ ℓ ^ N - 1`, where the Gauss valuation `v_ρ(R)` is less
than `N ρ` and `ρ ≤ 1`. Then `v(P(y)) ≤ v_ρ(R)` at some point `y` with `v(y) ≥ ρ`. -/
lemma exists_ellVal_eval_le_gaussVal {ρ : ℚ≥0} (hρ : ρ ≤ 1) {N j : ℕ} {P R : (intQpBar ℓ)[X]}
    (h_congr : (1 + X) ^ ℓ ^ N - 1 ∣ (1 + X) ^ j * P - R) (hR : gaussVal ρ R < N * (ρ : ℝ≥0)) :
    ∃ y : intQpBar ℓ, (ρ : ℝ≥0) ≤ ellVal (y : PadicAlgCl ℓ) ∧
      ellVal (P.eval y).val ≤ gaussVal ρ R := by
  obtain ⟨y, hy, h_generic⟩ : ∃ y : intQpBar ℓ, (ρ : ℝ≥0) ≤ ellVal (y : PadicAlgCl ℓ) ∧
      ellVal (R.eval y).val = gaussVal ρ R := by
    simpa only [forall_const] using exists_forall_ellVal_eval_eq_gaussVal ρ fun _ : Unit ↦ R
  have h_dvd : (1 + y) ^ ℓ ^ N - 1 ∣ (1 + y) ^ j * P.eval y - R.eval y := by
    simpa using eval_dvd (x := y) h_congr
  have h_lt : ellVal (R.eval y).val < ellVal ((1 + y) ^ j * P.eval y - R.eval y).val :=
    calc ellVal (R.eval y).val = gaussVal ρ R := h_generic
      _ < N * (ρ : ℝ≥0) := hR
      _ ≤ ellVal ((1 + y) ^ ℓ ^ N - 1).val := le_ellVal_one_add_pow_sub_one hρ hy N
      _ ≤ ellVal ((1 + y) ^ j * P.eval y - R.eval y).val := dvd_iff_ellVal_le.1 h_dvd
  refine ⟨y, hy, ?_⟩
  calc ellVal (P.eval y).val
      ≤ ellVal ((1 + y) ^ j * P.eval y).val := dvd_iff_ellVal_le.1 (dvd_mul_left _ _)
    _ = ellVal (R.eval y).val := ellVal_eq_of_lt_ellVal_sub (by rwa [← AddSubgroupClass.coe_sub])
    _ = gaussVal ρ R := h_generic

end Congruence

section Line

variable {ℓ : ℕ} [ThePrime ℓ] {E σ : Type} [Field E] [EmbeddedNumberField E]
  [NumberField.IsCMField E] {q : ℕ} {Q : Finset (FinPlace E)}

/-- The polynomial `(1 + X) ^ (h g)`, with the exponent `h g ∈ ℤ / q` read as a natural number. It
is the restriction of `ψ_X(g) = ∏ (1 + X_j) ^ (h_j g)` to the line on which all variables but the
one belonging to `h` vanish. -/
def lineChar (h : Gal(Ω/E) →* Multiplicative (ZMod q)) (g : Gal(Ω/E)) : (intQpBar ℓ)[X] :=
  (1 + X) ^ (h g).toAdd.val

/-- Let the `h_i` be characters `Gal(Ω/E) → ℤ / q`, let `Q` be a finite set of primes of `E`, and
let `a` be an element of the group ring of `Cl_Q = U1ClassGroup Q`, the finite ideles `u` with
`u ū = 1` modulo those in `Eˣ` and the units that are `≡ 1` at the primes of `Q`. The value of
`ψ_X = ∏ (1 + X_i) ^ h_i` (`universalChar`) on `a`, at the point with `j`-th coordinate `y` and all
others `0`, is the value of `(1 + X) ^ h_j` (`lineChar`) on `a` at `X = y`. -/
lemma eval_single_groupRingEval_universalChar [Fintype σ] [DecidableEq σ]
    (h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)) (j : σ) (y : intQpBar ℓ)
    (a : MonoidAlgebra (intQpBar ℓ) (U1ClassGroup Q)) :
    MvPolynomial.eval (Pi.single j y) (groupRingEval (universalChar h) a) =
      (groupRingEval (lineChar (h j)) a : (intQpBar ℓ)[X]).eval y := by
  have h_line (g : Gal(Ω/E)) :
      MvPolynomial.eval (Pi.single j y) (universalChar h g) = (lineChar (h j) g).eval y := by
    rw [eval_universalChar, prod_eq_single_of_mem j (mem_univ j) fun i _ hi ↦ by simp [hi]]
    simp [lineChar]
  calc MvPolynomial.eval (Pi.single j y) (groupRingEval (universalChar h) a)
      = groupRingEval (fun g ↦ MvPolynomial.eval (Pi.single j y) (universalChar h g)) a :=
        map_groupRingEval (MvPolynomial.aeval (Pi.single j y)).toLinearMap (universalChar h) a
    _ = groupRingEval (fun g ↦ (lineChar (h j) g).eval y) a := by rw [funext h_line]
    _ = (groupRingEval (lineChar (h j)) a : (intQpBar ℓ)[X]).eval y :=
        (map_groupRingEval (leval y) (lineChar (h j)) a).symm

/-- For a function `f` on `Gal(Ω/E)` with polynomial values, extended linearly to the group ring of
`Cl_Q = U1ClassGroup Q` (`groupRingEval`), evaluation of the polynomials at a point `y` commutes
with this extension. -/
lemma coe_eval_groupRingEval (f : Gal(Ω/E) → (intQpBar ℓ)[X]) (y : intQpBar ℓ)
    (a : MonoidAlgebra (intQpBar ℓ) (U1ClassGroup Q)) :
    (((groupRingEval f a).eval y : intQpBar ℓ) : PadicAlgCl ℓ) =
      groupRingEval (fun g : Gal(Ω/E) ↦ (((f g).eval y : intQpBar ℓ) : PadicAlgCl ℓ)) a :=
  map_groupRingEval (Algebra.linearMap (intQpBar ℓ) (PadicAlgCl ℓ) ∘ₗ leval y) f a

/-- At `X = ζ - 1` with `ζ ^ q = 1`, the value of `(1 + X) ^ h` (`lineChar`) on an element `a` of
the group ring of `Cl_Q` is the value of the character `ζ ^ h` on `a`. -/
lemma coe_eval_groupRingEval_lineChar [NeZero q] (h : Gal(Ω/E) →* Multiplicative (ZMod q))
    {ζ : intQpBar ℓ} (hζ : (ζ : PadicAlgCl ℓ) ^ q = 1)
    (a : MonoidAlgebra (intQpBar ℓ) (U1ClassGroup Q)) :
    (((groupRingEval (lineChar h) a : (intQpBar ℓ)[X]).eval (ζ - 1) : intQpBar ℓ) : PadicAlgCl ℓ) =
      groupRingEval ((AddChar.zmodChar q hζ).toMonoidHom.comp h) a := by
  rw [coe_eval_groupRingEval]
  exact congrArg (groupRingEval · a) (funext fun g ↦ by simp [lineChar, AddChar.zmodChar_apply])

/-- At `X = 0`, the value of `(1 + X) ^ h` (`lineChar`) on an element `a` of the group ring of
`Cl_Q` is the value of the trivial character on `a`. -/
lemma coe_eval_zero_groupRingEval_lineChar (h : Gal(Ω/E) →* Multiplicative (ZMod q))
    (a : MonoidAlgebra (intQpBar ℓ) (U1ClassGroup Q)) :
    (((groupRingEval (lineChar h) a : (intQpBar ℓ)[X]).eval 0 : intQpBar ℓ) : PadicAlgCl ℓ) =
      groupRingEval (1 : Gal(Ω/E) →* PadicAlgCl ℓ) a := by
  rw [coe_eval_groupRingEval]
  exact congrArg (groupRingEval · a) (funext fun g ↦ by simp [lineChar])

end Line

/-- A natural number `q ≡ 1` modulo a positive power of `ℓ` is an `ℓ`-adic unit. -/
lemma norm_natCast_eq_one_of_modEq {ℓ : ℕ} [ThePrime ℓ] {q N : ℕ} (hN : N ≠ 0)
    (hq : q ≡ 1 [MOD ℓ ^ N]) : ‖(q : PadicAlgCl ℓ)‖ = 1 :=
  have h_coprime : q.Coprime ℓ :=
    Nat.coprime_of_mul_modEq_one 1 <| by simpa using hq.of_dvd (dvd_pow_self ℓ hN)
  h_coprime.symm.norm_natCast_eq_one _

/-- If `q ≡ 1` modulo `ℓ ^ N`, then `q - 1` has valuation (`ellVal`) at least `N`. -/
lemma le_ellVal_natCast_sub_one {ℓ : ℕ} [ThePrime ℓ] {q N : ℕ} (hq : q ≡ 1 [MOD ℓ ^ N]) :
    (N : ℝ≥0∞) ≤ ellVal (q - 1 : PadicAlgCl ℓ) := by
  simpa using dvd_iff_ellVal_le.1 ((Int.castRingHom (intQpBar ℓ)).map_dvd hq.symm.dvd)

namespace StickelbergerSystem

variable {ℓ : ℕ} [ThePrime ℓ] {E ι O : Type} [Field E] [EmbeddedNumberField E]
  [NumberField.IsCMField E] [CommRing O]
  {S₀ : Finset (FinPlace E)} {g₀ : Gal(Ω/E)} (Y : StickelbergerSystem ℓ S₀ g₀)

/-- Near `g₀` the values of the continuous character `ϑ = Y.twistChar` of the Stickelberger system
`Y` are congruent to `ϑ(g₀)` modulo `ℓ ^ M`. -/
lemma eventually_le_ellVal_sub (M : ℕ) :
    ∀ᶠ g : Gal(Ω/E) in nhds g₀, (M : ℝ≥0∞) ≤ ellVal
      (Y.twistChar g - Y.twistChar g₀ : PadicAlgCl ℓ) := by
  have h_pos : 0 < ‖(ℓ : PadicAlgCl ℓ) ^ M‖ := norm_pos_iff.2 (pow_ne_zero M (NeZero.ne _))
  filter_upwards [(Units.continuous_val.comp Y.continuous_twistChar).continuousAt.eventually
    (Metric.closedBall_mem_nhds _ h_pos)] with g hg using
    by simpa using ellVal_le_ellVal (mem_closedBall_iff_norm.1 hg)

variable {U : ι → Gal(Ω/E) → Prop} {W : Set Gal(Ω/E)} {N : ℕ} {P₀ : FinPlace E}
  {J : Finset (FinPlace E)} {x : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)}

open scoped Classical in
/-- The norm relation of a Stickelberger system along tied primes. If `ζ ^ ℓ ^ N = 1`, the value of
the character `ζ ^ h_{P₀}` at `Θ_J` is its value at `Θ_{P₀}` times the product, over `v ≠ P₀` in `J`
and all `e`, of `(1 - a q ^ (-e)) (1 - a⁻¹ q ^ (-e))` (`eulerFactor`), where `a = ϑ(φ_v) ζ` and `q`
is the norm of `v`. -/
lemma groupRingEval_element_eq_mul_prod_eulerFactor (h_tied : IsTiedPrimes ℓ S₀ U W N P₀ J x)
    {ζ : PadicAlgCl ℓ} (hζ : ζ ^ ℓ ^ N = 1) :
    groupRingEval ((AddChar.zmodChar (ℓ ^ N) hζ).toMonoidHom.comp (x P₀).1.character)
        (Y.element J) =
      groupRingEval ((AddChar.zmodChar (ℓ ^ N) hζ).toMonoidHom.comp (x P₀).1.character)
          (Y.element {P₀}) *
        ∏ v ∈ J.erase P₀,
          eulerFactor Y.exponents ((Y.twistChar (x v).1.frob : PadicAlgCl ℓ) * ζ) v.q := by
  set ψ : Gal(Ω/E) →* PadicAlgCl ℓ :=
    (AddChar.zmodChar (ℓ ^ N) hζ).toMonoidHom.comp (x P₀).1.character with hψ_def
  have hψ : IsFromU1 (placesDividing E ℓ) ({P₀} : Finset (FinPlace E)) ψ := by
    simpa using (h_tied.isAuxPrimeDataAt P₀ h_tied.first_mem).toIsFromU1.map _
  have hψ_frob (v : FinPlace E) (hv : v ∈ J.erase P₀) : ψ (x v).1.frob = ζ := by
    simpa [hψ_def, h_tied.char_frob_eq_ite v (mem_of_mem_erase hv) (ne_of_mem_erase hv) P₀
      h_tied.first_mem] using AddChar.zmodChar_apply' hζ 1
  have h_union : {P₀} ∪ J.erase P₀ = J := by rw [← insert_eq, insert_erase h_tied.first_mem]
  calc groupRingEval ψ (Y.element J)
      = groupRingEval ψ (Y.element {P₀}) * ∏ v ∈ J.erase P₀,
          eulerFactor Y.exponents ((Y.twistChar (x v).1.frob : PadicAlgCl ℓ) * ψ (x v).1.frob)
            v.q := by
        conv_lhs => rw [← h_union]
        exact Y.groupRingEval_element_union (disjoint_singleton_left.2 (notMem_erase P₀ J))
          (h_tied.auxiliary.mono h_union.subset) hψ
          (fun v hv ↦ (h_tied.isAuxPrimeDataAt v (mem_of_mem_erase hv)).isPlaceOver)
          (fun v hv ↦ (h_tied.isAuxPrimeDataAt v (mem_of_mem_erase hv)).isFrob)
    _ = groupRingEval ψ (Y.element {P₀}) * ∏ v ∈ J.erase P₀,
          eulerFactor Y.exponents ((Y.twistChar (x v).1.frob : PadicAlgCl ℓ) * ζ) v.q :=
        congrArg _ (prod_congr rfl fun v hv ↦ by rw [hψ_frob v hv])

open scoped Classical in
/-- The congruence `(1 + X) ^ j₀ P(X, 0) ≡ R₀(X) R(X)` modulo `(1 + X) ^ ℓ ^ N - 1`, for `N ≠ 0`.
The polynomials `P(X, 0)` and `R₀(X)` are the values of `(1 + X) ^ h₀` (`lineChar`) at `Θ_J` and
`Θ_{P₀}`, where `h₀ = (x P₀).1.character`, and `j₀ = #(J \ {P₀}) * r` with `r` the length of
`Y.exponents`. The polynomial `R` collects the Euler factors at the primes other than `P₀`, and its
Gauss valuation of radius `ρ` is at most `2 j₀ ρ`. -/
lemma exists_congruence_lineChar_element (h_tied : IsTiedPrimes ℓ S₀ U W N P₀ J x) (hN : N ≠ 0)
    (ρ : ℚ≥0) :
    ∃ R : (intQpBar ℓ)[X],
      gaussVal ρ R ≤ #(J.erase P₀) * (Y.exponents.length * (2 * (ρ : ℝ≥0))) ∧
      (1 + X) ^ ℓ ^ N - 1 ∣
        (1 + X) ^ (Y.exponents.length * #(J.erase P₀)) *
            groupRingEval (lineChar (x P₀).1.character) (Y.element J) -
          groupRingEval (lineChar (x P₀).1.character) (Y.element {P₀}) * R := by
  -- `R` is the product of the polynomials for the Euler factors at the primes `v ≠ P₀`. The
  -- congruence is checked at the roots `ζ - 1` of the modulus, where it is the norm relation.
  let euler (v : FinPlace E) (ζ : intQpBar ℓ) : PadicAlgCl ℓ :=
    eulerFactor Y.exponents ((Y.twistChar (x v).1.frob : PadicAlgCl ℓ) * (ζ : PadicAlgCl ℓ)) v.q
  have h_poly (v : FinPlace E) (hv : v ∈ J.erase P₀) : ∃ R : (intQpBar ℓ)[X],
      gaussVal ρ R ≤ Y.exponents.length * (2 * (ρ : ℝ≥0)) ∧ ∀ ζ : intQpBar ℓ, ζ ≠ 0 →
        (R.eval (ζ - 1) : intQpBar ℓ) = (ζ : PadicAlgCl ℓ) ^ Y.exponents.length * euler v ζ :=
    exists_polynomial_eulerFactor ρ Y.exponents (Y.norm_twistChar _)
      (norm_natCast_eq_one_of_modEq hN (h_tied.isAuxPrimeDataAt v (mem_of_mem_erase hv)).norm_modEq)
  choose! R hR_le hR_eval using h_poly
  refine ⟨∏ v ∈ J.erase P₀, R v, ?_, one_add_X_pow_sub_one_dvd fun ζ hζ ↦ ?_⟩
  · rw [gaussVal_prod, ← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ hR_le
  have hζ_coe : (ζ : PadicAlgCl ℓ) ^ ℓ ^ N = 1 := mod_cast hζ
  have hζ_ne : ζ ≠ 0 := (IsUnit.of_pow_eq_one hζ (NeZero.ne _)).ne_zero
  have h_prod : ((∏ v ∈ J.erase P₀, R v).eval (ζ - 1) : intQpBar ℓ) =
      (ζ : PadicAlgCl ℓ) ^ (Y.exponents.length * #(J.erase P₀)) * ∏ v ∈ J.erase P₀, euler v ζ := by
    rw [eval_prod, SubmonoidClass.coe_finsetProd, prod_congr rfl fun v hv ↦ hR_eval v hv ζ hζ_ne,
      prod_mul_distrib, prod_const, pow_mul]
  have h_norm_rel :
      ((groupRingEval (lineChar (x P₀).1.character) (Y.element J)).eval (ζ - 1) : intQpBar ℓ) =
        ((groupRingEval (lineChar (x P₀).1.character) (Y.element {P₀})).eval (ζ - 1) : intQpBar ℓ) *
          ∏ v ∈ J.erase P₀, euler v ζ := by
    rw [coe_eval_groupRingEval_lineChar _ hζ_coe, coe_eval_groupRingEval_lineChar _ hζ_coe,
      Y.groupRingEval_element_eq_mul_prod_eulerFactor h_tied hζ_coe]
  rw [eval_sub, sub_eq_zero, eval_mul, eval_mul, Subtype.ext_iff, MulMemClass.coe_mul,
    MulMemClass.coe_mul, h_norm_rel, h_prod]
  simp [mul_left_comm]

/-- A Stickelberger system `Y` for a set `S₀` of places and an element `g₀ ∈ Gal(Ω/E)` gives
elements `Θ_Q = Y.element Q` of the group rings of class groups `Cl_Q` with a norm relation, a
character `ϑ = Y.twistChar` with `ϑ(g₀) ≠ 1` and a list of `r` integers `e` (`Y.exponents`). Let
`β = v(1(Θ_∅)) + 2 r v(ϑ(g₀) - 1)`, where `1` is the trivial character and `v = ellVal`. Let `J` be
tied auxiliary primes with first prime `P₀`, so the norm `q` of `P₀` is `≡ 1` modulo `ℓ ^ N`, and
let `φ = (x P₀).1.frob` be its Frobenius element. If `β < M ≤ N` and `ϑ(φ) ≡ ϑ(g₀)` modulo `ℓ ^ M`,
then `v(1(Θ_{P₀})) ≤ β`, since each factor `1 - ϑ(φ) ^ (±1) q ^ (-e)` is congruent to
`1 - ϑ(g₀) ^ (±1)` modulo `ℓ ^ M`. -/
lemma ellVal_one_element_singleton_le (h_tied : IsTiedPrimes ℓ S₀ U W N P₀ J x) {M : ℕ}
    (hM : Y.β < M) (hMN : M ≤ N)
    (h_frob : (M : ℝ≥0∞) ≤ ellVal (Y.twistChar (x P₀).1.frob - Y.twistChar g₀ : PadicAlgCl ℓ)) :
    ellVal (groupRingEval (1 : Gal(Ω/E) →* PadicAlgCl ℓ) (Y.element {P₀})) ≤ Y.β := by
  classical
  have h_data : IsAuxPrimeDataAt (placesDividing E ℓ) P₀ (x P₀).1 :=
    h_tied.isAuxPrimeDataAt P₀ h_tied.first_mem
  have hM_pos : 0 < M := Nat.cast_pos.1 hM.pos
  have hN : N ≠ 0 := (hM_pos.trans_le hMN).ne'
  have h_norm_rel : groupRingEval (1 : Gal(Ω/E) →* PadicAlgCl ℓ) (Y.element {P₀}) =
      groupRingEval (1 : Gal(Ω/E) →* PadicAlgCl ℓ) (Y.element ∅) *
        eulerFactor Y.exponents (Y.twistChar (x P₀).1.frob : PadicAlgCl ℓ) P₀.q := by
    rw [← insert_empty_eq P₀]
    have h_aux := h_tied.auxiliary.mono (singleton_subset_iff.2 h_tied.first_mem)
    simpa only [MonoidHom.one_apply, mul_one] using Y.element_insert ∅ P₀ (notMem_empty P₀)
      h_aux 1 IsFromU1.one _ h_data.isPlaceOver _ h_data.isFrob
  have hq : (M : ℝ≥0∞) ≤ ellVal (P₀.q - 1 : PadicAlgCl ℓ) :=
    (Nat.cast_le.2 hMN).trans (le_ellVal_natCast_sub_one h_data.norm_modEq)
  have h_euler : ellVal (eulerFactor Y.exponents (Y.twistChar (x P₀).1.frob : PadicAlgCl ℓ) P₀.q) ≤
      Y.exponents.length * (2 * ellVal (Y.twistChar g₀ - 1 : PadicAlgCl ℓ)) :=
    ellVal_eulerFactor_le Y.exponents (Y.norm_twistChar _) (Y.norm_twistChar _)
      (norm_natCast_eq_one_of_modEq hN h_data.norm_modEq) h_frob hq (le_add_self.trans_lt hM)
  rw [h_norm_rel, β]
  exact ellVal_mul_le.trans (add_le_add le_rfl h_euler)

/-- The system `Y`, for a set `S₀` of places and `g₀ ∈ Gal(Ω/E)`, gives elements `Θ_Q = Y.element Q`
of the group rings of class groups `Cl_Q` with a norm relation, a character `ϑ = Y.twistChar` and
`r` integers (`Y.exponents`); `β = v(1(Θ_∅)) + 2 r v(ϑ(g₀) - 1)`, with `v = ellVal`. Suppose
`ϑ(φ_{P₀}) ≡ ϑ(g₀)` modulo `ℓ ^ M`, `β + 1 < M ≤ N ρ`, and a natural number `s₀ ≥ 1` satisfies
`2 r #J ≤ s₀` and `s₀ ρ < 1`. Then `v(P(y)) ≤ β + s₀ ρ` at some point `y` whose coordinates have
valuation at least `ρ`. -/
theorem exists_point_ellVal_universalChar_le (h_tied : IsTiedPrimes ℓ S₀ U W N P₀ J x)
    {M s₀ : ℕ} {ρ : ℚ≥0} (hM : Y.β + 1 < M)
    (h_frob : (M : ℝ≥0∞) ≤ ellVal (Y.twistChar (x P₀).1.frob - Y.twistChar g₀ : PadicAlgCl ℓ))
    (hs₀ : 1 ≤ s₀) (h_card : 2 * Y.exponents.length * #J ≤ s₀) (hρ : s₀ * ρ < 1)
    (h_level : M ≤ N * ρ) :
    ∃ y : J → intQpBar ℓ, (∀ j : J, (ρ : ℝ≥0) ≤ ellVal (y j : PadicAlgCl ℓ)) ∧
      ellVal (MvPolynomial.eval y
          (groupRingEval (universalChar fun j : J ↦ (x j).1.character) (Y.element J))).val ≤
        Y.β + s₀ * (ρ : ℝ≥0) := by
  -- The point lies on the line on which all variables but the one of `P₀` vanish. There `P` is
  -- congruent to `R₀ R₁` up to a power of `1 + X`, and `v_ρ(R₀ R₁) ≤ β + s₀ ρ < N ρ`.
  classical
  have hρ_le : ρ ≤ 1 := (le_mul_of_one_le_left zero_le (mod_cast hs₀)).trans hρ.le
  have hMN : M ≤ N := mod_cast h_level.trans (mul_le_of_le_one_right zero_le hρ_le)
  let R₀ : (intQpBar ℓ)[X] := groupRingEval (lineChar (x P₀).1.character) (Y.element {P₀})
  have hN : N ≠ 0 := ((Nat.cast_pos.1 hM.pos : 0 < M).trans_le hMN).ne'
  obtain ⟨R₁, hR₁_le, h_congr⟩ : ∃ R₁ : (intQpBar ℓ)[X],
      gaussVal ρ R₁ ≤ #(J.erase P₀) * (Y.exponents.length * (2 * (ρ : ℝ≥0))) ∧
      (1 + X) ^ ℓ ^ N - 1 ∣ (1 + X) ^ (Y.exponents.length * #(J.erase P₀)) *
        groupRingEval (lineChar (x P₀).1.character) (Y.element J) - R₀ * R₁ :=
    Y.exists_congruence_lineChar_element h_tied hN ρ
  have hR₀ : gaussVal ρ R₀ ≤ Y.β := by
    refine (gaussVal_le_eval_zero R₀).trans ?_
    rw [coe_eval_zero_groupRingEval_lineChar]
    exact Y.ellVal_one_element_singleton_le h_tied (le_self_add.trans_lt hM) hMN h_frob
  have hR₁ : gaussVal ρ R₁ ≤ s₀ * (ρ : ℝ≥0) := by
    have h_count : #(J.erase P₀) * (Y.exponents.length * 2) ≤ s₀ :=
      calc #(J.erase P₀) * (Y.exponents.length * 2) ≤ #J * (Y.exponents.length * 2) :=
          Nat.mul_le_mul_right _ card_erase_le
        _ = 2 * Y.exponents.length * #J := by ring
        _ ≤ s₀ := h_card
    calc gaussVal ρ R₁ ≤ #(J.erase P₀) * (Y.exponents.length * 2) * (ρ : ℝ≥0) := by
          rwa [mul_assoc, mul_assoc]
      _ ≤ s₀ * (ρ : ℝ≥0) := mul_le_mul_left (mod_cast h_count) _
  have hR : gaussVal ρ (R₀ * R₁) ≤ Y.β + s₀ * (ρ : ℝ≥0) :=
    (gaussVal_mul _ _).trans_le (add_le_add hR₀ hR₁)
  have hR_lt : gaussVal ρ (R₀ * R₁) < N * (ρ : ℝ≥0) :=
    calc gaussVal ρ (R₀ * R₁) ≤ Y.β + s₀ * (ρ : ℝ≥0) := hR
      _ ≤ Y.β + 1 := add_le_add le_rfl (mod_cast hρ.le)
      _ < M := hM
      _ ≤ N * (ρ : ℝ≥0) := mod_cast h_level
  obtain ⟨y, hy, hP⟩ : ∃ y : intQpBar ℓ, (ρ : ℝ≥0) ≤ ellVal (y : PadicAlgCl ℓ) ∧
      ellVal ((groupRingEval (lineChar (x P₀).1.character) (Y.element J)).eval y).val ≤
        gaussVal ρ (R₀ * R₁) :=
    exists_ellVal_eval_le_gaussVal hρ_le h_congr hR_lt
  refine ⟨Pi.single ⟨P₀, h_tied.first_mem⟩ y, fun j ↦ ?_, ?_⟩
  · obtain rfl | hj := eq_or_ne j ⟨P₀, h_tied.first_mem⟩
    · simpa using hy
    · simp [hj, ellVal_zero]
  · rw [eval_single_groupRingEval_universalChar]
    exact hP.trans hR

end StickelbergerSystem

end New.Selmer

end
