import New.Reduction.Data.Magnitudes

/-!
# Chosen places, characters of given weight, finiteness of pairs and sizes of the different

Fix admissible data `D` (`New.Data`) with primes p₀, p₁ (p_i is `D.levelPrime i`) and an integer
`D.piMBar` of K of norm p₀p₁. The chosen places are the finite places of E that divide the complex
conjugate of `D.piMBar`.

The file defines residue characters at the chosen places, characters of U(1)(𝔸) of given weight and
pairs, and proves that there are finitely many pairs. It also bounds the generator of the different
of E and the root discriminant at the infinite places between `x ^ 10` and `x ^ 12`, where `log x`
is `D.logX`.

## Main definitions and results

* `New.Data.IsChosen`, `New.Data.ChosenPlace`: the chosen places, and those above p_i. Each lies
  above p₀ or p₁ (`New.Data.exists_levelPrime_mem_of_isChosen`). A place above p_i has norm p_i
  (`New.Data.q_eq_levelPrime`).
* `New.Data.chiMLocal`: residue characters of order q₂ at the chosen places, trivial elsewhere. At a
  chosen place it is the q₂-th power of a character `New.Data.chiMLocalRoot` of order q₂².
* `New.Data.chiZero`, `New.Data.chiM`: characters of U(1)(𝔸) of weight -w₀ and trivial tame part,
  and of weight 0 and tame part `New.Data.chiMLocal`. By
  `New.AutChar.exists_hasWeight_of_prod_eq_one` they exist because the formula of
  `New.AutChar.HasWeight` gives 1 on the integral rational points of U(1), which are q₁-th roots of
  unity (`New.Data.exists_char_hasWeight`).
* `New.Data.CriticalPair`: a character of weight -c with tame part trivial off the chosen places,
  and an integer z with 1 ≤ z ≤ t and z ≤ c ≤ 4b. There are finitely many
  (`New.Data.finite_criticalPair`).
* `New.Data.hasLogBound_deltaE`: at every infinite place the generator `New.Parameters.deltaE` of
  the different has absolute value in `[x ^ 10, x ^ 12]`.
* `New.Data.rootDisc_mem_Icc`, `New.Data.hasLogBound_rootDisc`: so does the root discriminant
  `New.Data.rootDisc`, their geometric mean. The class `D.HasLogBound u F l` says `|F| ≤ exp l` for
  `u = true` and `exp l ≤ F` for `u = false`; so `(if u then 12 else 10) * log x` gives both bounds
  at once.

Notions from other files:
* `New.Data.E`: The field E = K(ζ), ζ a primitive root of unity of order q₁, a multiple of q₀ that
  depends on the exponent s = `D.towerExp` of the data; `New.Data.Φ` is the type of its infinite
  places.
* `New.AutChar`: The group of continuous circle-valued characters of U(1)(𝔸), the norm-one adeles of
  the CM field E, trivial on elements coming from E.
* `New.AutChar.HasWeight`: μ has weight e and tame part ψ: almost all residue characters ψ_w are
  trivial, and μ(u) = ∏_v u_v^{e(v)} · ∏_w ψ_w(u mod w) whenever u has integral finite part.
* `New.Parameters.q₂`: The natural number q₂ = (q₀d)^(s+6); q₂² divides p_i - 1.
* `New.Data.liftWeight`: The number w_j(σ) = κ(σ) + (j + 1/2) Δ, with κ = `New.Data.weight`, the gap
  Δ = `New.Data.gap` and Δ/2 = `New.Data.halfGap`.
-/

noncomputable section

/-! ## Chosen places and characters of given weight -/

namespace New.Data

open Ideal NumberField Finset MulChar Parameters NeZero AutChar Nat

attribute [local instance low] Fintype.ofFinite

variable {P : Parameters} (D : Data P) {i : Fin 2} {w : FinPlace D.E}

/-- The complex conjugate of the integer `D.piMBar` of K, of norm p₀p₁, as an integer of E; the
chosen places are its prime divisors. -/
abbrev piM : 𝓞 D.E := star (algebraMap (𝓞 P.K) (𝓞 D.E) D.piMBar)

/-- The finite place w of E is chosen: it divides the complex conjugate of the integer `D.piMBar` of
K, of norm p₀p₁. -/
def IsChosen (w : FinPlace D.E) : Prop := D.piM ∈ w.asIdeal

/-! ### The chosen places -/

/-- The chosen places above the prime p_i = `D.levelPrime i`: the finite places w of E that are
chosen, that is, divide the complex conjugate of `D.piMBar` (`New.Data.IsChosen`, written out), and
divide p_i. -/
protected abbrev ChosenPlace (i : Fin 2) : Type :=
  {w : FinPlace D.E // D.piM ∈ w.asIdeal ∧ ↑(D.levelPrime i) ∈ w.asIdeal}

/-- The product of `D.piM` and its complex conjugate is `D.M = p₀ p₁` in 𝓞_E. -/
lemma piM_mul_star : D.piM * star D.piM = D.M := by
  have h_conj : algebraMap (𝓞 P.K) (𝓞 D.E) (star D.piMBar) = D.piM :=
    RingOfIntegers.ext (map_star_CM (algebraMap P.K D.E) (D.piMBar : P.K))
  rw [star_star, ← h_conj, ← map_mul, mul_comm, D.piMBar_mul_star]
  simp [M]

@[simp]
lemma piMBar_ne_zero : D.piMBar ≠ 0 := fun h_zero ↦ by
  simpa [h_zero, NeZero.ne] using D.piMBar_mul_star

lemma piM_ne_zero : D.piM ≠ 0 := by simp

/-- The data `D` carry two distinct primes p₀, p₁ and an integer `D.piMBar` of K of norm p₀p₁;
`D.piM` is the complex conjugate (`star`) of its image in 𝓞_E. For i = 0 and i = 1, the product of
`D.piM` and its conjugate is p_i = `D.levelPrime i` times a natural number prime to p_i. -/
lemma exists_piM_mul_star_eq_levelPrime_mul_coprime {i : Fin 2} : ∃ c : ℕ,
    D.piM * star D.piM = D.levelPrime i * c ∧ (D.levelPrime i).Coprime c := by
  have h_ne : i ≠ i.rev := by fin_cases i <;> decide
  have h_coprime : (D.levelPrime i).Coprime (D.levelPrime i.rev) :=
    (coprime_primes (D.levelPrime_prime i) (D.levelPrime_prime i.rev)).2
      (D.levelPrime_injective.ne h_ne)
  have h_prod : D.M = D.levelPrime i * D.levelPrime i.rev := by
    fin_cases i <;> simp [M, mul_comm]
  exact ⟨D.levelPrime i.rev, by rw [piM_mul_star, h_prod, Nat.cast_mul], h_coprime⟩

/-- If a finite place w of E is chosen, that is, its prime ideal contains `D.piM` (an integer of E
whose product with its complex conjugate is p₀p₁), then w lies above one of the two primes
p₀ = `D.levelPrime 0`, p₁ = `D.levelPrime 1` of the data `D`. -/
lemma exists_levelPrime_mem_of_isChosen (hw : D.IsChosen w) :
    ∃ i : Fin 2, ↑(D.levelPrime i) ∈ w.asIdeal := by
  -- The prime `w` contains `D.piM * star D.piM = p₀ p₁`, hence one of the two factors.
  have h_mem : D.piM * star D.piM ∈ w.asIdeal := mul_mem_right _ _ hw
  rw [piM_mul_star, M, Nat.cast_mul] at h_mem
  exact Fin.exists_fin_two.2 (w.isPrime.mem_or_mem h_mem)

/-- A finite place w of E whose prime ideal contains `D.piM` (`D.IsChosen w`) lies above p₀ or p₁.
So the set of such places is the union over i = 0, 1 of the places that contain both `D.piM` and p_i
(`D.ChosenPlace i`). -/
lemma isChosen_iff : D.IsChosen w ↔ ∃ i : Fin 2, D.IsChosen w ∧ ↑(D.levelPrime i) ∈ w.asIdeal :=
  ⟨fun hw ↦ (D.exists_levelPrime_mem_of_isChosen hw).imp fun _ h_mem ↦ ⟨hw, h_mem⟩,
    fun ⟨_, hw, _⟩ ↦ hw⟩

/-- If a finite place w of E lies above the prime p_i = `D.levelPrime i` of the data, then its
absolute norm `w.q`, the number of elements of the residue field, equals p_i; that is, w has residue
degree one. -/
lemma q_eq_levelPrime (hw : ↑(D.levelPrime i) ∈ w.asIdeal) : w.q = D.levelPrime i :=
  q_eq_of_modEq_one (D.levelPrime_modEq_one i) hw

lemma finite_isChosen : {w : FinPlace D.E | D.IsChosen w}.Finite := by
  simp [IsChosen, ← dvd_span_singleton, finite_factors]

/-! ### The residue characters ω -/

/-- Let w be a chosen place of E: its prime ideal contains `D.piM`, the complex conjugate of the
integer `D.piMBar` of K of norm p₀p₁. Then the residue field at w has a complex multiplicative
character `T` of order q₂², where q₂ = `P.q₂ D.towerExp` is (q₀d)^(s+6) for s = `D.towerExp`. -/
lemma exists_mulChar_orderOf_eq_sq_of_isChosen (hw : D.IsChosen w) :
    ∃ T : MulChar (ResField w) ℂ, orderOf T = P.q₂ D.towerExp ^ 2 := by
  -- The residue field has `p_i` elements for some `i`, and `q₂ ^ 2 ∣ p_i - 1`.
  obtain ⟨i, h_mem⟩ : ∃ i : Fin 2, ↑(D.levelPrime i) ∈ w.asIdeal :=
    D.exists_levelPrime_mem_of_isChosen hw
  have h_dvd : P.q₂ D.towerExp ^ 2 ∣ Fintype.card (ResField w) - 1 := by
    simpa [← Nat.card_eq_fintype_card, card_ResField, D.q_eq_levelPrime h_mem] using
      D.dvd_levelPrime_sub_one i
  exact exists_mulChar_orderOf _ h_dvd (Complex.isPrimitiveRoot_exp _ (NeZero.ne _))

/-- A fixed complex multiplicative character of order q₂² of the residue field at a chosen place. -/
def chiMLocalRoot (h : D.IsChosen w) : MulChar (ResField w) ℂ :=
  (D.exists_mulChar_orderOf_eq_sq_of_isChosen h).choose

lemma orderOf_chiMLocalRoot (hw : D.IsChosen w) :
    orderOf (D.chiMLocalRoot hw) = P.q₂ D.towerExp ^ 2 :=
  (D.exists_mulChar_orderOf_eq_sq_of_isChosen hw).choose_spec

open scoped Classical in
/-- The residue characters ω_w: at a chosen place the q₂-th power of the character
`New.Data.chiMLocalRoot` of order q₂², and trivial elsewhere. -/
def chiMLocal (w : FinPlace D.E) : MulChar (ResField w) ℂ :=
  if h : D.IsChosen w then D.chiMLocalRoot h ^ P.q₂ D.towerExp else 1

/-- At a chosen place, ω_w = `D.chiMLocal w` is the q₂-th power of the fixed character of order
q₂². -/
lemma chiMLocal_of_isChosen (hw : D.IsChosen w) :
    D.chiMLocal w = D.chiMLocalRoot hw ^ P.q₂ D.towerExp := dite_eq_left hw

lemma orderOf_chiMLocal (hw : D.IsChosen w) : orderOf (D.chiMLocal w) = P.q₂ D.towerExp := by
  rw [D.chiMLocal_of_isChosen hw, orderOf_pow' _ (NeZero.ne _), D.orderOf_chiMLocalRoot hw, sq,
    Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (NeZero.pos _)]

@[simp]
lemma chiMLocal_eq_one_of_not_isChosen (hw : ¬D.IsChosen w) : D.chiMLocal w = 1 := dite_eq_right hw

/-- Let w be a finite place of E and ω_w = `D.chiMLocal w` the character of its residue field that
is the q₂-th power of a fixed character of order q₂² if w divides `D.piM`, and trivial otherwise.
Then ω_w(x) = 1 for every x in the residue field with x^q₁ = 1. -/
lemma chiMLocal_apply_eq_one_of_pow_q₁_eq_one {x : ResField w} (hx : x ^ D.q₁ = 1) :
    D.chiMLocal w x = 1 := by
  by_cases hw : D.IsChosen w
  · -- At a chosen place `D.chiMLocal w` is a `q₂`-th power, and `q₁ ∣ q₂`.
    have h_dvd : D.q₁ ∣ P.q₂ D.towerExp := (dvd_mul_right _ P.d).trans q₁_mul_d_dvd_q₂
    have hx_pow : x ^ P.q₂ D.towerExp = 1 := by
      obtain ⟨c, hc⟩ := h_dvd
      rw [hc, pow_mul, hx, one_pow]
    calc D.chiMLocal w x = D.chiMLocalRoot hw (x ^ P.q₂ D.towerExp) := by
          rw [D.chiMLocal_of_isChosen hw, pow_apply' _ (NeZero.ne _), map_pow]
      _ = 1 := by rw [hx_pow, map_one]
  · have hx_unit : IsUnit x := .of_pow_eq_one hx (NeZero.ne _)
    rw [D.chiMLocal_eq_one_of_not_isChosen hw, one_apply hx_unit]

/-- Let `ψ` give, for each finite place w of E, a complex multiplicative character of the residue
field at w. If `ψ w = 1`, then for every integer n the w-component of ωⁿψ, where ω = `D.chiMLocal`,
raised to the power q₂ = `P.q₂ D.towerExp`, is trivial. -/
lemma chiMLocal_zpow_mul_pow_eq_one {ψ : (w : FinPlace D.E) → MulChar (ResField w) ℂ} (n : ℤ)
    (hψ : ψ w = 1) : (D.chiMLocal ^ n * ψ) w ^ P.q₂ D.towerExp = 1 := by
  by_cases hw : D.IsChosen w
  · simp [hψ, ← D.orderOf_chiMLocal hw]
  · simp [hψ, hw]

/-! ### The characters `chiZero` and `chiM`, and pairs -/

/-- Let γ be an element of `unitary D.E`, that is, γγ̄ = 1 in E, and suppose γ is integral over ℤ.
Then γ is a power of ζ = `P.ζ D.towerExp`, the primitive root of unity of order q₁. -/
lemma exists_zeta_pow_eq_of_isIntegral {γ : unitary D.E} (hγ : IsIntegral ℤ (γ : D.E)) :
    ∃ k : ℕ, P.ζ D.towerExp ^ k = γ := by
  have h_order : IsOfFinOrder (γ : D.E) :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨_, NeZero.pos _, pow_torsionOrder_eq_one γ hγ⟩
  exact (exists_zeta_pow_eq h_order).imp fun _ hk ↦ hk.right

/-- For every k, the product ∏_v γ_v^{w₀(v)} over the infinite places v of E is 1 at γ = ζ^k. Here
γ_v = `New.Φ v γ` is the image of γ under the complex embedding chosen at v, and
ζ = `P.ζ D.towerExp` is the primitive root of unity of order q₁ = `D.q₁` in E. The exponent
w₀(v) = `D.liftWeight 0 v` is the natural number κ(v) + r⁸, where κ(v) = `D.weight v` is a multiple
of q₁ given with the data and r⁸ = `D.halfGap` does not depend on v. -/
lemma prod_phi_zeta_pow_pow_liftWeight_zero_eq_one (k : ℕ) :
    ∏ v : D.Φ, New.Φ v (P.ζ D.towerExp ^ k) ^ D.liftWeight 0 v = 1 := by
  -- The weight `D.liftWeight 0` is `halfGap` mod `q₁` at every place, and `ζ` has norm `1` to `K`.
  have h_weight (v : D.Φ) : D.liftWeight 0 v ≡ D.halfGap [MOD D.q₁] := by
    simpa [liftWeight_eq] using (D.q₁_dvd_weight v).modEq_zero_nat.add_right D.halfGap
  have h_pow : (P.ζ D.towerExp ^ k) ^ D.q₁ = 1 := by
    rw [pow_right_comm, isPrimitiveRoot_zeta.pow_eq_one, one_pow]
  calc _ = ∏ v : D.Φ, New.Φ v ((P.ζ D.towerExp ^ k) ^ D.halfGap) :=
        prod_congr rfl fun v _ ↦ by rw [← map_pow, pow_eq_pow_of_modEq (h_weight v) h_pow]
    _ = Algebra.norm P.K ((P.ζ D.towerExp ^ k) ^ D.halfGap) := prod_phi_eq_norm
    _ = 1 := by simp [norm_zeta_eq_one]

/-- For all natural numbers a and n there is a character μ of U(1)(𝔸), the norm-one adeles of E,
trivial on the elements coming from E, of weight v ↦ -a·w₀(v) and tame part (ω_w^n)_w: for u with
integral finite part, μ(u) = ∏_v u_v^{-a·w₀(v)} · ∏_w ω_w(u mod w)^n, over the infinite places v and
the finite places w. Here w₀(v) = `D.liftWeight 0 v` is the natural number `D.weight v + D.r ^ 8`,
and ω_w = `D.chiMLocal w` is a character of the residue field at w, of order q₂ if w divides `D.piM`
and trivial otherwise. -/
lemma exists_char_hasWeight (a n : ℕ) :
    ∃ μ : AutChar D.E, HasWeight μ (fun v : InfinitePlace D.E ↦ -a * D.liftWeight 0 v)
      (D.chiMLocal ^ n) := by
  -- By `exists_hasWeight_of_prod_eq_one` it suffices that the formula of `HasWeight` gives `1` on
  -- an integer `γ` with `γ γ̄ = 1`. Such a `γ` is a root of unity, hence a power of `ζ`, and
  -- `γ ^ q₁ = 1`.
  refine exists_hasWeight_of_prod_eq_one (S := D.finite_isChosen.toFinset)
    (fun w hw ↦ by simp [D.chiMLocal_eq_one_of_not_isChosen (by simpa using hw)]) fun γ hγ ↦ ?_
  obtain ⟨k, hk⟩ : ∃ k : ℕ, P.ζ D.towerExp ^ k = γ :=
    D.exists_zeta_pow_eq_of_isIntegral (algebraMap_mem_Ô.1 hγ)
  have hγ_pow : (γ : D.E) ^ D.q₁ = 1 := by
    rw [← hk, pow_right_comm, isPrimitiveRoot_zeta.pow_eq_one, one_pow]
  have h_inf : ∏ v : D.Φ, New.Φ v (γ : D.E) ^ (-a * D.liftWeight 0 v : ℤ) = 1 := by
    simp_rw [mul_comm (-a : ℤ), zpow_mul, zpow_natCast, prod_zpow, ← hk,
      D.prod_phi_zeta_pow_pow_liftWeight_zero_eq_one, one_zpow]
  rw [h_inf, one_mul]
  -- At a finite place the residue of `γ` is a `q₁`-th root of unity.
  refine prod_eq_one fun w _ ↦ ?_
  set x : ResField w := reduceAt w ⟨algebraMap D.E (𝔸f D.E) γ, hγ⟩ with x_def
  have hx : x ^ D.q₁ = 1 := by simp [x_def, ← map_pow, hγ_pow, ← OneMemClass.one_def]
  obtain ⟨u, hu⟩ : IsUnit x := .of_pow_eq_one hx (NeZero.ne _)
  rw [← hu, Pi.pow_apply, pow_apply_coe, hu, D.chiMLocal_apply_eq_one_of_pow_q₁_eq_one hx, one_pow]

/-- A fixed character of U(1)(𝔸), trivial on rational points, of weight −w₀ (`New.Data.liftWeight`
at j = 0) and trivial tame part. -/
def chiZero : AutChar D.E := (D.exists_char_hasWeight 1 0).choose

/-- A fixed character of U(1)(𝔸), trivial on rational points, of weight 0 and tame part ω
(`New.Data.chiMLocal`). -/
def chiM : AutChar D.E := (D.exists_char_hasWeight 0 1).choose

lemma chiZero_hasWeight :
    D.chiZero.HasWeight (fun v : InfinitePlace D.E ↦ -D.liftWeight 0 v) 1 := by
  simpa [chiZero] using (D.exists_char_hasWeight 1 0).choose_spec

lemma chiM_hasWeight : D.chiM.HasWeight 0 D.chiMLocal := by
  simpa [chiM, Pi.zero_def] using (D.exists_char_hasWeight 0 1).choose_spec

/-- A pair: an integer 1 ≤ z ≤ t and a character ν of U(1)(𝔸) of weight −c, with z ≤ c(v) ≤ 4b at
every infinite place v and tame part supported on the chosen places. Here t = `D.t` is the natural
number 5r, r the rank of the target, and b = `D.b` is the real scale b of the data, the weight at
the b-places. -/
structure CriticalPair where
  /-- The character ν of `U(1)(𝔸)`, trivial on rational points. -/
  character : AutChar D.E
  /-- The function c: minus the weight of ν at each infinite place. -/
  negWeight : D.Φ → ℕ
  /-- The tame part ψ of ν: a character of the residue field at each finite place. -/
  tamePart : (w : New.FinPlace D.E) → MulChar (ResField w) ℂ
  /-- The integer of the pair, a lower bound for c. -/
  z : ℕ
  /-- ν has weight -c and tame part ψ. -/
  hasWeight : character.HasWeight (fun v : D.Φ ↦ -negWeight v) tamePart
  /-- The tame part is trivial off the chosen places. -/
  tamePart_eq_one (w : New.FinPlace D.E) (hw : ¬D.IsChosen w) : tamePart w = 1
  /-- `1 ≤ z ≤ t`. -/
  z_mem : z ∈ Set.Icc 1 D.t
  /-- c is at least `z` at every infinite place. -/
  le_negWeight (v : D.Φ) : z ≤ negWeight v
  /-- c is at most `4 b` at every infinite place. -/
  negWeight_le (v : D.Φ) : negWeight v ≤ 4 * D.b

end New.Data

/-!
## Finiteness of pairs

The type `New.Data.CriticalPair` is finite. The input is the finiteness of the set of characters of
a given weight and tame part (`New.AutChar.finite_setOf_hasWeight`).
-/

section FinitePairs

open Set New AutChar Data CriticalPair

/-- There are finitely many pairs for the data `D`: an integer `z ∈ [1, t]` with a character of
`U(1)(𝔸)` of weight `-c`, `z ≤ c v ≤ 4 b`, whose tame part is trivial off the chosen places. -/
instance New.Data.finite_criticalPair {P : Parameters} {D : Data P} : Finite D.CriticalPair := by
  -- The weight, the integer `z` and the tame part range over finite sets, and there are finitely
  -- many characters of a given weight and tame part.
  let S : Finset (FinPlace D.E) := D.finite_isChosen.toFinset
  let data (p : D.CriticalPair) :
      Iic (fun _ : D.Φ ↦ ⌊4 * D.b⌋₊) × Icc 1 D.t × ∀ w : S, MulChar (ResField w.val) ℂ :=
    (⟨p.negWeight, fun v ↦ Nat.le_floor (p.negWeight_le v)⟩, ⟨p.z, p.z_mem⟩, S.restrict p.tamePart)
  have h_data {p q : D.CriticalPair} (h_eq : data p = data q) :
    p.negWeight = q.negWeight ∧ p.z = q.z ∧ p.tamePart = q.tamePart := by
    obtain ⟨hc, hz, hψ⟩ : p.negWeight = q.negWeight ∧ p.z = q.z ∧ S.restrict p.tamePart = S.restrict
      q.tamePart := by
      simpa [data, Subtype.ext_iff] using h_eq
    refine ⟨hc, hz, funext fun w ↦ ?_⟩
    by_cases hw : D.IsChosen w
    · exact congrFun hψ ⟨w, by simpa [S] using hw⟩
    · rw [p.tamePart_eq_one w hw, q.tamePart_eq_one w hw]
  rw [← finite_univ_iff]
  refine .of_finite_fibers data (toFinite _) ?_
  rintro _ ⟨p, -, rfl⟩
  refine .of_finite_image (f := CriticalPair.character)
    ((finite_setOf_hasWeight (fun v : D.Φ ↦ -p.negWeight v) p.tamePart).subset ?_) ?_
  · rintro _ ⟨q, ⟨-, hq⟩, rfl⟩
    obtain ⟨hc, -, hψ⟩ := h_data hq
    rw [← hc, ← hψ]
    exact q.hasWeight
  · -- Two pairs with the same data and the same character agree; the other fields are proofs.
    rintro q ⟨-, hq⟩ q' ⟨-, hq'⟩ hν
    obtain ⟨hc, hz, hψ⟩ := h_data (hq.trans hq'.symm)
    cases q
    cases q'
    congr

end FinitePairs

/-! ## Bounds for the different and the root discriminant at infinity -/

namespace New.Parameters

open Real Polynomial NeZero Finset NumberField

variable {P : Parameters} {s : ℕ}

/-- At every infinite place `v` of `E = P.E s`, the generator `δ = P.deltaE s` of the different has
`|δ|_v = A * towerDeg s * √d` for some `A > 0` with `|log A| ≤ P.constantBound`. Here `d = P.d` is
the prime with `K = ℚ(√-d)`, `towerDeg s = q₁ / q₀` is the quotient of the orders of the roots of
unity `ζ` and `ζ ^ towerDeg s`, `q₀ = P.q₀` the fixed modulus, and `P.constantBound` is a sum of
constants that depend only on `q₀` and `d`. -/
lemma exists_abs_log_le_and_apply_deltaE_eq (v : P.Φ s) :
    ∃ A : ℝ, 0 < A ∧ |log A| ≤ P.constantBound ∧ v (P.deltaE s).val = A * towerDeg s * √P.d := by
  -- The cyclotomic polynomial of order `q₁` is `P₀(X ^ towerDeg s)`, `P₀` that of order `q₀`, so
  -- `A = |P₀'(ξ)|` for the primitive `q₀`-th root of unity `ξ = ζ ^ towerDeg s`.
  have hζ : IsPrimitiveRoot (v.embedding (P.ζ s)) (P.q₁ s) :=
    isPrimitiveRoot_zeta.map_of_injective v.embedding.injective
  set ξ : ℂ := v.embedding (P.ζ s) ^ towerDeg s with ξ_def
  have hξ : ξ ∈ primitiveRoots P.q₀ ℂ :=
    (mem_primitiveRoots one_le).2 (hζ.pow one_le (mul_comm P.q₀ (towerDeg s)))
  set A : ℝ := ‖(cyclotomic P.q₀ ℂ).derivative.eval ξ‖ with A_def
  -- Chain rule for `P₀(X ^ towerDeg s)` at the image of `ζ`, which has absolute value `1`.
  have h_chain : v.embedding (P.relDifferentGen s) = (cyclotomic P.q₀ ℂ).derivative.eval ξ *
      (towerDeg s * v.embedding (P.ζ s) ^ (towerDeg s - 1)) :=
    calc _ = (cyclotomic (P.q₁ s) ℂ).derivative.eval (v.embedding (P.ζ s)) := by
          simp [← eval_map_apply, ← derivative_map]
      _ = _ := by simp [← expand_towerDeg_cyclotomic, derivative_expand, ξ_def]
  have h_relDiff : v (P.relDifferentGen s) = A * towerDeg s := by
    simp [← v.norm_embedding_eq, h_chain, A_def, hζ.norm'_eq_one NeZero.out]
  have hA_pos : 0 < A := by
    simpa [h_relDiff, NeZero.pos] using v.pos_iff.2 (P.relDifferentGen_ne_zero s)
  -- `|log A|` is one of the terms of the sum in `P.constantBound`.
  have h_term :
      |log A| ≤ ∑ w ∈ primitiveRoots P.q₀ ℂ, |log ‖(cyclotomic P.q₀ ℂ).derivative.eval w‖| :=
    single_le_sum (f := fun w : ℂ ↦ |log ‖(cyclotomic P.q₀ ℂ).derivative.eval w‖|)
      (fun _ _ ↦ abs_nonneg _) hξ
  refine ⟨A, hA_pos, h_term.trans ?_, by rw [infinitePlace_apply_deltaE, h_relDiff]⟩
  rw [constantBound, ← add_assoc]
  exact le_add_of_nonneg_left (by positivity)

/-- At every infinite place `v` of `E = P.E s`, the absolute value of the generator `P.deltaE s` of
the different has the order of magnitude of the root discriminant `rootDiscr (P.E s)` (this is
`D.rootDisc` for data `D` of exponent `s`): their logarithms differ by at most
`2 * P.constantBound`. -/
theorem abs_log_deltaE_sub_log_rootDiscr_le (v : P.Φ s) :
    |log (v (P.deltaE s).val) - log (rootDiscr (P.E s))| ≤ 2 * P.constantBound := by
  -- All `log |δ|_w`, `δ = P.deltaE s`, are within `P.constantBound` of one number `Q`, and so is
  -- their mean.
  let Q : ℝ := log (towerDeg s * √P.d)
  let f : ℕ := Core.numInfPlaces (P.E s)
  have hQ_ne : (towerDeg s * √P.d : ℝ) ≠ 0 := by simp [NeZero.ne]
  have h_place (w : P.Φ s) : w (P.deltaE s).val ≠ 0 ∧ |log (w (P.deltaE s).val) - Q| ≤
    P.constantBound := by
    obtain ⟨A, hA, h_log, h_eq⟩ := exists_abs_log_le_and_apply_deltaE_eq w
    rw [h_eq, mul_assoc, log_mul hA.ne' hQ_ne, add_sub_cancel_right]
    exact ⟨mul_ne_zero hA.ne' hQ_ne, h_log⟩
  have h_sum : f * (log (rootDiscr (P.E s)) - Q) = ∑ w : P.Φ s, (log (w (P.deltaE s).val) - Q) := by
    simp [f, ← log_prod fun w _ ↦ (h_place w).left, prod_deltaE_eq_rootDiscr_pow, mul_sub]
  have h_mean : |log (rootDiscr (P.E s)) - Q| ≤ P.constantBound := by
    refine le_of_mul_le_mul_left ?_ (mod_cast NeZero.pos f : (0 : ℝ) < f)
    calc _ = |∑ w : P.Φ s, (log (w (P.deltaE s).val) - Q)| := by rw [← h_sum, abs_mul, Nat.abs_cast]
      _ ≤ ∑ _w : P.Φ s, P.constantBound := by grw [abs_sum_le_sum_abs, (h_place _).right]
      _ = f * P.constantBound := by simp [f, Core.numInfPlaces]
  calc _ ≤ |log (v (P.deltaE s).val) - Q| + |Q - log (rootDiscr (P.E s))| := abs_sub_le _ Q _
    _ ≤ 2 * P.constantBound := by grw [(h_place v).right, abs_sub_comm, h_mean, two_mul]

end New.Parameters

namespace New.Data

open Real Polynomial NeZero Parameters Finset

variable {P : Parameters} (D : Data P)

/-- At every infinite place `v : D.Φ` of the field `E` of exponent `s = D.towerExp`, the generator
`δ = P.deltaE s` of the different has `|δ|_v` in `[x ^ 10, x ^ 12]`, where `x = exp D.logX` is the
smallest of the three scales `x`, `x₁`, `b` of the data: the upper bound for `u = true`, the lower
bound for `u = false`. -/
instance hasLogBound_deltaE (v : D.Φ) (u : Bool) :
    D.HasLogBound u (v (P.deltaE D.towerExp)) ((if u then 12 else 10) * D.logX) := by
  -- The term `log A`, bounded by `P.constantBound`, is negligible against `log x`, while
  -- `towerDeg s` has size about `x ^ 11`.
  obtain ⟨A, hA, h_log, h_eq⟩ := exists_abs_log_le_and_apply_deltaE_eq v
  rw [h_eq, ← exp_log hA]
  -- Instance search bounds the product `exp (log A) * towerDeg s * √d` factor by factor. The
  -- sum of the exponents is compared with `10 log x` and `12 log x` by `h_log` and
  -- `D.scale_inequalities`.
  exact .of_lower_of_upper (by cases u <;> grind [D.scale_inequalities])

/-- The root discriminant `rd_E = D.rootDisc` of the field `E = D.E` lies in `[x ^ 10, x ^ 12]`. -/
lemma rootDisc_mem_Icc : D.rootDisc ∈ Set.Icc (D.x ^ 10) (D.x ^ 12) := by
  have h_prod : D.rootDisc ^ D.f = ∏ v : D.Φ, v (P.deltaE D.towerExp) :=
    prod_deltaE_eq_rootDiscr_pow.symm
  have h_lower (v : D.Φ) : D.x ^ 10 ≤ v (P.deltaE D.towerExp) := by
    simpa [← exp_nat_mul] using D.hasLogLower_iff.1 (D.hasLogBound_deltaE v false)
  have h_upper (v : D.Φ) : v (P.deltaE D.towerExp) ≤ D.x ^ 12 := by
    simpa [← exp_nat_mul] using le_of_abs_le (D.hasLogUpper_iff.1 (D.hasLogBound_deltaE v true))
  -- Compare `f`-th powers, `f` the number of infinite places.
  constructor
  · refine le_of_pow_le_pow_left₀ (ne D.f) (rootDiscr_pos D.E).le ?_
    grw [h_prod, ← h_lower, prod_const, card_univ]
  · refine le_of_pow_le_pow_left₀ (ne D.f) (by positivity) ?_
    grw [h_prod, h_upper, prod_const, card_univ]

/-- The root discriminant of `E` has the upper exponent `12 log x` (`u = true`) and the lower
exponent `10 log x` (`u = false`), where `log x = D.logX`. -/
instance hasLogBound_rootDisc (u : Bool) :
    D.HasLogBound u D.rootDisc ((if u then 12 else 10) * D.logX) :=
  .of_mem_Icc (D.x ^ 10) (D.x ^ 12) D.rootDisc_mem_Icc (by cases u <;> simp)

end New.Data

end
