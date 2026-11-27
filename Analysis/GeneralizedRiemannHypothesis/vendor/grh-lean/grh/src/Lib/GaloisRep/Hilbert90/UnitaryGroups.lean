import Lib.GaloisRep.Hilbert90.TameActions

/-!
# Hilbert 90 for unitary groups over profinite rings and for finite ideles

This file proves Hilbert 90 for the unitary group over a profinite ring, with a congruence modulo
`m`. On the way it constructs fixed units in `O[X]/Q`
(`New.exists_fixed_isUnit_pow_mul_one_add_mul_eq_pow`) and orthonormal frames fixed by `τ` for
invertible hermitian matrices (`New.exists_fixed_orthonormal_frame`). It also proves Hilbert 90 for
the finite ideles of `L`, for an automorphism `σ` of `L/K` acting through `New.adeleMap`. This
follows from Galois descent for the semilinear map `x ↦ u * σ x`, together with the fact that two of
its fixed points have a common divisor that is again fixed.

The main results `New.exists_fixed_orthonormal_frame` and `New.unitary_hilbert90_at_level` share
these hypotheses: `New.IsProfiniteRing O` (`O` is profinite); `New.IsTameAtLevel τ p 0`, which says
that `τ ^ p = 1`, `0 < p` and some element has trace `1`; `τ` commutes with `star` and fixes `c`,
and `c - star c` is a unit.

The lemmas before them concern the polynomial `X * (-w) ^ k`, for an inverse `w` of `1 + m X` modulo
`Q`, and endomorphisms of `O[X]/Q`; they state their own hypotheses.

## Main definitions and results

* `New.unitary_hilbert90_at_level`: Hilbert 90 for the unitary group, with a congruence modulo `m`.
* `New.hilbert90_finite_idele`: Hilbert 90 for the finite ideles, for an automorphism of `L/K`.

Notions from other files:
* `New.IsTameAtLevel σ p m`: `σ ^ p = 1` with `0 < p`, `σ m = m`, some element has trace `1` modulo
  `m`, and no `σ ^ i` with `0 < i < p` is trivial modulo a prime not containing `m`.
* `New.IsProfiniteRing R`: every sequence has a unique limit modulo each natural number `M ≠ 0`,
  along the hyperfilter.

## Relation to the literature

Known; see `Lib.GaloisRep.Hilbert90.TameActions` for sources.
-/

/-!
## Hilbert 90 for unitary groups over profinite rings
-/

section UnitaryHilbert90

open Matrix Polynomial AdjoinRoot Finset Ideal New.U RingHom

namespace New

variable {O n : Type*} [CommRing O] [Fintype n] [DecidableEq n] [StarRing O] {τ : O →+* O} {p : ℕ}

omit [StarRing O] in
/-- Let `g` be a ring endomorphism of `O` and `s` a polynomial such that `Q` divides
`(Q.map g).comp s`. Then `q ↦ (q.map g).comp s` passes to a ring endomorphism `θ` of `O[X]/Q`. -/
lemma exists_adjoinRoot_map_comp {Q : O[X]} (g : O →+* O) (s : O[X]) (hs : Q ∣ (Q.map g).comp s) :
    ∃ θ : AdjoinRoot Q →+* AdjoinRoot Q, ∀ q : O[X],
      θ (AdjoinRoot.mk Q q) = AdjoinRoot.mk Q ((q.map g).comp s) := by
  have h_le : span {Q} ≤ (span {Q}).comap (s.compRingHom.comp (mapRingHom g)) := by
    simpa [mem_span_singleton] using hs
  exact ⟨quotientMap _ _ h_le, fun q ↦ quotientMap_mk⟩

omit [StarRing O] in
/-- If `w` inverts `1 + m X` modulo `Q`, that is `a * Q + w * (1 + m X) = 1`, and `k ≤ 1`, then at
a root `B` of `Q` in an `O`-algebra `A`, any `C` with `C * (1 + m B) ^ k = (-1) ^ k * B` is the
value of `X * (-w) ^ k` at `B`. -/
private lemma aeval_X_mul_neg_pow_eq_of_mul_one_add_smul_pow_eq {A : Type*} [Ring A] [Algebra O A]
    {m : O} {Q a w : O[X]} (hw₀ : a * Q + w * (1 + m • X) = 1) {k : ℕ} (hk : k ≤ 1) {B C : A}
    (hB : Q.aeval B = 0) (hC : C * (1 + m • B) ^ k = (-1) ^ k * B) :
    (X * (-w) ^ k).aeval B = C := by
  rw [mul_comm w] at hw₀
  have h_inv : (1 + m • B) * aeval B w = 1 := by simpa [hB] using congrArg (aeval B) hw₀
  interval_cases k
  · simpa using hC.symm
  · calc (X * (-w) ^ 1).aeval B = (-1) ^ 1 * B * aeval B w := by simp
      _ = C * ((1 + m • B) ^ 1 * aeval B w) := by rw [← hC, mul_assoc]
      _ = C := by rw [pow_one, h_inv, mul_one]

omit [StarRing O] in
/-- If `θ` acts on `O[X]/Q` by applying `τ` to the coefficients, then its `i`-th iterate applies
`τ ^ i`. -/
private lemma iterate_mk_eq_mk_map_pow {Q : O[X]} {θ : AdjoinRoot Q →+* AdjoinRoot Q}
    (hθ : ∀ q : O[X], θ (mk Q q) = mk Q (q.map τ)) (i : ℕ) (q : O[X]) :
    θ^[i] (mk Q q) = mk Q (q.map (τ ^ i)) := by
  induction i generalizing q with
  | zero => simp [RingHom.one_def]
  | succ i ih => simp [hθ, ih, Polynomial.map_map, pow_succ, RingHom.mul_def]

omit [StarRing O] in
/-- If `θ` acts on `O[X]/Q` by applying `τ` to the coefficients and `τ` is tame at level `x`
(`New.IsTameAtLevel`), then `θ` is tame at level `x`, viewed as a constant of `O[X]/Q`. -/
private lemma isTameAtLevel_adjoinRoot_of_forall_mk_eq_mk_map {Q : O[X]}
    {θ : AdjoinRoot Q →+* AdjoinRoot Q} (hθ : ∀ q : O[X], θ (mk Q q) = mk Q (q.map τ)) {x : O}
    (h_tame : IsTameAtLevel τ p x) : IsTameAtLevel θ p (AdjoinRoot.of Q x) := by
  have h_semiconj : Function.Semiconj (AdjoinRoot.of Q) τ θ := fun a ↦ by simp [hθ, ← mk_C]
  have hθ_pow : θ ^ p = 1 := by
    refine RingHom.ext fun z ↦ ?_
    obtain ⟨q, rfl⟩ := mk_surjective z
    simp [iterate_mk_eq_mk_map_pow hθ, h_tame.pow_eq_one, RingHom.one_def]
  exact h_tame.of_semiconj (AdjoinRoot.of Q) h_semiconj hθ_pow

/-- Let `Q = charpoly Y`, let `w` invert `1 + m X` modulo `Q`, and let
`Yᴴ * (1 + m Y) ^ k = (-1) ^ k * Y` with `k ≤ 1`. Then `Q` divides `Q̄ ∘ (X * (-w) ^ k)`, where `Q̄`
applies `star` to the coefficients of `Q`: the value of `X * (-w) ^ k` at `Y` is `Yᴴ`, whose
characteristic polynomial is `Q̄`, and `charpoly Y` divides `(charpoly q(Y)).comp q` for every `q`.
-/
private lemma dvd_map_comp_X_mul_neg_pow_of_charpoly_eq {Y : Matrix n n O} {m : O} {Q a w : O[X]}
    (hQ : Y.charpoly = Q) (hw₀ : a * Q + w * (1 + m • X) = 1) {k : ℕ} (hk : k ≤ 1)
    (hY_rel : Yᴴ * (1 + m • Y) ^ k = (-1) ^ k * Y) :
    Q ∣ (Q.map (starRingEnd O)).comp (X * (-w) ^ k) := by
  subst hQ
  have h_val : (X * (-w) ^ k).aeval Y = Yᴴ :=
    aeval_X_mul_neg_pow_eq_of_mul_one_add_smul_pow_eq hw₀ hk Y.aeval_self_charpoly hY_rel
  have h_conj : Yᵀ.map (starRingEnd O) = Yᴴ := rfl
  have h_char : Yᴴ.charpoly = Y.charpoly.map (starRingEnd O) := by
    rw [← h_conj, charpoly_map, charpoly_transpose]
  have h_dvd := charpoly_dvd_charpoly_aeval_comp (Y := Y) (X * (-w) ^ k)
  rwa [h_val, h_char] at h_dvd

/-- In `O[X]/Q`, let `θ` apply `τ` to the coefficients, and let `ρ` apply `star` to the
coefficients and send `X` to `X * (-w) ^ k`, where `w` inverts `1 + m X` and `τ m = m`. If `τ`
commutes with `star`, then `θ` and `ρ` commute. -/
private lemma commute_of_forall_mk_eq {Q w : O[X]} {m : O} {k : ℕ} (hm : τ m = m)
    (hτ : ∀ x : O, τ (star x) = star (τ x)) {θ ρ : AdjoinRoot Q →+* AdjoinRoot Q}
    (hθ : ∀ q : O[X], θ (mk Q q) = mk Q (q.map τ))
    (hρ : ∀ q : O[X], ρ (mk Q q) = mk Q ((q.map (starRingEnd O)).comp (X * (-w) ^ k)))
    (hw : mk Q w * (1 + mk Q (C m) * mk Q X) = 1) : Commute θ ρ := by
  -- `θ` fixes `1 + m X`, hence also its inverse `w`.
  have hθ_unit : θ (1 + mk Q (C m) * mk Q X) = 1 + mk Q (C m) * mk Q X := by
    simp [hθ, hm, -mk_C, -mk_X]
  have hθw : mk Q (w.map τ) = mk Q w := by
    rw [← hθ]
    refine left_inv_eq_right_inv ?_ ((mul_comm _ _).trans hw)
    rw [← hθ_unit, ← map_mul, hw, map_one]
  refine (commute_iff_eq θ ρ).mpr ?_
  ext a
  · simp [hθ, hρ, hτ, ← mk_C, starRingEnd_apply]
  · simp [hθ, hρ, hθw, ← mk_X]

/-- Let `ρ` apply `star` to the coefficients of `O[X]/Q` and send `X` to `X * (-w) ^ k`, where
`k ≤ 1`, `w` inverts `1 + m X` and `star m = m`. Then `ρ` is an involution. -/
private lemma sq_eq_one_of_forall_mk_eq {Q w : O[X]} {m : O} {k : ℕ} (hk : k ≤ 1)
    (hm_star : star m = m) {ρ : AdjoinRoot Q →+* AdjoinRoot Q}
    (hρ : ∀ q : O[X], ρ (mk Q q) = mk Q ((q.map (starRingEnd O)).comp (X * (-w) ^ k)))
    (hw : mk Q w * (1 + mk Q (C m) * mk Q X) = 1) : ρ ^ 2 = 1 := by
  -- `ρ` applies `star` twice to constants. On `X`, for `k = 1`: `ρ (1 + m X) = 1 - m X w = w`, so
  -- applying `ρ` to `w * (1 + m X) = 1` gives `ρ w * w = 1`, and `ρ (ρ X) = X * (-w) * (-ρ w) = X`.
  have hρ_X : ρ (mk Q X) = mk Q X * (-mk Q w) ^ k := by
    rw [hρ, Polynomial.map_X, X_comp, map_mul, map_pow, map_neg]
  have hρ_Cm : ρ (mk Q (C m)) = mk Q (C m) := by
    rw [hρ, Polynomial.map_C, C_comp, starRingEnd_apply, hm_star]
  interval_cases k
  · ext a
    · simp [hρ, ← mk_C, starRingEnd_apply]
    · simp [hρ_X, ← mk_X]
  · have hρw : ρ (mk Q w) * mk Q w = 1 := by
      have h_image : ρ (mk Q w) * (1 + mk Q (C m) * (mk Q X * (-mk Q w) ^ 1)) = 1 := by
        rw [← hρ_X, ← hρ_Cm, ← map_mul, ← map_one ρ, ← map_add, ← map_mul, hw]
      have h_w : 1 + mk Q (C m) * (mk Q X * (-mk Q w) ^ 1) = mk Q w := by
        linear_combination (-1 : AdjoinRoot Q) * hw
      rwa [h_w] at h_image
    have h_ρρX : ρ (ρ (mk Q X)) = mk Q X := by
      rw [hρ_X, map_mul, map_pow, map_neg, hρ_X]
      linear_combination mk Q X * hρw
    ext a
    · simp [hρ, ← mk_C, starRingEnd_apply]
    · simpa [sq, ← mk_X] using h_ρρX

/-- Descent in the `θ`-fixed part of the profinite ring `O[X]/Q`, for `τ` tame at level `0` fixing
`c` (with `c - star c` a unit), `m` fixed by `τ` and `star`, and `k ≤ 1`. Here `θ` applies `τ` to
the coefficients, and the involution `ρ`, commuting with `θ`, applies `star` to them and sends `X`
to `X * (-w) ^ k`, where `w` inverts `1 + m X`. Some `θ`-fixed unit `g`, the class of
`1 + m X ^ (1 - k) y` with `y` fixed by `θ`, has `g ^ (1 - k) * (1 + m X) * ρ g = g ^ k`. -/
private lemma exists_fixed_isUnit_pow_mul_one_add_mul_eq_pow {m c : O}
    (h_tame_zero : IsTameAtLevel τ p 0) (hc : τ c = c) (hc_unit : IsUnit (c - star c))
    (hm_star : star m = m) (hm : τ m = m) {Q w : O[X]} (h_prof : IsProfiniteRing (AdjoinRoot Q))
    {k : ℕ} (hk : k ≤ 1) {θ ρ : AdjoinRoot Q →+* AdjoinRoot Q}
    (hθ : ∀ q : O[X], θ (mk Q q) = mk Q (q.map τ))
    (hρ : ∀ q : O[X], ρ (mk Q q) = mk Q ((q.map (starRingEnd O)).comp (X * (-w) ^ k)))
    (hw : mk Q w * (1 + mk Q (C m) * mk Q X) = 1) (h_comm : Commute θ ρ) (hρ_sq : ρ ^ 2 = 1) :
    ∃ (y : O[X]) (g : AdjoinRoot Q), mk Q (y.map τ) = mk Q y ∧
      g = mk Q (1 + m • (X ^ (1 - k) * y)) ∧ θ g = g ∧ IsUnit g ∧
      g ^ (1 - k) * (1 + mk Q (C m) * mk Q X) * ρ g = g ^ k := by
  -- The `θ`-fixed subring `F` is profinite, and `ρ` restricts to an involution `r` of `F`, tame at
  -- the level `m X ^ (1 - k)`. Descent along `r` solves the equation: by the norm theorem for
  -- `k = 0`, and by Hilbert 90 for `k = 1`.
  let F : Subring (AdjoinRoot Q) := θ.eqLocus 1
  have h_mem {q : O[X]} (hq : q.map τ = q) : mk Q q ∈ F := (hθ q).trans (congrArg _ hq)
  have hρ_mem (x : AdjoinRoot Q) (hx : x ∈ F) : ρ x ∈ F :=
    (RingHom.congr_fun h_comm.eq x).trans (congrArg ρ hx)
  let r : F →+* F := ρ.restrict F F hρ_mem
  have hr_val (x : F) : (r x : AdjoinRoot Q) = ρ x := rfl
  have hρ_of (a : O) : ρ (AdjoinRoot.of Q a) = AdjoinRoot.of Q (star a) := by
    rw [← mk_C, hρ, Polynomial.map_C, C_comp, starRingEnd_apply, mk_C]
  have hρ_root : ρ (root Q) = root Q * (-mk Q w) ^ k := by
    rw [← mk_X, hρ, Polynomial.map_X, X_comp, map_mul, map_pow, map_neg, mk_X]
  have hCm : (C m).map τ = C m := by rw [Polynomial.map_C, hm]
  -- `N j` is the class of `m X ^ (1 - j)`: `N 0 = m X` and `N 1 = m`
  let N (j : ℕ) : F := ⟨mk Q (C m), h_mem hCm⟩ * ⟨mk Q X, h_mem (map_X τ)⟩ ^ (1 - j)
  have hθ_tame : IsTameAtLevel θ p 0 := by
    simpa using isTameAtLevel_adjoinRoot_of_forall_mk_eq_mk_map hθ h_tame_zero
  have hF_prof : IsProfiniteRing F := h_prof.eqLocus hθ_tame
  have hr_tame : IsTameAtLevel r 2 (N k) := by
    let γ : F := ⟨mk Q (C c), h_mem (q := C c) (by rw [Polynomial.map_C, hc])⟩
    have hr_sq : r ^ 2 = 1 := RingHom.ext fun x ↦ Subtype.ext (RingHom.congr_fun hρ_sq x)
    -- `γ - r γ` is the class of the unit `c - star c`
    have hγ_unit : IsUnit (γ - r γ) :=
      .of_map F.subtype _ (by simp [γ, hr_val, hρ_of, hc_unit, IsUnit.map, ← map_sub])
    have hr_N : r (N k) = N k := by
      interval_cases k
      · simp [N, hr_val, hρ_of, hρ_root, hm_star, Subtype.ext_iff]
      · simp [N, hr_val, hρ_of, hm_star, Subtype.ext_iff]
    exact .of_sq_eq_one_of_isUnit_sub hr_sq hγ_unit hr_N
  have h_mul : mk Q w * ((1 + N 0 : F) : AdjoinRoot Q) = 1 := by simpa [N] using hw
  have hu : IsUnit (1 + N 0) := .of_map F.subtype _ (.of_mul_eq_one_right _ h_mul)
  -- For `k = 0` the unit `1 + m X` is fixed by `r`, hence a norm; for `k = 1` it has norm one,
  -- hence is a coboundary. Either way a unit `g ≡ 1` modulo `N k` splits it along `r`.
  obtain ⟨g, hg_dvd, hg⟩ : ∃ g : Fˣ, N k ∣ g - 1 ∧ g ^ (1 - k) * (1 + N 0) * r g = g ^ k := by
    interval_cases k
    · have hr_fix : r (1 + N 0) = 1 + N 0 := by
        simp [N, hr_val, hρ_of, hρ_root, hm_star, Subtype.ext_iff]
      obtain ⟨z, -, hz_lev, hz⟩ := hr_tame.exists_prod_range_pow_apply_eq (.inr hF_prof) hu hr_fix
        (by simp)
      -- `z⁻¹ * (z * r z) * r z⁻¹ = 1`
      have h_split : ((z⁻¹ : Fˣ) : F) * (1 + N 0) * r ((z⁻¹ : Fˣ) : F) = 1 := by
        simp [← hz, ← map_mul, prod_range_succ]
      exact ⟨z⁻¹, hz_lev, by simpa using h_split⟩
    · -- `r (1 + m X) = 1 - m X w`, and `(1 + m X) * (1 - m X w) = 1` because `w * (1 + m X) = 1`
      have h_norm_one : (1 + N 0) * r (1 + N 0) = 1 := by
        suffices h_val : (1 + mk Q (C m) * mk Q X) * (1 + -(mk Q (C m) * (mk Q X * mk Q w))) = 1 by
          simpa [N, hr_val, hρ_of, hρ_root, hm_star, Subtype.ext_iff] using h_val
        linear_combination -(mk Q (C m) * mk Q X) * hw
      have h_lev : N 1 ∣ (1 + N 0) - 1 := ⟨⟨mk Q X, h_mem (map_X τ)⟩, by simp [N]⟩
      have h_prod : ∏ i ∈ range 2, (r ^ i) (1 + N 0) = 1 := by
        simpa [prod_range_succ] using h_norm_one
      obtain ⟨g, hg_lev, hg⟩ := hr_tame.hilbert90_unit (.inr hF_prof) hu h_lev h_prod
      exact ⟨g, hg_lev, by simpa using hg⟩
  obtain ⟨y₀, hg_lev⟩ : ∃ y₀ : F, (g : F) - 1 = N k * y₀ := hg_dvd
  obtain ⟨y, hy⟩ : ∃ y : O[X], mk Q y = y₀ := mk_surjective (y₀ : AdjoinRoot Q)
  have hy_fix : mk Q (y.map τ) = mk Q y := by
    rw [← hθ, hy]
    exact y₀.prop
  have hg_mk : ((g : F) : AdjoinRoot Q) = mk Q (1 + m • (X ^ (1 - k) * y)) := by
    simpa [N, smul_eq_C_mul, mul_assoc, sub_eq_iff_eq_add', Subtype.ext_iff, hy] using hg_lev
  refine ⟨y, g, hy_fix, hg_mk, (g : F).prop, g.isUnit.map F.subtype, ?_⟩
  simpa [N, hr_val, Subtype.ext_iff] using hg

universe w in
/-- The polynomials `y`, `z`, `z'` over `O` solve the norm equations of
`New.exists_isTwistedRoot_of_charpoly_eq` at an element `B` of an `O`-algebra `A` with `star`. Write
`T` for the value of `1 + m X ^ (1 - k) y` at `B`. -/
structure IsTwistedRoot (τ : O →+* O) (p : ℕ) (m : O) (k : ℕ) {A : Type w} [Ring A] [StarRing A]
    [Algebra O A] (B : A) (y z z' : O[X]) : Prop where
  /-- `y` and `τ y` have the same value at `B`. -/
  aeval_map_eq : (y.map τ).aeval B = y.aeval B
  /-- If `τ` is tame at level `m`, then `1 + m z'` is a left inverse of `1 + m z` at `B`. -/
  aeval_mul_eq_one : IsTameAtLevel τ p m → aeval B ((1 + m • z') * (1 + m • z)) = 1
  /-- If `τ` is tame at level `m`, then `T` is the value of the twisted norm of `1 + m z`. -/
  aeval_twistedNorm_eq : IsTameAtLevel τ p m →
    aeval B (twistedNorm (Polynomial.map τ) p (1 + m • z)) = aeval B (1 + m • (X ^ (1 - k) * y))
  /-- If `B⋆ (1 + m B) ^ k = (-1) ^ k B`, then `T ^ (1 - k) (1 + m B) T⋆ = T ^ k`. -/
  pow_mul_star_eq_pow : star B * (1 + m • B) ^ k = (-1) ^ k * B →
    aeval B (1 + m • (X ^ (1 - k) * y)) ^ (1 - k) * (1 + m • B) *
      star (aeval B (1 + m • (X ^ (1 - k) * y))) = aeval B (1 + m • (X ^ (1 - k) * y)) ^ k

universe w in
/-- Roots in `O[X]/Q`. Let `O` be profinite, let `τ` be tame at level `0` (`τ ^ p = 1`, `0 < p`,
and some element has trace `1`), commute with `star` and fix `c`, with `c - star c` a unit. Let `m`
be fixed by `τ` and `star`, let `1 + m Y` be invertible, with `Y` hermitian (`k = 0`) or with
`Yᴴ (1 + m Y) = -Y` (`k = 1`), and let `Q = charpoly Y` be fixed by `τ`. Then some polynomials
`y`, `z`, `z'` satisfy `New.IsTwistedRoot τ p m k B y z z'` at every root `B` of `Q` in an
`O`-algebra `A` with a compatible `star`. -/
lemma exists_isTwistedRoot_of_charpoly_eq (hO : IsProfiniteRing O) {m c : O}
    (h_tame_zero : IsTameAtLevel τ p 0) (hc : τ c = c) (hc_unit : IsUnit (c - star c))
    (hτ : ∀ x : O, τ (star x) = star (τ x)) {Y : Matrix n n O} (hm_star : star m = m)
    (hm : τ m = m) {Q : O[X]} (hQ : Y.charpoly = Q) (hQτ : Q.map τ = Q) {k : ℕ} (hk : k ≤ 1)
    (hY_rel : Yᴴ * (1 + m • Y) ^ k = (-1) ^ k * Y) (hY_unit : IsUnit (1 + m • Y)) :
    ∃ y z z' : O[X], ∀ ⦃A : Type w⦄ [Ring A] [StarRing A] [Algebra O A] [StarModule O A] ⦃B : A⦄,
      Q.aeval B = 0 → IsTwistedRoot τ p m k B y z z' := by
  -- Work in `O[X]/Q` with two commuting maps: `θ`, acting by `τ` on coefficients, and an
  -- involution `ρ` that becomes `star` at each root `B` obeying the relation of `Y`. Solve for `T`
  -- in the `θ`-fixed ring by tame descent along `ρ`, write it as a norm by tame descent along `θ`,
  -- and evaluate at `B`.
  have h_coprime : IsCoprime Q (1 + m • X) := by
    rw [← hQ, ← isUnit_aeval_iff_isCoprime]
    simpa using hY_unit
  obtain ⟨a, w, hw₀⟩ : ∃ a w : O[X], a * Q + w * (1 + m • X) = 1 := h_coprime
  have hQ_monic : Q.Monic := hQ ▸ Y.charpoly_monic
  obtain ⟨θ, hθ⟩ :
      ∃ θ : AdjoinRoot Q →+* AdjoinRoot Q, ∀ q : O[X], θ (mk Q q) = mk Q (q.map τ) := by
    simpa using exists_adjoinRoot_map_comp (Q := Q) τ X (by rw [comp_X, hQτ])
  have hQ_dvd : Q ∣ (Q.map (starRingEnd O)).comp (X * (-w) ^ k) :=
    dvd_map_comp_X_mul_neg_pow_of_charpoly_eq hQ hw₀ hk hY_rel
  obtain ⟨ρ, hρ⟩ := exists_adjoinRoot_map_comp (starRingEnd O) (X * (-w) ^ k) hQ_dvd
  have hw : mk Q w * (1 + mk Q (C m) * mk Q X) = 1 := by
    simpa [smul_eq_C_mul] using congrArg (mk Q) hw₀
  have h_comm : Commute θ ρ := commute_of_forall_mk_eq hm hτ hθ hρ hw
  have hρ_sq : ρ ^ 2 = 1 := sq_eq_one_of_forall_mk_eq hk hm_star hρ hw
  have h_prof : IsProfiniteRing (AdjoinRoot Q) :=
    hO.of_addEquiv_pi (powerBasisAux' hQ_monic).equivFun.toAddEquiv
  obtain ⟨y, g, hy_fix, hg_mk, hθg, hg_unit, hg_rel⟩ :=
    exists_fixed_isUnit_pow_mul_one_add_mul_eq_pow h_tame_zero hc hc_unit hm_star hm h_prof hk hθ
      hρ hw h_comm hρ_sq
  -- At tame level `m` the `θ`-fixed unit `g ≡ 1 mod m` is a norm along `θ`.
  have hg_lev : AdjoinRoot.of Q m ∣ g - 1 := by simp [hg_mk, ← C_mul']
  have h_norm (ht : IsTameAtLevel τ p m) : ∃ (u : (AdjoinRoot Q)ˣ) (z' z : O[X]),
      (u : AdjoinRoot Q) = 1 + mk Q (m • z) ∧ (↑u⁻¹ : AdjoinRoot Q) = 1 + mk Q (m • z') ∧
      ∏ i ∈ range p, (θ ^ i) u = g := by
    obtain ⟨u, ⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩, hu⟩ :=
      (isTameAtLevel_adjoinRoot_of_forall_mk_eq_mk_map hθ ht).exists_prod_range_pow_apply_eq
        (.inr h_prof) hg_unit
        hθg hg_lev
    -- write the cofactors of `m` in `u - 1` and `u⁻¹ - 1` as classes of polynomials
    obtain ⟨z, rfl⟩ := mk_surjective a₁
    obtain ⟨z', rfl⟩ := mk_surjective b₁
    refine ⟨u, z', z, ?_, ?_, hu⟩
    · simpa [sub_eq_iff_eq_add', ← C_mul'] using ha₁
    · simpa [sub_eq_iff_eq_add', ← C_mul'] using hb₁
  choose! u z' z hz hz' hu_norm using h_norm
  refine ⟨y, z, z', fun A _ _ _ _ B hB ↦ ?_⟩
  -- Evaluate at the root `B` of `Q`, through the map `f` from `O[X]/Q` to `A`.
  let f : AdjoinRoot Q →ₐ[O] A :=
    Quotient.liftₐ _ (aeval B) (by simp [mem_span_singleton', hB])
  have hf (q : O[X]) : f (mk Q q) = q.aeval B := rfl
  refine ⟨?_, fun ht ↦ ?_, fun ht ↦ ?_, fun h_rel ↦ ?_⟩
  · rw [← hf, ← hf, hy_fix]
  · -- `1 + m z'` and `1 + m z` are the classes of `u⁻¹` and `u`
    simp [← hf, ← hz ht, ← hz' ht]
  · -- the twisted norm of `1 + m z` is the class of the `θ`-norm of `u`, which is `g`
    simp [← hf, ← (hu_norm ht).trans hg_mk, twistedNorm_map_eq_prod, hz ht,
      iterate_mk_eq_mk_map_pow hθ]
  · -- `f` turns `ρ` into `star`, since `X * (-w) ^ k` has the value `star B` at `B`.
    have h_star_root : (X * (-w) ^ k).aeval B = star B :=
      aeval_X_mul_neg_pow_eq_of_mul_one_add_smul_pow_eq hw₀ hk hB h_rel
    have hf_ρ (q : O[X]) : f (ρ (mk Q q)) = star (q.aeval B) := by
      rw [hρ, hf, aeval_comp, h_star_root, star_aeval]
    have hf_g : f g = aeval B (1 + m • (X ^ (1 - k) * y)) := by rw [hg_mk, hf]
    have hf_ρ_g : f (ρ g) = star (aeval B (1 + m • (X ^ (1 - k) * y))) := by rw [hg_mk, hf_ρ]
    have h_rel_f : f (g ^ (1 - k) * (1 + mk Q (C m) * mk Q X) * ρ g) = f (g ^ k) :=
      congrArg f hg_rel
    have hf_of (a : O) : f (AdjoinRoot.of Q a) = algebraMap O A a := by rw [← mk_C, hf, aeval_C]
    have hf_root : f (root Q) = B := by rw [← mk_X, hf, aeval_X]
    simpa [hf_g, hf_ρ_g, hf_of, hf_root, ← Algebra.smul_def] using h_rel_f

/-- Orthonormal frame. Let `O` be profinite, let `τ` be tame at level `0` (`τ ^ p = 1`, `0 < p`,
and some element has trace `1`), commute with `star` and fix `c`, with `c - star c` a unit. Then an
invertible hermitian matrix `h` fixed by `τ` has an orthonormal frame fixed by `τ`: a matrix `g`
with `gᴴ h g = 1` and `g.map τ = g`, of the form `g = 1 + W (h - 1)`. -/
lemma exists_fixed_orthonormal_frame (hO : IsProfiniteRing O) {c : O}
    (h_tame_zero : IsTameAtLevel τ p 0) (hc : τ c = c) (hc_unit : IsUnit (c - star c))
    (hτ : ∀ x : O, τ (star x) = star (τ x))
    {h : Matrix n n O} (hh_unit : IsUnit h) (h_herm : hᴴ = h) (h_fixed : h.map τ = h) :
    ∃ g W : Matrix n n O, g = 1 + W * (h - 1) ∧ g.map τ = g ∧ gᴴ * h * g = 1 := by
  -- Apply `exists_isTwistedRoot_of_charpoly_eq` with `m = 1`, `k = 0`, `Y = h - 1` at the root
  -- `B = h - 1`: it gives `T = 1 + (h - 1) * y(h - 1)` with `T * h * Tᴴ = 1`, and `g = Tᴴ`.
  have h_charpoly : (h - 1).charpoly.map τ = (h - 1).charpoly := by
    simp [← charpoly_map, h_fixed, Matrix.map_sub]
  have h_rel : (h - 1)ᴴ * (1 + (1 : O) • (h - 1)) ^ 0 = (-1) ^ 0 * (h - 1) := by simpa
  obtain ⟨y, _z, _z', hy⟩ := exists_isTwistedRoot_of_charpoly_eq hO h_tame_zero hc hc_unit hτ
    (star_one _) τ.map_one
    (Y := h - 1) rfl h_charpoly (k := 0) bot_le h_rel (by simpa)
  -- `y` is fixed by `τ` at `h - 1`, and `T * h * Tᴴ = 1`
  obtain ⟨hy_fix, -, -, h_polar⟩ := hy (h - 1).aeval_self_charpoly
  refine ⟨1 + (y.aeval (h - 1))ᴴ * (h - 1), (y.aeval (h - 1))ᴴ, rfl, ?_, ?_⟩
  · simp [conjTranspose_map _ hτ, map_aeval_matrix, h_fixed, hy_fix, Matrix.map_add, Matrix.map_sub]
  · -- `g` is `Tᴴ`, as `h - 1` is hermitian
    simpa [h_herm, star] using h_polar

/-- Hilbert 90 for the unitary group `U 1` (matrices with `gᴴ g = 1`) at level `m`. Let `O` be
profinite, let `τ` be tame at level `0` and at level `m`, commute with `star` and fix `c`, with
`c - star c` a unit, and let `star m = m`. Tame at level `m` means: `τ m = m`, `τ ^ p = 1`, `0 < p`,
some `e` has `∑ i < p, τ^i e ≡ 1` mod `m`, and every prime modulo which some `τ^i` with `0 < i < p`
is the identity contains `m`. If the unitary `s` is `1 + m Y` and its twisted norm
`s · τ s ⋯ τ^{p-1} s` is `1` (`mapEnd hτ` applies `τ` to the entries), then `s · τ g = g`, that is
`s = g · (τ g)⁻¹`, for a unitary `g = 1 + m W`. -/
lemma unitary_hilbert90_at_level (hO : IsProfiniteRing O) {m c : O}
    (h_tame_zero : IsTameAtLevel τ p 0) (hc : τ c = c) (hc_unit : IsUnit (c - star c))
    (hτ : ∀ x : O, τ (star x) = star (τ x)) (s : U (1 : Matrix n n O)) {Y : Matrix n n O}
    (hm_star : star m = m) (h_tame : IsTameAtLevel τ p m) (hs : (s : Matrix n n O) = 1 + m • Y)
    (hs_norm : ((twistedNorm (mapEnd hτ) p s : U (1 : Matrix n n O)) : Matrix n n O) = 1) :
    ∃ (g : U (1 : Matrix n n O)) (W : Matrix n n O),
      s * mapEnd hτ g = g ∧ (g : Matrix n n O) = 1 + m • W := by
  -- Split `s` in `GL n O` by some `k ≡ 1 mod m`, then correct `k` to a unitary `k * g` by a
  -- `τ`-fixed orthonormal frame `g` of the hermitian matrix `kᴴ * k`.
  have h_norm : twistedNorm (GeneralLinearGroup.map τ) p (s : GL n O) = 1 :=
    (map_twistedNorm (U 1).subtype (fun g ↦ rfl) p s).symm.trans (Units.ext hs_norm)
  obtain ⟨k, W, hk_cob, hk⟩ := h_tame.hilbert90_gl (.inr hO) (s : GL n O) hs h_norm
  -- `kᴴ * k` is fixed by `τ` because `sᴴ * s = 1`.
  have h_prod : ((s : Matrix n n O) * k.val.map τ)ᴴ * ((s : Matrix n n O) * k.val.map τ) =
      k.valᴴ * k.val := by rw [hk_cob]
  have h_fix : (k.valᴴ * k.val).map τ = k.valᴴ * k.val := by
    simpa [conjTranspose_map _ hτ, ← inv_val_eq_conjTranspose, mul_assoc] using h_prod
  have hkk_unit : IsUnit (k.valᴴ * k.val) := (star k * k).isUnit
  obtain ⟨g, V, hg, hg_fix, hg_frame⟩ :=
    exists_fixed_orthonormal_frame hO h_tame_zero hc hc_unit hτ hkk_unit (by simp) h_fix
  have h_lev : k.valᴴ * k.val - 1 = m • (W + Wᴴ * k.val) := by
    simp [hk, hm_star, mul_add, add_mul, smul_add, smul_smul, add_comm, add_left_comm, add_assoc,
      sub_eq_iff_eq_add']
  refine ⟨of isUnit_one (k.val * g) (by simpa [conjTranspose_mul, Matrix.mul_assoc] using hg_frame),
    W + k.val * V * (W + Wᴴ * k.val), ?_, ?_⟩
  · -- on matrices, `s * τ (k g) = (s * τ k) * τ g = k * g`
    simp [Units.ext_iff, U.map, ← mul_assoc, hk_cob, hg_fix, Subtype.ext_iff]
  · calc k.val * g = k.val + m • (k.val * V * (W + Wᴴ * k.val)) := by
          simp [hg, h_lev, mul_add, mul_assoc]
      _ = 1 + m • (W + k.val * V * (W + Wᴴ * k.val)) := by rw [smul_add, ← add_assoc, ← hk]

end New

end UnitaryHilbert90

/-!
## Hilbert 90 for finite ideles

`New.hilbert90_finite_idele` is Hilbert's Theorem 90 for the finite adeles of `L` and an
automorphism `σ` of `L/K`, acting through `New.adeleMap`. It follows from Galois descent for the
semilinear map `x ↦ u * σ x`, together with the fact that two of its fixed points have a common
divisor that is again fixed.
-/

section IdeleHilbert90

open AlgEquiv Valued

namespace New

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L] {σ : Gal(L/K)} {u : 𝔸f L}

/-- The `i`-th iterate of the action of `σ` on finite adeles is the action of `σ ^ i`. -/
lemma adeleMap_gal_pow (i : ℕ) :
    adeleMap (σ : L →+* L) ^ i = adeleMap (↑(σ ^ i) : L →+* L) := by
  induction i with
  | zero =>
    ext1 x
    simp [aut_one]
  | succ i ih =>
    ext1 x
    rw [pow_succ, RingHom.coe_mul, Function.comp_apply, ih, adeleMap_adeleMap, pow_succ]
    rfl

/-- Let `a` and `b` be finite adeles of `L` that solve `u * σ x = x`, where `σ` acts through
`New.adeleMap`. Then some solution `c` divides both: at each place take whichever of `a`, `b` has
the larger valuation. -/
lemma exists_dvd_dvd_mul_adeleMap_eq {a b : 𝔸f L} (ha : u * adeleMap (σ : L →+* L) a = a)
    (hb : u * adeleMap (σ : L →+* L) b = b) :
    ∃ c : 𝔸f L, c ∣ a ∧ c ∣ b ∧ u * adeleMap (σ : L →+* L) c = c := by
  let c : 𝔸f L := b + idem {w | v (b w) ≤ v (a w)} * (a - b)
  have c_apply (w : FinPlace L) : c w = if v (b w) ≤ v (a w) then a w else b w := by
    by_cases h : v (b w) ≤ v (a w) <;> simp [c, h]
  have dvd_of_le {x : 𝔸f L} (hx : ∀ w : FinPlace L, v (x w) ≤ v (c w)) : c ∣ x := by
    obtain ⟨y, -, hy⟩ := exists_eq_mul_iff_v_le.mpr hx
    exact ⟨y, hy⟩
  have ha_le (w : FinPlace L) : v (a w) ≤ v (c w) := by grind
  have hb_le (w : FinPlace L) : v (b w) ≤ v (c w) := by simp [c_apply, apply_ite]
  refine ⟨c, dvd_of_le ha_le, dvd_of_le hb_le, DFunLike.ext _ _ fun w ↦ ?_⟩
  have haw : u w * adeleMap (σ : L →+* L) a w = a w := by rw [← finAdele_mul_apply, ha]
  have hbw : u w * adeleMap (σ : L →+* L) b w = b w := by rw [← finAdele_mul_apply, hb]
  change u w * adeleMap (σ : L →+* L) c w = c w
  by_cases hw : u w = 0
  · -- both `a` and `b`, hence `c`, vanish at a zero of `u`
    have ha_zero : a w = 0 := by rw [← haw, hw, zero_mul]
    simp [c_apply, hw, ha_zero, show b w = 0 by rw [← hbw, hw, zero_mul]]
  · rw [adeleMap_apply (σ : L →+* L) rfl] at haw hbw ⊢
    -- Since `σ` preserves valuations, the choice at `w` agrees with that at the pullback of `w`.
    have h_choice : v (b w) ≤ v (a w) ↔
        v (b (FinPlace.comap (σ : L →+* L) w)) ≤ v (a (FinPlace.comap (σ : L →+* L) w)) := by
      rw [← haw, ← hbw]
      simp [zero_lt_iff, hw, v_locMap_eq_of_surjective (σ : L →+* L) rfl σ.surjective]
    rw [c_apply, c_apply, if_congr h_choice rfl rfl]
    split_ifs
    exacts [haw, hbw]

/-- Hilbert's Theorem 90 for finite ideles. Let `σ ∈ Gal(L/K)` have order `n`, and let the finite
adele `u` of `L` have norm `∏_{i < n} σ ^ i u = 1`. Then `u * σ c = c` for some invertible finite
adele `c`. -/
lemma hilbert90_finite_idele [NumberField K]
    (hu : ∏ i ∈ Finset.range (orderOf σ), adeleMap (↑(σ ^ i) : L →+* L) u = 1) :
    ∃ c : 𝔸f L, IsUnit c ∧ u * adeleMap (σ : L →+* L) c = c := by
  -- By Galois descent `1` lies in the `L`-span of the solutions of `u * σ c = c`. Any two solutions
  -- have a common divisor that is a solution, so a single solution divides `1`.
  let τ : 𝔸f L →ₛₗ[(σ : L →+* L)] 𝔸f L :=
    { toFun x := u * adeleMap σ x
      map_add' x y := by rw [map_add, mul_add]
      map_smul' r x := by simp [Algebra.smul_def, mul_left_comm] }
  -- `τ^[n] x = (∏ i < n, σ ^ i u) * σ ^ n x`; for `n = orderOf σ` this is `x`, by `hu`.
  have τ_order (x : 𝔸f L) : τ^[orderOf σ] x = x := by
    simp [τ, iterate_mul_apply, adeleMap_gal_pow, aut_one, hu]
  -- Descent (`σ` is tame at level `1`) at the prime `⊥` of the field `L`.
  obtain ⟨r, hr, h_span⟩ :=
    (isTameAtLevel_gal σ).exists_smul_mem_span_fixedPoints τ τ_order ⊥ one_ne_zero
  -- Every element of the span of the solutions is divisible by a solution.
  have divisible (x : 𝔸f L) (hx : x ∈ Submodule.span L (Function.fixedPoints τ)) :
      ∃ c : 𝔸f L, c ∣ x ∧ u * adeleMap σ c = c := by
    induction hx using Submodule.span_induction with
    | mem c hc => exact ⟨c, dvd_rfl, hc⟩
    | zero => exact ⟨0, dvd_refl 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha_dvd, ha⟩ := hx
      obtain ⟨b, hb_dvd, hb⟩ := hy
      obtain ⟨c, hca, hcb, hc⟩ := exists_dvd_dvd_mul_adeleMap_eq ha hb
      exact ⟨c, dvd_add (hca.trans ha_dvd) (hcb.trans hb_dvd), hc⟩
    | smul r x _ hx =>
      obtain ⟨c, hc_dvd, hc⟩ := hx
      exact ⟨c, dvd_smul_of_dvd r hc_dvd, hc⟩
  have one_mem : (1 : 𝔸f L) ∈ Submodule.span L (Function.fixedPoints τ) := by
    simpa [smul_smul, Ideal.mem_bot.not.mp hr] using h_span (r⁻¹ • 1)
  obtain ⟨c, hc_dvd, hc⟩ := divisible 1 one_mem
  exact ⟨c, isUnit_of_dvd_one hc_dvd, hc⟩

end New

end IdeleHilbert90
