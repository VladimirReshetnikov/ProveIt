import Lib.General.LinearAlgebra.MatrixPolynomials

/-!
# Hilbert 90 for GL_n and units under tame actions on Artinian, finite or profinite rings

This file gives versions of Hilbert's theorem 90, with congruence conditions, for a ring
endomorphism `σ` of finite order of a finite, Artinian or profinite ring. It proves Hilbert 90 for
`GL n` and for units at level `m`, and the surjectivity of the norm onto fixed units `≡ 1 mod m`.
`New.IsTameAtLevel σ p m` means: `σ ^ p = 1` with `0 < p`, `σ m = m`, some element has trace `1`
modulo `m`, and no `σ ^ i` with `0 < i < p` is trivial modulo a prime not containing `m`.
`New.IsProfiniteRing R` means: every sequence `x` has a unique `L` with `x N ≡ L` modulo each
natural number `M ≠ 0`, for `N` in a set of the hyperfilter.
`New.twistedNorm τ p δ` is the twisted norm `δ · τ δ ⋯ τ^(p-1) δ` of `δ` in a monoid.

## Main definitions and results

* `New.IsTameAtLevel.hilbert90_gl`, `New.IsTameAtLevel.hilbert90_unit`: a cocycle `≡ 1 mod m` is a
  coboundary of an element `≡ 1 mod m`, for `GL n` and for units.
* `New.IsTameAtLevel.exists_prod_range_pow_apply_eq`: a fixed unit `≡ 1 mod m` is the norm of a unit
  `≡ 1 mod m`.
* `New.IsProfiniteRing.exists_algHom_semiconj`, `New.IsProfiniteRing.finite_quotient_natCast`,
  `New.isTameAtLevel_quotientNatMap`, bundled in
  `New.IsTameAtLevel.exists_algHom_semiconj_quotientNatMap`: a limit map from the finite quotients
  `R ⧸ (N !)` reduces the profinite case to the finite one.

## Relation to the literature

Known result: Hilbert 90 for GL_n and norm surjectivity on units, cyclic action, congruence level.
This is done over Artinian, finite or profinite rings, where the action need only be free away from
an invariant element m and have an element of trace one modulo m. Cocycles, coboundaries and units
are congruent to 1 modulo m. Source: A. Speiser 1919;
J.-P. Serre, Corps locaux, 1962, Ch. X §1 Prop. 3 and Ch. V §2; S. Chase, D. Harrison, A. Rosenberg,
Galois theory and Galois cohomology of commutative rings, Mem. AMS 52, 1965; for the norm on O[γ],
P. Scholze, The Langlands-Kottwitz approach for some simple Shimura varieties, 2013, Lemma 2.2.
-/

section TameDescent

open Matrix Finset Filter Subgroup Nat Function Ideal Quotient MulEquiv Algebra

namespace New

variable {R n B V : Type*} [CommRing R] [CommRing B] [Fintype n] [DecidableEq n]
  {σ : R →+* R} {p : ℕ} {m x : R} {θ : B →+* B} [AddCommGroup V] [Module R V]

/-! ### The five conditions of a tame action -/

lemma IsTameAtLevel.apply_eq_self (h_tame : IsTameAtLevel σ p m) : σ m = m := h_tame.1

/-- For a tame action at level `m`, some `e` has trace `∑ i < p, (σ ^ i) e` congruent to `1`
modulo `m`. -/
lemma IsTameAtLevel.exists_dvd_sum_sub_one (h_tame : IsTameAtLevel σ p m) :
    ∃ e : R, m ∣ ∑ i ∈ range p, (σ ^ i) e - 1 :=
  let ⟨_, h_trace, _⟩ := h_tame; h_trace

lemma IsTameAtLevel.pow_eq_one (h_tame : IsTameAtLevel σ p m) : σ ^ p = 1 :=
  let ⟨_, _, h_pow, _⟩ := h_tame; h_pow

lemma IsTameAtLevel.pos (h_tame : IsTameAtLevel σ p m) : 0 < p :=
  let ⟨_, _, _, hp, _⟩ := h_tame; hp

/-- No inertia away from the level: if `0 < i < p` and `σ ^ i` is the identity modulo a prime `P`,
then `m ∈ P`. -/
lemma IsTameAtLevel.mem_of_forall_sub_mem (h_tame : IsTameAtLevel σ p m) {i : ℕ}
    (hi : i ∈ Set.Ioo 0 p) (P : Ideal R) [P.IsPrime] (h_triv : ∀ y : R, (σ ^ i) y - y ∈ P) :
    m ∈ P :=
  let ⟨_, _, _, _, h_inertia⟩ := h_tame; h_inertia i hi P h_triv

/-! ### Norms, traces and examples of tame actions -/

/-- If `τ` sends each `a i` to `a (i + 1)` and `a p = a 0`, then `τ` fixes the product of the
`a i` with `i < p`. -/
@[to_additive fixed_sum /-- If `τ` sends each `a i` to `a (i + 1)` and `a p = a 0`, then `τ` fixes
the sum of the `a i` with `i < p`. -/]
lemma map_prod_range_eq_self_of_periodic {M : Type*} [CommMonoid M] (τ : M →* M) (a : ℕ → M)
    (h_period : a p = a 0) (h_succ : ∀ i : ℕ, a (i + 1) = τ (a i)) :
    τ (∏ i ∈ range p, a i) = ∏ i ∈ range p, a i := by
  -- `τ` shifts the factors cyclically.
  cases p with
  | zero => simp
  | succ p =>
    calc
      τ (∏ i ∈ range (p + 1), a i) = ∏ i ∈ range (p + 1), a (i + 1) := by
        simp only [map_prod, h_succ]
      _ = (∏ i ∈ range p, a (i + 1)) * a (p + 1) := prod_range_succ _ p
      _ = ∏ i ∈ range (p + 1), a i := by rw [h_period, prod_range_succ']

/-- For a ring endomorphism `σ` of `R`, an element `m` and `p : ℕ`, the `p`-th iterate of
`y ↦ m * σ y` sends `x` to the norm `∏ i < p, (σ ^ i) m` times `(σ ^ p) x`. -/
lemma iterate_mul_apply :
    ∀ x : R, (fun y : R ↦ m * σ y)^[p] x = (∏ i ∈ range p, (σ ^ i) m) * (σ ^ p) x := by
  -- one more step multiplies by `m` and shifts every factor of the norm by `σ`
  induction p with
  | zero => simp
  | succ p ih =>
    intro x
    rw [iterate_succ_apply', ih, map_mul, map_prod, prod_range_succ', pow_zero, RingHom.coe_one,
      id_eq]
    simp only [RingHom.coe_pow, iterate_succ_apply']
    ring

/-- If Gal(L/K) is finite, every K-automorphism σ of the field L is tame (`New.IsTameAtLevel`) at
level 1, with exponent the order of σ. -/
lemma isTameAtLevel_gal {K L : Type*} [Field K] [Field L] [Algebra K L] (σ : Gal(L/K))
    [Finite Gal(L/K)] :
    IsTameAtLevel (R := L) σ (orderOf σ) 1 := by
  -- At level `1` the first two conditions are trivial.
  refine ⟨map_one _, ⟨0, by simp⟩, ?_, orderOf_pos σ, ?_⟩
  · -- `(σ : L →+* L) ^ k` acts as `σ ^ k`, and `σ ^ orderOf σ = 1` in `Gal(L/K)`
    ext y
    simp [← AlgEquiv.coe_pow]
  · -- the only prime of the field `L` is `⊥`, so `σ ^ i = 1`, which `0 < i < orderOf σ` excludes
    intro i ⟨hi_pos, hi_lt⟩ P _ h_triv
    have h_id : σ ^ i = 1 := by
      ext y
      simpa [eq_bot_of_prime P, sub_eq_zero, ← AlgEquiv.coe_pow] using h_triv y
    exact absurd h_id (pow_ne_one_of_lt_orderOf hi_pos.ne' hi_lt)

lemma isTameAtLevel_one : IsTameAtLevel 1 1 m :=
  ⟨rfl, ⟨1, by simp⟩, one_pow 1, one_pos, fun i ⟨_, _⟩ ↦ by omega⟩

/-- If a ring endomorphism `σ` of a commutative ring `R` has `σ ^ 2 = 1`, some `x - σ x` is a unit,
and `σ m = m`, then `σ` acts tamely (`New.IsTameAtLevel`) at level `m` with exponent `2`. -/
lemma IsTameAtLevel.of_sq_eq_one_of_isUnit_sub (hσ : σ ^ 2 = 1) (hx : IsUnit (x - σ x))
    (hm : σ m = m) :
    IsTameAtLevel σ 2 m := by
  obtain ⟨z, hz⟩ := hx.exists_right_inv
  have hσσ (y : R) : σ (σ y) = y := by simpa [sq] using RingHom.congr_fun hσ y
  -- `σ` negates `x - σ x`, hence also its inverse `z`, so `x * z` has trace `(x - σ x) * z = 1`
  have h_map : (σ x - x) * σ z = 1 := by simpa [hσσ] using congrArg σ hz
  have hσz : σ z = -z := by linear_combination (-σ z) * hz - z * h_map
  refine ⟨hm, ⟨x * z, ?_⟩, hσ, two_pos, ?_⟩
  · have h_trace : x * z + σ x * σ z = 1 := by linear_combination σ x * hσz + hz
    simp [sum_range_succ, h_trace]
  · -- `σ` is not trivial modulo any prime, since `x - σ x` is a unit
    intro i ⟨hi_pos, hi_lt⟩ P _ h_triv
    obtain rfl : i = 1 := by omega
    have h_mem : x - σ x ∈ P := sub_mem_comm_iff.mp (by simpa using h_triv x)
    exact P.mem_of_dvd hx.dvd h_mem

lemma isFixedPt_prod_range_pow_apply (hσ : σ ^ p = 1) : IsFixedPt σ (∏ i ∈ range p, (σ ^ i) x) :=
  map_prod_range_eq_self_of_periodic (σ : R →* R) (fun i ↦ (σ ^ i) x) (by rw [hσ, pow_zero])
    fun i ↦ by simp [iterate_succ_apply', -iterate_succ]

/-! ### Profinite rings -/

/-- The ring of integral finite adeles of a number field E satisfies the profiniteness condition
`New.IsProfiniteRing`. -/
lemma isProfiniteRing_intAdeles {E : Type*} [Field E] [NumberField E] : IsProfiniteRing (Ô E) := by
  -- `Ô E` is compact Hausdorff, so `x` has a unique limit along `hyperfilter ℕ`; the sets
  -- `M • Ô E`, `M ≠ 0`, are a basis of neighbourhoods of `0`, so this is the limit in
  -- `IsProfiniteRing`.
  intro x
  have h_compact : CompactSpace (Ô E) := isCompact_iff_compactSpace.mp isCompact_Ô
  have h_basis :
      (nhds (0 : 𝔸f E)).HasBasis (fun M : ℕ ↦ M ≠ 0) fun M : ℕ ↦ (fun y : 𝔸f E ↦ M • y) '' Ô E :=
    ⟨fun U ↦ by aesop (add simp mem_nhds_zero_finAdele_iff)⟩
  have key (L : Ô E) :
      (∀ M : ℕ, M ≠ 0 → ∀ᶠ N : ℕ in hyperfilter ℕ, (M : Ô E) ∣ x N - L) ↔
        ((hyperfilter ℕ).map x).lim = L := by
    -- the limit along the ultrafilter is a limit in the sense of `Tendsto` in `𝔸f E`
    rw [Ultrafilter.lim_eq_iff_le_nhds, Ultrafilter.coe_map]
    change _ ↔ Tendsto x (hyperfilter ℕ) (nhds L)
    rw [tendsto_subtype_rng, ← tendsto_sub_nhds_zero_iff, h_basis.tendsto_right_iff]
    simp [dvd_def, Subtype.ext_iff, eq_comm]
  simpa only [key] using existsUnique_eq'

/-- If `R` is profinite (`New.IsProfiniteRing`) and `B` is an additive retract of `R`, through
additive maps `i : B → R` and `r : R → B` with `r (i x) = x`, then `B` is profinite. -/
lemma IsProfiniteRing.of_retract (hR : IsProfiniteRing R) (i : B →+ R) (r : R →+ B)
    (hri : ∀ x : B, r (i x) = x) : IsProfiniteRing B := by
  -- The limit of `x` in `B` is `r` of the limit of `i ∘ x` in `R`. Both maps are additive, so they
  -- preserve divisibility by a natural number.
  intro x
  obtain ⟨L, hL, h_unique⟩ := hR (i ∘ x)
  -- `r` carries `M ∣ i (x N) - L` to `M ∣ x N - r L`
  have h_dvd_r (M N : ℕ) (h_dvd : (M : R) ∣ i (x N) - L) : (M : B) ∣ x N - r L := by
    obtain ⟨c, hc⟩ := h_dvd
    refine ⟨r c, ?_⟩
    simpa [hri, ← nsmul_eq_mul] using congrArg r hc
  -- `i` carries `M ∣ x N - y` to `M ∣ i (x N) - i y`
  have h_dvd_i (M N : ℕ) (y : B) (h_dvd : (M : B) ∣ x N - y) : (M : R) ∣ i (x N) - i y := by
    obtain ⟨c, hc⟩ := h_dvd
    refine ⟨i c, ?_⟩
    simpa [← nsmul_eq_mul] using congrArg i hc
  refine ⟨r L, fun M hM ↦ (hL M hM).mono fun N ↦ h_dvd_r M N, fun y hy ↦ ?_⟩
  -- a limit `y` of `x` gives the limit `i y` of `i ∘ x`
  have hiy : i y = L := h_unique (i y) fun M hM ↦ (hy M hM).mono fun N ↦ h_dvd_i M N y
  rw [← hiy, hri y]

omit [DecidableEq n] in
/-- If `R` is profinite (`New.IsProfiniteRing`), so is every ring `B` that is isomorphic as an
additive group to `n → R`, through `coords`, for a finite type `n`. -/
lemma IsProfiniteRing.of_addEquiv_pi (hR : IsProfiniteRing R) (coords : B ≃+ (n → R)) :
    IsProfiniteRing B := by
  -- `n → R` is profinite, with limits taken coordinatewise, and `B` is a retract of it.
  have h_pi : IsProfiniteRing (n → R) := by
    intro x
    -- `L k` is the limit of the `k`-th coordinates, and `hL` says that it is the only one
    obtain ⟨L, hL⟩ : ∃ L : n → R, ∀ (k : n) (L' : R),
        (∀ M : ℕ, M ≠ 0 → ∀ᶠ N : ℕ in hyperfilter ℕ, (M : R) ∣ x N k - L') ↔ L k = L' :=
      forall_existsUnique_iff.mp fun k ↦ hR fun N ↦ x N k
    refine ⟨L, fun M hM ↦ ?_, fun L' hL' ↦ ?_⟩
    · -- each coordinate converges, and `n` is finite
      filter_upwards [eventually_all.mpr fun k ↦ (hL k (L k)).mpr rfl M hM] with N hN
      exact pi_dvd_iff.mpr fun k ↦ by simpa using hN k
    · funext k
      refine ((hL k (L' k)).mp fun M hM ↦ ?_).symm
      exact (hL' M hM).mono fun N hN ↦ by simpa using pi_dvd_iff.mp hN k
  exact h_pi.of_retract coords.toAddMonoidHom coords.symm coords.left_inv

/-- If `R` is profinite (`New.IsProfiniteRing`) and `σ` is tame at level `0`, so that `σ ^ p = 1`
and some element of `R` has trace `1`, then the subring `σ.eqLocus 1` of elements fixed by `σ` is
profinite. -/
lemma IsProfiniteRing.eqLocus (hR : IsProfiniteRing R) (h_tame : IsTameAtLevel σ p 0) :
    IsProfiniteRing (σ.eqLocus 1) := by
  -- With `e` of trace one, `x ↦ ∑ i < p, σ^[i] (e * x)` is an additive retraction of `R` onto the
  -- fixed ring.
  obtain ⟨e, he⟩ := h_tame.exists_dvd_sum_sub_one
  have h_trace : ∑ i ∈ range p, σ^[i] e = 1 := by simpa [sub_eq_zero] using he
  have h_period (y : R) : σ^[p] y = y := by
    rw [← RingHom.coe_pow, h_tame.pow_eq_one, RingHom.coe_one, id_eq]
  have h_fixed (x : R) : IsFixedPt σ (∑ i ∈ range p, σ^[i] (e * x)) :=
    fixed_sum (σ : R →+ R) (fun i ↦ σ^[i] (e * x)) (h_period (e * x))
      fun i ↦ iterate_succ_apply' σ i (e * x)
  let retract : R →+ σ.eqLocus 1 :=
    .mk' (fun x ↦ ⟨∑ i ∈ range p, σ^[i] (e * x), h_fixed x⟩) fun x y ↦
      Subtype.ext (by simp [mul_add, sum_add_distrib])
  refine hR.of_retract (σ.eqLocus 1).subtype.toAddMonoidHom retract fun x ↦ Subtype.ext ?_
  -- for a fixed `x` the sum is the trace of `e` times `x`
  show ∑ i ∈ range p, σ^[i] (e * x) = x
  have hx_iter (i : ℕ) : σ^[i] (x : R) = x := iterate_fixed x.prop i
  simp only [iterate_map_mul, hx_iter, ← sum_mul, h_trace, one_mul]

/-! ### Passing to finite quotients and descent at a prime -/

/-- Tameness passes along a ring homomorphism `f : R →+* B` that intertwines `σ` with an
endomorphism `θ` of `B`, provided `θ ^ p = 1`; the level becomes `f m`. -/
lemma IsTameAtLevel.of_semiconj (h_tame : IsTameAtLevel σ p m) (f : R →+* B) (hf : Semiconj f σ θ)
    (hθ : θ ^ p = 1) : IsTameAtLevel θ p (f m) := by
  obtain ⟨e, he⟩ : ∃ e : R, m ∣ ∑ i ∈ range p, (σ ^ i) e - 1 := h_tame.exists_dvd_sum_sub_one
  -- `f` intertwines the powers of `σ` with those of `θ`
  have h_pow (i : ℕ) (y : R) : (θ ^ i) (f y) = f ((σ ^ i) y) := by
    rw [RingHom.coe_pow, RingHom.coe_pow, (hf.iterate_right i).eq]
  have h_trace : f m ∣ ∑ i ∈ range p, (θ ^ i) (f e) - 1 := by simpa [h_pow] using map_dvd f he
  refine ⟨IsFixedPt.map h_tame.apply_eq_self hf, ⟨f e, h_trace⟩, hθ, h_tame.pos,
    fun i hi P _ h_triv ↦ ?_⟩
  have h_comap (y : R) : (σ ^ i) y - y ∈ P.comap f := by simpa [h_pow] using h_triv (f y)
  exact h_tame.mem_of_forall_sub_mem hi (P.comap f) h_comap

lemma span_natCast_le_comap (σ : R →+* R) (N : ℕ) : span {(N : R)} ≤ (span {(N : R)}).comap σ := by
  simp [span_le]

/-- The ring endomorphism of `R ⧸ (N)` induced by `σ`, for a natural number `N`. -/
def quotientNatMap (σ : R →+* R) (N : ℕ) : R ⧸ span {(N : R)} →+* R ⧸ span {(N : R)} :=
  quotientMap (span {(N : R)}) σ (span_natCast_le_comap σ N)

private lemma quotientNatMap_mk (σ : R →+* R) (N : ℕ) (x : R) :
    quotientNatMap σ N (mk (span {(N : R)}) x) = mk (span {(N : R)}) (σ x) := rfl

/-- Let `R` be profinite (`New.IsProfiniteRing`) and `σ` a ring endomorphism of `R`. Some
`R`-algebra map `Λ` from the families of residues modulo `N !` to `R` carries the maps
`quotientNatMap σ (N !)` to `σ`. -/
lemma IsProfiniteRing.exists_algHom_semiconj (hR : IsProfiniteRing R) (σ : R →+* R) :
    ∃ Λ : (∀ N : ℕ, R ⧸ span {((N ! : ℕ) : R)}) →ₐ[R] R,
      Semiconj Λ (Pi.map fun N : ℕ ↦ quotientNatMap σ N !) σ := by
  -- `Λ x` is the limit along the hyperfilter of lifts of the residues `x N`. Limits are unique and
  -- `M ∣ N !` for large `N`, so `Λ` commutes with every operation that passes to the quotients:
  -- sums, products, constants and `σ`.
  let I (N : ℕ) : Ideal R := span {(N : R)}
  replace hR (x : ℕ → R) :
      ∃! L : R, ∀ M : ℕ, M ≠ 0 → ∀ᶠ N : ℕ in hyperfilter ℕ, mk (I M) (x N) = mk (I M) L := by
    simpa [I, ← eq_zero_iff_dvd, sub_eq_zero] using hR x
  choose Λ hΛ_lim hΛ_uniq using fun x : ∀ N : ℕ, R ⧸ I N ! ↦ hR fun N ↦ (x N).out
  have hΛ_op {F : R → R → R} (G : ∀ M : ℕ, R ⧸ I M → R ⧸ I M → R ⧸ I M)
      (hG : ∀ {M : ℕ}, Semiconj₂ (mk (I M)) F (G M)) (x y : ∀ N : ℕ, R ⧸ I N !) :
      Λ (fun N ↦ G (N !) (x N) (y N)) = F (Λ x) (Λ y) := by
    -- By uniqueness it is enough that `F (Λ x) (Λ y)` is a limit of the lifts, modulo each `M`.
    refine (hΛ_uniq _ (F (Λ x) (Λ y)) fun M hM ↦ ?_).symm
    filter_upwards [hΛ_lim x M hM, hΛ_lim y M hM, hyperfilter_le_atTop (mem_atTop M)] with
      N hx hy hMN
    -- The lift of `G (x N) (y N)` and `F` of the lifts agree modulo `N !`, hence modulo `M`.
    have h_fact : mk (I N !) (G (N !) (x N) (y N)).out = mk (I N !) (F (x N).out (y N).out) := by
      simp [hG.eq]
    have h_dvd : (M : R) ∣ N ! := cast_dvd_cast (dvd_factorial (pos_of_ne_zero hM) hMN)
    calc
      mk (I M) (G (N !) (x N) (y N)).out = mk (I M) (F (x N).out (y N).out) :=
        mk_span_eq_iff_dvd_sub.mpr (h_dvd.trans (mk_span_eq_iff_dvd_sub.mp h_fact))
      _ = mk (I M) (F (Λ x) (Λ y)) := by rw [hG.eq, hx, hy, ← hG.eq]
  -- constants and `σ` are operations that ignore both or the first of their arguments
  have hΛ_const (a : R) : Λ (fun N ↦ mk (I N !) a) = a :=
    hΛ_op (fun M _ _ ↦ mk (I M) a) (fun _ _ ↦ rfl) (x := 0) (y := 0)
  have hΛ_mul (x y : ∀ N : ℕ, R ⧸ I N !) : Λ (x * y) = Λ x * Λ y := hΛ_op _ (map_mul _) x y
  have hΛ_add (x y : ∀ N : ℕ, R ⧸ I N !) : Λ (x + y) = Λ x + Λ y := hΛ_op _ (map_add _) x y
  have hΛ_σ (x : ∀ N : ℕ, R ⧸ I N !) : Λ (fun N ↦ quotientNatMap σ N ! (x N)) = σ (Λ x) :=
    hΛ_op (F := fun _ b ↦ σ b) (fun M _ b ↦ quotientNatMap σ M b) (fun _ _ ↦ rfl)
      (x := 0) (y := x)
  exact ⟨{ toFun := Λ, map_one' := hΛ_const 1, map_mul' := hΛ_mul, map_zero' := hΛ_const 0,
           map_add' := hΛ_add, commutes' := hΛ_const }, hΛ_σ⟩

/-- Each quotient `R ⧸ (N)` of a profinite ring `R` by a natural number `N ≠ 0` is finite. -/
lemma IsProfiniteRing.finite_quotient_natCast (hR : IsProfiniteRing R) {N : ℕ} (hN : N ≠ 0) :
    Finite (R ⧸ span {(N : R)}) := by
  -- A sequence of distinct residues would have a limit, so it would be constant on a set of the
  -- hyperfilter; but it takes each value at most once, and finite sets are not in it.
  refine .of_not_infinite fun h_inf ↦ ?_
  let x : ℕ ↪ R ⧸ span {(N : R)} := h_inf.natEmbedding _
  obtain ⟨L, hL, -⟩ := hR fun n ↦ (x n).out
  have h_ev : ∀ᶠ n : ℕ in hyperfilter ℕ, x n = mk (span {(N : R)}) L := by
    simpa [← eq_zero_iff_dvd, sub_eq_zero] using hL N hN
  exact ((Set.toFinite {mk (span {(N : R)}) L}).preimage_embedding x).notMem_hyperfilter h_ev

/-- If `σ` is tame at level `m`, the map `quotientNatMap σ N` it induces on `R ⧸ (N)` is tame at
the residue of `m`. -/
lemma isTameAtLevel_quotientNatMap (h_tame : IsTameAtLevel σ p m) (N : ℕ) :
    IsTameAtLevel (quotientNatMap σ N) p (mk (span {(N : R)}) m) := by
  have hq : Semiconj (mk (span {(N : R)})) σ (quotientNatMap σ N) := fun _ ↦ rfl
  have h_per (y : R) : IsPeriodicPt σ p y := by
    show σ^[p] y = y
    simp [← RingHom.coe_pow, h_tame.pow_eq_one]
  have hq_pow : quotientNatMap σ N ^ p = 1 :=
    ringHom_ext (RingHom.ext fun y ↦ (h_per y).map hq)
  exact h_tame.of_semiconj _ hq hq_pow

/-- Let `R` be profinite (`New.IsProfiniteRing`) and `σ` tame at level `m`. Then some
`R`-algebra map `Λ` from the families of residues modulo `N !` to `R` carries the maps
`quotientNatMap σ (N !)` to `σ`, and each quotient `R ⧸ (N !)` is finite, with
`quotientNatMap σ (N !)` tame at the residue of `m`. -/
lemma IsTameAtLevel.exists_algHom_semiconj_quotientNatMap (h_tame : IsTameAtLevel σ p m)
    (hR : IsProfiniteRing R) :
    ∃ Λ : (∀ N : ℕ, R ⧸ span {((N ! : ℕ) : R)}) →ₐ[R] R,
      Semiconj Λ (Pi.map fun N : ℕ ↦ quotientNatMap σ N !) σ ∧
      ∀ N : ℕ, Finite (R ⧸ span {((N ! : ℕ) : R)}) ∧
        IsTameAtLevel (quotientNatMap σ N !) p (mk (span {((N ! : ℕ) : R)}) m) := by
  obtain ⟨Λ, hΛ⟩ := hR.exists_algHom_semiconj σ
  exact ⟨Λ, hΛ, fun N ↦
    ⟨hR.finite_quotient_natCast (factorial_ne_zero N), isTameAtLevel_quotientNatMap h_tame _⟩⟩

/-- Galois descent at a prime. Let `σ` be tame at level `m`, meaning `σ m = m`, `σ ^ p = 1` with
`0 < p`, some `e` has `∑ i < p, (σ ^ i) e ≡ 1 mod m`, and for `0 < i < p` every prime ideal modulo
which `σ ^ i` is the identity contains `m`. If `τ` is a `σ`-semilinear map on `V` with `τ^[p] = id`
and `P` is a prime not containing `m`, then some `r ∉ P` multiplies `V` into the span of the vectors
fixed by `τ`. -/
lemma IsTameAtLevel.exists_smul_mem_span_fixedPoints (h_tame : IsTameAtLevel σ p m)
    (τ : V →ₛₗ[σ] V) (hτ : ∀ v : V, τ^[p] v = v) (P : Ideal R) [hP : IsPrime P] (hm : m ∉ P) :
    ∃ r ∉ P, ∀ v : V, r • v ∈ Submodule.span R (fixedPoints τ) := by
  -- Given `v`, put `L w = ∑ z < p, w z • τ^[z] v` for a family `w` of scalars. On an orbit
  -- `w z = (σ ^ z) a` this is `∑ τ^[z] (a • v)`, which `τ` fixes; so `L` sends the span of the
  -- orbits into the span of the fixed vectors. Orbits are closed under products, and each `σ ^ i`
  -- moves some `u i` modulo `P`. So the span contains a `w` with `w 0 ∉ P` and `w z = 0` for
  -- `0 < z < p`, and for it `L w = w 0 • v`.
  have h_move (i : ℕ) (hi : i ∈ Set.Ioo 0 p) : ∃ a : R, (σ ^ i) a - a ∉ P := by
    by_contra! h_triv
    exact hm (h_tame.mem_of_forall_sub_mem hi P h_triv)
  choose! u hu using h_move
  let orbit : R →+* ℕ → R := RingHom.pi fun i : ℕ ↦ σ ^ i
  let w : ℕ → R := ∏ i ∈ Ioo 0 p, ((σ ^ i) (u i) • 1 - orbit (u i))
  have hw_mem : w ∈ Submodule.span R (orbit.range : Set (ℕ → R)) := by
    have h_adjoin : w ∈ adjoin R (orbit.range : Set (ℕ → R)) := prod_mem fun i _ ↦
      sub_mem (Subalgebra.smul_mem _ (one_mem _) _) (subset_adjoin ⟨u i, rfl⟩)
    simpa using (adjoin_eq_span R (orbit.range : Set (ℕ → R))).le h_adjoin
  have hw_zero (z : ℕ) (hz : z ∈ Ioo 0 p) : w z = 0 := by simp [w, orbit, prod_eq_zero hz]
  -- `w 0` is the product of the `(σ ^ i) (u i) - u i`, none of which lies in `P`
  have hw0 : w 0 ∉ P := by
    have h_eval : w 0 = ∏ i ∈ Ioo 0 p, ((σ ^ i) (u i) - u i) := by simp [w, orbit]
    rw [h_eval, hP.prod_mem_iff]
    rintro ⟨i, hi, h_mem⟩
    exact hu i (mem_Ioo.mp hi) h_mem
  refine ⟨w 0, hw0, fun v ↦ ?_⟩
  let L : (ℕ → R) →ₗ[R] V := ∑ z ∈ range p, (LinearMap.proj z).smulRight (τ^[z] v)
  have hL_orbit (a : R) : L (orbit a) ∈ fixedPoints τ := by
    have h_period : (σ ^ p) a • τ^[p] v = (σ ^ 0) a • τ^[0] v := by
      rw [h_tame.pow_eq_one, hτ, pow_zero, iterate_zero_apply]
    have h_succ (z : ℕ) : (σ ^ (z + 1)) a • τ^[z + 1] v = τ ((σ ^ z) a • τ^[z] v) := by
      simp only [map_smulₛₗ, RingHom.coe_pow, iterate_succ_apply']
    simp only [L, LinearMap.sum_apply]
    exact fixed_sum (τ : V →+ V) (fun z ↦ (σ ^ z) a • τ^[z] v) h_period h_succ
  have hL_w : L w = w 0 • v := by
    rw [LinearMap.sum_apply, sum_eq_single_of_mem 0 (mem_range.mpr h_tame.pos)]
    · simp
    · intro z hz hz_ne
      simp [hw_zero z (mem_Ioo.mpr ⟨pos_of_ne_zero hz_ne, mem_range.mp hz⟩)]
  have h_le : (Submodule.span R (orbit.range : Set (ℕ → R))).map L ≤ .span R (fixedPoints τ) :=
    (L.map_span_le _ _).mpr <| by
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span (hL_orbit a)
  exact h_le ⟨w, hw_mem, hL_w⟩

/-! ### Hilbert 90 and norms at level `m` -/

/-- Let `R` be Artinian, `σ` tame at level `m`, `d ≡ 1 mod m`, and let the ideal `M` contain every
`(σ ^ i) d`. Then some `σ`-fixed multiple `N` of `m` is `≡ 1 mod M` and lies in each prime that
does not contain `d`. -/
lemma IsTameAtLevel.exists_fixed_separating (h_tame : IsTameAtLevel σ p m)
    (hart : IsArtinianRing R) {d : R} (hd : m ∣ 1 - d) {M : Ideal R}
    (hM : ∀ i : ℕ, (σ ^ i) d ∈ M) :
    ∃ N : R,
      σ N = N ∧
      m ∣ N ∧
      Ideal.Quotient.mk M N = 1 ∧
      ∀ P : Ideal R, P.IsPrime → d ∉ P → N ∈ P := by
  -- With `d ^ (l + 1) * y = d ^ l`, every prime contains `d` or `1 - d * y`. Take for `N` the norm
  -- of `a = (1 - d) * (1 - d * y)`.
  obtain ⟨l, y, hy⟩ := hart.exists_pow_succ_smul_dvd d (1 : R)
  have hy_mul : d ^ (l + 1) * y = d ^ l := by simpa [smul_eq_mul] using hy
  let a : R := (1 - d) * (1 - d * y)
  have ha_dvd : a ∣ ∏ i ∈ range p, (σ ^ i) a := dvd_prod_of_mem _ (mem_range.mpr h_tame.pos)
  -- each factor `(σ ^ i) a` is `≡ 1 mod M`, because `(σ ^ i) d ∈ M`
  have h_one : Ideal.Quotient.mk M (∏ i ∈ range p, (σ ^ i) a) = 1 := by
    rw [map_prod]
    exact prod_eq_one fun i _ ↦ by simp [a, -RingHom.coe_pow, eq_zero_iff_mem.mpr (hM i)]
  -- `d ^ l * a = 0`, so a prime that does not contain `d` contains `a`, hence the norm
  have h_zero : d ^ l * a = 0 := by
    calc d ^ l * a = (1 - d) * (d ^ l - d ^ (l + 1) * y) := by simp only [a]; ring
      _ = 0 := by rw [hy_mul, sub_self, mul_zero]
  refine ⟨∏ i ∈ range p, (σ ^ i) a, isFixedPt_prod_range_pow_apply h_tame.pow_eq_one,
    (hd.mul_right _).trans ha_dvd, h_one, fun P hP hdP ↦ ?_⟩
  have ha_mem : a ∈ P :=
    (hP.mem_or_mem_of_mul_eq_zero h_zero).resolve_left (P.primeCompl.pow_mem hdP l)
  exact P.mem_of_dvd ha_dvd ha_mem

/-- Let `σ` be tame at level `m`: `σ m = m`, `σ ^ p = 1` with `0 < p`, some `e` has trace
`∑ i < p, (σ ^ i) e ≡ 1 mod m`, and for `0 < i < p` every prime modulo which `σ ^ i` is the identity
contains `m`. Let `τ v = c * σ v` be a `σ`-semilinear map of period `p` on `n × n` matrices over
`R`, and let `P` be a prime not containing `m`. Then some `τ`-fixed matrix has determinant outside
`P`. -/
lemma IsTameAtLevel.exists_fixed_det_notMem (h_tame : IsTameAtLevel σ p m) {c : Matrix n n R}
    {τ : Matrix n n R →ₛₗ[σ] Matrix n n R}
    (hτ : ∀ v : Matrix n n R, τ v = c * v.map σ) (hτ_period : ∀ v : Matrix n n R, τ^[p] v = v)
    (P : Ideal R) [P.IsPrime] (hm : m ∉ P) : ∃ v : Matrix n n R, τ v = v ∧ v.det ∉ P := by
  -- `r • 1` is a combination of fixed matrices `G i`, with `r ∉ P`. Expand its determinant, a power
  -- of `r`, by columns. As `τ` acts column by column, a matrix whose columns are taken from the
  -- `G i` is fixed, and one of these has determinant outside `P`.
  by_contra! h_all
  obtain ⟨r, hr, h_span⟩ := h_tame.exists_smul_mem_span_fixedPoints τ hτ_period P hm
  obtain ⟨k, s, G, hG⟩ : ∃ (k : ℕ) (s : Fin k → R) (G : Fin k → fixedPoints τ),
      ∑ i : Fin k, s i • (G i : Matrix n n R) = r • 1 :=
    Submodule.mem_span_set'.mp (h_span 1)
  have h_det : (∑ i, s i • (G i).val)ᵀ.det ∈ P := by
    -- The rows of the transpose are sums, so the multilinear `det` expands into a sum over the
    -- choices `f j` of one summand `s (f j) • (G (f j))ᵀ j` for each row `j`.
    have h_rows : (∑ i, s i • (G i).val)ᵀ = fun j : n ↦ ∑ i, s i • (G i).valᵀ j :=
      funext₂ fun j l ↦ by simp [Matrix.sum_apply, Finset.sum_apply]
    rw [h_rows]
    change detRowAlternating (fun j : n ↦ ∑ i, s i • (G i).valᵀ j) ∈ P
    rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
    refine sum_mem fun f _ ↦ ?_
    rw [MultilinearMap.map_smul_univ]
    refine P.smul_mem _ ?_
    have h_fixed : τ (of fun i j : n ↦ (G (f j)).val i j) = of fun i j : n ↦ (G (f j)).val i j :=
      (hτ _).trans <| ext fun i j ↦ congrFun₂ ((hτ _).symm.trans (G (f j)).prop) i j
    have h_mem : (of fun (i j) ↦ (G (f j) : Matrix n n R) i j).det ∈ P := h_all _ h_fixed
    rwa [← det_transpose] at h_mem
  -- but the determinant of `r • 1` is a power of `r`, which lies outside `P`
  have h_pow : r ^ Fintype.card n ∈ P := by simpa [hG] using h_det
  exact P.primeCompl.pow_mem hr (Fintype.card n) h_pow

/-- Let `σ` be tame at level `m`: `σ m = m`, `σ ^ p = 1` with `0 < p`, some `e` has trace
`∑ i < p, (σ ^ i) e ≡ 1 mod m`, and for `0 < i < p` every prime modulo which `σ ^ i` is the identity
contains `m`. Let `τ v = c * σ v` be a `σ`-semilinear map on `n × n` matrices over `R`, where
`c = 1 + m • Y` and `τ^[p]` is the identity. Then some `τ`-fixed matrix is `≡ 1 mod m`, that is, of
the form `1 + m • W`. -/
lemma IsTameAtLevel.exists_fixed_eq_one_add_smul (h_tame : IsTameAtLevel σ p m)
    {c Y : Matrix n n R} (hY : c = 1 + m • Y) {τ : Matrix n n R →ₛₗ[σ] Matrix n n R}
    (hτ : ∀ v : Matrix n n R, τ v = c * v.map σ) (hτ_period : ∀ v : Matrix n n R, τ^[p] v = v) :
    ∃ g : Matrix n n R, τ g = g ∧ ∃ W : Matrix n n R, g = 1 + m • W := by
  -- Average `e • 1` over the orbit of `τ`, where `e` has trace `1 + m * w`.
  obtain ⟨e, w, he⟩ := h_tame.exists_dvd_sum_sub_one
  -- `τ` maps `1 + m • v` to `1 + m • (Y + τ v)`, so `τ^[i] 1 = 1 + m • Z i`
  have h_step (v : Matrix n n R) : τ (1 + m • v) = 1 + m • (Y + τ v) := by
    simp [hτ, hY, Matrix.map_add, Matrix.map_smul, h_tame.apply_eq_self, mul_add, add_mul,
      smul_add, add_assoc]
  let Z (i : ℕ) : Matrix n n R := (fun v : Matrix n n R ↦ Y + τ v)^[i] 0
  have hZ (i : ℕ) : τ^[i] 1 = 1 + m • Z i := by
    induction i with
    | zero => simp [Z]
    | succ i ih => simp only [iterate_succ_apply', ih, h_step, Z]
  -- `τ^[i]` is `σ ^ i`-semilinear
  have h_smul (i : ℕ) (a : R) (v : Matrix n n R) : τ^[i] (a • v) = (σ ^ i) a • τ^[i] v := by
    induction i with
    | zero => simp
    | succ i ih => simp [iterate_succ_apply', ih, -iterate_succ]
  have h_fixed : τ (∑ i ∈ range p, τ^[i] (e • 1)) = ∑ i ∈ range p, τ^[i] (e • 1) :=
    fixed_sum τ.toAddMonoidHom (fun i ↦ τ^[i] (e • 1)) (hτ_period (e • 1))
      fun i ↦ iterate_succ_apply' τ i (e • 1)
  refine ⟨_, h_fixed, w • 1 + ∑ i ∈ range p, (σ ^ i) e • Z i, ?_⟩
  calc
    ∑ i ∈ range p, τ^[i] (e • 1) = ∑ i ∈ range p, (σ ^ i) e • (1 + m • Z i) := by
      simp only [h_smul, hZ]
    _ = (∑ i ∈ range p, (σ ^ i) e) • 1 + m • ∑ i ∈ range p, (σ ^ i) e • Z i := by
      simp only [smul_add, sum_add_distrib, sum_smul, smul_sum, smul_comm m]
    _ = 1 + m • (w • 1 + ∑ i ∈ range p, (σ ^ i) e • Z i) := by
      rw [eq_add_of_sub_eq' he]
      simp [add_smul, mul_smul, add_assoc]

/-- Hilbert 90 for `GL n` at level `m` over an Artinian ring `R`, the main case of
`New.IsTameAtLevel.hilbert90_gl`. Let `σ` be tame at level `m`, meaning `σ m = m`, `σ ^ p = 1` with
`0 < p`, some `e` has `∑ i < p, (σ ^ i) e ≡ 1 mod m`, and for `0 < i < p` every prime ideal modulo
which `σ ^ i` is the identity contains `m`. If `c = 1 + m • Y` is invertible with
`c · σ c ⋯ σ^(p-1) c = 1` (`σ` applied entrywise), then `c · σ k = k` for an invertible
`k = 1 + m • W`. -/
lemma IsTameAtLevel.hilbert90_gl_of_isArtinianRing (h_tame : IsTameAtLevel σ p m)
    (hart : IsArtinianRing R) (c : GL n R) {Y : Matrix n n R} (hY : c.val = 1 + m • Y)
    (hc : twistedNorm (GeneralLinearGroup.map σ) p c = 1) :
    ∃ k : GL n R, ∃ W : Matrix n n R, c * k.val.map σ = k ∧ k.val = 1 + m • W := by
  -- We look for an invertible fixed point `≡ 1 mod m` of `τ v = c * σ v`. Among the fixed points
  -- `≡ 1 mod m` take `g` with a maximal set of primes not containing `det g`. If `det g` were not a
  -- unit, a repair at a maximal ideal containing it would enlarge that set.
  let τ : Matrix n n R →ₛₗ[σ] Matrix n n R := .mulLeft R c.val ∘ₛₗ σ.toSemilinearMap.mapMatrix
  have hτ_apply (v : Matrix n n R) : τ v = c * v.map σ := rfl
  have hτ (i : ℕ) (v : Matrix n n R) :
      τ^[i] v = twistedNorm (GeneralLinearGroup.map σ) i c * v.map (σ ^ i) := by
    induction i with
    | zero => simp [twistedNorm]
    | succ i ih =>
      rw [iterate_succ_apply', ih, hτ_apply]
      simp [twistedNorm_succ', Matrix.map_mul, Matrix.map_map, mul_assoc,
        (Function.Commute.self_iterate σ i).comp_eq]
  have hτ_period (v : Matrix n n R) : τ^[p] v = v := by simp [hτ, hc, h_tame.pow_eq_one]
  obtain ⟨g, ⟨hg, W, hW⟩, hmax⟩ := exists_maximalFor_of_wellFoundedGT
    (fun g ↦ τ g = g ∧ ∃ W : Matrix n n R, g = 1 + m • W) (fun g ↦ PrimeSpectrum.basicOpen g.det)
    (h_tame.exists_fixed_eq_one_add_smul hY hτ_apply hτ_period)
  suffices h_unit : IsUnit g.det from ⟨.mk'' g h_unit, W, hg, hW⟩
  by_contra h_nonunit
  obtain ⟨M, hM, hgM⟩ := exists_max_ideal_of_mem_nonunits h_nonunit
  -- As `g` is fixed, `det g` is a unit times each `(σ ^ i) (det g)`, so these lie in `M` too.
  have h_conj (i : ℕ) : (σ ^ i) g.det ∈ M := by
    have h_det : g.det = (twistedNorm (GeneralLinearGroup.map σ) i c).val.det * (σ ^ i) g.det := by
      conv_lhs => rw [← iterate_fixed hg i, hτ, det_mul]
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
    have h_unit : IsUnit (twistedNorm (GeneralLinearGroup.map σ) i c).val.det := by simp
    rwa [h_det, M.unit_mul_mem_iff_mem h_unit] at hgM
  have hm_dvd : m ∣ 1 - g.det := by simp [hW, ← eq_zero_iff_dvd, det_one_add_smul m]
  obtain ⟨N, hN_fixed, ⟨z, hz⟩, hN_one, hN_mem⟩ :
      ∃ N : R, σ N = N ∧ m ∣ N ∧ Ideal.Quotient.mk M N = 1 ∧
        ∀ P : Ideal R, P.IsPrime → g.det ∉ P → N ∈ P :=
    h_tame.exists_fixed_separating hart hm_dvd h_conj
  -- `m ∉ M`, because `m ∣ N` and `N ≡ 1 mod M`
  have hmM : m ∉ M := fun hm_mem ↦ by
    have hN_mem_M : N ∈ M := by simpa [hz] using M.mul_mem_right z hm_mem
    exact hM.ne_top <| (eq_top_iff_one M).mpr <| by
      simp [← eq_zero_iff_mem, hN_one] at hN_mem_M
  obtain ⟨v, hv, hvM⟩ := h_tame.exists_fixed_det_notMem hτ_apply hτ_period M hmM
  -- Repair: `g - N • (g - v)` is fixed and `≡ 1 mod m`; it is `≡ g` at the primes not containing
  -- `det g` and `≡ v` at `M`. This contradicts the maximality of `g`.
  have h_fixed : τ (g - N • (g - v)) = g - N • (g - v) := by simp [hg, hv, hN_fixed]
  have h_cong : g - N • (g - v) = 1 + m • (W - z • (g - v)) := by
    rw [hz, mul_smul, smul_sub m, ← add_sub_assoc, ← hW]
  have h_le : PrimeSpectrum.basicOpen g.det ≤ PrimeSpectrum.basicOpen (g - N • (g - v)).det := by
    rintro ⟨P, hP⟩ hgP
    have hN_zero : mk P N = 0 := eq_zero_iff_mem.mpr (hN_mem P hP hgP)
    simpa [← eq_zero_iff_mem, RingHom.map_det, g.map_sub, hN_zero, map_smul'] using hgP
  have h_mem : ⟨M, hM.isPrime⟩ ∈ PrimeSpectrum.basicOpen (g - N • (g - v)).det := by
    simpa [← eq_zero_iff_mem, RingHom.map_det, g.map_sub, hN_one, map_smul'] using hvM
  exact hmax ⟨h_fixed, _, h_cong⟩ h_le h_mem hgM

/-- Hilbert 90 for `GL n` at level `m`. Let `R` be Artinian or profinite, and let `σ` be tame at
level `m`, meaning `σ m = m`, `σ ^ p = 1` with `0 < p`, some `e` has `∑ i < p, (σ ^ i) e ≡ 1 mod m`,
and for `0 < i < p` every prime ideal modulo which `σ ^ i` is the identity contains `m`. If
`c = 1 + m • Y` is invertible with `c · σ c ⋯ σ^(p-1) c = 1` (`σ` applied entrywise), then
`c = k · (σ k)⁻¹`, written `c · σ k = k`, for an invertible `k = 1 + m • W`. -/
lemma IsTameAtLevel.hilbert90_gl (h_tame : IsTameAtLevel σ p m)
    (hR : IsArtinianRing R ∨ IsProfiniteRing R) (c : GL n R) {Y : Matrix n n R}
    (hY : c.val = 1 + m • Y) (hc : twistedNorm (GeneralLinearGroup.map σ) p c = 1) :
    ∃ k : GL n R, ∃ W : Matrix n n R, c * k.val.map σ = k ∧ k.val = 1 + m • W := by
  rcases hR with hart | hR
  · exact h_tame.hilbert90_gl_of_isArtinianRing hart c hY hc
  -- Profinite case: solve in each finite quotient `R ⧸ N !` and apply the limit map entrywise.
  let q (N : ℕ) : R ⧸ span {(N : R)} →+* R ⧸ span {(N : R)} := quotientNatMap σ N
  have h_lim : ∃ Λ : (∀ N : ℕ, R ⧸ span {(N ! : R)}) →ₐ[R] R,
      Semiconj Λ (Pi.map fun N : ℕ ↦ q N !) σ ∧
      ∀ N : ℕ, Finite (R ⧸ span {(N ! : R)}) ∧ IsTameAtLevel (q N !) p m :=
    h_tame.exists_algHom_semiconj_quotientNatMap hR
  choose Λ hΛ hfin htame using h_lim
  let π (N : ℕ) : R →+* R ⧸ span {(N ! : R)} := mk (span {(N ! : R)})
  have hY_map (N : ℕ) : (GeneralLinearGroup.map (π N) c).val = 1 + π N m • Y.map (π N) := by
    ext
    simp_all [one_apply]
  -- reduction modulo `N !` turns `σ` into `q N !`, so it keeps the twisted norm `1`
  have h_comm (N : ℕ) (δ : GL n R) : GeneralLinearGroup.map (π N) (GeneralLinearGroup.map σ δ) =
      GeneralLinearGroup.map (q N !) (GeneralLinearGroup.map (π N) δ) :=
    GeneralLinearGroup.ext fun _ _ ↦ rfl
  have hc_map (N : ℕ) :
      twistedNorm (GeneralLinearGroup.map (q N !)) p (GeneralLinearGroup.map (π N) c) = 1 := by
    rw [← map_twistedNorm _ (h_comm N), hc, map_one]
  choose k W hk hW using fun N ↦
    (htame N).hilbert90_gl_of_isArtinianRing inferInstance _ (hY_map N) (hc_map N)
  -- `L` is the `R`-algebra map from families of matrices over the quotients to matrices over `R`
  let L : (∀ N : ℕ, Matrix n n (R ⧸ span {(N ! : R)})) →ₐ[R] Matrix n n R :=
    Λ.mapMatrix.comp (piAlgEquiv (n := n) R).symm.toAlgHom
  refine ⟨(piUnits.symm k).map L, L W, ?_, ?_⟩
  · -- apply `L` to the equations `hk`: `L` fixes the constant `c` and commutes with `σ`
    have h_const : L (fun N ↦ (GeneralLinearGroup.map (π N) c).val) = c :=
      ext fun i j ↦ Λ.commutes (c i j)
    have h_σ : L (fun N ↦ (k N).val.map (q N !)) = (L fun N ↦ (k N).val).map σ :=
      ext fun i j ↦ hΛ _
    calc (c : Matrix n n R) * (L fun N ↦ (k N).val).map σ
        = L ((fun N ↦ (GeneralLinearGroup.map (π N) c).val) * fun N ↦ (k N).val.map (q N !)) := by
          rw [map_mul, h_const, h_σ]
      _ = L fun N ↦ (k N).val := congrArg L (funext hk)
  · -- apply `L` to the congruences `hW`
    calc _ = L (fun N ↦ (k N : Matrix n n (R ⧸ span {(N ! : R)}))) := rfl
      _ = L (1 + m • W) := congrArg L (funext hW)
      _ = 1 + m • L W := by rw [map_add, map_one, map_smul]

/-- Hilbert 90 for units at level `m`: let the commutative ring `R` be Artinian or profinite
(`IsProfiniteRing`: every sequence has a unique limit along the hyperfilter for the topology of the
ideals `(M)`). Let `σ` be tame at level `m` (`IsTameAtLevel σ p m`: `σ m = m`, `0 < p`, `σ ^ p = 1`,
some `e` has trace `∑ i < p, (σ ^ i) e ≡ 1 mod m`, and for `0 < i < p` every prime ideal modulo
which `σ ^ i` is the identity contains `m`). Then every unit `x ≡ 1 mod m` of norm
`x · σ x ⋯ σ^(p-1) x = 1` is `g / σ g`, i.e. `x * σ g = g`, for a unit `g ≡ 1 mod m`. -/
lemma IsTameAtLevel.hilbert90_unit (h_tame : IsTameAtLevel σ p m)
    (hR : IsArtinianRing R ∨ IsProfiniteRing R) (hx : IsUnit x) (hx_one : m ∣ x - 1)
    (hx_norm : ∏ i ∈ range p, (σ ^ i) x = 1) :
    ∃ g : Rˣ, m ∣ g - 1 ∧ x * σ g = g := by
  -- apply `hilbert90_gl` to the `1 × 1` matrix `x` and take the determinant of the solution
  obtain ⟨y, hy⟩ : ∃ y : R, x - 1 = m * y := hx_one
  let c : GL Unit R := diagGL fun _ : Unit ↦ hx.unit
  have hc_val : c.val = 1 + m • of fun _ _ ↦ y := by
    ext i j
    simpa [c] using eq_add_of_sub_eq' hy
  have hc_norm : twistedNorm (GeneralLinearGroup.map σ) p c = 1 := by aesop
  obtain ⟨k, W, hk, hW⟩ := h_tame.hilbert90_gl hR c hc_val hc_norm
  -- `k` is a `1 × 1` matrix, so its determinant is its only entry
  refine ⟨k.det, ?_, ?_⟩
  · have h_det : (k.det : R) = 1 + m * W () () := by simp [hW]
    rw [h_det, add_sub_cancel_left]
    exact dvd_mul_right m _
  · have h_entry : (c.val * k.val.map σ) () () = k.val () () := by rw [hk]
    simpa [c] using h_entry

/-- The case of `New.IsTameAtLevel.exists_prod_range_pow_apply_eq` where `R` is finite. Let `σ` be
tame at level `m`, meaning `σ m = m`, `σ ^ p = 1` with `0 < p`, some `e` has
`∑ i < p, (σ ^ i) e ≡ 1 mod m`, and for `0 < i < p` every prime ideal modulo which `σ ^ i` is the
identity contains `m`. Then every `σ`-fixed unit `x ≡ 1 mod m` is the norm `∏ i < p, (σ ^ i) z` of a
unit `z` with `z ≡ 1 mod m` and `z⁻¹ ≡ 1 mod m`. -/
lemma IsTameAtLevel.exists_norm_of_finite (h_tame : IsTameAtLevel σ p m) [Finite R] (hx : IsUnit x)
    (hσx : σ x = x) (hx_one : m ∣ x - 1) :
    ∃ z : Rˣ, m ∣ z - 1 ∧ m ∣ z⁻¹ - 1 ∧ ∏ i ∈ range p, (σ ^ i) z = x := by
  -- Count in the group `H` of units `≡ 1 mod m`, on which `σ ^ i` acts as `s i`. Norms are fixed,
  -- and by Hilbert 90 there are at least as many norms as fixed elements.
  have hσ : σ ^ p = 1 := h_tame.pow_eq_one
  let H : Subgroup Rˣ :=
    ((mk (span {m})).toMonoidHom.comp (Units.coeHom R)).ker.copy {x | m ∣ (x : R) - 1}
      (by simp [Set.ext_iff, ← eq_zero_iff_dvd, sub_eq_zero])
  -- each `σ ^ i` maps `H` to itself, as `σ m = m`
  have h_stable (i : ℕ) :
      Set.MapsTo (Units.map ((σ ^ i : R →+* R) : R →* R)) (H : Set Rˣ) (H : Set Rˣ) := by
    intro y hy
    have h_dvd : (σ ^ i) m ∣ (σ ^ i) ((y : R) - 1) := map_dvd (σ ^ i) hy
    show m ∣ ((Units.map ↑(σ ^ i) y : Rˣ) : R) - 1
    simpa [iterate_fixed h_tame.apply_eq_self] using h_dvd
  let s (i : ℕ) : H →* H := (Units.map ↑(σ ^ i)).restrict (h_stable i)
  let norm : H →* H := (range p).prod s
  let cob : H →* H := s 0 / s 1
  have h_s_coe (i : ℕ) (z : H) : ((s i z : Rˣ) : R) = (σ ^ i) ((z : Rˣ) : R) := rfl
  have h_norm_coe (z : H) : ((norm z : Rˣ) : R) = ∏ i ∈ range p, (σ ^ i) ((z : Rˣ) : R) := by
    simp [norm, h_s_coe]
  -- Norms are fixed by `σ`, and the kernel of `cob : z ↦ z / σ z` is the group of fixed elements.
  have h_range : norm.range ≤ cob.ker := by
    rintro _ ⟨z, rfl⟩
    apply div_eq_one_of_eq
    ext
    -- both sides are the norm of `z`, which `σ` fixes
    simpa [h_s_coe, h_norm_coe] using (isFixedPt_prod_range_pow_apply hσ
      (x := ((z : Rˣ) : R))).eq.symm
  -- Hilbert 90: elements of norm one are coboundaries.
  have h_ker : norm.ker ≤ cob.range := by
    intro u hu
    have hu_norm : ∏ i ∈ range p, (σ ^ i) ((u : Rˣ) : R) = 1 := by
      rw [← h_norm_coe, MonoidHom.mem_ker.mp hu]
      rfl
    obtain ⟨g, hg, hgu⟩ :=
      h_tame.hilbert90_unit (.inl inferInstance) (u : Rˣ).isUnit u.prop hu_norm
    exact ⟨⟨g, hg⟩, div_eq_of_eq_mul'' (Subtype.ext (Units.ext hgu.symm))⟩
  -- Hence there are at least as many norms as fixed elements.
  have h_card : Nat.card cob.ker ≤ Nat.card norm.range :=
    calc
      Nat.card cob.ker = cob.range.index := index_range.symm
      _ ≤ norm.ker.index := index_antitone h_ker
      _ = Nat.card norm.range := index_ker norm
  have hx_fixed : (⟨hx.unit, hx_one⟩ : H) ∈ cob.ker :=
    div_eq_one_of_eq (Subtype.ext (Units.ext hσx.symm))
  obtain ⟨z, hz⟩ : ∃ z : H, norm z = ⟨hx.unit, hx_one⟩ :=
    (eq_of_le_of_card_ge h_range h_card).ge hx_fixed
  refine ⟨z, z.prop, z⁻¹.prop, ?_⟩
  rw [← h_norm_coe, hz]
  exact hx.unit_spec

/-- Norms for a tame action at level `m`, meaning that `σ m = m`, `σ ^ p = 1` with `0 < p`, some `e`
has trace `∑ i < p, (σ ^ i) e ≡ 1 mod m`, and for `0 < i < p` every prime modulo which `σ ^ i` is
the identity contains `m`. If the commutative ring `R` is finite or profinite, every `σ`-fixed unit
`x ≡ 1 mod m` is the norm `z · σ z ⋯ σ^(p-1) z` of a unit `z` with `z ≡ 1` and `z⁻¹ ≡ 1 mod m`. -/
lemma IsTameAtLevel.exists_prod_range_pow_apply_eq (h_tame : IsTameAtLevel σ p m)
    (hR : Finite R ∨ IsProfiniteRing R) (hx : IsUnit x) (hσx : σ x = x) (hx_one : m ∣ x - 1) :
    ∃ z : Rˣ, m ∣ z - 1 ∧ m ∣ z⁻¹ - 1 ∧ ∏ i ∈ range p, (σ ^ i) z = x := by
  rcases hR with hfin | hR
  · exact h_tame.exists_norm_of_finite hx hσx hx_one
  -- Profinite case: solve in each finite quotient `R ⧸ N !` and apply the limit map `Λ`.
  let q (N : ℕ) : R ⧸ span {(N : R)} →+* R ⧸ span {(N : R)} := quotientNatMap σ N
  obtain ⟨Λ, hΛ, h_quotient⟩ : ∃ Λ : (∀ N : ℕ, R ⧸ span {(N ! : R)}) →ₐ[R] R,
      Semiconj Λ (Pi.map fun N : ℕ ↦ q N !) σ ∧
      ∀ N : ℕ, Finite (R ⧸ span {(N ! : R)}) ∧ IsTameAtLevel (q N !) p m :=
    h_tame.exists_algHom_semiconj_quotientNatMap hR
  choose h_finite h_tame_quotient using h_quotient
  have hx_fixed (N : ℕ) : q N ! (mk _ x) = mk _ x := by rw [quotientNatMap_mk, hσx]
  choose z hz hz_inv hz_norm using fun N ↦
    (h_tame_quotient N).exists_norm_of_finite (hx.map _) (hx_fixed N) (map_dvd _ hx_one)
  -- `Λ` keeps congruences modulo `m`
  have h_cong (y : ∀ N : ℕ, R ⧸ span {(N ! : R)})
      (hy : ∀ N : ℕ, mk (span {(N ! : R)}) m ∣ y N - 1) : m ∣ Λ y - 1 := by
    simpa using map_dvd Λ (pi_dvd_iff.mpr hy : algebraMap R _ m ∣ y - 1)
  use (piUnits.symm z).map Λ, h_cong _ hz, h_cong _ hz_inv
  -- `Λ` intertwines the powers of `σ`, is multiplicative and sends the residues of `x` to `x`
  have h_iter (i : ℕ) (y : ∀ N : ℕ, R ⧸ span {(N ! : R)}) :
      (σ ^ i) (Λ y) = Λ (fun N ↦ (q N ! ^ i) (y N)) := by
    rw [RingHom.coe_pow, ← (hΛ.iterate_right i).eq y, Pi.map_iterate]
    rfl
  have h_norms : Λ (fun N ↦ ∏ i ∈ range p, (q N ! ^ i) (z N : R ⧸ span {(N ! : R)})) = x :=
    (congrArg Λ (funext hz_norm)).trans (Λ.commutes x)
  calc ∏ i ∈ range p, (σ ^ i) (Λ fun N ↦ (z N : R ⧸ span {(N ! : R)}))
      = ∏ i ∈ range p, Λ (fun N ↦ (q N ! ^ i) (z N : R ⧸ span {(N ! : R)})) :=
        prod_congr rfl fun i _ ↦ h_iter i _
    _ = x := by rw [← map_prod, prod_fn, h_norms]

end New

end TameDescent
