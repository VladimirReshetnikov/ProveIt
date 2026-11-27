import Lib.Adelic.AutomorphicForms.HeckeEigenforms
import Lib.GaloisRep.BaseChange.CommutingHeckeFamilies

/-!
# Matching unit pairs at congruence levels and at unramified places of a step

This file concerns base change along a step `E' / E` (`New.IsStep`): an extension of prime degree
with a character `μ` of the finite ideles of `E`. It constructs levels at which the unit functions
match in the sense of `New.IsMatchingPair`.

## Main definitions and results

* `New.cocyclesSplit_and_isMatchingPair_of_congruence`: at a principal congruence level over a
  profinite ring with tame action, the cocycles split and the indicator functions of the level form
  a matching pair.
* `New.IsStepUnramifiedAt`: `w` is unramified in `E'`, and `μ ∘ Nm` kills the local units above `w`.
* `New.exists_isTameAtLevel_intAdeleMap`: `σ ≠ 1` is tame (`New.IsTameAtLevel`) on the integral
  adeles of `E'` at every `σ`-fixed level that vanishes at the totally ramified places dividing a
  fixed integer `C`.
* `New.exists_isBaseChangeLevel`: below any open subgroup `H` over `E` there are local levels over
  `E'` whose groups above any set of places are `σ`-stable, have split cocycles, and carry matching
  indicator functions.

Notions from other files:
* `New.IsTameAtLevel`: the conditions on a ring endomorphism `τ` with `τ ^ p = 1` and a level `m`
  under which descent works.
* `New.CocyclesSplit`: every `s` in `K` of twisted norm `1` under `τ` is a coboundary `t * (τ t)⁻¹`
  on the support of `u`, for some `t ∈ K` that is `1` off it.
* `New.IsMatchingPair`: a function `f` and a twisted function `φ` match, one characteristic
  polynomial at a time, through a polynomial root (`New.IsNormRoot`).
* `New.localLevel`: the elements of `New.Gf E n` whose component at each place of a set `S` lies in
  a given local group, by default `GL_n` of the local integers, with no condition outside `S`.

## Relation to the literature

Known; see `Lib.GaloisRep.BaseChange.PrimeDegreeTransfer` for sources.
-/

/-!
## Matching pairs at a congruence level over a profinite ring

The main lemma, `New.cocyclesSplit_and_isMatchingPair_of_congruence`, is the local input to the
comparison of trace formulas in base change at places with a principal congruence level.
-/

section UnitPairs

open Matrix Polynomial New U Set

/-- If `ι Y = v • (g - 1)` with `ι` injective, `ι` carries `τ` to `σ`, and `σ` fixes `v` and the
characteristic polynomial of `g`, then `τ` fixes the characteristic polynomial of `Y`. -/
lemma New.charpoly_map_eq_self_of_smul_sub_one {O R n : Type} [CommRing O] [CommRing R] [Fintype n]
    [DecidableEq n] {ι : O →+* R} (h_inj : (⇑ι).Injective) {τ : O →+* O} {σ : R →+* R}
    (hιτ : ∀ x : O, ι (τ x) = σ (ι x)) {v : R} (hσv : σ v = v) {Y : Matrix n n O} {g : Matrix n n R}
    (hY : Y.map ι = v • (g - 1)) (hg : g.charpoly.map σ = g.charpoly) :
    Y.charpoly.map τ = Y.charpoly := by
  -- Compare coefficients after applying the injective `ι`: `ι` carries `charpoly Y` to the
  -- characteristic polynomial of `v • (g - 1)`, whose coefficients are powers of `v` times those
  -- of `charpoly (g - 1) = (charpoly g).comp (X + 1)`, and `σ` fixes all of these.
  have h_shift : (g - 1).charpoly = g.charpoly.comp (X + 1) := by
    simpa using g.charpoly_sub_scalar 1
  refine Polynomial.ext fun i ↦ h_inj ?_
  rw [coeff_map, hιτ]
  simp [← coeff_map, ← charpoly_map, hY, hσv, hg, h_shift, charpoly_smul_coeff,
    Polynomial.map_add, map_comp]

/-- Let `O` be integrally closed in `R`, and let `-C` be a matrix over `R` killed by a monic
polynomial over `O`. If `M ∣ m` in `O`, then `det (1 + m • C)` is the image of an element of `O`
that is `1` modulo `M`. -/
lemma New.exists_det_one_add_smul_eq {O R k : Type} [CommRing O] [CommRing R] [Algebra O R]
    [Fintype k] [DecidableEq k] (h_closed : IsIntegrallyClosedIn O R) {C : Matrix k k R} {F : O[X]}
    (hF : F.Monic) (hC : aeval (-C) (F.map (algebraMap O R)) = 0) {m M : O} (hM : M ∣ m) :
    ∃ w : O, (1 + m • C).det = 1 + algebraMap O R (M * w) := by
  -- The characteristic polynomial of `-C` divides a power of `F`, so its coefficients are integral
  -- and come from `O`. Its reverse takes the value `det (1 + m • C)` at `m` and `1` at `0`.
  have h_dvd : (-C).charpoly ∣ (F ^ Fintype.card k).map (algebraMap O R) := by
    simpa [hC] using charpoly_dvd_charpoly_aeval_comp (Y := -C) (F.map (algebraMap O R))
  have h_int : (-C).charpoly.reverse ∈ lifts (algebraMap O R) := by
    refine (reverse _).lifts_iff_coeff_lifts.mpr fun i ↦ h_closed.isIntegral_iff.mp ?_
    simpa [reverse] using isIntegral_coeff_of_dvd _ _ (hF.pow _) (charpoly_monic _) h_dvd _
  obtain ⟨Q, hQ⟩ := (mem_lifts _).mp h_int
  obtain ⟨w, hw⟩ : M ∣ Q.eval m - Q.eval 0 := hM.trans (by simpa using Q.sub_dvd_eval_sub m 0)
  use w
  rw [← hw]
  simp [← eval_map_apply, hQ, eval_det, ← smul_eq_mul_diagonal, reverse_charpoly, charpolyRev]

/-- Let `ι Y = v • (g - 1)`. For a polynomial `r` over `O`, the characteristic polynomial of `r Y`
at `r (v • (B - 1))` is a multiple of the characteristic polynomial of `g` at `B`. -/
lemma New.aeval_charpoly_dvd_of_smul_sub_one {O R n k : Type} [CommRing O] [CommRing R] [Fintype n]
    [DecidableEq n] [Fintype k] [DecidableEq k] {ι : O →+* R} {v : R} {Y : Matrix n n O}
    {g : Matrix n n R} (hY : Y.map ι = v • (g - 1)) (B : Matrix k k R) (r : O[X]) :
    aeval B g.charpoly ∣ aeval (aeval (v • (B - 1)) (r.map ι)) ((aeval Y r).charpoly.map ι) := by
  -- `charpoly g` divides `(charpoly s(g)).comp s`; evaluate at `B` and read `s(g)` as `ι (r(Y))`.
  let s : R[X] := (r.map ι).comp (v • (X - 1))
  have h_dvd : g.charpoly ∣ (aeval g s).charpoly.comp s := charpoly_dvd_charpoly_aeval_comp s
  simpa [s, ← hY, ← map_aeval_matrix, charpoly_map, aeval_comp] using aeval_dvd B h_dvd

/-- For a unitary `γ`, a hermitian `v` and `a` with `a * v * v = v`, the matrix `B = v • (γ - 1)`
satisfies `star B * (1 + a • B) = -B`. -/
lemma New.star_smul_sub_one_mul_one_add_smul_eq_neg {R n : Type} [CommRing R] [StarRing R]
    [Fintype n] [DecidableEq n] {a v : R} (hav : a * v * v = v) (hv_star : star v = v)
    (γ : U (1 : Matrix n n R)) :
    star (v • (γ.val.val - 1)) * (1 + a • v • (γ.val.val - 1)) = -(v • (γ.val.val - 1)) := by
  -- Expand with `γᴴ = γ⁻¹`; `match_scalars` leaves one scalar identity for each of the
  -- coefficients, which follow from `a * v * v = v` and `star v = v`.
  simp [← inv_val_eq_conjTranspose, smul_smul, mul_add, mul_sub, sub_mul, star]
  match_scalars <;> grind

/-- The two support conditions of `New.IsMatchingPair` for the indicator functions of a subgroup
`L` of `G`. Let `Nm : G → G` map `L` into itself, and let `γ ∈ L` imply `a ∈ L`. Then the
indicator of `L` takes the same value at `j x` and at `a` whenever `j x = γ = Nm a`, and
`a⁻¹ * δ ∈ L` whenever `Nm δ = γ` and `δ` lies in the support of the indicator of `L`. -/
lemma indicator_comp_eq_and_inv_mul_mem_of_mem_imp_mem {G A : Type*} [Group G] {L : Subgroup G}
    {Nm : G → G} (j : A → G) (h_norm_mem : ∀ {δ : G}, δ ∈ L → Nm δ ∈ L) {γ a : G}
    (ha_mem : γ ∈ L → a ∈ L) :
    (∀ x : A, j x = γ → Nm a = γ → (indicator L 1 ∘ j) x = indicator L (1 : G → ℂ) a) ∧
    ∀ δ : G, Nm δ = γ → indicator L (1 : G → ℂ) δ ≠ 0 → a⁻¹ * δ ∈ L := by
  classical
  constructor
  · rintro x hjx rfl
    have h_iff : Nm a ∈ L ↔ a ∈ L := ⟨ha_mem, h_norm_mem⟩
    simp [hjx, Set.indicator_apply, h_iff]
  · rintro δ rfl hδ_supp
    have hδ_mem : δ ∈ L := by simpa using hδ_supp
    exact mul_mem (inv_mem (ha_mem (h_norm_mem hδ_mem))) hδ_mem

/-- Roots for one matrix in `New.cocyclesSplit_and_isMatchingPair_of_congruence`
(`ι = algebraMap O R`). Let `O` be profinite and integrally closed in `R`. Let `τ` commute with
`star`, be tame at levels `0` and `m = star m`, fix a `c` with `c - star c` a unit, and satisfy
`ι ∘ τ = σ ∘ ι`. Let `v` be `star`- and `σ`-fixed with `ι m * v = ι u` and `ι u * v = v`. If
`ι Y = v • (g - 1)`, `1 + m • Y` is a unit and `σ` fixes the characteristic polynomial of `g`, then
there are polynomials `z`, `z'` over `O` with the following property at `B' = v • (B - 1)`, for each
root `B` of that polynomial: `1 + m z'` inverts `1 + m z`, and the twisted norm
`T = (1 + m z) ⋯ τ^{p-1}(1 + m z)` has `(1 + m • B') * star T = T` if
`star B' * (1 + m • B') = -B'`. -/
lemma New.exists_twisted_root_of_smul_sub_one {O R n : Type} [CommRing O] [CommRing R]
    [Algebra O R] [StarRing O] {τ : O →+* O} {p : ℕ} {m c u : O} (hO : IsProfiniteRing O)
    (hτ_tame : IsTameAtLevel τ p 0) (hc : τ c = c) (h_unit : IsUnit (c - star c))
    (hm_star : star m = m) (hm_tame : IsTameAtLevel τ p m) (hτ : ∀ x : O, τ (star x) = star (τ x))
    [Fintype n] [DecidableEq n] [StarRing R] [StarModule O R]
    (h_closed : IsIntegrallyClosedIn O R) {σ : R →+* R} {v : R}
    (hιτ : ∀ x : O, algebraMap O R (τ x) = σ (algebraMap O R x))
    (hmv : algebraMap O R m * v = algebraMap O R u) (huv : algebraMap O R u * v = v)
    (hv_star : star v = v) (hσv : σ v = v) {Y : Matrix n n O} {g : U (1 : Matrix n n R)}
    (hY : Matrix.map Y (algebraMap O R) = v • (g.val.val - 1)) (hY_unit : IsUnit (1 + m • Y))
    (hP : g.val.val.charpoly.map σ = g.val.val.charpoly) :
    ∃ z z' : O[X], ∀ {k : Type} [Fintype k] [DecidableEq k] {B : Matrix k k R},
      aeval B g.val.val.charpoly = 0 →
      let B' := v • (B - 1)
      let T := aeval B' (twistedNorm (.map τ) p (1 + m • z))
      aeval B' ((1 + m • z') * (1 + m • z)) = 1 ∧
      (star B' * (1 + m • B') = -B' → (1 + m • B') * star T = T) := by
  set ι : O →+* R := algebraMap O R
  have hι : ∀ x : O, ι (star x) = star (ι x) := algebraMap_star_comm
  have h_inj : (⇑ι).Injective := h_closed.algebraMap_injective
  -- The hypotheses of `exists_isTwistedRoot_of_charpoly_eq` for `Y` can be checked after applying
  -- `ι`.
  have h_rel : Yᴴ * (1 + m • Y) ^ 1 = (-1) ^ 1 * Y := by
    apply map_injective h_inj
    simp [hY, hmv, huv, hv_star, conjTranspose_map _ hι, Matrix.map_neg,
      ← inv_val_eq_conjTranspose, ← mul_assoc, smul_sub, mul_add, Matrix.map_add, map_smul',
      mul_sub, sub_mul, smul_smul]
  obtain ⟨y, z, z', h_roots⟩ := exists_isTwistedRoot_of_charpoly_eq hO hτ_tame hc h_unit hτ hm_star
    hm_tame.left rfl
    (charpoly_map_eq_self_of_smul_sub_one h_inj hιτ hσv hY hP) le_rfl h_rel hY_unit
  refine ⟨z, z', fun {k} _ _ B hB ↦ ?_⟩
  -- `B' = v • (B - 1)` is a root of the characteristic polynomial of `Y`.
  have h_root : aeval (v • (B - 1)) Y.charpoly = 0 := by
    simpa [ι, hB] using aeval_charpoly_dvd_of_smul_sub_one hY B X
  obtain ⟨-, h_inv, h_norm, h_split⟩ := h_roots (B := v • (B - 1)) h_root
  refine ⟨h_inv hm_tame, fun h_rel_B ↦ ?_⟩
  -- The exponents in `exists_isTwistedRoot_of_charpoly_eq` are `0` and `1` here.
  simpa only [h_norm hm_tame, tsub_self, pow_zero, one_mul, pow_one] using
    h_split (by simpa only [pow_one, neg_one_mul] using h_rel_B)

/-- Determinants for one matrix in `New.exists_isNormRoot_and_mem_of_mem`, where `ι` is
`algebraMap O R` and `m = u * M`. Let `O` be integrally closed in `R`, let `ι Y = v • (g - 1)`, let
`B` be a root of the characteristic polynomial of `g`, and let `(1 + m z') (1 + m z)` be `1` at
`B' = v • (B - 1)`. Then `det ((1 + m z) (B'))` is `1 + ι (M * w)` for some `w` over `O`, with
inverse `1 + ι (M * w')` for some `w'` over `O`. -/
lemma New.exists_det_one_add_smul_aeval_eq_of_smul_sub_one {O R n k : Type} [CommRing O]
    [CommRing R] [Algebra O R] [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (h_closed : IsIntegrallyClosedIn O R) {u M m : O} (hm_eq : u * M = m) {v : R}
    {Y : Matrix n n O} {g : Matrix n n R} (hY : Matrix.map Y (algebraMap O R) = v • (g - 1))
    {B : Matrix k k R} (hB : aeval B g.charpoly = 0) {z z' : O[X]}
    (h_prod : aeval (v • (B - 1)) ((1 + m • z') * (1 + m • z)) = 1) :
    ∃ w w' : O, (1 + algebraMap O R (M * w)) * (1 + algebraMap O R (M * w')) = 1 ∧
      (1 + m • aeval (v • (B - 1)) z).det = 1 + algebraMap O R (M * w) := by
  -- For a polynomial `r` over `O`, the matrix `-r (v • (B - 1))` is killed by the characteristic
  -- polynomial of `-r Y`, since `B` is a root of the characteristic polynomial of `g`.
  set ι : O →+* R := algebraMap O R
  have h_det (r : O[X]) : ∃ w : O, (1 + m • aeval (v • (B - 1)) r).det = 1 + ι (M * w) := by
    have h_killed : aeval (-aeval (v • (B - 1)) r) ((aeval Y (-r)).charpoly.map ι) = 0 := by
      simpa [ι, hB] using aeval_charpoly_dvd_of_smul_sub_one hY B (-r)
    exact exists_det_one_add_smul_eq h_closed (charpoly_monic _) h_killed (Dvd.intro_left u hm_eq)
  obtain ⟨w, hw⟩ := h_det z
  obtain ⟨w', hw'⟩ := h_det z'
  -- Take determinants in `(1 + m z') (1 + m z) = 1` at `v • (B - 1)`.
  have h_prod_eval : (1 + m • aeval (v • (B - 1)) z') * (1 + m • aeval (v • (B - 1)) z) = 1 := by
    simpa only [map_mul, map_add, map_one, map_smul] using h_prod
  have h_inv : (1 + ι (M * w')) * (1 + ι (M * w)) = 1 := by
    rw [← hw, ← hw', ← Matrix.det_mul, h_prod_eval, Matrix.det_one]
  exact ⟨w, w', mul_eq_one_symm h_inv, hw⟩

/-- The root for one characteristic polynomial in
`New.cocyclesSplit_and_isMatchingPair_of_congruence`, in its setting, with `u` and `v` `star`-fixed,
`σ v = v` and `u * m = m`. Suppose `Y s` over `O` has `ι (Y s) = v • (s - 1)` for each `s ∈ L`, and
one `g ∈ L` has `1 + m • Y g` a unit and a `σ`-fixed characteristic polynomial `P`. Then some root
`z` for `P` (`New.IsNormRoot`; among its conditions, its value at each matrix root `B` of `P` has
determinant in `D`) has `γ ∈ L → a ∈ L` for unitary `γ` of characteristic polynomial `P` and
`a * (u • z)(γ)ᴴ = (u • z)(γ)`. -/
lemma New.exists_isNormRoot_and_mem_of_mem {O R n : Type} [CommRing O] [CommRing R] [Algebra O R]
    [StarRing O] {τ : O →+* O} {p : ℕ} {m c : O} (u : O) (hO : IsProfiniteRing O)
    (hτ_tame : IsTameAtLevel τ p 0) (hc : τ c = c) (h_unit : IsUnit (c - star c))
    (hm_star : star m = m) (hm_tame : IsTameAtLevel τ p m) (hτ : ∀ x : O, τ (star x) = star (τ x))
    [Fintype n] [DecidableEq n] [StarRing R] [StarModule O R]
    (h_closed : IsIntegrallyClosedIn O R) {σ : R →+* R} {v : R} {M : O}
    {L : Subgroup (U (1 : Matrix n n R))} {D : Subgroup Rˣ} (hm_eq : u * M = m)
    (hιτ : ∀ x : O, algebraMap O R (τ x) = σ (algebraMap O R x))
    (hmv : algebraMap O R m * v = algebraMap O R u) (huv : algebraMap O R u * v = v)
    (hL : ∀ g : U (1 : Matrix n n R),
      g ∈ L ↔ ∃ Y : Matrix n n O, Matrix.map Y (algebraMap O R) = v • (g.val.val - 1))
    (hD : ∀ (y z : O) (h_inv : (1 + algebraMap O R (M * y)) * (1 + algebraMap O R (M * z)) = 1),
      Units.mkOfMulEqOne (1 + algebraMap O R (M * y)) (1 + algebraMap O R (M * z)) h_inv ∈ D)
    (hu_star : star (algebraMap O R u) = algebraMap O R u) (hv_star : star v = v)
    (hum : algebraMap O R u * algebraMap O R m = algebraMap O R m) (hσv : σ v = v)
    (Y : ∀ s : U (1 : Matrix n n R), s ∈ L → Matrix n n O)
    (hY : ∀ (s : U (1 : Matrix n n R)) (hs : s ∈ L),
      Matrix.map (Y s hs) (algebraMap O R) = v • (s.val.val - 1))
    {g : U (1 : Matrix n n R)} (hg : g ∈ L) (hg_unit : IsUnit (1 + m • Y g hg))
    (hP : g.val.val.charpoly.map σ = g.val.val.charpoly) :
    ∃ z : Polynomial R, IsNormRoot n σ p (algebraMap O R u) D g.val.val.charpoly z ∧
      ∀ γ a : U (1 : Matrix n n R), γ.val.val.charpoly = g.val.val.charpoly →
        IsRootQuotient γ (algebraMap O R u • z) a.val → γ ∈ L → a ∈ L := by
  classical
  set ι : O →+* R := algebraMap O R
  have hι : ∀ x : O, ι (star x) = star (ι x) := algebraMap_star_comm
  -- `q r` is `r` read in the coordinate `v • (X - 1)`
  let q : O[X] →+* R[X] := (compRingHom (v • (X - 1))).comp (mapRingHom ι)
  obtain ⟨z, z', h_at⟩ := exists_twisted_root_of_smul_sub_one hO hτ_tame hc h_unit hm_star hm_tame
    hτ h_closed hιτ hmv huv hv_star hσv (hY g hg) hg_unit hP
  have h_self (γ : U (1 : Matrix n n R)) (hγ : γ.val.val.charpoly = g.val.val.charpoly) :
      aeval γ.val.val g.val.val.charpoly = 0 := by rw [← hγ, aeval_self_charpoly]
  -- The root is `q (1 + m z)`: first the conditions of `IsNormRoot`, then `a ∈ L`.
  refine ⟨q (1 + m • z), ⟨?_, fun γ hγ ↦ ⟨fun _ B hB ↦ ?_, ?_⟩⟩, fun γ a hγ ha ↦ ?_⟩
  · simp [q, hum, Polynomial.map_add, smul_smul, sub_mul]
  · -- The determinant of the root at `B` is a unit `1 + ι (M * w)` of the kind that `D` contains.
    obtain ⟨w, w', h_inv, h_det⟩ : ∃ w w' : O, (1 + ι (M * w)) * (1 + ι (M * w')) = 1 ∧
        (1 + m • aeval (v • (B - 1)) z).det = 1 + ι (M * w) :=
      exists_det_one_add_smul_aeval_eq_of_smul_sub_one h_closed hm_eq (hY g hg) hB (h_at hB).left
    have h_q_eval : aeval B (q (1 + m • z)) = 1 + m • aeval (v • (B - 1)) z := by
      simp [q, ι, AlgHom.map_smul_of_tower, aeval_comp, aeval_map_algebraMap]
    have h_det_eq : (aeval B (q (1 + m • z))).det = 1 + ι (M * w) := by rw [h_q_eval, h_det]
    exact ⟨_, hD _ _ h_inv, h_det_eq.symm⟩
  · -- `B' = v • (γ - 1)` satisfies `star B' * (1 + m • B') = -B'`.
    have hB :
        star (v • (γ.val.val - 1)) * (1 + m • v • (γ.val.val - 1)) = -(v • (γ.val.val - 1)) := by
      simpa only [algebraMap_smul, ι] using
        star_smul_sub_one_mul_one_add_smul_eq_neg (a := ι m) (by rw [hmv, huv]) hv_star γ
    -- `q` commutes with taking norms, as `σ` fixes `v`
    have hq (r : O[X]) : q (r.map τ) = (q r).map σ := by
      simp [q, hσv, Polynomial.map_map, show ι.comp τ = σ.comp ι from RingHom.ext hιτ, map_comp]
    have hT : aeval γ.val.val (twistedNorm (.map σ) p (q (1 + m • z))) =
        aeval (v • (γ.val.val - 1)) (twistedNorm (.map τ) p (1 + m • z)) := by
      simpa [q, ι, aeval_comp] using
        congrArg (aeval γ.val.val) (map_twistedNorm q.toMonoidHom hq p (1 + m • z)).symm
    rw [IsRootQuotient, hT, ← hmv, mul_smul, algebraMap_smul]
    exact (h_at (h_self γ hγ)).2 hB
  -- If `γ ∈ L`, multiply `a * Zᴴ = Z` on the `u`-part, `Z = (1 + m z) (Y γ)`, by the adjoint of the
  -- inverse `1 + m z'`; this shows that `v • (a - 1)` comes from `O`.
  intro hγ_mem
  have h_inv : aeval (v • (γ.val.val - 1)) ((1 + m • z') * (1 + m • z)) = 1 :=
    (h_at (h_self γ hγ)).1
  have h_va_eq : v • a.val.val = v • (aeval (v • (γ.val.val - 1)) (1 + m • z) *
      (aeval (v • (γ.val.val - 1)) (1 + m • z'))ᴴ) := by
    let W : Matrix n n R := (aeval γ.val.val (q (1 + m • z')))ᴴ
    have h_mul : v • (a.val.val * (aeval γ.val.val (ι u • q (1 + m • z)))ᴴ) * W =
        v • aeval γ.val.val (ι u • q (1 + m • z)) * W := congrArg (fun x ↦ v • x * W) ha
    simpa [W, h_inv, huv, hu_star, ι, -algebraMap_smul, mul_comm v, ← map_mul, q, mul_assoc,
      -map_add, -Polynomial.map_add, ← conjTranspose_mul, aeval_comp, smul_smul] using h_mul
  refine (hL a).mpr ⟨u • (z.aeval (Y γ hγ_mem) + (1 + m • z).aeval (Y γ hγ_mem) *
    (z'.aeval (Y γ hγ_mem))ᴴ), ?_⟩
  simp [hm_star, conjTranspose_map _ hι, map_aeval_matrix, ι, smul_sub, ← hmv, hY, add_assoc,
    mul_smul, smul_comm v, h_va_eq, Matrix.map_add, map_smul', mul_add]

/-- Let `O` be profinite and integrally closed in `R`. Let `τ`, with `τ ^ p = 1`, be tame on `O` at
the levels `0` and `m = u * M` (`star m = m`), commute with `star`, and fix some `c` with
`c - star c` a unit. `ι = algebraMap O R` carries `τ` to a `σ` that commutes with `star`;
`mapEnd hσ` applies `σ` to each entry of a unitary matrix. Let `L` be the `σ`-stable group of
unitary `g` over `R` with `v • (g - 1)` over `O`, where `m * v = u` and `u * v = v`. Then (a) the
cocycles in `L` split on the support of `u`, and (b) for any map `j : A → U 1`, the indicator of `L`
and its pull-back along `j` form a matching pair (`New.IsMatchingPair`) for every `D` that holds the
units `1 + ι (M * y)`. -/
lemma New.cocyclesSplit_and_isMatchingPair_of_congruence {O R n : Type} [CommRing O] [CommRing R]
    [Algebra O R] [StarRing O] {τ : O →+* O} {p : ℕ} {m c : O} (u : O) (hO : IsProfiniteRing O)
    (hτ_tame : IsTameAtLevel τ p 0) (hc : τ c = c) (h_unit : IsUnit (c - star c))
    (hm_star : star m = m) (hm_tame : IsTameAtLevel τ p m) (hτ : ∀ x : O, τ (star x) = star (τ x))
    [Fintype n] [DecidableEq n] [StarRing R] (h_starModule : StarModule O R)
    (h_closed : IsIntegrallyClosedIn O R) {σ : R →+* R} (hσ : ∀ (x : R), σ (star x) = star (σ x))
    {v : R} {M : O} {L : Subgroup (U (1 : Matrix n n R))} {D : Subgroup Rˣ} {A : Type*}
    {j : A → U (1 : Matrix n n R)} (hm_eq : u * M = m)
    (hL_tw : ∀ k ∈ L, mapEnd (n := n) (σ := σ) hσ k ∈ L)
    (hιτ : ∀ x : O, algebraMap O R (τ x) = σ (algebraMap O R x))
    (hmv : algebraMap O R m * v = algebraMap O R u) (huv : algebraMap O R u * v = v)
    (hL : ∀ g : U (1 : Matrix n n R),
      g ∈ L ↔ ∃ Y : Matrix n n O, Matrix.map Y (algebraMap O R) = v • (g.val.val - 1))
    (hD : ∀ (y z : O) (h_inv : (1 + algebraMap O R (M * y)) * (1 + algebraMap O R (M * z)) = 1),
      Units.mkOfMulEqOne (1 + algebraMap O R (M * y)) (1 + algebraMap O R (M * z)) h_inv ∈ D) :
    -- (a)
    CocyclesSplit p (algebraMap O R u) L (mapEnd hσ) ∧
    -- (b)
    IsMatchingPair (A := A) hσ p (algebraMap O R u) D j L (indicator L 1 ∘ j) (indicator L 1) := by
  classical
  -- An element `s ∈ L` has `v • (s - 1) = ι Y` with `Y` over `O`, and `1 + m • Y` is a unitary
  -- matrix over `O` that lifts the `u`-part `cutAt s` of `s`. Both claims are transported from `O`:
  -- the first is Hilbert 90 at level `m`, the second uses the root that
  -- `New.exists_isNormRoot_and_mem_of_mem` gives.
  set ι : O →+* R := algebraMap O R
  have hι : ∀ x : O, ι (star x) = star (ι x) := algebraMap_star_comm
  have h_inj : (⇑ι).Injective := h_closed.algebraMap_injective
  -- `ι u` is an idempotent with `ι u * ι m = ι m`. The relations with `ι m` determine `ι u` and
  -- `v`, so `star` and `σ`, which fix `ι m`, fix them too.
  have hu : ι u * ι u = ι u := by linear_combination (1 - ι u) * hmv + ι m * huv
  have hum : ι u * ι m = ι m := by rw [← hm_eq, map_mul, ← mul_assoc, hu]
  have h_unique {a b : R} (hmb : ι m * b = a) (hab : a * b = b) (ham : a * ι m = ι m) :
      a = ι u ∧ b = v := by
    have ha : a = ι u := by linear_combination (ι u - 1) * hmb - b * hum + (1 - a) * hmv + v * ham
    exact ⟨ha, by linear_combination (b + v) * ha - hab - b * hmv + v * hmb + huv⟩
  have h_fixed (φ : R →+* R) (hφ : φ (ι m) = ι m) : φ (ι u) = ι u ∧ φ v = v := by
    apply h_unique
    · rw [← hmv, map_mul φ, hφ]
    · rw [← map_mul φ, huv]
    · rw [← hφ, ← map_mul φ, hum]
  obtain ⟨hu_star, hv_star⟩ : star (ι u) = ι u ∧ star v = v :=
    h_fixed (starRingEnd R) (by rw [starRingEnd_apply, ← hι, hm_star])
  obtain ⟨hσu, hσv⟩ := h_fixed σ (by rw [← hιτ, hm_tame.apply_eq_self])
  let e : U (1 : Matrix n n O) →* U (1 : Matrix n n R) := map ι hι (one_map_ringHom ι)
  choose Y hY using fun s ↦ (hL s).mp
  have h_lift (s : U (1 : Matrix n n R)) (hs : s ∈ L) :
      ∃ S : U (1 : Matrix n n O), S.val.val = 1 + m • Y s hs ∧ e S = cutAt hu hu_star s := by
    refine mem_range_map hι h_inj isUnit_one _ ?_
    simp [hY, hmv, Matrix.map_add, map_smul', smul_smul, cutAt, cutGL]
    module
  choose S hS hS_cut using h_lift
  have h_norm_mem {δ : U (1 : Matrix n n R)} : δ ∈ L → twistedNorm (mapEnd hσ) p δ ∈ L :=
    twistedNorm_mem (mapEnd hσ) p hL_tw
  refine ⟨fun s hs hN ↦ ?_, ?_, ?_⟩
  · -- the lift of `s` has norm `1` too, so it is a coboundary of some `t ≡ 1` mod `m`
    -- `e` and `cutAt` commute with the twists, so `e` carries the norm of `S s` to that of `s`.
    have h_e_comm (δ : U (1 : Matrix n n O)) : e (mapEnd hτ δ) = mapEnd hσ (e δ) := by
      simp [Units.ext_iff, e, U.map, hιτ, Function.comp_def]
    have h_cut_comm (δ : U (1 : Matrix n n R)) :
        cutAt hu hu_star (mapEnd hσ δ) = mapEnd hσ (cutAt hu hu_star δ) := by
      simp [Units.ext_iff, U.map, hσu, cutAt, cutGL, Matrix.map_add, map_smul']
    have h_norm : e (twistedNorm (mapEnd hτ) p (S s hs)) = e 1 := by
      rw [map_twistedNorm (σ := mapEnd hσ) e h_e_comm, hS_cut,
        ← map_twistedNorm (cutAt hu hu_star) h_cut_comm, hN, map_one, map_one]
    obtain ⟨t, W, ht : S s hs * mapEnd hτ t = t, hW : t.val.val = 1 + m • W⟩ :=
      unitary_hilbert90_at_level hO hτ_tame hc h_unit hτ (S s hs) hm_star hm_tame (hS s hs)
        (map_injective h_inj (congrArg (fun x : U (1 : Matrix n n R) ↦ x.val.val) h_norm))
    have h_et_mem : e t ∈ L := (hL (e t)).mpr ⟨u • W, by
      simp [e, U.map, hW, hmv, mul_comm v, map_smul', Matrix.map_add, smul_smul]⟩
    have h_et_off : (1 - ι u) • (e t).val.val = (1 - ι u) • 1 := by
      simp [e, U.map, hW, hum, Matrix.map_add, map_smul', smul_smul, sub_mul]
    refine ⟨e t, h_et_mem, h_et_off, ?_⟩
    -- On the `u`-part, `t⁻¹ * s * τ t = 1` is `e` applied to `t⁻¹ * S * τ t = 1`.
    have h_cob :
        ι u • (e (t⁻¹ * (S s hs * mapEnd hτ t))).val.val = ι u • (e (t⁻¹ * t)).val.val := by rw [ht]
    simpa [e, U.map, hS, hY, hmv, hu, hιτ, add_mul, mul_assoc, smul_sub, Function.comp_def,
      Matrix.map_add, map_smul', smul_smul, sub_mul, mul_add, mul_sub] using h_cob
  · -- the indicator of `L` is invariant under twisted conjugation by `L`
    simp +contextual [mul_mem_cancel_left, mul_mem_cancel_right, hL_tw, indicator]
  -- The polynomial is that of some `g`, which lies in `L` by the supports.
  rintro _ ⟨g, hg_supp, rfl⟩ hP
  have hg : g ∈ L := by
    rcases hg_supp with ⟨x, hx_supp, rfl⟩ | ⟨δ, hδ_supp, rfl⟩
    · simpa using hx_supp
    · exact h_norm_mem (by simpa using hδ_supp)
  obtain ⟨z, hz_root, hz_mem⟩ := exists_isNormRoot_and_mem_of_mem u hO hτ_tame hc h_unit hm_star
    hm_tame hτ h_closed hm_eq hιτ hmv huv hL hD hu_star hv_star hum hσv Y hY hg
    ⟨(S g hg).val, hS g hg⟩ hP
  exact ⟨z, hz_root, fun γ a hγ ha ↦
    indicator_comp_eq_and_inv_mul_mem_of_mem_imp_mem j h_norm_mem (hz_mem γ a hγ ha)⟩

end UnitPairs

/-!
## Unramified places of a step and levels with matching unit pairs

`New.placesAbove E' S` is the set of places above `S` and its conjugates, `New.idem A` the adele
that is `1` at the places of `A` and `0` elsewhere, `New.kerCompNorm E' μ` the kernel of `μ ∘ Nm`,
`New.baseChangeGf` the inclusion of the unitary groups, `New.galoisGf σ` the Galois action, and
`New.IsMatchingPairAbove` the matching condition `New.IsMatchingPair` above `S`.
-/

section BaseChangeLevel

open NumberField Matrix Set Valued Module Ideal Subtype

namespace New

variable {E E' n : Type} [Field E] [CMType E] [Field E'] [Algebra E E']

section

variable [NumberField E'] (μ : (𝔸f E)ˣ →* ℂˣ)

/-- The place `u` of `E'` is unramified for the step `E' / E` and the character `μ`: its inertia
group is not all of `Gal(E'/E)`, and `μ` kills the norms of the local units at `u`. -/
structure IsStepUnramifiedPlace (u : FinPlace E') : Prop where
  /-- The inertia group of `u` is not all of `Gal(E'/E)`. -/
  exists_notMem_inertia : ∃ τ : Gal(E'/E), τ ∉ u.asIdeal.inertia Gal(E'/E)
  /-- `μ` is trivial on the norms of the local units at `u`. -/
  apply_localNorm_eq_one (x : (LocField u)ˣ) (hx : v x.val = 1) :
    μ (locIdele (u.below E) (localNorm E u x)) = 1

variable (E') in
/-- The place `w` of `E` is unramified for the step `E' / E` and the character `μ`: so is every
place of `E'` above it. -/
def IsStepUnramifiedAt (w : FinPlace E) : Prop :=
  ∀ u : FinPlace E', u.below E = w → IsStepUnramifiedPlace μ u

end

variable [CMType E'] [Fintype n] [DecidableEq n] (σ : Gal(E'/E)) (μ : (𝔸f E)ˣ →* ℂˣ)

/-- The subgroup `L` of the finite adelic unitary group over `E'` is a level at which the
indicator functions match above the set `S` of places of `E` and its conjugates: `L` is open and
stable under `σ`, its cocycles split above `S`, and the indicator function of `L` matches its
pull-back to `E`. -/
structure IsMatchingLevel (S : Set (FinPlace E)) (L : Subgroup (Gf E' n)) : Prop where
  /-- `L` is open. -/
  isOpen : L.IsOpen
  /-- `L` is stable under `σ`. -/
  galoisGf_mem_iff (k : Gf E' n) : galoisGf σ k ∈ L ↔ k ∈ L
  /-- The cocycles in `L` are coboundaries above `S`. -/
  cocyclesSplit : CocyclesSplit (finrank E E') (idem (placesAbove E' S)) L (galoisGf σ)
  /-- The indicator function of `L` and its pull-back to `E` form a matching pair above `S`. -/
  isMatchingPairAbove_indicator :
    IsMatchingPairAbove σ μ S L (indicator L 1 ∘ baseChangeGf (E' := E')) (indicator L 1)

/-- The local levels `K u` over `E'` form a base change level below the subgroup `H` of the finite
adelic unitary group over `E`. -/
structure IsBaseChangeLevel (H : Subgroup (Gf E n))
    (K : (u : FinPlace E') → Subgroup (GL n (LocField u))) : Prop where
  /-- Each `K u` lies in `GL_n(O_u)`. -/
  le_localIntGL (u : FinPlace E') : K u ≤ localIntGL n u
  /-- The group cut out by `K` above any set `S` and its conjugates is a matching level. -/
  isMatchingLevel (S : Set (FinPlace E)) :
    IsMatchingLevel σ μ S (localLevel n (placesAbove E' S) K)
  /-- The elements over `E` that lie in `K u` at every `u` lie in `H`. -/
  comap_le : (localLevel n univ K).comap baseChangeGf ≤ H
  /-- `K u = GL_n(O_u)` at the places `u` above an unramified place `w` and its conjugate, when
  `H` contains the integral points supported at `w` and its conjugate (`maxCompactAt n w`). -/
  eq_localIntGL (w : FinPlace E) (hw : IsStepUnramifiedAt E' μ w) (hH : maxCompactAt n w ≤ H)
    (u : FinPlace E') (hu : u ∈ placesAbove E' {w}) : K u = localIntGL n u

end New

namespace New

variable {E E' n : Type} [Field E] [CMType E] [Field E'] [CMType E'] [Algebra E E']
  [Fintype n] [DecidableEq n] {σ : Gal(E'/E)} (hσ : σ ≠ 1)
  {μ : (𝔸f E)ˣ →* ℂˣ} [hμ : IsStep (E := E) E' μ] {f : E →+* E}

/-- If the conjugate place `star u` is unramified for the step, so is `u`. -/
lemma IsStepUnramifiedPlace.of_star {u : FinPlace E'}
    (h_unram : IsStepUnramifiedPlace μ (star u)) : IsStepUnramifiedPlace μ u := by
  constructor
  · -- An element outside the inertia group of `star u` is outside that of `u`, since complex
    -- conjugation commutes with it.
    obtain ⟨τ, hτ⟩ := h_unram.exists_notMem_inertia
    refine ⟨τ, fun h_inertia ↦ hτ fun x ↦ ?_⟩
    have h_comm : τ • star x = star (τ • x) := RingOfIntegers.ext (map_star_CM τ.toRingHom _)
    have h_mem : τ • star x - star x ∈ u.asIdeal := h_inertia (star x)
    simpa [h_comm] using h_mem
  · -- For the norm `z` of a local unit `y`, `μ` kills `z * star z`, and `star z` is the norm of a
    -- local unit at `star u`, which `μ` kills too.
    intro y hy
    let z : (𝔸f E)ˣ := Units.map (adeleNorm E E') (locIdele u y)
    have h_sign : μ (z * star z) = 1 :=
      (hμ.apply_norm_eq_one_iff z).2 ⟨1, locIdele u y, by simp [z]⟩
    have h_star : μ (star z) = 1 := by
      rw [← units_map_adeleNorm_star, star_locIdele, adeleNorm_locIdele]
      exact h_unram.apply_localNorm_eq_one _ (by simpa using hy)
    have h_norm : z = locIdele (u.below E) (localNorm E u y) := adeleNorm_locIdele u y
    rwa [map_mul, h_star, mul_one, h_norm] at h_sign

/-- The finite adele that is `1` at the places of `A` and `x` at the others. -/
noncomputable def adeleOneOn {F : Type} [Field F] [NumberField F] (A : Set (FinPlace F))
    (x : 𝔸f F) : 𝔸f F :=
  x + idem A * (1 - x)

/-- The adele `adeleOneOn A x`, which is `1` on `A` and `x` off `A`, is continuous in `x`. -/
@[fun_prop]
lemma continuous_adeleOneOn {F : Type} [Field F] [NumberField F] (A : Set (FinPlace F)) :
    Continuous (adeleOneOn A) := by
  unfold adeleOneOn
  fun_prop

/-- If `a * b = 1`, the adeles that are `1` on `A` and `a`, resp. `b`, off `A` are inverse to each
other. -/
lemma adeleOneOn_mul_adeleOneOn_of_mul_eq_one (A : Set (FinPlace E')) {a b : 𝔸f E'}
    (h_mul : a * b = 1) : adeleOneOn A a * adeleOneOn A b = 1 := by
  -- `idem A` is idempotent, so the product is `a * b` off `A` and `1` on `A`.
  unfold adeleOneOn
  linear_combination (1 - idem A) * h_mul + ((1 - a) * (1 - b)) * idem_mul_self A

/-- Let every place of the set `T` of places of `E` be unramified for the step. Then so is every
place of `E'` above a place of `T` or above the conjugate of one. -/
lemma isStepUnramifiedPlace_of_mem_placesAbove {T : Set (FinPlace E)}
    (hT : ∀ w ∈ T, IsStepUnramifiedAt E' μ w) {u : FinPlace E'} (hu : u ∈ placesAbove E' T) :
    IsStepUnramifiedPlace μ u := by
  -- Either `u` lies above `T`, or `star u` does.
  rcases hu with h_below | h_star_below
  · exact hT (u.below E) h_below u rfl
  · exact (hT (star (u.below E)) h_star_below (star u) (below_star u)).of_star

/-- Let `μ` kill the norms of the local units at the places of `A`. For `x` near `0`, a unit idele
congruent to `1` modulo `adeleOneOn A x` lies in `kerCompNorm E' μ`, the kernel of `μ ∘ Nm`. -/
lemma eventually_mem_kerCompNorm_of_apply_localNorm_eq_one {A : Set (FinPlace E')}
    (hA : ∀ u ∈ A, ∀ x : (LocField u)ˣ, v x.val = 1 →
      μ (locIdele (u.below E) (localNorm E u x)) = 1) :
    ∀ᶠ x : 𝔸f E' in nhds (0 : 𝔸f E'), ∀ y ∈ Ô E', ∀ d ∈ idelesUnitOff ∅,
      d.val - adeleOneOn A x * y = 1 → d ∈ kerCompNorm E' μ := by
  -- By compactness (the tube lemma) it is enough to see this at `x = 0`. There such an idele is
  -- `1` off `A`, and on `A` its components are local units, whose norms `μ` kills.
  have h_compact : IsCompact ((Ô E' : Set (𝔸f E')) ×ˢ
      ((idelesUnitOff (∅ : Set (FinPlace E')) : Set (𝔸f E')ˣ) \ (kerCompNorm E' μ).carrier)) :=
    isCompact_Ô.prod (isCompact_idelesUnitOff_empty.diff hμ.isClopen_kerCompNorm.isOpen)
  refine (h_compact.eventually_forall_mem
      (fun x (p : 𝔸f E' × (𝔸f E')ˣ) ↦ p.snd.val - adeleOneOn A x * p.fst) {1}ᶜ ?_).mono
    fun x hx y hy d hd h_eq ↦ by_contra fun h_notMem ↦ hx (y, d) ⟨hy, hd, h_notMem⟩ h_eq
  rintro ⟨y, d⟩ ⟨-, hd, h_notMem⟩
  refine isOpen_ne.mem_nhds fun h_eq ↦
    h_notMem (mem_of_locIdele_mem hμ.isClopen_kerCompNorm.isClosed fun u ↦ ?_)
  show μ (Units.map (adeleNorm E E') (locIdele u (ideleAt u d))) = 1
  rw [adeleNorm_locIdele]
  by_cases hu : u ∈ A
  · exact hA u hu _ (mem_idelesUnitOff.1 hd u (notMem_empty u))
  · have hd_one : ideleAt u d = 1 := Units.ext <| by
      simpa [adeleOneOn, hu, ideleAt] using congrArg (fun z : 𝔸f E' ↦ z u) h_eq
    simp [hd_one]

/-- Let `A` be a set of unramified places. For `x` near `0`, the norm of a unit idele congruent to
`1` modulo `adeleOneOn A x` is killed by `μ`. -/
lemma eventually_mem_kerCompNorm {A : Set (FinPlace E')} (hA : ∀ u ∈ A, IsStepUnramifiedPlace μ u) :
    ∀ᶠ x : 𝔸f E' in nhds (0 : 𝔸f E'), ∀ y ∈ Ô E', ∀ d ∈ idelesUnitOff ∅,
      d.val - adeleOneOn A x * y = 1 → d ∈ kerCompNorm E' μ :=
  eventually_mem_kerCompNorm_of_apply_localNorm_eq_one fun u hu ↦ (hA u hu).apply_localNorm_eq_one

/-- Let the open subgroup `H` contain the integral points that are trivial on `S`, and let no place
of `A` lie above `S`. For `x` near `0`, an integral point `g` over `E` whose matrix over `E'` is
congruent to `1` modulo `adeleOneOn A x` lies in `H`. -/
lemma eventually_mem_of_baseChangeGf_congr {H : Subgroup (Gf E n)} (hH : H.IsOpen)
    {S : Set (FinPlace E)} (hS : stdLevel E n ⊓ Gf.trivialOn n S ≤ H) {A : Set (FinPlace E')}
    (hA : ∀ u ∈ A, u.below E ∉ S) :
    ∀ᶠ x : 𝔸f E' in nhds (0 : 𝔸f E'),
      ∀ Y : Matrix n n (𝔸f E'), (∀ i j : n, Y i j ∈ Ô E') → ∀ g ∈ stdLevel E n,
      (baseChangeGf g : Gf E' n).val.val - adeleOneOn A x • Y = 1 → g ∈ H := by
  -- By compactness (the tube lemma) it is enough to see this at `x = 0`. There such a point is `1`
  -- at the places of `S`, since no place above `S` is in `A`, so it lies in `H`.
  refine ((isCompact_Ô.matrix.prod (isCompact_stdLevel.diff hH)).eventually_forall_mem
      (fun x (p : Matrix n n (𝔸f E') × Gf E n) ↦
        p.snd.val.val.map (finAdeleIncl E E') - adeleOneOn A x • p.fst) {1}ᶜ ?_).mono ?_
  · rintro ⟨Y, g⟩ ⟨-, hg, h_notMem⟩
    refine isOpen_ne.mem_nhds fun h_eq ↦ h_notMem (hS ⟨hg, Gf.mem_trivialOn.2 fun w hw ↦ ?_⟩)
    obtain ⟨u, rfl⟩ := FinPlace.comap_surjective (algebraMap E E') w
    have huA : u ∉ A := fun hu ↦ hA u hu hw
    refine GeneralLinearGroup.ext fun i j ↦ (locMap (algebraMap E E') (w := u) rfl).injective ?_
    have h_entry : (g.val.val.map (finAdeleIncl E E')) i j u = (1 + adeleOneOn A 0 • Y) i j u := by
      rw [eq_add_of_sub_eq h_eq]
    refine h_entry.trans ?_
    by_cases hij : i = j <;> simp [adeleOneOn, hij, huA]
  · intro x hx Y hY g hg h_eq
    by_contra h_notMem
    exact hx (Y, g) ⟨hY, hg, h_notMem⟩ h_eq

/-- The elements `g` of `GL_n(O_u)` with `k * (g - 1)` integral at `u`. For `k` the inverse of an
integral adele `m`, this is the principal congruence subgroup of level `m` at `u`. -/
noncomputable def congruenceLevel {F : Type} [Field F] [NumberField F] (n : Type) [Fintype n]
    [DecidableEq n] (k : 𝔸f F) (u : FinPlace F) :
    Subgroup (GL n (LocField u)) :=
  congruenceGL ((v.leSubmodule 1).comap (.mulLeft v.integer (k u))) id

/-- An element `g` of `GL_n` of the completion at `u` lies in `congruenceLevel n k u` exactly when
it lies in `GL_n(O_u)` and `k * (g - 1)` has integral entries at `u`. -/
lemma mem_congruenceLevel {k : 𝔸f E'} {u : FinPlace E'} {g : GL n (LocField u)} :
    g ∈ congruenceLevel n k u ↔ g ∈ localIntGL n u ∧ ∀ i j : n, k u * (g.val - 1) i j ∈ LocInt u :=
  .rfl

/-- Let `k` be the inverse of an integral adele `m`. Then `g` lies in the level given by
`congruenceLevel n k` at the places above `S` and their conjugates exactly when `k * (g - 1)` is
integral at these places: the integrality of `g` itself follows. -/
lemma mem_localLevel_congruenceLevel {m : Ô E'} {k : 𝔸f E'} (hmk : m * k = 1)
    (S : Set (FinPlace E)) (g : Gf E' n) :
    g ∈ localLevel n (placesAbove E' S) (congruenceLevel n k) ↔
      ∀ i j : n, idem (placesAbove E' S) * k * (g.val.val - 1) i j ∈ Ô E' := by
  -- The congruence makes `g` integral (multiply by `m`), and the entries of `g⁻¹` at `u` are
  -- conjugate to those of `g` at `star u`.
  simp only [mem_congruenceLevel, mem_localLevel, mul_assoc, idem_mul_mem_Ô, finAdele_mul_apply,
    ← atPlace_sub_one_apply, forall_and, mem_intGL]
  -- What is left is integrality of `g` and `g⁻¹` and the congruence, at each place above `S`. The
  -- congruence implies the rest; it matches the right side up to the order of the quantifiers.
  have h_swap : (∀ u ∈ placesAbove E' S, ∀ i j : n, k u * ((g.atPlace u).val - 1) i j ∈ LocInt u) ↔
      ∀ i j : n, ∀ u ∈ placesAbove E' S, v (k u * ((g.atPlace u).val - 1) i j) ≤ 1 :=
    ⟨fun h i j u hu ↦ h u hu i j, fun h u hu i j ↦ h i j u hu⟩
  refine (and_iff_right_of_imp fun h_cong ↦ ?_).trans h_swap
  have h_int (u : FinPlace E') (hu : u ∈ placesAbove E' S) (i j : n) :
      (g.atPlace u).val i j ∈ LocInt u := by
    have hm_int : (m : 𝔸f E') u ∈ LocInt u := mem_Ô.1 m.prop u
    simpa [← mul_assoc, ← finAdele_mul_apply, hmk, sub_eq_add_neg, add_mem_cancel_right,
      Matrix.one_apply, ite_mem] using mul_mem hm_int (h_cong u hu i j)
  refine ⟨h_int, fun u hu i j ↦ ?_⟩
  have h_int_star : (g.atPlace (star u)).val j i ∈ LocInt (star u) :=
    h_int (star u) (star_mem_placesAbove.2 hu) j i
  rw [g.atPlace_star rfl] at h_int_star
  exact (v_locMap_le_one_iff ..).1 h_int_star

/-- The integral adeles are integrally closed in the finite adeles, as each local ring of integers
is in its field. -/
lemma isIntegrallyClosedIn_Ô : IsIntegrallyClosedIn (Ô E') (𝔸f E') := by
  refine Subring.isIntegrallyClosedIn_iff.mpr fun x hx ↦ mem_Ô.mpr fun u ↦ ?_
  exact (Valuation.integer.integers (v.comap (evalAt u))).mem_of_integral
    (hx.map_of_comp_eq (Subring.inclusion (iInf_le _ u)) 1 rfl)

/-- The ring homomorphism from the integral finite adeles of `E` to those of `F` induced by an
embedding `f : E → F`. -/
noncomputable def intAdeleMap {F : Type} [Field F] [NumberField F] (f : E →+* F) : Ô E →+* Ô F :=
  (adeleMap f).restrict (Ô E) (Ô F) fun _ ↦ (adeleMap_mem_Ô f).mpr

/-- For a ring endomorphism `f` of `E`, the `i`-th iterate of `intAdeleMap f` is the restriction of
`adeleMap f ^ i` to the integral adeles. -/
@[simp] lemma intAdeleMap_iterate (i : ℕ) (x : Ô E) :
    ((intAdeleMap f)^[i] x : 𝔸f E) = (adeleMap f ^ i) x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih => exact ih (intAdeleMap f x)

omit [CMType E] [CMType E'] in
/-- If `σ` moves the place `u`, then `σ` is not in the inertia group of `u`. -/
lemma notMem_inertia_of_comap_ne {u : FinPlace E'} (h_moved : u.comap σ ≠ u) :
    σ ∉ u.asIdeal.inertia Gal(E'/E) := by
  -- If `σ` were trivial modulo `u`, then `x` and `σ • x` would lie in `u` together.
  refine fun h_inertia ↦ h_moved ?_
  ext x
  have h_diff : RingOfIntegers.mapRingHom (σ : E' →+* E') x - x ∈ u.asIdeal := h_inertia x
  simpa using u.asIdeal.add_mem_iff_right (b := x) h_diff

variable (σ) in
include hμ in
/-- There is an integral adele `c` of `E'` fixed by `σ` such that `c - star c` is a unit. -/
lemma exists_intAdeleMap_eq_isUnit_sub_star :
    ∃ c : Ô E', intAdeleMap σ c = c ∧ IsUnit (c - star c) := by
  -- Take the image of an integral adele `z` of `E` with `z - star z` a unit.
  obtain ⟨z, hz⟩ : ∃ z : Ô E, IsUnit (z - star z) := exists_isUnit_sub_star_Ô
  let c : Ô E' := intAdeleMap (algebraMap E E') z
  have hc_sub : c - star c = intAdeleMap (algebraMap E E') (z - star z) :=
    Subtype.ext (by simp [c, intAdeleMap, adeleMap_star])
  refine ⟨c, Subtype.ext (by simp [c, intAdeleMap, mem_range_finAdeleIncl_iff.1]), ?_⟩
  simpa only [hc_sub] using hz.map (intAdeleMap (algebraMap E E'))

/-- Let `m * k = 1` with `k` fixed by `σ`. Then the level given by `congruenceLevel n k` at the
places above `S` and their conjugates is stable under `σ`. -/
lemma galoisGf_mem_localLevel_congruenceLevel_iff {m : Ô E'} {k : 𝔸f E'} (hmk : m * k = 1)
    (hk_fixed : adeleMap (σ : E' →+* E') k = k) (S : Set (FinPlace E)) (g : Gf E' n) :
    galoisGf σ g ∈ localLevel n (placesAbove E' S) (congruenceLevel n k) ↔
      g ∈ localLevel n (placesAbove E' S) (congruenceLevel n k) := by
  -- `σ` fixes `idem (placesAbove E' S) * k` and preserves integrality.
  have h_apply (i j : n) :
      (galoisGf σ g).val.val i j = adeleMap (σ : E' →+* E') (g.val.val i j) := rfl
  have h_entry (i j : n) : idem (placesAbove E' S) * k * ((galoisGf σ g).val.val - 1) i j =
      adeleMap (σ : E' →+* E') (idem (placesAbove E' S) * k * (g.val.val - 1) i j) := by
    simp [h_apply, hk_fixed, Matrix.one_apply, adeleMap_idem_placesAbove]
  simp only [mem_localLevel_congruenceLevel hmk, h_entry, adeleMap_mem_Ô]

/-- Let `m` be an integral adele fixed by `star`, with an inverse `k` fixed by `σ`. Suppose that
`σ` is tame at level `e * m` for every integral `e` that it fixes, and that `μ` kills the norms of
the unit ideles congruent to `1` modulo `m`. Then the principal congruence level of `m` above any
`S` is a matching level. -/
lemma isMatchingLevel_congruenceLevel {m : Ô E'} {k : 𝔸f E'} (hmk : m * k = 1)
    (hm_star : star m = m) (hk_fixed : adeleMap (σ : E' →+* E') k = k)
    (h_tame : ∀ e : Ô E', intAdeleMap σ e = e →
      IsTameAtLevel (intAdeleMap σ) (finrank E E') (e * m))
    (h_idele : ∀ y ∈ Ô E', ∀ d ∈ idelesUnitOff ∅,
      d.val - (m : 𝔸f E') * y = 1 → d ∈ kerCompNorm E' μ)
    (S : Set (FinPlace E)) :
    IsMatchingLevel σ μ S (localLevel n (placesAbove E' S) (congruenceLevel n k)) := by
  -- Apply `cocyclesSplit_and_isMatchingPair_of_congruence` to the ring `Ô E'`, the idempotent `e`
  -- of the places above `S` and the level `e * m`.
  let L : Subgroup (Gf E' n) := localLevel n (placesAbove E' S) (congruenceLevel n k)
  have mem_L_iff_entries (g : Gf E' n) :
      g ∈ L ↔ ∀ i j : n, idem (placesAbove E' S) * k * (g.val.val - 1) i j ∈ Ô E' :=
    mem_localLevel_congruenceLevel hmk S g
  have h_stable (g : Gf E' n) : galoisGf σ g ∈ L ↔ g ∈ L :=
    galoisGf_mem_localLevel_congruenceLevel_iff hmk hk_fixed S g
  have h_open : L.IsOpen := by
    show IsOpen {g : Gf E' n | g ∈ L}
    simp only [mem_L_iff_entries]
    exact isOpen_Ô.matrix.preimage_of_continuous
  have mem_L_iff_lift (g : Gf E' n) : g ∈ L ↔ ∃ Y : Matrix n n (Ô E'),
      Y.map (Ô E').subtype = (idem (placesAbove E' S) * k) • (g.val.val - 1) := by
    rw [mem_L_iff_entries g]
    refine ⟨fun h_int ↦ ⟨fun i j ↦ ⟨_, h_int i j⟩, rfl⟩, fun ⟨Y, hY⟩ i j ↦ ?_⟩
    exact mem_of_eq_of_mem (congr_fun₂ hY i j).symm (Y i j).prop
  -- The idempotent `e` is fixed by `σ` and `star`, and `e * k` inverts `e * m` on the `e`-part.
  let e : Ô E' := ⟨idem (placesAbove E' S), idem_mem_Ô _⟩
  have he_fixed : intAdeleMap σ e = e :=
    Subtype.ext (by simp [e, intAdeleMap, adeleMap_idem_placesAbove])
  have he_star : star e = e := Subtype.ext (by simp [e, star_idem, preimage])
  have hem_star : star (e * m) = e * m := by rw [star_mul', he_star, hm_star]
  have hem_mul_ek : (e * m).val * (e * k) = e := by
    rw [MulMemClass.coe_mul, mul_mul_mul_comm]
    simp [e, hmk, idem_mul_self]
  have he_mul_ek : (e : 𝔸f E') * (e * k) = e * k := by simp [e, ← mul_assoc, idem_mul_self]
  -- An idele that, like its inverse, is `1` modulo `m` is a unit idele, so `μ` kills its norm.
  have h_mem_ker (y y' : Ô E') (h_inv : (1 + (m * y).val) * (1 + (m * y').val) = 1) :
      .mkOfMulEqOne _ _ h_inv ∈ kerCompNorm E' μ := by
    have h_unit : Units.mkOfMulEqOne _ _ h_inv ∈ idelesUnitOff (∅ : Set (FinPlace E')) :=
      idelesUnitOff_empty.ge ((Submonoid.mem_units_iff ..).2
        ⟨(1 + m * y).prop, (1 + m * y').prop⟩)
    exact h_idele y y.prop _ h_unit (add_sub_cancel_right _ _)
  -- The inputs on `Ô E'`: `σ` is tame at level `0`, and commutes with `star` and with the
  -- inclusion into `𝔸f E'`.
  have h_tame_zero : IsTameAtLevel (intAdeleMap σ) (finrank E E') (0 : Ô E') := by
    simpa only [zero_mul] using h_tame 0 (map_zero _)
  obtain ⟨c, hc_fixed, hc_unit⟩ := exists_intAdeleMap_eq_isUnit_sub_star σ
  have h_star_comm (x : Ô E') :
      intAdeleMap (σ : E' →+* E') (star x) = star (intAdeleMap (σ : E' →+* E') x) :=
    Subtype.ext (adeleMap_star _ x.val)
  have h_starModule : StarModule (Ô E') (𝔸f E') := ⟨fun r x ↦ star_mul' r.val x⟩
  have h_algebraMap (x : Ô E') : algebraMap (Ô E') (𝔸f E') (intAdeleMap σ x) =
      adeleMap (σ : E' →+* E') (algebraMap (Ô E') (𝔸f E') x) := by
    simp [intAdeleMap, Algebra.algebraMap_ofSubring]
  obtain ⟨h_split, h_pair⟩ :=
    cocyclesSplit_and_isMatchingPair_of_congruence (M := m) (v := e * k) e isProfiniteRing_intAdeles
      h_tame_zero
      hc_fixed hc_unit hem_star (h_tame e he_fixed) h_star_comm h_starModule isIntegrallyClosedIn_Ô
      (adeleMap_star σ) rfl (fun g ↦ (h_stable g).2) h_algebraMap hem_mul_ek he_mul_ek
      mem_L_iff_lift h_mem_ker
  exact
    { isOpen := h_open
      galoisGf_mem_iff := h_stable
      cocyclesSplit := h_split
      isMatchingPairAbove_indicator := h_pair }

/-- At a place `u` of `A` the adele `adeleOneOn A x` is `1`, so the level
`congruenceLevel n (adeleOneOn A x) u` is all of `GL_n(O_u)`. -/
lemma congruenceLevel_adeleOneOn_eq_localIntGL_of_mem {A : Set (FinPlace E')} (x : 𝔸f E')
    {u : FinPlace E'} (hu : u ∈ A) : congruenceLevel n (adeleOneOn A x) u = localIntGL n u := by
  ext g
  simp +contextual [adeleOneOn, mem_congruenceLevel, mem_intGL, sub_mem, hu, Matrix.one_apply,
    ite_mem]

/-- Let `m * k = 1`, and let `H` contain every integral point `g` over `E` whose matrix over `E'` is
congruent to `1` modulo `m`. Then `H` contains every point over `E` whose base change lies in
`congruenceLevel n k u` at every place `u` of `E'`, as `g - 1 = m • k • (g - 1)`. -/
lemma comap_localLevel_congruenceLevel_le {H : Subgroup (Gf E n)} {m : Ô E'} {k : 𝔸f E'}
    (hmk : m * k = 1)
    (h_mem_of_congr : ∀ Y : Matrix n n (𝔸f E'), (∀ i j : n, Y i j ∈ Ô E') → ∀ g ∈ stdLevel E n,
      (baseChangeGf g : Gf E' n).val.val - (m : 𝔸f E') • Y = 1 → g ∈ H) :
    (localLevel n univ (congruenceLevel n k)).comap baseChangeGf ≤ H := by
  intro g hg
  have h_at (u : FinPlace E') : (baseChangeGf g : Gf E' n).atPlace u ∈ congruenceLevel n k u :=
    mem_localLevel.1 hg u (mem_univ u)
  have hg_int : g ∈ stdLevel E n := by
    rw [← baseChangeGf_mem_stdLevel (E' := E'), mem_stdLevel_iff]
    exact fun u ↦ (mem_congruenceLevel.1 (h_at u)).left
  let Y : Matrix n n (𝔸f E') := k • ((baseChangeGf g : Gf E' n).val.val - 1)
  have hY_int (i j : n) : Y i j ∈ Ô E' := by
    refine mem_Ô.2 fun u ↦ ?_
    show k u * ((baseChangeGf g : Gf E' n).val.val - 1) i j u ∈ LocInt u
    simpa only [atPlace_sub_one_apply] using (mem_congruenceLevel.1 (h_at u)).right i j
  have h_eq : (baseChangeGf g : Gf E' n).val.val - (m : 𝔸f E') • Y = 1 := by
    rw [smul_smul, hmk, one_smul, sub_sub_self]
  exact h_mem_of_congr Y hY_int g hg_int h_eq

include hσ hμ

/-- For a step `E' / E` and `σ ≠ 1` there is an integer `C ≠ 0` with the following property. Let
`m` be an integral adele of `E'` fixed by `σ` whose reduction vanishes at every place `u` of `E'`
that divides `C` and has all of `Gal(E'/E)` as inertia group (a totally ramified place). Then `σ`
acts tamely on the integral adeles at level `m` (`IsTameAtLevel`). -/
lemma exists_isTameAtLevel_intAdeleMap :
    ∃ C : ℕ, C ≠ 0 ∧ ∀ m : Ô E', intAdeleMap σ m = m →
      (∀ u : FinPlace E', (C : 𝓞 E') ∈ u.asIdeal →
        (∀ g : Gal(E'/E), g ∈ u.asIdeal.inertia Gal(E'/E)) → reduceAt u m = 0) →
      IsTameAtLevel (intAdeleMap σ) (finrank E E') m := by
  -- `C` is the absolute norm of the ideal of `σ • x - x`, for an integer `x` moved by `σ`. The main
  -- point is the last clause of `IsTameAtLevel`: a prime `P` modulo which `σ ^ i` is trivial
  -- contains `m`.
  obtain ⟨e, he⟩ : ∃ e : 𝓞 E', Algebra.trace E E' e = 1 := hμ.exists_trace_eq_one
  have h_pow : Function.Bijective fun j : Fin (finrank E E') ↦ σ ^ j.val :=
    bijective_pow_of_ne_one_of_prime_finrank hσ
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E', σ • x ≠ x :=
    not_forall.1 ((IsGaloisGroup.faithful (𝓞 E) (B := 𝓞 E')).eq_of_smul_eq_smul.mt hσ)
  have hC : ((span {σ • x - x}).absNorm : 𝓞 E') ≠ 0 := by
    simpa [absNorm_eq_zero_iff, sub_eq_zero] using hx
  refine ⟨(span {σ • x - x}).absNorm, mod_cast hC, fun m hm h_red ↦ ⟨hm, ?_, ?_, finrank_pos, ?_⟩⟩
  · -- The powers of `σ` exhaust the Galois group, so the sum is the trace of `e`, which is `1`.
    refine ⟨algebraMap (𝓞 E') (Ô E') e, 0, Subtype.ext ?_⟩
    have h_trace : ∑ τ : Gal(E'/E), τ (e : E') = 1 := by
      rw [← trace_eq_sum_automorphisms, he, map_one]
    simpa [← h_pow.sum_comp, adeleMap_gal_pow, Finset.sum_range, sub_eq_zero] using
      congrArg (algebraMap E' (𝔸f E')) h_trace
  · -- `σ ^ finrank E E' = 1` on the finite adeles.
    ext y
    simp [adeleMap_pow_finrank_eq_one]
  -- `σ ^ i` generates the Galois group and acts trivially modulo the prime `u` of `𝓞 E'` under `P`.
  rintro i ⟨hi_pos : 0 < i, hi_lt : i < finrank E E'⟩ P _ hP
  have hi_ne : σ ^ i ≠ 1 := by
    simpa [hi_pos.ne'] using h_pow.injective.ne (a₁ := ⟨i, hi_lt⟩) (a₂ := ⟨0, finrank_pos⟩)
  have hi_mem : σ ^ i ∈ (P.under (𝓞 E')).inertia Gal(E'/E) := by
    intro y
    -- The image of `(σ ^ i) • y - y` in the integral adeles is `(σ ^ i) ȳ - ȳ` for the image `ȳ`
    -- of `y`, which is in `P`.
    have h_smul : ((σ ^ i • y : 𝓞 E') : E') = (σ ^ i) (y : E') := rfl
    have h_map : algebraMap (𝓞 E') (Ô E') ((σ ^ i) • y - y) =
        (intAdeleMap σ ^ i) (algebraMap (𝓞 E') (Ô E') y) - algebraMap (𝓞 E') (Ô E') y :=
      Subtype.ext (by simp [adeleMap_gal_pow, h_smul, -AlgEquiv.coe_pow])
    exact mem_comap.2 (mem_of_eq_of_mem h_map (hP _))
  have h_inertia : ∀ g : Gal(E'/E), g ∈ (P.under (𝓞 E')).inertia Gal(E'/E) :=
    (bijective_pow_of_ne_one_of_prime_finrank hi_ne).surjective.forall.2 fun j ↦ pow_mem hi_mem j
  -- So `u` contains `σ • x - x` and its norm `C`; in particular `u` is a place.
  have hC_mem : ((span {σ • x - x}).absNorm : 𝓞 E') ∈ P.under (𝓞 E') :=
    (span_singleton_le_iff_mem _).2 (h_inertia σ x) (absNorm_mem _)
  let u : FinPlace E' := ⟨P.under (𝓞 E'), inferInstance, fun h_bot ↦ hC (h_bot.le hC_mem)⟩
  have hm_red : m ∈ RingHom.ker (reduceAt u) := h_red u hC_mem h_inertia
  -- The kernel of reduction at `u` contains `C ≠ 0`, so it is generated by its contraction `u` to
  -- `𝓞 E'` (`map_under_Ô`), and `u` lies in `P`.
  rw [← map_under_Ô hC (I := RingHom.ker (reduceAt u)) (algebraMap_ResField_eq_zero.2 hC_mem)]
    at hm_red
  exact map_le_of_le_comap (fun _ ↦ algebraMap_ResField_eq_zero.1) hm_red

/-- Let `E'/E` be a step with character `μ` (`IsStep`): `E` contains a primitive 5040th root of
unity, and `E'` is a CM field Galois over `E` of prime degree. Let `σ ≠ 1` in `Gal(E'/E)` and let
`H` be an open subgroup of the finite adelic unitary group over `E`. Then some family `K` of
subgroups `K u` of `GL n` over the completions `E'_u` at the finite places `u` is a base change
level below `H` (`IsBaseChangeLevel σ μ H K`). -/
lemma exists_isBaseChangeLevel {H : Subgroup (Gf E n)} (hH : H.IsOpen) :
    ∃ K : (u : FinPlace E') → Subgroup (GL n (LocField u)), IsBaseChangeLevel σ μ H K := by
  -- Call `w` good if it is unramified and `w`, `star w` avoid the finite set `S₀` below. Let `A`
  -- be the places of `E'` above the good places and their conjugates, and `m` the integral adele
  -- that is `1` on `A` and a sufficiently divisible integer `N * C` off `A`. Take for `K u` the
  -- principal congruence subgroup of level `m`.
  obtain ⟨C, hC, h_tame⟩ := exists_isTameAtLevel_intAdeleMap hσ
  -- `S₀` avoids the places at which `H` is maximal (`hS₀_good`), and `H` contains the integral
  -- points that are trivial on `S₀` (`hS₀_le`).
  obtain ⟨S₀, hS₀_good, hS₀_le⟩ := exists_inf_trivialOn_le hH
  let A : Set (FinPlace E') := placesAbove E' {w | IsStepUnramifiedAt E' μ w ∧ w ∉ conjClosure S₀}
  have hA_unram (u : FinPlace E') (hu : u ∈ A) : IsStepUnramifiedPlace μ u :=
    isStepUnramifiedPlace_of_mem_placesAbove (fun w hw ↦ hw.left) hu
  have hA_off (u : FinPlace E') (hu : u ∈ A) : u.below E ∉ (S₀ : Set (FinPlace E)) := by
    rcases hu with ⟨-, h_notMem⟩ | ⟨-, h_notMem⟩
    · exact fun hS₀ ↦ h_notMem (.inl hS₀)
    · exact fun hS₀ ↦ h_notMem (.inr (by simpa using hS₀))
  -- Both congruence conditions hold at `x = N * C` for a suitable `N ≠ 0`.
  obtain ⟨N, hN, h_small⟩ := mem_nhds_zero_finAdele_iff.1
    ((eventually_mem_kerCompNorm hA_unram).and
      (eventually_mem_of_baseChangeGf_congr hH hS₀_le hA_off))
  obtain ⟨h_idele, h_group⟩ := h_small C (by simp)
  let m : Ô E' := N * C + ⟨idem A, idem_mem_Ô A⟩ * (1 - N * C)
  have hm : adeleOneOn A (N * C) = m := by simp [adeleOneOn, m]
  rw [hm] at h_idele h_group
  -- `k` is the inverse of `m` in the adeles.
  let k : 𝔸f E' := adeleOneOn A (algebraMap E' (𝔸f E') (N * C)⁻¹)
  have hmk : m * k = 1 := by
    rw [← hm]
    refine adeleOneOn_mul_adeleOneOn_of_mul_eq_one A ?_
    have h_ne : (N * C : E') ≠ 0 := by positivity
    simpa only [map_mul, map_natCast, map_one] using
      congrArg (algebraMap E' (𝔸f E')) (mul_inv_cancel₀ h_ne)
  have hm_star : star m = m := Subtype.ext (by simp [m, A, star_idem, preimage])
  have hk_fixed : adeleMap (σ : E' →+* E') k = k := by
    simp [k, A, adeleOneOn, adeleMap_idem_placesAbove]
  have hm_fixed : intAdeleMap σ m = m :=
    Subtype.ext (by simp [m, A, intAdeleMap, adeleMap_idem_placesAbove])
  -- `σ` is tame at `e * m` for every fixed `e`: a totally ramified place is off `A`, so `m = N * C`
  -- there, which vanishes modulo a place dividing `C`.
  have h_tame_m (e : Ô E') (he_fixed : intAdeleMap σ e = e) :
      IsTameAtLevel (intAdeleMap σ) (finrank E E') (e * m) := by
    refine h_tame (e * m) (by rw [map_mul, he_fixed, hm_fixed]) fun u hCu h_inertia ↦ ?_
    have huA : u ∉ A := fun hu ↦
      (hA_unram u hu).exists_notMem_inertia.elim fun τ hτ ↦ hτ (h_inertia τ)
    have hC_red : (C : ResField u) = 0 := by simpa using algebraMap_ResField_eq_zero.2 hCu
    simp [m, hC_red, huA]
  refine ⟨congruenceLevel n k,
    { le_localIntGL := fun u g hg ↦ (mem_congruenceLevel.1 hg).left
      isMatchingLevel := isMatchingLevel_congruenceLevel hmk hm_star hk_fixed h_tame_m h_idele
      comap_le := comap_localLevel_congruenceLevel_le hmk h_group
      eq_localIntGL := fun w h_unram hH_max u hu ↦ ?_ }⟩
  -- Such a place `w` is good, so above it `k u = 1` and the level is all of `GL_n(O_u)`.
  have hw_good : {w} ⊆ {w | IsStepUnramifiedAt E' μ w ∧ w ∉ conjClosure S₀} :=
    singleton_subset_iff.2 ⟨h_unram, not_or.2 (hS₀_good w hH_max)⟩
  have huA : u ∈ A := hu.imp (fun h ↦ hw_good h) fun h ↦ hw_good h
  exact congruenceLevel_adeleOneOn_eq_localIntGL_of_mem _ huA

end New

end BaseChangeLevel
