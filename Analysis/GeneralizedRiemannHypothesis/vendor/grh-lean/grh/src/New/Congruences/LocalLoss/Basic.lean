import Lib.GaloisRep.Main.LocalConditions
import Lib.General.NumberTheory.PadicLimitsValuation
import New.Reduction.Data.AdmissibleData

/-!
# Local loss above ℓ: main summand weights, b-places, crystalline relations and crystalline colength

This file provides the data for the bound on the loss of a lift at the places of `E` above `ℓ`
(`New.Selmer.eventually_exists_inClass_sum_dualDefect_le`). It defines the conditions on the weights
of a main summand and the unit of that bound, and studies the signs of the embeddings in a Galois
orbit that define b-places. Fix `ι : ℂ ≃ ℚ̄_ℓ` through `New.PadicIso`. For `e : E → ℚ̄_ℓ` and `g` in
`New.Gp ℓ`,
`New.Selmer.complexEmbeddingOf e g = ι⁻¹ ∘ g⁻¹ ∘ e`. `New.Selmer.cmSign σ` is `1` if `σ` belongs to
the CM type and `-1` if not.

## Main definitions and results

* `New.Selmer.crystallineLoss`, `New.Selmer.defectBound`: the crystalline loss, and the unit of the
  bound on the total loss of a lift.
* `New.Selmer.ribetCocycles.exists_graph_subrepresentation`: for an element `a` of a noetherian ring
  `O` and finitely many matrix representations `u x` of a group, a cocycle with values in `(O/aO)^d`
  that obeys every linear relation among the families `(u x g - 1)_x` comes from an equivariant map
  on a subrepresentation, given by its graph. Its domain contains the families `(u x g - 1)_x` and
  all multiples of a power of `a` (Artin–Rees).
* `New.Selmer.SummandCoordIndex`, `New.Selmer.summandRep`: the summands of a lift, namely the main
  summand and `t` powers of the inverse cyclotomic character (`New.Selmer.tateTwist`).
* `New.Selmer.crysCocyclesAt`, `New.Selmer.crysRelations`: the crystalline cocycles at `v`, and the
  union over the places `v` above `ℓ` of the linear relations that hold on them, read as relations
  on functions on the global Galois group.
* `New.Selmer.crystallineColength`: the length by which cocycles in `New.Selmer.ribetCocycles`, with
  values in `(O/ℓ^M O)^n`, can miss these relations.

Notions from other files:
* `New.Parameters`: The fixed parameters: a multiple `q₀` of `18480 = 16 · 3 · 5 · 7 · 11` and a
  prime `d` with `d ≡ q₀/2 - 1 mod q₀`. For these, `P.E s = K(ζ)`, where `K = ℚ(√-d)` and `P.ζ s` is
  a root of unity of order `P.q₁ s = 3^c 2^s q₀`, `c = ⌊log₃ s⌋ + 5`. The group `P.Φ s` of infinite
  places of `P.E s` is identified with `(ℤ/q₁)ˣ`, and `P.placeClass` reduces it modulo a divisor of
  `q₁`.
* `New.Data`: The admissible data `D`. Among them are the ranks `m`, `r`, `k = r + 1 - m`, the
  length `t = 5r`, the weight `natB` and the set `D.bPlaces` of b-places of `D.E = P.E D.towerExp`,
  which lies in the cyclotomic field of order `D.cyclotomicConductor = q₁ d`.
* `New.Gp`: The absolute Galois group G_p = Gal(Q̄_p over Q_p).
* `New.Period.crysCocycles`: Z_f(T), the module of maps c: Γ → T such that some y in B⊗T, B = B_max,
  has 1⊗c(g) = gy − y for all g.
* `New.CoeffRing`: Rings of integers of finite Galois extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`.

## Relation to the literature

See `Lib.PadicHodge.BlochKato` and `Lib.ClassField.Places.LocalFields` for sources.
-/

noncomputable section

namespace New.Selmer

/-!
## Signs of embeddings, jump conditions of a main summand and the defect bound

* `New.Selmer.IsMainSummandWeights`: where the jumps of a main summand lie and how many are small or
  negative.

The numbers `D.k = D.r + 1 - D.m`, `D.halfGap = D.r ^ 8` (half the gap) and `D.natB` are read off
the data.
-/

section MainSummandWeights

variable {E : Type*} [Field E] {P : Parameters} (D : Data P)

open scoped Classical in
/-- The sign of a complex embedding σ of E: 1 if σ is the embedding the CM type chooses at its
place, and −1 otherwise. -/
def cmSign [c : PlaceEmbedding E] (σ : E →+* ℂ) : ℤˣ :=
  if σ = c.Φ (NumberField.InfinitePlace.mk σ) then 1 else -1

/-- The complex embedding ι⁻¹ ∘ g⁻¹ ∘ e of E, for e: E → ℚ̄_ℓ and g in G_ℓ. -/
def complexEmbeddingOf {ℓ : ℕ} [Fact ℓ.Prime] [PadicIso ℓ] (e : E →+* PadicAlgCl ℓ) (g : Gp ℓ) :
    E →+* ℂ :=
  ιℓ.symm.toRingHom.comp (g⁻¹.toRingHom.comp (α := E) e)

/-- The conditions on the jumps `J σ` (a multiset of integers for each complex embedding `σ`) of a
main summand of rank `r` with a string of length `t`, for admissible data `D`: each jump is low or
near `∓w_j(σ)`, where `w_j = D.liftWeight j` is the weight of the `j`-th lift, `j ≤ D.m`; few jumps
have `|u| ≤ 2 halfGap²`, and at most `r` jumps at `σ` and `σ̄` together are negative. -/
structure IsMainSummandWeights (r t : ℕ) (J : (D.E →+* ℂ) → Multiset ℤ) where
  /-- The rank `r` lies between `1` and `D.r`. -/
  rank_mem : r ∈ Set.Icc 1 D.r
  /-- The length `t` of the string is at most `D.t`. -/
  t_le : t ≤ D.t
  /-- For one `j ≤ m`, each jump `u` at an embedding `σ` is low, `Δ / 4 ≤ |u| ≤ 2 m Δ` with
  `Δ = D.gap = 2 halfGap`, or high: within `D.t` of `-w_j(σ)` if `σ` is in the CM type, of `w_j(σ)`
  otherwise. -/
  low_or_high : ∃ j ≤ D.m, ∀ σ : D.E →+* ℂ, ∀ u ∈ J σ,
    D.gap ≤ 4 * u.natAbs ∧ u.natAbs ≤ 2 * D.m * D.gap ∨
    |cmSign σ * u + D.liftWeight j (NumberField.InfinitePlace.mk σ)| ≤ D.t
  /-- At most `r m / k` jumps `u` at `σ` are small: `|u| ≤ 2 halfGap²`. -/
  card_small_le (σ : D.E →+* ℂ) : (J σ).countP (·.natAbs ≤ 2 * D.halfGap ^ 2) * D.k ≤ r * D.m
  /-- At most `r` jumps at `σ` and `σ̄` together are negative. -/
  card_neg_le (σ : D.E →+* ℂ) : (J σ).countP (· < 0) + (J (star σ)).countP (· < 0) ≤ r

/-- Let `σ` be a complex embedding of the field `E` of the admissible data `D`, with sign
`cmSign σ` equal to `1` if `σ` belongs to the CM type and `-1` if not. Let `w` be the weight
`D.liftWeight j` of the character of the `j`-th lift at the infinite place of `σ`, and let
`D.t = 5 * D.r`. If an integer `u` lies within `D.t` of `-cmSign σ * w`, then `|u|` exceeds every
`B` with `B + D.t < w`. -/
lemma lt_natAbs_of_abs_add_liftWeight_le {D : Data P} {j B : ℕ} {σ : D.E →+* ℂ} {u : ℤ}
    (hB : B + D.t < D.liftWeight j (NumberField.InfinitePlace.mk σ))
    (h_near : |cmSign σ * u + D.liftWeight j (NumberField.InfinitePlace.mk σ)| ≤ D.t) :
    B < u.natAbs := by
  rw [abs_le] at h_near
  obtain hσ | hσ := Int.units_eq_one_or (cmSign σ) <;>
    simp only [hσ, Units.val_neg, Units.val_one] at h_near <;> omega

/-- The crystalline loss of three natural numbers h, b, l: the l-adic valuation of the product of
(2b)! and P^(h³), where P is the product of the natural numbers k with
max(b − 30h³, 0) < k ≤ b + 30h³. -/
@[irreducible]
def crystallineLoss (h b l : ℕ) : ℕ :=
  padicValNat l
    ((2 * b).factorial * (∏ k ∈ Finset.Ioc (b - 30 * h ^ 3) (b + 30 * h ^ 3), k) ^ h ^ 3)

/-- The unit at `l` of the bound on the loss of a lift, for the data `D`:
`10⁶ (m/k) (natB v_l(M) + crystallineLoss halfGap natB l)`, where `v_l` is the `l`-adic valuation
and `M = D.M` is the product of the two level primes. -/
def defectBound (l : ℕ) : NNReal :=
  10 ^ 6 * (D.m / D.k * (D.natB * padicValNat l D.M + crystallineLoss D.halfGap D.natB l))

end MainSummandWeights

/-!
## Spacing and signs of the b-places in a Galois orbit

For `e : E → ℚ̄_ℓ`, each `g` gives a complex embedding `New.Selmer.complexEmbeddingOf e g`, and so
an infinite place. The infinite places of `E` form a group identified with `(ℤ/q₁)ˣ` through the
action on the root of unity `New.Parameters.ζ`.

The results use two properties of the set `D.bPlaces` of b-places: its members have class `-1`
modulo `q₀` (`New.Data.placeClass_of_mem_bPlaces`) and it is sparse (`New.Data.sparse`).
-/

section BPlaceSpacing

open Fact Int ZMod IsCyclotomicExtension Parameters IsAlgClosed

variable {P : Parameters} {D : Data P} {ℓ : ℕ} [hp : Fact ℓ.Prime]

/-- The field `D.E` of the data `D` lies in the cyclotomic field of order
`D.cyclotomicConductor = q₁ d`. So an element `g` of `Gp ℓ = Gal(ℚ̄_ℓ/ℚ_ℓ)` that fixes every `ζ` in
`ℚ̄_ℓ` with `ζ ^ D.cyclotomicConductor = 1` has `g (e x) = e x` for every embedding `e : D.E → ℚ̄_ℓ`
and every `x`. -/
lemma fixes_emb_of_fixes_rootsOfUnity {e : D.E →+* PadicAlgCl ℓ} {g : Gp ℓ}
    (h_roots : ∀ ζ : PadicAlgCl ℓ, ζ ^ D.cyclotomicConductor = 1 → g ζ = ζ) (x : D.E) :
    g (e x) = e x := by
  -- `e` extends to an embedding `ψ` of the cyclotomic field, which a root of unity generates
  let _ : Algebra (P.E D.towerExp) (cycloField (P.q₁ D.towerExp * P.d)) := toCycloField.toAlgebra
  obtain ⟨ψ, hψ⟩ : ∃ ψ : cycloField D.cyclotomicConductor →ₐ[ℚ] PadicAlgCl ℓ,
      ψ.domRestrict D.E = e.toRatAlgHom :=
    surjective_domRestrict_of_isAlgebraic (E := cycloField D.cyclotomicConductor) e.toRatAlgHom
  have h_zeta : g (ψ (zeta D.cyclotomicConductor ℚ _)) = ψ (zeta D.cyclotomicConductor ℚ _) :=
    h_roots _ (by rw [← map_pow, zeta_pow, map_one])
  have h_fix : (g.restrictScalars ℚ : PadicAlgCl ℓ →ₐ[ℚ] PadicAlgCl ℓ).comp ψ = ψ :=
    ((zeta_spec D.cyclotomicConductor ℚ _).powerBasis ℚ).algHom_ext h_zeta
  have hx : ψ (algebraMap D.E (cycloField D.cyclotomicConductor) x) = e x := DFunLike.congr_fun hψ x
  rw [← hx]
  exact DFunLike.congr_fun h_fix _

/-- A complex embedding `σ` sends `√-d` to `cmSign σ` times the chosen square root of `-d`. -/
lemma map_sqrtNegDInE_eq_cmSign_mul (σ : D.E →+* ℂ) :
    σ (P.sqrtNegDInE D.towerExp) = cmSign σ * QuadField.sqrtNegD P.d := by
  -- `σ` or its conjugate is chosen by the CM type at its place, and conjugation negates `√-d`
  obtain hσ | hσ := Φ_mk_eq_or_star_eq σ <;> rw [← hσ] <;> simp [cmSign, ← RCLike.star_def]

/-- Let `E = K(ζ)` with `K = ℚ(√-d)` and `ζ = P.ζ D.towerExp` a root of unity. For an infinite place
`w` of `E`, `Φ w` is the embedding at `w` that belongs to the CM type, the one that sends `√-d` to
the chosen complex root. For a complex embedding `σ` with place `w`, `Φ w` sends `ζ` to
`σ ζ ^ cmSign σ`. -/
lemma map_zeta_eq_zpow_cmSign (σ : D.E →+* ℂ) :
    Φ (NumberField.InfinitePlace.mk σ) (P.ζ D.towerExp) = σ (P.ζ D.towerExp) ^ (cmSign σ).val := by
  obtain hσ | hσ := Φ_mk_eq_or_star_eq σ
  · -- `σ` is the embedding chosen by the CM type at its place: sign `1`
    rw [← hσ]
    simp [cmSign]
  · -- `σ` is its conjugate: sign `-1`, and conjugation inverts `P.ζ`
    rw [← hσ]
    simp [cmSign, ← RCLike.star_def, ← map_star_complex]

variable [PadicIso ℓ]

/-- Let `P` be the parameters of the data `D`, `ζ = P.ζ D.towerExp` the root of unity of order `q₁`
in `E`, `e : E → ℚ̄_ℓ`, and `g`, `g'` in `Gp ℓ = Gal(ℚ̄_ℓ/ℚ_ℓ)`, with complex embeddings
`σ = complexEmbeddingOf e g = ι⁻¹ ∘ g⁻¹ ∘ e` and `σ' = ι⁻¹ ∘ g'⁻¹ ∘ e` for the fixed `ι : ℂ ≃ ℚ̄_ℓ`.
Suppose `g' * g⁻¹` raises `e ζ ^ ℓ ^ a` to the power `ℓ ^ n`. Let `y` be the ratio of the places of
`σ` and `σ'` in the group `P.Φ D.towerExp ≃ (ℤ/q₁)ˣ` of infinite places of `E`. For `m ∣ q₁` prime
to `ℓ ^ a`, the reduction `P.placeClass hm y` of `y` modulo `m` is
`cmSign σ * cmSign σ' * ℓ ^ n`. -/
lemma placeClass_eq_cmSign_mul_pow (e : D.E →+* PadicAlgCl ℓ) (g g' : Gp ℓ) (a n : ℕ)
    (h_act : (g' * g⁻¹) (e (P.ζ D.towerExp) ^ ℓ ^ a) = (e (P.ζ D.towerExp) ^ ℓ ^ a) ^ ℓ ^ n)
    {y : P.Φ D.towerExp} (m : ℕ) (hm : m ∣ P.q₁ D.towerExp) (h_coprime : (ℓ ^ a).Coprime m)
    (hy : NumberField.InfinitePlace.mk (complexEmbeddingOf e g') * y =
      NumberField.InfinitePlace.mk (complexEmbeddingOf e g)) :
    (P.placeClass hm y).val =
      (cmSign (complexEmbeddingOf e g) * cmSign (complexEmbeddingOf e g') : ℤ) * ℓ ^ n := by
  -- A place sends `P.ζ` to the value of its embedding or to the inverse, according to `cmSign`, and
  -- `y` acts on `P.ζ` as the power `k`, its class mod `q₁`. Comparing the two places on `P.ζ`
  -- gives an equation between powers of the primitive root `z`, hence a congruence of exponents.
  set z : PadicAlgCl ℓ := e (P.ζ D.towerExp)
  set k : ℕ := (P.placeMulEquiv D.towerExp y : ZMod (P.q₁ D.towerExp)).val
  have z_prim : IsPrimitiveRoot z (P.q₁ D.towerExp) :=
    isPrimitiveRoot_zeta.map_of_injective e.injective
  have h_places :
      complexEmbeddingOf e g (P.ζ D.towerExp) ^ (cmSign (complexEmbeddingOf e g)).val =
        (complexEmbeddingOf e g' (P.ζ D.towerExp) ^ (cmSign (complexEmbeddingOf e g')).val) ^
          k := by
    rw [← map_zeta_eq_zpow_cmSign, ← map_zeta_eq_zpow_cmSign, ← hy, phi_mul, galOfPlace_zeta,
      map_pow]
  generalize cmSign (complexEmbeddingOf e g) = s,
    cmSign (complexEmbeddingOf e g') = s' at h_places ⊢
  -- carry the equation over to `PadicAlgCl ℓ` by `ιℓ`, then apply `g'`
  have h_padic : (g' * g⁻¹) z ^ s.val = (z ^ s'.val) ^ k := by
    simpa [complexEmbeddingOf] using congrArg (fun w : ℂ ↦ g' (ιℓ w)) h_places
  -- raise to the power `ℓ ^ a`, where `h_act` applies
  have h_pow : z ^ ((ℓ : ℤ) ^ n * s * ℓ ^ a) = z ^ ((s' : ℤ) * k * ℓ ^ a) :=
    calc
      z ^ ((ℓ : ℤ) ^ n * s * ℓ ^ a) = ((z ^ ℓ ^ a) ^ ℓ ^ n) ^ s.val := by
        simp only [← zpow_natCast, ← zpow_mul, Nat.cast_pow, mul_rotate ((ℓ : ℤ) ^ a)]
      _ = ((g' * g⁻¹) z ^ s.val) ^ ℓ ^ a := by
        rw [← h_act, map_pow, ← zpow_natCast, ← zpow_natCast, zpow_comm]
      _ = z ^ ((s' : ℤ) * k * ℓ ^ a) := by
        simp only [h_padic, ← zpow_natCast, ← zpow_mul, Nat.cast_pow]
  have h_dvd : (P.q₁ D.towerExp : ℤ) ∣ (ℓ ^ n * s - s' * k) * ℓ ^ a := by
    have z_ne : z ≠ 0 := z_prim.ne_zero (NeZero.ne _)
    rw [← z_prim.zpow_eq_one_iff_dvd, sub_mul, zpow_sub₀ z_ne, h_pow,
      div_self (zpow_ne_zero _ z_ne)]
  -- modulo `m` the factor `ℓ ^ a` cancels
  have h_dvd_sub : (m : ℤ) ∣ ℓ ^ n * s - s' * k :=
    h_coprime.symm.cast.dvd_of_dvd_mul_right (mod_cast hm.natCast.trans h_dvd)
  have h_mod : ((s' : ℤ) * k : ZMod m) = ℓ ^ n * (s : ℤ) :=
    mod_cast (intCast_eq_intCast_iff_dvd_sub (s' * k) (ℓ ^ n * s) m).2 h_dvd_sub
  -- multiply by the sign `s'`, whose square is `1`
  calc
    (P.placeClass hm y).val = (s' : ℤ) * ((s' : ℤ) * k) := by
      simp [k, placeClass, unitsMap, ← mul_assoc, ← Int.cast_mul]
    _ = (s * s' : ℤ) * ℓ ^ n := by simp [h_mod, mul_comm, mul_left_comm, mul_assoc]

/-- Spacing of the b-places `D.bPlaces`, the sparse set of infinite places of `E` of weight `b` in
the data `D`. Let `e : E → ℚ̄_ℓ` for a prime `ℓ ≤ D.k * D.t = (D.r + 1 - D.m) * (5 * D.r)`, and let
`0 < i < n < l₀ s`, where `s = D.towerExp` and `l₀ s` is the least power of `3` above `27 s`. Let
`g' * g⁻¹` and `g' * g₁⁻¹` in `Gp ℓ` raise `e ζ ^ ℓ ^ a` to the powers `ℓ ^ n` and `ℓ ^ i`, where
`ζ = P.ζ s` generates `E` over `K = ℚ(√-d)`. Each `γ` in `Gp ℓ = Gal(ℚ̄_ℓ/ℚ_ℓ)` gives the complex
embedding `complexEmbeddingOf e γ = ι⁻¹ ∘ γ⁻¹ ∘ e`, for the fixed `ι : ℂ ≃ ℚ̄_ℓ`. If the embeddings
given by `g` and `g'` lie over b-places, then the one given by `g₁` does not. -/
lemma notMem_bPlaces_of_short_arc {e : D.E →+* PadicAlgCl ℓ} {g g' g₁ : Gp ℓ} {a i n : ℕ}
    (h_mem : NumberField.InfinitePlace.mk (complexEmbeddingOf e g) ∈ D.bPlaces)
    (h_mem' : NumberField.InfinitePlace.mk (complexEmbeddingOf e g') ∈ D.bPlaces)
    (h_act : (g' * g⁻¹) (e (P.ζ D.towerExp) ^ ℓ ^ a) = (e (P.ζ D.towerExp) ^ ℓ ^ a) ^ ℓ ^ n)
    (h_act₁ : (g' * g₁⁻¹) (e (P.ζ D.towerExp) ^ ℓ ^ a) = (e (P.ζ D.towerExp) ^ ℓ ^ a) ^ ℓ ^ i)
    (hℓ_le : ℓ ≤ D.k * D.t) (hi_pos : 0 < i) (hi_lt : i < n) (hn_lt : n < l₀ D.towerExp) :
    NumberField.InfinitePlace.mk (complexEmbeddingOf e g₁) ∉ D.bPlaces := by
  -- By `placeClass_eq_cmSign_mul_pow`, the ratios of the places of `g₁` and `g` to that of `g'` are
  -- `± ℓ ^ i` and `± ℓ ^ n` modulo the part of `q₁` prime to `ℓ`, which the sparseness of
  -- `D.bPlaces` excludes.
  intro h_mem₁
  have h_coprime : (ℓ ^ a).Coprime (ordCompl[ℓ] D.q₁) :=
    (Nat.coprime_ordCompl hp.out (NeZero.ne D.q₁)).pow_left a
  let place (γ : Gp ℓ) : P.Φ D.towerExp := NumberField.InfinitePlace.mk (complexEmbeddingOf e γ)
  have h_ratio₁ : (P.placeClass (Nat.ordCompl_dvd D.q₁ ℓ) (place g₁ / place g')).val =
      (cmSign (complexEmbeddingOf e g₁) * cmSign (complexEmbeddingOf e g') : ℤ) * ℓ ^ i :=
    placeClass_eq_cmSign_mul_pow e g₁ g' a i h_act₁ _ _ h_coprime
      (mul_div_cancel (place g') (place g₁))
  have h_ratio : (P.placeClass (Nat.ordCompl_dvd D.q₁ ℓ) (place g / place g')).val =
      (cmSign (complexEmbeddingOf e g) * cmSign (complexEmbeddingOf e g') : ℤ) * ℓ ^ n :=
    placeClass_eq_cmSign_mul_pow e g g' a n h_act _ _ h_coprime
      (mul_div_cancel (place g') (place g))
  exact D.sparse ℓ hp.out hℓ_le i n hi_pos hi_lt hn_lt
    ⟨place g', h_mem', place g₁, h_mem₁, place g, h_mem,
      cmSign (complexEmbeddingOf e g₁) * cmSign (complexEmbeddingOf e g'),
      cmSign (complexEmbeddingOf e g) * cmSign (complexEmbeddingOf e g'), h_ratio₁, h_ratio⟩

/-- Let the prime `ℓ` divide `D.cyclotomicConductor = q₁ d`, let `e : E → ℚ̄_ℓ`, and let `g`, `g'`
be in `Gp ℓ = Gal(ℚ̄_ℓ/ℚ_ℓ)`. Suppose the complex embeddings
`complexEmbeddingOf e g = ι⁻¹ ∘ g⁻¹ ∘ e` and `ι⁻¹ ∘ g'⁻¹ ∘ e`, for the fixed `ι : ℂ ≃ ℚ̄_ℓ`, both
lie over b-places: members of the set `D.bPlaces` of infinite places of `E` of weight `b`, all of
class `-1` modulo `q₀`. Then both or neither belong to the CM type, so their signs `cmSign`
agree. -/
lemma cmSign_eq_of_mem_bPlaces {e : D.E →+* PadicAlgCl ℓ} {g g' : Gp ℓ}
    (h_mem : NumberField.InfinitePlace.mk (complexEmbeddingOf e g) ∈ D.bPlaces)
    (h_mem' : NumberField.InfinitePlace.mk (complexEmbeddingOf e g') ∈ D.bPlaces)
    (hℓ_cond : ℓ ∣ D.cyclotomicConductor) :
    cmSign (complexEmbeddingOf e g) = cmSign (complexEmbeddingOf e g') := by
  -- Suppose the signs are opposite, and split by whether `ℓ` divides `q₁` or `ℓ = d`.
  by_contra h_ne
  have h_neg : cmSign (complexEmbeddingOf e g) = -cmSign (complexEmbeddingOf e g') :=
    units_ne_iff_eq_neg.1 h_ne
  by_cases hℓ_q₁ : ℓ ∣ D.q₁
  · -- `ℓ ∣ q₁`: `g * g'⁻¹` sends `x = (1 + √-d) / 2` to `1 - x`, so both have the same norm;
    -- it is `< 1` as `ℓ` divides `x * (1 - x)`, against `x + (1 - x) = 1`.
    set x : PadicAlgCl ℓ := e (P.betaKInE D.towerExp)
    have sqrt_sum : complexEmbeddingOf e g (P.sqrtNegDInE D.towerExp) +
        complexEmbeddingOf e g' (P.sqrtNegDInE D.towerExp) = 0 := by
      rw [map_sqrtNegDInE_eq_cmSign_mul, map_sqrtNegDInE_eq_cmSign_mul, h_neg]
      simp
    -- apply `g ∘ ιℓ` to `sqrt_sum`
    have x_conj : (g * g'⁻¹) x = 1 - x := by
      have h_padic : 2 * x - 1 + (2 * (g * g'⁻¹) x - 1) = 0 := by
        simpa [sqrtNegDInE, map_ofNat, complexEmbeddingOf] using
          congrArg (fun w : ℂ ↦ g (ιℓ w)) sqrt_sum
      linear_combination h_padic / 2
    -- the Galois group acts on `PadicAlgCl ℓ` by isometries
    have norm_eq : ‖1 - x‖ = ‖x‖ := by simpa [← x_conj] using dist_smul (g * g'⁻¹) x 0
    have x_mul : x * (1 - x) = ((P.d + 1) / 4 : ℕ) := by
      simpa [map_ofNat] using congrArg
        (fun w : NumberField.RingOfIntegers (P.E D.towerExp) ↦ e w)
          (P.betaKInE_mul_one_sub D.towerExp)
    have norm_mul_lt : ‖x‖ * ‖x‖ < 1 :=
      calc
        ‖x‖ * ‖x‖ = ‖(((P.d + 1) / 4 : ℕ) : PadicAlgCl ℓ)‖ := by rw [← x_mul, norm_mul, norm_eq]
        _ < 1 := by
          rw [← map_natCast (algebraMap ℚ_[ℓ] _), PadicAlgCl.norm_extends]
          exact Padic.norm_natCast_lt_one_iff.2 (P.dvd_d_add_one_div_four_of_dvd_q₁ out hℓ_q₁)
    have one_le : 1 ≤ ‖x‖ := by simpa [norm_eq] using dist_triangle_max 1 (1 - x) 0
    exact (one_le_mul_of_one_le_of_one_le one_le one_le).not_gt norm_mul_lt
  · -- `ℓ = d`: `g' * g⁻¹` acts on `P.ζ` as some power `d ^ n`, so the ratio of the two places is
    -- both `-d ^ n` and `1` modulo `q₀` (b-places have class `-1`); but no power of `d` is `-1`.
    have ℓ_eq : ℓ = P.d :=
      (Nat.prime_dvd_prime_iff_eq out out).1 ((hp.out.dvd_mul.1 hℓ_cond).resolve_left hℓ_q₁)
    have hζ_pow : (e (P.ζ D.towerExp) ^ ℓ ^ 0) ^ D.q₁ = 1 := by
      simp [← map_pow, isPrimitiveRoot_zeta.pow_eq_one]
    obtain ⟨n, hn⟩ : ∃ n : ℕ,
        (g' * g⁻¹) (e (P.ζ D.towerExp) ^ ℓ ^ 0) = (e (P.ζ D.towerExp) ^ ℓ ^ 0) ^ ℓ ^ n :=
      exists_apply_eq_pow hℓ_q₁ hζ_pow (g' * g⁻¹)
    let τ : P.Φ D.towerExp := NumberField.InfinitePlace.mk (complexEmbeddingOf e g)
    let τ' : P.Φ D.towerExp := NumberField.InfinitePlace.mk (complexEmbeddingOf e g')
    have hq₀_dvd : P.q₀ ∣ P.q₁ D.towerExp := P.q₀.dvd_mul_right (towerDeg D.towerExp)
    have h_ratio : (P.placeClass hq₀_dvd (τ / τ')).val =
        (cmSign (complexEmbeddingOf e g) * cmSign (complexEmbeddingOf e g') : ℤ) * ℓ ^ n :=
      placeClass_eq_cmSign_mul_pow e g g' 0 n hn P.q₀ hq₀_dvd (by simp) (mul_div_cancel τ' τ)
    have h_one : (1 : ZMod P.q₀) = -P.d ^ n := by
      simpa [τ, τ', D.placeClass_of_mem_bPlaces, h_mem, h_mem', h_neg, ℓ_eq] using h_ratio
    exact P.d_pow_ne_neg_one n (by rw [h_one, neg_neg])

end BPlaceSpacing

/-! ## Cocycles obeying the relations among the u(g) − 1, and summands of a lift -/

section CocyclesAndSummands

open Matrix LinearMap Module Submodule Finsupp Ideal

open scoped Pointwise

section Cocycles

variable {O X G σ d : Type*} [CommRing O] [Group G] [Fintype σ] [DecidableEq σ] [Fintype d]
  [DecidableEq d] (u : X → G →* Matrix σ σ O) (ρ : G →* Matrix d d O)

/-- The cocycles `c : G → B ^ d` for `ρ`, with values in any `O`-module `B`, that obey the linear
relations among the families `(u x g - 1)_x`: for finitely supported `θ : G → O`, if
`∑ θ g • (u x g - 1) = 0` for all `x`, then `∑ θ g • c g = 0`. -/
def ribetCocyclesIn (B : Type*) [AddCommGroup B] [Module O B] : Submodule O (G → d → B) where
  carrier := {c ∈ obeying (cocycleRelations ρ) B | ∀ θ : G →₀ O,
    linearCombination O (fun (g : G) (x : X) ↦ u x g - 1) θ = 0 → linearCombination O c θ = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro c c' ⟨h_coc, h_rel⟩ ⟨h_coc', h_rel'⟩
    refine ⟨add_mem h_coc h_coc', fun θ hθ ↦ ?_⟩
    simpa [h_rel θ hθ, h_rel' θ hθ] using (bilinearCombination O O).map_add₂ c c' θ
  smul_mem' := by
    rintro s c ⟨h_coc, h_rel⟩
    refine ⟨smul_mem _ s h_coc, fun θ hθ ↦ ?_⟩
    exact ((bilinearCombination O O).map_smul₂ s c θ).trans (smul_eq_zero_of_right s (h_rel θ hθ))

/-- The cocycles `c : G → (O / a) ^ d` for `ρ` that obey the linear relations among the families
`(u x g - 1)_x`: the case `B = O / a` of `ribetCocyclesIn`. -/
abbrev ribetCocycles (a : O) : Submodule O (G → d → QuotSpan a) :=
  ribetCocyclesIn u ρ (QuotSpan a)

variable {u ρ} in
lemma mem_ribetCocycles {a : O} {c : G → d → QuotSpan a} :
    c ∈ ribetCocycles u ρ a ↔
      (∀ g h : G, c (g * h) = c g + ρ g • c h) ∧
      ∀ θ : G →₀ O,
        linearCombination O (fun (g : G) (x : X) ↦ u x g - 1) θ = 0 → linearCombination O c θ = 0 :=
  and_congr_left' mem_obeying_cocycleRelations

/-- For finite `X` and noetherian `O`, a cocycle `c : G → (O/a)^d` in `ribetCocycles u ρ a` extends
to an equivariant map on a submodule: for some `k` there is a subrepresentation `Y` of (families of
matrices) × `(O/a)^d`, with `g` acting by left multiplication with `(u x g)_x` and through `ρ`
(`actionRep`), whose points are determined by their first component and which contains
`((u x g - 1)_x + a ^ k • v, c g)` for all `g` and all families `v`.

This is a consequence of the Artin–Rees lemma for the principal ideal `(a)`: with `I` the span of
the families `(u x g - 1)_x`, the elements of `I` divisible by `a ^ k` lie in `a • I` for some
`k`. -/
lemma ribetCocycles.exists_graph_subrepresentation [Finite X] [IsNoetherianRing O] {a : O}
    {c : G → d → QuotSpan a} (hc : c ∈ ribetCocycles u ρ a) :
    ∃ (k : ℕ) (Y : Subrepresentation ((actionRep O (X → Matrix σ σ O) (MonoidHom.pi u)).prod
      (actionRep O (d → QuotSpan a) ρ))),
      Function.Injective (fun y : Y.toSubmodule ↦ y.val.fst) ∧
      ∀ (g : G) (v : X → Matrix σ σ O), ((fun x : X ↦ u x g - 1) + a ^ k • v, c g) ∈ Y := by
  -- `Y` is the graph of the map that sends `u g - 1` to `c g`, extended by zero to `a ^ (k + 1)`
  -- times everything. By Artin–Rees, for a suitable `k` the span of the `u g - 1` meets these
  -- multiples inside `a` times the span, where the map vanishes as `a` kills its values.
  let L : (G →₀ O) →ₗ[O] X → Matrix σ σ O := linearCombination O fun g x ↦ u x g - 1
  let C : (G →₀ O) →ₗ[O] d → QuotSpan a := linearCombination O c
  obtain ⟨h_coc, h_ker : ∀ θ : G →₀ O, L θ = 0 → C θ = 0⟩ := mem_ribetCocycles.1 hc
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ n ≥ k, a ^ n • (⊤ : Submodule O (X → Matrix σ σ O)) ⊓ L.range =
      a ^ (n - k) • (a ^ k • ⊤ ⊓ L.range) := by
    simpa only [span_singleton_pow, ideal_span_singleton_smul] using
      (span {a}).exists_pow_inf_eq_pow_smul L.range
  -- `N (θ, v) = (L θ + a ^ (k + 1) • v, C θ)`, and `Y` is its range
  let N : (G →₀ O) × (X → Matrix σ σ O) →ₗ[O] (X → Matrix σ σ O) × (d → QuotSpan a) :=
    (L.prod C).coprod (a ^ (k + 1) • inl O (X → Matrix σ σ O) (d → QuotSpan a))
  -- the action of `g` on the target of `N` is induced by a linear map `shift g` of the source
  let shift (g : G) : End O ((G →₀ O) × (X → Matrix σ σ O)) :=
    prodMap (lsum O fun h ↦ lsingle (g * h) - lsingle g) (mulLeft O fun x ↦ u x g)
  have h_shift (g : G) :
      ((actionRep O (X → Matrix σ σ O) (MonoidHom.pi u)).prod (actionRep O (d → QuotSpan a) ρ)) g
        ∘ₗ N = N ∘ₗ shift g := by
    -- both components are checked on the generators, by the cocycle rule and `mul_sub`
    ext <;> simp [N, L, C, shift, h_coc, mul_sub]
  refine ⟨k + 1, ⟨N.range, ?_⟩, ?_, fun g v ↦ ?_⟩
  · rintro g _ ⟨z, rfl⟩
    exact ⟨shift g z, (LinearMap.congr_fun (h_shift g) z).symm⟩
  · -- a point `N (θ, v)` of `Y` with first component zero is zero
    refine (injective_iff_map_eq_zero
      (domRestrict (fst O (X → Matrix σ σ O) (d → QuotSpan a)) N.range)).2 ?_
    rintro ⟨_, ⟨θ, v⟩, rfl⟩ (h_fst : (N (θ, v)).fst = 0)
    have hv : L θ = a ^ (k + 1) • -v := by simpa [N, add_eq_zero_iff_eq_neg] using h_fst
    -- by `hk`, `L θ = L (a • η)` for some `η`; so `C θ = a • C η = 0`
    have h_mem : L θ ∈ a ^ (k + 1) • (⊤ : Submodule O (X → Matrix σ σ O)) ⊓ L.range :=
      ⟨⟨-v, Submodule.mem_top, hv.symm⟩, L.mem_range_self θ⟩
    rw [hk (k + 1) k.le_succ] at h_mem
    obtain ⟨w, ⟨-, η, hw : L η = w⟩, hη : a ^ (k + 1 - k) • w = L θ⟩ := h_mem
    have h_aη : a • C η = 0 := funext fun i : d ↦ smul_quot_eq_zero_of_dvd dvd_rfl (C η i)
    have h_snd : C θ = 0 := by simpa [h_aη] using h_ker (a • η - θ) (by simp [← hη, hw])
    exact Subtype.ext (Prod.ext h_fst (by simpa [N] using h_snd))
  · exact ⟨(.single g 1, v), by simp [N, L, C]⟩

end Cocycles

/-- The index sets of the summands of a lift: `r` for the main summand, and one point for each of
the `t` characters, which are `1 × 1` summands. -/
def SummandCoordIndex (r : Type) {t : ℕ} : Option (Fin t) → Type
  | none => r
  | .some _ => Unit

/-- Each index set `SummandCoordIndex r i` is finite if `r` is. -/
instance {r : Type} [inst : Fintype r] {t : ℕ} :
    ∀ i : Option (Fin t), Fintype (SummandCoordIndex r i)
  | none => inst
  | .some _ => PUnit.fintype

/-- Each index set `SummandCoordIndex r i` has decidable equality if `r` has. -/
instance {r : Type} [inst : DecidableEq r] {t : ℕ} :
    ∀ i : Option (Fin t), DecidableEq (SummandCoordIndex r i)
  | none => inst
  | .some _ => instDecidableEqPUnit

variable {d : Type} [Fintype d] [DecidableEq d] {t ℓ : ℕ} [ThePrime ℓ] {E : Type} [Field E]
  [EmbeddedNumberField E] {O : CoeffRing ℓ} (T : Gal(Ω/E) →* Matrix d d O)

/-- The summands of a lift: `T` on the main summand, and on the summand of `e : Fin t` the Tate
twist `O(-e)`, the `e`-th power of the inverse cyclotomic character. -/
def summandRep : ∀ i : Option (Fin t), Gal(Ω/E) →* Matrix (SummandCoordIndex d i)
  (SummandCoordIndex d i) O
  | none => T
  | Option.some e => tateTwist ℓ E O e

end CocyclesAndSummands

/-!
## Crystalline conditions above ℓ as relations on cocycles, and crystalline colength

* `New.Selmer.localChart`: a chosen identification of the decomposition group at `v` with a subgroup
  of `Gal(ℚ̄_ℓ / ℚ_ℓ)`.

A relation is a finitely supported matrix-valued `f`, and `c` obeys it if `∑ γ, f γ • c γ = 0`.
`New.relationsOn Z` is the set of relations that hold on `Z`, `New.obeying R B` the module of
functions with values in `Bⁿ` that obey the relations `R`, and `New.relLength S T` the length of
`S / (S ⊓ T)`.
-/

section CrystallineConditions

variable (ℓ : ℕ) [ThePrime ℓ] {n : Type*} [Fintype n] [DecidableEq n]
  (E : Type) [Field E] [CMFieldWithRoot5040 E] (v : placesDividing E ℓ) {O : CoeffRing ℓ}

/-- A chosen embedding Ω → ℚ̄_ℓ that induces the chosen place of Ω above v, together with the
homomorphism to Gal(ℚ̄_ℓ over ℚ_ℓ) from the decomposition group of that place that goes with it in
the sense of `New.GaloisRep.InducesPlace`. -/
instance localChart : GaloisRep.PadicPlaceEmbedding E (placeOver v.1) ℓ :=
  -- An embedding of `Ω` into `PadicAlgCl ℓ` induces the place, which lies above `ℓ`; it gives the
  -- open embedding of the decomposition group. Both chosen maps are read off the type of `loc`.
  have loc :=
    (exists_inducesPlace E _
      (exists_comap_intQpBar_eq
        (v.1.isPlaceOver_placeOver.valuation_natCast_lt_one_iff.2 v.2)).choose_spec).choose_spec
  { isOpen_range := ⟨loc.2.1.2⟩, inducesPlace := loc, .. }

variable {ℓ E} (u : Gal(Ω/E) →* Matrix n n O)

/-- For g in Gal(ℚ̄_ℓ over ℚ_ℓ), the embedding of the coefficient ring O in ℂ_ℓ sending x to
g(x). -/
def coefficientEmbedding (O : CoeffRing ℓ) (g : Gp ℓ) : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ] :=
  IsScalarTower.toAlgHom ℤ_[ℓ] (PadicAlgCl ℓ) ℂ_[ℓ]
    |>.comp (g.toAlgHom.restrictScalars ℤ_[ℓ])
    |>.comp O.val.val

/-- The O-module Z_f at v: crystalline cocycles (`New.Period.crysCocycles`) of the decomposition
group of the chosen place above v, with values in O^n acted on through u. -/
def crysCocyclesAt : Submodule O (decompGroup Gal(Ω/E) (placeOver v.val) → n → ↑O) :=
  Period.crysCocycles
    (actionRep O (n → ↑O) (u.comp (decompGroup Gal(Ω/E) (placeOver v.val)).subtype))

/-- The linear relations that hold on the crystalline cocycles `New.Selmer.crysCocyclesAt v u` for
some v above ℓ, extended by zero from the decomposition group to relations on functions on
Gal(Ω/E). -/
def crysRelations : Set (Gal(Ω/E) →₀ Matrix n n O) :=
  ⋃ v : placesDividing E ℓ, Finsupp.mapDomain Subtype.val '' relationsOn (crysCocyclesAt v u)

/-- The crystalline colength of the summand `u` modulo `ℓ ^ M`, with respect to a family `w` of
matrix representations of Gal(Ω/E): the length of the module of cocycles for `u` with values in
`(O/ℓ^M)^n` that obey every linear relation among the `(w x g - 1)_x` (`New.Selmer.ribetCocycles`),
modulo those that also obey the relations `New.Selmer.crysRelations u` of the crystalline cocycles
above `ℓ`. -/
abbrev crystallineColength {X σ : Type*} [Fintype σ] [DecidableEq σ]
    (w : X → Gal(Ω/E) →* Matrix σ σ O) (M : ℕ) : ℕ∞ :=
  relLength (ribetCocycles w u (ℓ ^ M)) (obeying (crysRelations u) (QuotSpan ((ℓ : ↑O) ^ M)))

/-- Let `E` be a CM field in the algebraic closure `Ω` of `ℚ` with a primitive `5040`-th root of
unity, `O` the ring of integers of a finite Galois extension of `ℚ_ℓ` in `ℚ̄_ℓ`, and `u` a matrix
representation of `Gal(Ω/E)` over `O`. A function `c : Gal(Ω/E) → (O/a)^n` obeys the relations
`New.Selmer.crysRelations u` if and only if, for every place `v` of `E` above `ℓ`, its restriction
to the decomposition group of the chosen place over `v` obeys every linear relation
(`New.relationsOn`) that holds on the crystalline cocycles `New.Selmer.crysCocyclesAt v u`. -/
lemma obeying_crysRelations (u : Gal(Ω/E) →* Matrix n n O) {a : ↑O} :
    obeying (crysRelations u) (QuotSpan a) =
      ⨅ v : placesDividing E ℓ, (obeying (relationsOn (crysCocyclesAt v u)) (QuotSpan a)).comap
        (LinearMap.funLeft O (n → QuotSpan a) (↑)) := by
  ext c
  -- A relation pushed forward by `Finsupp.mapDomain` is evaluated on the restriction of `c`.
  simp [crysRelations, obeying, forall_comm (α := _ →₀ _), LinearMap.funLeft, Function.comp_def]

end CrystallineConditions

/-!
## Embeddings at a place above ℓ, local degree and Tate twists

`New.Selmer.IsCompletionGroup e j` says that `j` is an open embedding onto the elements that fix
`e E`.
-/

section LocalEmbeddings

open Period IsAlgClosed GaloisRep Set Algebra.IsAlgebraic Setoid QuotientGroup

variable {ℓ : ℕ} [ThePrime ℓ] {E Γ : Type _} [Field E] [Group Γ] [TopologicalSpace Γ]
  {e : E →+* PadicAlgCl ℓ} {j : Γ →* Gp ℓ}

/-- Every `ℤ_ℓ`-algebra map `O → ℂ_ℓ` is the restriction of an element of `Gp ℓ`, the Galois
group of `ℚ̄_ℓ` over `ℚ_ℓ`: it equals `coefficientEmbedding O g` for some `g`. -/
lemma coefficientEmbedding_surjective {O : CoeffRing ℓ} : (coefficientEmbedding O).Surjective := by
  intro γ
  -- Extend `γ` to an embedding `φ` of the algebraic extension `PadicAlgCl ℓ` of `O` in the
  -- algebraically closed field `ℂ_[ℓ]`; every such embedding comes from an element of `Gp ℓ`.
  let : Algebra O ℂ_[ℓ] := γ.toAlgebra
  have : Algebra.IsAlgebraic O (PadicAlgCl ℓ) := (isAlgebraic_iff_top ℤ_[ℓ] O).1 inferInstance
  have : Module.IsTorsionFree O ℂ_[ℓ] := (faithfulSMul_tower_top ℤ_[ℓ] O ℂ_[ℓ]).to_isTorsionFree
  let φ : PadicAlgCl ℓ →ₐ[O] ℂ_[ℓ] := IsAlgClosed.lift
  obtain ⟨g, hg⟩ := exists_gp_eq_algHom (φ.restrictScalars ℤ_[ℓ])
  refine ⟨g, AlgHom.ext fun x ↦ ?_⟩
  calc coefficientEmbedding O g x = φ x := (hg x).symm
    _ = γ x := φ.commutes x

/-- Let `emb` be an embedding `Ω → ℚ̄_ℓ` that induces the place `A` of `Ω`, with its map
`emb.toGp` from the decomposition group of `A` to `Gp ℓ = Gal(ℚ̄_ℓ/ℚ_ℓ)`. An element `g` of this
group acts on `O` through the Tate twist `tateTwist ℓ E O c`, the `c`-th power of the inverse
cyclotomic character, as the power `-c` of the local cyclotomic character at `emb.toGp g`. -/
lemma tateTwist_smul [CMFieldWithRoot5040 E] {O : CoeffRing ℓ} {A : ClosurePlace}
    {emb : PadicPlaceEmbedding E A ℓ} (c : ℕ) (g : decompGroup Gal(Ω/E) A) (x : Unit → ↑O) :
    tateTwist ℓ E O c g.val • x = cyclotomicGp (emb.toGp g) ^ (-c : ℤ) • x := by
  simp [funext_iff, emb.cyclotomicGp_eq_cyclotomicChar, tateTwist, cyclotomicInv, Units.smul_def,
    Algebra.smul_def]

variable [PadicIso ℓ]

/-- Let `j : Γ → Gp ℓ` be an open embedding whose image is the group of elements that fix `e E`
pointwise (`IsCompletionGroup e j`). Then `g` and `g'` give the same complex embedding
`ι⁻¹ ∘ g⁻¹ ∘ e` if and only if `g * g'⁻¹` is in the image of `j`. -/
lemma IsCompletionGroup.complexEmbeddingOf_eq_iff (hj : IsCompletionGroup e j) {g g' : Gp ℓ} :
    complexEmbeddingOf e g = complexEmbeddingOf e g' ↔ g * g'⁻¹ ∈ j.range := by
  have h_range : ∀ g : Gp ℓ, g ∈ j.range ↔ ∀ x : E, g (e x) = e x := hj.2
  -- the left side says that `g⁻¹` and `g'⁻¹` agree on `e E`, the right that `g * g'⁻¹` fixes it
  simp [complexEmbeddingOf, g.symm_apply_eq, eq_comm, RingHom.ext_iff, h_range]

/-- Let `j : Γ → Gp ℓ` be an open embedding whose image is the group of elements that fix `e E`
pointwise. The index of this image is the number of distinct complex embeddings
`complexEmbeddingOf e g = ι⁻¹ ∘ g⁻¹ ∘ e`, for `g` in `Gp ℓ`. -/
lemma IsCompletionGroup.index_eq_card_range (hj : IsCompletionGroup e j) :
    j.range.index = Nat.card (range (complexEmbeddingOf e)) := by
  -- Two elements give the same embedding iff their inverses lie in one coset of `j.range`.
  have h_left (g g' : Gp ℓ) : leftRel j.range g g' ↔ ker (complexEmbeddingOf e) g⁻¹ g'⁻¹ := by
    simp [hj.complexEmbeddingOf_eq_iff, leftRel_eq]
  exact Nat.card_congr
    ((Quotient.congr (Equiv.inv (Gp ℓ)) h_left).trans
      (quotientKerEquivRange (complexEmbeddingOf e)))

/-- Let `E` be a CM field in the algebraic closure `Ω` of `ℚ` with a primitive `5040`-th root of
unity, and `ι : ℂ ≃ ℚ̄_ℓ` the isomorphism fixed by `PadicIso ℓ`. Let `v` and `w` be places of `E`
above the prime `ℓ`, and `e_v`, `e_w` the restrictions to `E` of the embeddings `Ω → ℚ̄_ℓ` of their
charts `localChart`. If `ι⁻¹ ∘ g⁻¹ ∘ e_v = ι⁻¹ ∘ g'⁻¹ ∘ e_w` for some `g` and `g'` in
`Gp ℓ = Gal(ℚ̄_ℓ/ℚ_ℓ)`, then `v = w`: a complex embedding determines its place above `ℓ`. -/
lemma eq_of_complexEmbeddingOf_localChart_eq [CMFieldWithRoot5040 E] {v w : placesDividing E ℓ}
    {g g' : Gp ℓ}
    (h_eq : complexEmbeddingOf ((localChart ℓ E v).e.comp (algebraMap E Ω)) g =
      complexEmbeddingOf ((localChart ℓ E w).e.comp (algebraMap E Ω)) g') :
    v = w := by
  -- the valuation ring that the chart at a place pulls back lies over that place
  have h_over (v : placesDividing E ℓ) :
      IsPlaceOver ((intQpBar ℓ).comap (localChart ℓ E v).e) v.1 := by
    obtain ⟨⟨h_comap : (intQpBar ℓ).comap (localChart ℓ E v).e = placeOver v.1, -⟩, -⟩ :=
      (localChart ℓ E v).inducesPlace
    simpa only [h_comap] using FinPlace.isPlaceOver_placeOver v.1
  ext x
  -- `x` lies in the place exactly when its image has norm `< 1`, and `Gp ℓ` acts by isometries.
  have h_norm :
      ‖(ιℓ (complexEmbeddingOf ((localChart ℓ E v).e.comp (algebraMap E Ω)) g x) : ℂ_[ℓ])‖ < 1 ↔
      ‖(ιℓ (complexEmbeddingOf ((localChart ℓ E w).e.comp (algebraMap E Ω)) g' x) : ℂ_[ℓ])‖ <
        1 := by
    rw [h_eq]
  simpa [← h_over v x, ← h_over w x, comap_apply_lt_one_iff, complexEmbeddingOf, ← smul_coe_Cp]
    using h_norm

open scoped Classical in
/-- Let `E` be a CM field in the algebraic closure `Ω` of `ℚ` with a primitive `5040`-th root of
unity, and `ι : ℂ ≃ ℚ̄_ℓ` the isomorphism fixed by `PadicIso ℓ`. For each place `v` of `E` above the
prime `ℓ`, the chart `localChart ℓ E v` has an embedding `Ω → ℚ̄_ℓ` that induces a place above `v`.
Its restriction `e` to `E` gives the complex embeddings `complexEmbeddingOf e g = ι⁻¹ ∘ g⁻¹ ∘ e`,
for `g` in `Gp ℓ = Gal(ℚ̄_ℓ/ℚ_ℓ)`. For distinct `v` these sets of embeddings are disjoint, so the
sums of `a` over them add up to at most the sum of `a` over all complex embeddings of `E`. -/
lemma sum_complexEmbeddingOf_le [CMFieldWithRoot5040 E] (a : (E →+* ℂ) → ℕ) :
    ∑ v : placesDividing E ℓ,
        ∑ σ : E →+* ℂ with
          ∃ g : Gp ℓ, complexEmbeddingOf ((localChart ℓ E v).e.comp (algebraMap E Ω)) g = σ,
        a σ ≤
      ∑ σ : E →+* ℂ, a σ := by
  let R (v : placesDividing E ℓ) : Finset (E →+* ℂ) :=
    {σ : E →+* ℂ | ∃ g : Gp ℓ, complexEmbeddingOf ((localChart ℓ E v).e.comp
      (algebraMap E Ω)) g = σ}
  -- An embedding determines its place, so the sets for distinct places are disjoint.
  have h_disj : Set.PairwiseDisjoint (Finset.univ : Finset (placesDividing E ℓ)) R :=
    fun v _ w _ hvw ↦ Finset.disjoint_filter.2 fun σ _ ⟨g, hg⟩ ⟨g', hg'⟩ ↦
      hvw (eq_of_complexEmbeddingOf_localChart_eq (hg.trans hg'.symm))
  rw [← Finset.sum_biUnion h_disj]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end LocalEmbeddings

end New.Selmer

end
