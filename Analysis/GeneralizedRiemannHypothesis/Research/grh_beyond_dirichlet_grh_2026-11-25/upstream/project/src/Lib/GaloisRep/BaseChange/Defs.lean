import Lib.Adelic.Unitary.Defs

/-!
# Twisted norms, matching pairs and base change maps for unitary groups

This file sets up base change for unitary groups along a ring endomorphism `σ` of finite order.
Finally it defines the Galois action on `New.Gf E' n` and the base change map from the finite adelic
unitary group `New.Gf E n`, the matrices `g` over the finite adeles with `gᴴ g = 1`, for an
extension `E'/E` of CM fields.

## Main definitions and results

* `New.twistedNorm`: the twisted norm `δ · τ δ ⋯ τ^(p-1) δ` in a monoid. `New.twistedNorm_conj`
  shows that twisted conjugation of `δ` conjugates the norm. `New.twistedNorm_mem` and
  `New.map_twistedNorm` show that it respects stable subgroups and equivariant maps.
* `New.IsTameAtLevel`: the conditions on a ring endomorphism `σ` and a level `m` under which descent
  works.
* `New.IsRootQuotient`, `New.IsNormRoot`: a polynomial `z`, depending only on the characteristic
  polynomial of `γ`, that gives a candidate `a = z(γ) / z(γ)ᴴ` for an element of norm `γ`.
* `New.IsMatchingPair`: `φ` is invariant under twisted conjugation by `K`, and `f` and `φ` match
  point by point along `γ ↦ a`.
* `New.CocyclesSplit`: the cocycles in `K` are coboundaries on the support of `u`.
* `New.baseChangeGf`: the map `Gf E n → Gf E' n` induced by the inclusion of finite adeles.

Notions from other files:
* `New.U J`: the unitary group of a matrix `J` over a commutative ring with involution, the `g` in
  `GL_n(R)` with `gᴴ J g = J`. In this file `J = 1`.
* `New.U.map`: for a ring homomorphism `f` commuting with the involutions and carrying `J` to `J'`,
  the homomorphism `U(J) → U(J')` applying `f` to each entry.
* `New.FinPlace E`: the finite places of a number field `E`. For a finite place `u`, `u.comap f` is
  the place below `u` along a ring homomorphism `f`, and `u.below E` is the place of `E` below `u`.
* `New.adeleMap`: for an embedding of number fields, the induced ring homomorphism of finite adeles.

## Relation to the literature

Known; see `Lib.GaloisRep.BaseChange.PrimeDegreeTransfer` for sources.
-/

namespace New

/-! ## Twisted norms, tame actions and profinite rings -/

section TwistedNorm

variable {G R n M Γ : Type*} [Group G] [Monoid M] [Monoid Γ] [CommRing R] [Fintype n]
  [DecidableEq n] (τ : M →* M) (σ : R →+* R) (p : ℕ) [StarRing R]

/-- The twisted norm `δ · τ(δ) ⋯ τ^{p−1}(δ)` of `δ` in a monoid `M`: the product, in order, of the
first `p` iterates `τ^[i] δ`. Here `τ : M → M` is any map. -/
@[local simp]
def twistedNorm (τ : M → M) (p : ℕ) (δ : M) : M := ((List.range p).map fun i ↦ τ^[i] δ).prod

lemma twistedNorm_succ (τ : M → M) (p : ℕ) (δ : M) :
    twistedNorm τ (p + 1) δ = twistedNorm τ p δ * τ^[p] δ := by
  simp [twistedNorm, List.range_add]

/-- The ring endomorphism `σ` acts tamely at level `m`: (a) `σ m = m`; (b) some `e` has trace
`∑ i < p, (σ ^ i) e` congruent to `1` modulo `m`; (c) `σ ^ p = 1`; (d) `0 < p`; (e) for `0 < i < p`,
every prime ideal `P` modulo which `σ ^ i` is the identity contains `m`, so there is no inertia at
the primes that do not contain `m`. -/
def IsTameAtLevel (m : R) : Prop :=
  σ m = m ∧
  (∃ e : R, m ∣ ∑ i ∈ Finset.range p, (σ ^ i) e - 1) ∧
  σ ^ p = 1 ∧ 0 < p ∧
  ∀ i ∈ Set.Ioo 0 p, ∀ (P : Ideal R) [Ideal.IsPrime P], (∀ x : R, (σ ^ i) x - x ∈ P) → m ∈ P

/-- A form of profiniteness that allows passing to the limit. Every sequence `x` has exactly one `L`
such that, for each natural number `M ≠ 0`, `M` divides `x N - L` for all `N` in a set of the
hyperfilter (a fixed ultrafilter on `ℕ` that contains the cofinite sets). For the topology given by
the ideals `(M)`, existence of `L` is a form of compactness and uniqueness says that only `0` is
divisible by every `M ≠ 0`. -/
def IsProfiniteRing (R : Type*) [CommRing R] : Prop :=
  ∀ x : ℕ → R, ∃! L : R, ∀ M ≠ (0 : ℕ), ∀ᶠ N : ℕ in Filter.hyperfilter ℕ, Nat.cast M ∣ x N - L

/-- The endomorphism of the unitary group `{g : gᴴ g = 1}` over `R` given by applying entrywise a
ring endomorphism `σ` commuting with the involution. -/
noncomputable abbrev U.mapEnd {σ : R →+* R} (hσ : ∀ x : R, σ (star x) = star (σ x)) :
    U (1 : Matrix n n R) →* U (1 : Matrix n n R) :=
  map σ hσ (one_map_ringHom σ)

/-- For a group endomorphism `τ` and an element `y` with `τ^[p] y = y`, the twisted conjugate
`y⁻¹ * δ * τ y` of `δ` has twisted norm `y⁻¹ * twistedNorm τ p δ * y`. -/
lemma twistedNorm_conj (τ : G →* G) (p : ℕ) {y : G} (hy : τ^[p] y = y) (δ : G) :
    twistedNorm τ p (y⁻¹ * δ * τ y) = y⁻¹ * twistedNorm τ p δ * y := by
  -- The product telescopes: its `i`-th factor is `(τ^[i] y)⁻¹ * τ^[i] δ * τ^[i + 1] y`.
  have h_partial (k : ℕ) :
      twistedNorm τ k (y⁻¹ * δ * τ y) = y⁻¹ * twistedNorm τ k δ * τ^[k] y := by
    induction k with
    | zero => simp [twistedNorm]
    | succ k ih =>
      have h_factor : τ^[k] (y⁻¹ * δ * τ y) = (τ^[k] y)⁻¹ * τ^[k] δ * τ^[k + 1] y := by
        rw [iterate_map_mul, iterate_map_mul, iterate_map_inv, Function.iterate_succ_apply]
      rw [twistedNorm_succ, twistedNorm_succ, ih, h_factor]
      group
  rw [h_partial, hy]

/-- If `τ` maps the subgroup `K` into itself, then the twisted norm of every `δ ∈ K` lies in `K`. -/
lemma twistedNorm_mem {K : Subgroup G} (τ : G → G) (p : ℕ) (hK : ∀ k ∈ K, τ k ∈ K) {δ : G}
    (hδ : δ ∈ K) : twistedNorm τ p δ ∈ K := by
  -- Every factor `τ^[i] δ` of the product lies in `K`, as `τ` and its iterates map `K` into `K`.
  show ((List.range p).map fun i ↦ τ^[i] δ).prod ∈ K
  refine Subgroup.list_prod_mem _ fun x hx ↦ ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  exact Set.MapsTo.iterate hK i hδ

/-- A monoid homomorphism `e` that intertwines `τ` on `Γ` with `σ` on `M` (`e (τ δ) = σ (e δ)`)
carries twisted norms for `τ` to twisted norms for `σ`. -/
lemma map_twistedNorm {σ : M → M} {τ : Γ → Γ} (e : Γ →* M)
    (h_comm : ∀ δ : Γ, e (τ δ) = σ (e δ)) (p : ℕ) :
    ∀ δ : Γ, e (twistedNorm τ p δ) = twistedNorm σ p (e δ) := by
  intro δ
  -- `e` intertwines every iterate of the two maps, hence each factor of the product.
  have h_iterate (i : ℕ) : e (τ^[i] δ) = σ^[i] (e δ) := Function.Semiconj.iterate_right h_comm i δ
  simp only [twistedNorm, map_list_prod, List.map_map, Function.comp_def, h_iterate]

/-- Splitting off the first factor of the twisted norm, for the monoid endomorphism `τ`. -/
lemma twistedNorm_succ' (δ : M) : twistedNorm τ (p + 1) δ = δ * τ (twistedNorm τ p δ) := by
  -- The factors after `δ` form the twisted norm of `τ δ`, which is `τ` of the twisted norm of `δ`.
  have h_tail : twistedNorm τ (p + 1) δ = δ * twistedNorm τ p (τ δ) := by
    simp [twistedNorm, List.range_succ_eq_map, Function.comp_def, Function.iterate_succ_apply]
  rw [h_tail, map_twistedNorm τ (fun x : M ↦ rfl) p δ]

end TwistedNorm

/-!
## Matching pairs and split cocycles

This section states when test functions on a set `A` (a unitary group over the base, mapped by `j`)
and on the unitary group over `R` match in base change. Here `σ` is a ring endomorphism of `R` that
commutes with `star`. `New.U.mapEnd h` is the action of `σ` on the unitary group, `New.twistedNorm`
is the twisted norm of length `q`, and `u : R` selects the places concerned. "The support of `u`"
means where `u` is `1`, as for an idempotent, though nothing here assumes `u * u = u`. The
conditions multiply by `u` or by `1 - u`.
-/

section MatchingPairDefs

open Matrix U Function

variable {R n A : Type*} [CommRing R] [Fintype n] [DecidableEq n] {σ : R →+* R} [StarRing R]
  (h : ∀ (x : R), σ (star x) = star (σ x)) (q : ℕ) (u : R) (D : Subgroup Rˣ)
  (γ : U (1 : Matrix n n R)) (P z : Polynomial R) (j : A → U (1 : Matrix n n R))
  (K : Subgroup (U (1 : Matrix n n R)))

/-- The relation `a * z(γ)ᴴ = z(γ)` between a matrix `a`, a polynomial `z` and a unitary `γ`, where
`z(γ)` is `z` evaluated at the matrix `γ.val.val` of `γ` and `ᴴ` is the conjugate transpose.
When `z(γ)ᴴ` is invertible it says `a = z(γ) * (z(γ)ᴴ)⁻¹`. -/
abbrev IsRootQuotient (a : Matrix n n R) : Prop := a * (z.aeval γ.val.val)ᴴ = z.aeval ↑γ

variable (n σ) in
/-- `z` is a root for `P` on the support of `u`: `(1 - u) • z = (1 - u) • 1`, and if some unitary
`γ` has characteristic polynomial `P`, then (a) `det z(A)` is the value of a unit in `D` for every
square matrix `A` with `P(A) = 0`, and (b) `(1 + u • (γ - 1)) * (N z)(γ)ᴴ = (N z)(γ)` for every
such `γ`, where `N z` is the product of the `q` conjugates of `z` under `σ`. The matrix in (b) is
`γ` on the support of `u` and `1` off it. -/
def IsNormRoot : Prop :=
  (1 - u) • z = (1 - u) • 1 ∧
  ∀ γ : U (1 : Matrix n n R), γ.val.val.charpoly = P →
    (∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) R), P.aeval A = 0 →
      (z.aeval A).det ∈ D.toSubmonoid.map (Units.coeHom R)) ∧
    IsRootQuotient γ (twistedNorm (Polynomial.map σ) q z) (1 + u • (γ - 1))

/-- `f` and `φ` match, with `Nm = twistedNorm (mapEnd h) q`: `φ` is invariant under
`δ ↦ k⁻¹ * δ * σ(k)` for `k ∈ K`, and each `σ`-fixed characteristic polynomial `P` of some `j g`
with `f g ≠ 0` or some `Nm δ` with `φ δ ≠ 0` has a root `z` (`New.IsNormRoot`) such that every
unitary `a` with `a * (u • z)(γ)ᴴ = (u • z)(γ)`, for `γ` of characteristic polynomial `P`, has
`f g = φ a` when `j g = γ = Nm a`, and `a⁻¹ * δ ∈ K` when `Nm δ = γ` and `φ δ ≠ 0`. -/
def IsMatchingPair (f : A → ℂ) (φ : U (1 : Matrix n n R) → ℂ) : Prop :=
  (∀ k ∈ K, ∀ δ : U 1, φ (k⁻¹ * δ * mapEnd h k) = φ δ) ∧
  ∀ P ∈ (·.val.val.charpoly) '' (j '' support f ∪ twistedNorm (mapEnd h) q '' support φ),
    P.map σ = P → ∃ z : Polynomial R,
    IsNormRoot n σ q u D P z ∧
    ∀ γ a : U (1 : Matrix n n R), γ.val.val.charpoly = P →
      IsRootQuotient γ (u • z) a.val →
      (∀ g : A, j g = γ → twistedNorm (mapEnd h) q a = γ → f g = φ a) ∧
      ∀ δ : U (1 : Matrix n n R), twistedNorm (mapEnd h) q δ = γ → φ δ ≠ 0 → a⁻¹ * δ ∈ K

/-- The cocycles in `K` split on the support of `u`: every `s ∈ K` whose twisted norm of length `q`
under `τ` is `1` has some `t ∈ K` with `(1 - u) • t = (1 - u) • 1` (`t` is `1` off the support of
`u`) and `u • (t⁻¹ * s * τ t) = u • 1` (on the support of `u`, `s = t * (τ t)⁻¹`). Here `.val.val`
is the matrix of an element of the unitary group. -/
def CocyclesSplit (τ : U (1 : Matrix n n R) → U (1 : Matrix n n R)) : Prop :=
  ∀ s ∈ K, twistedNorm τ q s = 1 → ∃ t ∈ K,
    (1 - u) • t.val.val = (1 - u) • 1 ∧ u • (t⁻¹ * s * τ t).val.val = u • 1

end MatchingPairDefs

/-! ## Base change and Galois action on finite adelic points -/

section BaseChangePoints

open Nat Function NumberField

variable {E E' : Type*} [Field E] [NumberField E] [Field E'] [NumberField E']
  [IsCMField E'] [Algebra E E'] {n : Type*} [Fintype n] [DecidableEq n] (σ : Gal(E'/E))

omit [NumberField E] [NumberField E'] [IsCMField E'] in
/-- Moving a finite place `u` of `E'` by `σ ∈ Gal(E'/E)` does not change the place of `E`
below it. -/
@[simp]
lemma below_comap (u : FinPlace E') : (u.comap σ : FinPlace E').below E = u.below E := by
  -- Restricting along `σ` and then to `E` is, by definition, restricting along the composite,
  -- and `σ` fixes `E`.
  show u.comap ((σ : E' →+* E').comp (algebraMap E E')) = u.comap (algebraMap E E')
  exact congrArg u.comap σ.toAlgHom.comp_algebraMap

omit [IsCMField E'] in
/-- In a Galois extension `E'/E` of prime degree `q = Module.finrank E E'`, the powers `σ ^ i`,
`0 ≤ i < q`, of any `σ ≠ 1` are the elements of the Galois group, each once. -/
lemma bijective_pow_of_ne_one_of_prime_finrank [IsGalois E E']
    [h : Fact (Module.finrank E E').Prime] {σ : Gal(E'/E)} (hσ : σ ≠ 1) :
    Bijective fun i : Fin (Module.finrank E E') ↦ σ ^ (i : ℕ) := by
  -- The Galois group has prime order `q`, so `σ ≠ 1` has order `q`: the `q` powers `σ ^ i` with
  -- `i < q` are distinct, and there are as many of them as elements of the group.
  have h_card : Nat.card Gal(E'/E) = Module.finrank E E' := IsGalois.card_aut_eq_finrank E E'
  have h_order : orderOf σ = Module.finrank E E' :=
    orderOf_eq_prime (by rw [← h_card, pow_card_eq_one']) hσ
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨fun i j h_pow_eq ↦ ?_, ?_⟩
  · exact Fin.ext (pow_injOn_Iio_orderOf (by simp [h_order]) (by simp [h_order]) h_pow_eq)
  · rw [h_card, Nat.card_fin]

/-- The homomorphism from the finite adelic unitary group over E to the one over E' induced by
the inclusion of finite adeles. -/
noncomputable def baseChangeGf [IsCMField E] : Gf E n →* Gf E' n :=
  U.map (adeleMap (algebraMap E E')) (adeleMap_star (algebraMap E E'))
    (one_map_ringHom (adeleMap (algebraMap E E')))

/-- The action of σ in Gal(E'/E) on the finite adelic unitary group over E', entry by entry. -/
noncomputable abbrev galoisGf : Gf E' n →* Gf E' n := U.mapEnd (adeleMap_star σ)

end BaseChangePoints

end New
