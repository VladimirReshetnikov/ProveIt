import Lib.GLn.SchurModule.SchurNorm
import Lib.PadicHodge.Characters
import Lib.Weil.DualPair.FiniteAction

/-!
# Attached Galois representations: traces, characteristic polynomials and rank one

This file sets up the statement that eigenforms on a definite unitary group have attached Galois
representations. Here `ιℓ` identifies `ℂ` with an algebraic closure of `ℚ_ℓ`, and `P` is a system of
complex polynomials, one for each finite place. A continuous representation `ρ` with non-degenerate
trace form, with an open map `j` to the Galois group, is attached to `P` when, along most Frobenius
elements (the filter `New.mostFrobenii`), its characteristic polynomials approach `ιℓ (P w)`. The
file shows that the characteristic polynomials are then determined by `P`, so two attached
representations have the same traces. It also shows that the representation attached to an
eigenform on the definite unitary group of rank one is the avatar of an algebraic Hecke character.

## Main definitions and results

* `New.GaloisRep.Attached`: a representation `ρ` of a topological group `H`, together with a map `j`
  from `H` to the Galois group (by default the identity), is attached to `P`. This means that `ρ` is
  continuous, has a non-degenerate trace form (`New.IsTraceNondeg`), `j` is open, and along most
  Frobenius elements the characteristic polynomials of `ρ` approach `ιℓ (P w)`.
* `New.GaloisRep.SphericalCompat`: the statement that an attached representation exists, and that
  every attached representation satisfies `New.GaloisRep.IsCompatibleAt` (unramified or crystalline,
  Hodge–Tate jumps, Hecke polynomial) at a place `w` where the form is spherical.
* `New.GaloisRep.Attached.tendsto_charpoly_coeff`: `ιℓ (P w)` tends to `det (X - ρ x)` as the
  Frobenius element at `w` tends to `j x`.
* `New.GaloisRep.Attached.trace_eq`: two representations attached to `P` have the same traces.
* `New.IsRankOneCharacter`: the infinity type of an algebraic Hecke character `θ` and its values at
  split places are read off from a form on `U(1)` and its weight.
* `New.GaloisRep.Attached.exists_det_eq_avatar`: in rank one, an attached representation is the
  avatar of such a character `θ`.

Notions from other files:
* `New.Ω`: an algebraic closure of `ℚ`.
* `New.Gf E n`: the finite adelic points of the definite unitary group of the CM field `E`.
* `New.IsEigenform f P`: `f ≠ 0`, and at almost all `w` of prime norm, `w` is split and `f` is
  spherical with Hecke polynomial `P w` (`New.HasHeckePolyAt`).
* `New.mostFrobenii E`: a filter on triples `(w, A, s)` of a place `w` of prime norm, a place `A` of
  `Ω` over `w` and a geometric Frobenius element `s` at `A` (`New.FrobeniusDatum`). "Most" means:
  every non-empty open set of the Galois group has a non-empty open part `O` such that, for almost
  all `w`, the property holds for every triple with `s` in `O`.
* `New.mostFrobeniiAt E g`: the same filter, refined by the condition that `s` lies near `g`.

## Relation to the literature

Known; see `Lib.GaloisRep.Main.OddRank` for sources.
-/

/-! ## Attached representations and the existence statement -/

namespace New.GaloisRep

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E n : Type} [Field E] [NumberField E] [Algebra E Ω]
  [Fintype n] [DecidableEq n]

/-- The representation `ρ` of `H`, read in the Galois group through a map `j`, is attached to the
system `P` of complex polynomials indexed by the finite places of `E`: `ρ` is continuous with
non-degenerate trace form, `j` is open, and for every `η > 0` the coefficients of
`det (X - ρ x) - ιℓ (P w)` have norm at most `η` for most Frobenius data `(w, A, s)` and all `x`
with `j x = s`. When `j` is omitted, `H` is the Galois group itself and `j` is the identity. -/
structure Attached (P : FinPlace E → Polynomial ℂ) {H : Type} [Group H] [TopologicalSpace H]
    (ρ : H →* GL n (PadicAlgCl ℓ)) (j : H → Gal(Ω/E) := by exact id) : Prop where
  /-- The representation is continuous. -/
  continuous : Continuous ρ
  /-- The trace form of the representation is non-degenerate. -/
  isTraceNondeg : IsTraceNondeg ρ
  /-- The map to the Galois group is open. -/
  isOpenMap : IsOpenMap j
  /-- Let `η > 0`. For most Frobenius data, with place `w` and Frobenius element `s`, and all `x`
  with `j x = s`, all coefficients of `det (X - ρ x) - ιℓ (P w)` have norm at most `η`. -/
  eventually_norm_coeff_le ⦃η : ℝ⦄ (hη : 0 < η) :
    ∀ᶠ y : FrobeniusDatum E in mostFrobenii E, ∀ x : H, j x = y.frob →
      ∀ i : ℕ, ‖((ρ x).val.charpoly - (P y.place).map ιℓ.toRingHom).coeff i‖ ≤ η

variable {E : Type} [Field E] [CMType E] [Algebra E Ω] in
/-- The local conditions on the Galois representation `r` at a place `A` of `Ω` over `w`, for a
function `f` of weight `κ` on the unitary group, with values in the space `WeylIndex n κ.1 → ℂ` of
the weight-`κ` representation, and the rank `N`: `r` is unramified or crystalline at `A`; it has the
Hodge–Tate jumps of `κ` in rank `N`; and if `w` is split and `f` has Hecke polynomial `Q` at `w`,
then `ιℓ Q` kills the action through `r` of every geometric Frobenius element `s` at `A`
(`PolyKillsAt`). -/
def IsCompatibleAt {κ : Weight E} (f : Gf E n → WeylIndex n κ.1 → ℂ) (N : ℕ)
    (w : FinPlace E) (r : GalRep ℓ E n) (A : ValuationSubring Ω) : Prop :=
  IsGoodAt r A ∧ HasJumpsAt r A (jumps κ N) ∧
  ∀ (hw : star w ≠ w) (Q : Polynomial ℂ), HasHeckePolyAt f w hw Q →
    ∀ s : Gal(Ω/E), IsFrob A w.q s⁻¹ → PolyKillsAt r A s (Q.map ιℓ.toRingHom)

variable (E n : Type) [Field E] [CMType E] [Algebra E Ω] [Fintype n] [DecidableEq n] in
/-- Every eigenform `f` of any weight `κ` on the standard definite unitary group
(`f ∈ (stdSpace E n).forms κ`: the right stabiliser of `f` is open, and `f (γ g)` is the weight-`κ`
action of a global `γ` on `f g`), with system of Hecke polynomials `P`, has an attached Galois
representation; and if `f` is spherical at `w`, every representation attached to `P` satisfies the
local conditions `IsCompatibleAt` in rank `N` at every place of `Ω` over `w`. -/
def SphericalCompat (N : ℕ) (w : FinPlace E) : Prop :=
  ∀ ⦃P : FinPlace E → Polynomial ℂ⦄ ⦃κ : Weight E⦄ ⦃f : Gf E n → WeylIndex n κ.1 → ℂ⦄,
    f ∈ (stdSpace E n).forms κ → IsEigenform f P →
      (∃ r : GalRep ℓ E n, Attached P r) ∧
      ∀ ⦃r : GalRep ℓ E n⦄, Attached P r →
        f ∈ sphericalAt (rightRegular ℂ (Gf E n) (WeylIndex n κ.1 → ℂ)) w →
        ∀ A : ValuationSubring Ω, IsPlaceOver A w → IsCompatibleAt f N w r A

section
variable {E : Type} [Field E] [CMType E] [Algebra E Ω]

/-- Let `E` be a CM field, `f` a function of weight `κ` on the finite adelic unitary group, `r` an
`ℓ`-adic representation of `Gal(Ω/E)` and `A` a place of `Ω`. If `r` satisfies the local conditions
`IsCompatibleAt` for `f` at `A`, then `r` is good at `A` (`IsGoodAt`): it is trivial on the inertia
group of `A` if `ℓ` is a unit at `A`, and its restriction to the decomposition group of `A` is
crystalline along every embedding of `Ω` in the algebraic closure of `ℚ_ℓ` that induces `A`
(`PadicPlaceEmbedding`). The rank `N` and the finite place `w` of `E` play no role here. -/
lemma IsCompatibleAt.isGoodAt {κ : Weight E} {f : Gf E n → WeylIndex n κ.1 → ℂ} {N : ℕ}
    {w : FinPlace E} {r : GalRep ℓ E n} {A : ValuationSubring Ω}
    (h_compat : IsCompatibleAt f N w r A) : IsGoodAt r A :=
  h_compat.1

/-- Let `E` be a CM field with a chosen CM type, and let `r` be an `ℓ`-adic representation of
`Gal(Ω/E)` satisfying `IsCompatibleAt f N w r A`, the local conditions at the place `A` of `Ω` for a
function `f` of weight `κ` on the unitary group `Gf E n`, in rank `N`. Then `r` has Hodge–Tate jumps
`jumps κ N` at `A`: for each local datum at `A` with embedding `e` and each `g ∈ Gal(ℚ̄_ℓ/ℚ_ℓ)`, the
jumps of `r` at `g`, with multiplicity, are given by the embedding `σ = ιℓ⁻¹ ∘ g⁻¹ ∘ e` of `E` in
`ℂ`. They are {j − 1 − λ_j} if `σ` is in the CM type and {λ_j + N − j} otherwise (1 ≤ j ≤ N), where
λ is the highest weight of `κ` at the place of `σ`. -/
lemma IsCompatibleAt.hasJumpsAt {κ : Weight E} {f : Gf E n → WeylIndex n κ.1 → ℂ} {N : ℕ}
    {w : FinPlace E} {r : GalRep ℓ E n} {A : ValuationSubring Ω}
    (h_compat : IsCompatibleAt f N w r A) : HasJumpsAt r A (jumps κ N) := by
  obtain ⟨-, h_jumps, -⟩ := h_compat
  exact h_jumps

/-- Suppose `r` satisfies `IsCompatibleAt f N w r A`, the local conditions at the place `A` of `Ω`
for the function `f` of weight `κ` on the unitary group in rank `N`. Suppose also that `w` is split
(`star w ≠ w`), that `f` has Hecke polynomial `Q` at `w`, and that `s⁻¹` is an arithmetic Frobenius
at `A` for the norm `w.q` of `w`, so that `s` is a geometric Frobenius. Then `ιℓ Q`, the image of
`Q` under the fixed isomorphism `ιℓ : ℂ ≃ ℚ̄_ℓ`, kills `s` at `A` for `r` (`PolyKillsAt`):
`(ιℓ Q)(r s) = 0` if `ℓ` is a unit at `A`, and otherwise the corresponding condition on Weil pairs
holds. -/
lemma IsCompatibleAt.polyKillsAt {κ : Weight E} {f : Gf E n → WeylIndex n κ.1 → ℂ} {N : ℕ}
    {w : FinPlace E} {r : GalRep ℓ E n} {A : ValuationSubring Ω}
    (h_compat : IsCompatibleAt f N w r A) {hw : star w ≠ w} {Q : Polynomial ℂ}
    (hQ : HasHeckePolyAt f w hw Q) {s : Gal(Ω/E)} (hs : IsFrob A w.q s⁻¹) :
    PolyKillsAt r A s (Q.map ιℓ.toRingHom) := by
  obtain ⟨-, -, h_kills⟩ := h_compat
  exact h_kills hw Q hQ s hs

/-- Assume `SphericalCompat E n N w`: every eigenform of any weight on the standard definite unitary
group has an attached Galois representation, and local conditions hold in rank `N` at places over
`w` where the form is spherical. Then an eigenform `f` of weight `κ` with Hecke polynomials `P` has
an attached `ℓ`-adic Galois representation. -/
lemma SphericalCompat.exists_attached {P : FinPlace E → Polynomial ℂ} {κ : Weight E}
    {f : Gf E n → WeylIndex n κ.1 → ℂ} {N : ℕ} {w : FinPlace E}
    (h : SphericalCompat (ℓ := ℓ) E n N w) (hf : f ∈ (stdSpace E n).forms κ)
    (h_eig : IsEigenform f P) : ∃ r : GalRep ℓ E n, Attached P r :=
  (h hf h_eig).1

/-- Assume `SphericalCompat E n N w`, and let `f` be an algebraic modular form of weight `κ` on
`stdSpace E n` that is an eigenform with Hecke polynomials `P` and is spherical at `w` for the right
regular action. Then every `r : GalRep ℓ E n` attached to `P` satisfies `IsCompatibleAt f N w r A`
at every place `A` of `Ω` over `w`. These local conditions say that `r` is unramified or crystalline
at `A`, has the Hodge–Tate jumps of `κ` in rank `N`, and, if `w` is split, `ιℓ Q` kills every
geometric Frobenius at `A` for the Hecke polynomial `Q` of `f` at `w`. -/
lemma SphericalCompat.isCompatibleAt {P : FinPlace E → Polynomial ℂ} {κ : Weight E}
    {f : Gf E n → WeylIndex n κ.1 → ℂ} {N : ℕ} {w : FinPlace E} {r : GalRep ℓ E n}
    {A : ValuationSubring Ω} (h : SphericalCompat (ℓ := ℓ) E n N w)
    (hf : f ∈ (stdSpace E n).forms κ) (h_eig : IsEigenform f P) (hr : Attached P r)
    (h_sph : f ∈ sphericalAt (rightRegular ℂ (Gf E n) (WeylIndex n κ.1 → ℂ)) w)
    (hA : IsPlaceOver A w) : IsCompatibleAt f N w r A :=
  (h hf h_eig).2 hr h_sph A hA

end

/-- If the polynomial `P` kills the square matrix `M`, then every root of the characteristic
polynomial of `M` is a root of `P`. -/
lemma isRoot_of_isRoot_charpoly {m K : Type*} [Fintype m] [DecidableEq m] [Field K]
    {M : Matrix m m K} {P : Polynomial K} {x : K} (hP : Polynomial.aeval M P = 0)
    (hx : M.charpoly.IsRoot x) : P.IsRoot x := by
  -- The characteristic polynomial of `aeval M P = 0` is a power of `X`, so that of `M` divides a
  -- power of `P`.
  have h_dvd : M.charpoly ∣ P ^ Fintype.card m := by
    simpa [hP] using charpoly_dvd_charpoly_aeval_comp (Y := M) P
  exact eq_zero_of_pow_eq_zero (by simpa using hx.dvd h_dvd : P.eval x ^ Fintype.card m = 0)

end New.GaloisRep

/-! ## Characteristic polynomials and traces of attached representations -/

namespace New

open Matrix Polynomial Filter Topology Metric IsUltrametricDist Units
variable {ℓ : ℕ} [ThePrime ℓ] {E n H : Type} [Field E] [EmbeddedNumberField E] [Fintype n]
  [DecidableEq n] [Group H] [TopologicalSpace H] {P : FinPlace E → ℂ[X]} {j : H → Gal(Ω/E)}
  {ρ : H →* GL n (PadicAlgCl ℓ)}

/-- A continuous character of a compact group with values in the algebraic closure of `ℚ_ℓ` has
values of absolute value `1`. -/
lemma norm_eq_one_of_continuous {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    {ψ : G →* (PadicAlgCl ℓ)ˣ} (hψ : Continuous ψ) (g : G) : ‖(ψ g).val‖ = 1 := by
  -- the norm has a maximum at some `a`; compare it with the values at `a * g` and `a / g`
  obtain ⟨a, ha⟩ : ∃ a : G, ∀ b : G, ‖(ψ b).val‖ ≤ ‖(ψ a).val‖ :=
    (continuous_val.comp hψ).norm.exists_forall_ge (by simp)
  apply le_antisymm
  · simpa [field] using ha (a * g)
  · simpa [field] using ha (a / g)

/-- For polynomials `D`, `R` over the algebraic closure of `ℚ_ℓ` with `R` monic, if all coefficients
of `D * R` have absolute value at most `η`, then so do all coefficients of `D`. -/
lemma norm_coeff_le_of_mul_monic {D R : (PadicAlgCl ℓ)[X]} {η : ℝ} (hR : R.Monic)
    (h_le : ∀ i : ℕ, ‖(D * R).coeff i‖ ≤ η) (i : ℕ) : ‖D.coeff i‖ ≤ η :=
  -- Gauss's lemma: the sup norm of the coefficients is multiplicative; `R` has a coefficient `1`
  calc ‖D.coeff i‖ = ‖D.coeff i‖ * ‖R.coeff R.natDegree‖ := by simp [hR]
    _ ≤ D.supNorm * R.supNorm :=
      mul_le_mul (D.le_supNorm i) (R.le_supNorm _) (norm_nonneg _) D.supNorm_nonneg
    _ = (D * R).supNorm := (D.gaussNorm_mul (v := NormedField.toAbsoluteValue (PadicAlgCl ℓ))
      isNonarchimedean_norm one_pos R).symm
    _ ≤ η := (supNorm_eq_iSup _).trans_le (ciSup_le h_le)

/-- The coefficients of the characteristic polynomial depend continuously on the matrix. -/
lemma continuous_coeff_charpoly (i : ℕ) :
    Continuous fun M : Matrix n n (PadicAlgCl ℓ) ↦ M.charpoly.coeff i := by
  -- it is a polynomial in the entries: a coefficient of the universal characteristic polynomial
  have h_eval : Continuous fun M : Matrix n n (PadicAlgCl ℓ) ↦
      MvPolynomial.eval M.uncurry ((charpoly.univ (PadicAlgCl ℓ) n).coeff i) :=
    (MvPolynomial.continuous_eval _).comp (by fun_prop)
  exact h_eval.congr fun M ↦ charpoly.univ_coeff_eval₂Hom n (RingHom.id _) M.uncurry i

/-- Here `E` is a number field embedded in `Ω` (`EmbeddedNumberField`). Let `ρ` be attached through
an open map `j` to the system of polynomials `P` (`GaloisRep.Attached`). As the Frobenius element at
`w` tends to `j x` (along most Frobenius data `(w, A, s)`, `New.mostFrobeniiAt`), the `i`-th
coefficient of `P w`, transported by `ιℓ`, tends to that of the characteristic polynomial of
`ρ x`. -/
lemma GaloisRep.Attached.tendsto_charpoly_coeff [PadicIso ℓ] (hρ : Attached P ρ j) (x : H) (i : ℕ) :
    Tendsto (fun y : FrobeniusDatum E ↦ ιℓ ((P y.place).coeff i)) (mostFrobeniiAt E (j x))
      (𝓝 ((ρ x).val.charpoly.coeff i)) := by
  -- Near `j x` a Frobenius element is `j z` with the coefficient at `z` within `η` of that at `x`,
  -- and `P` is within `η` of the polynomial at `z`; the distance is ultrametric.
  let c (z : H) : PadicAlgCl ℓ := (ρ z).val.charpoly.coeff i
  have hc : Continuous c := (continuous_coeff_charpoly i).comp (continuous_val.comp hρ.continuous)
  refine nhds_basis_closedBall.tendsto_right_iff.2 fun η hη ↦ ?_
  have h_nhds : j '' {z : H | c z ∈ closedBall (c x) η} ∈ 𝓝 (j x) :=
    hρ.isOpenMap.image_mem_nhds (hc.continuousAt (closedBall_mem_nhds _ hη))
  filter_upwards [mem_inf_of_left (hρ.eventually_norm_coeff_le hη),
    mem_inf_of_right (map_comap_le h_nhds)] with y h_close ⟨z, hz, hzy⟩
  have h_dist : ‖c z - ιℓ ((P y.place).coeff i)‖ ≤ η := by simpa [c] using h_close z hzy i
  -- every point of an ultrametric ball is a centre of it
  rwa [closedBall_eq_of_mem hz, mem_closedBall_iff_norm']

/-- If `ρ` on `H` and `σ` on `G`, of the same rank, are attached to the same system `P` through maps
`j`, `j'` to `Gal(Ω/E)`, then `ρ x` and `σ y` have the same trace whenever `j x = j' y`. -/
lemma GaloisRep.Attached.trace_eq [PadicIso ℓ] {G : Type} [Group G] [TopologicalSpace G]
    {j' : G → Gal(Ω/E)} {σ : G →* GL n (PadicAlgCl ℓ)} (hρ : Attached P ρ j) (hσ : Attached P σ j')
    (x : H) {y : G} (hxy : j x = j' y) : (ρ x).val.trace = (σ y).val.trace := by
  -- both characteristic polynomials are the limit of `ιℓ (P w)` as the Frobenius tends to `j x`
  have h_char : (ρ x).val.charpoly = (σ y).val.charpoly :=
    Polynomial.ext fun i ↦ tendsto_nhds_unique (hρ.tendsto_charpoly_coeff x i)
      (by simpa only [hxy] using hσ.tendsto_charpoly_coeff y i)
  simp [h_char, trace_eq_sum_roots_charpoly]

end New

/-!
## Rank one: the avatar of an algebraic Hecke character

The Galois representation attached to an eigenform on the definite unitary group of rank one is
computed from a character extending the scalars by which elements act on the form. This is used
to prove local-global compatibility for algebraic Hecke characters
(`New.GaloisRep.avatarCompatAt_of_hasPrimitiveRoot5040`).

`New.AlgHeckeChar E` consists of pairs of a character of the finite ideles with open kernel and an
infinity type that gives its values on principal ideles;
`New.AlgHeckeChar.avatar` is its `ℓ`-adic avatar. `New.ofSplitPlace hw g` is the element of the
finite adelic unitary group with component `g` at the split place `w`, and `New.rightRegular` is
right translation. `New.scalarFin (Fin 1) (New.divStar x)` is the element `x / star x` of `U(1)`.
-/

open Finset Matrix Fintype Filter Representation New
open NumberField (InfinitePlace)

/-- The scalars by which elements of a commutative group act on a non-zero vector `f` extend to a
character of the whole group. -/
lemma New.exists_character_of_eigenvalues {A V : Type*} [CommGroup A] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ A V) {f : V} (hf : f ≠ 0) :
    ∃ χ : A →* ℂˣ, ∀ (x : A) (c : ℂ), ρ x f = c • f → χ x = c := by
  -- On the subgroup `H` of pairs `(x, c)` with `ρ x f = c • f`, `c` is determined by `x`; since
  -- `ℂˣ` is divisible, the second projection extends to a character of `A`.
  let H : Subgroup (A × ℂˣ) :=
    { carrier := {p | ρ p.1 f = p.2 • f}
      mul_mem' := fun {p q} (hp : ρ p.1 f = p.2 • f) (hq : ρ q.1 f = q.2 • f) ↦ by
        simp [hp, hq, smul_smul, mul_comm]
      one_mem' := by simp
      inv_mem' := fun {p} (hp : ρ p.1 f = p.2 • f) ↦ by
        simp [inv_apply_eq_iff, hp, smul_smul] }
  have h_ker (a : H) (ha : a.val.1 = 1) : a.val.2 = 1 := by
    have h_act : ρ a.val.1 f = (a.val.2 : ℂ) • f := a.prop
    exact Units.ext ((smul_left_inj hf).mp (by simp [← h_act, ha]))
  obtain ⟨χ, -, hχ⟩ : ∃ χ : A →* ℂˣ, ⊥ ≤ χ.ker ∧ ∀ a : H, χ a.val.1 = a.val.2 :=
    exists_monoidHom_extend (.domRestrict (.fst A ℂˣ) H) (.domRestrict (.snd A ℂˣ) H) ⊥ h_ker
  refine ⟨χ, fun x c hc ↦ ?_⟩
  have hc_ne : c ≠ 0 := fun h ↦ hf (by simpa [h, hc] using (ρ.inv_self_apply x f).symm)
  exact congrArg Units.val (hχ ⟨(x, .mk0 c hc_ne), hc⟩)

variable {E : Type} [Field E] [CMType E]

/-- The map `x ↦ x / star x` (`divStar`) from the finite ideles of `E` to the norm-one adeles, read
as scalar matrices in `U(1)` (`scalarFin`), is continuous. -/
lemma New.continuous_scalarFin_divStar :
    Continuous fun x : (𝔸f E)ˣ ↦ scalarFin (Fin 1) (divStar x) :=
  (U.isClosedEmbedding_coe isUnit_one).continuous_iff.2 <|
    .matrix_diagonal (continuous_pi fun _ ↦ continuous_subtype_val.comp divStar.continuous)

/-- At a split place `w`, the element `x / star x` of `U(1)` for the idele with component `x` at `w`
and `1` elsewhere is the scalar matrix `x` embedded at `w`. -/
lemma New.scalarFin_divStar_locIdele {w : FinPlace E} (hw : w.IsSplit) (x : (LocField w)ˣ) :
    scalarFin (Fin 1) (divStar (locIdele w x)) = ofSplitPlace hw (.scalar (Fin 1) x) := by
  refine Subtype.ext (Units.ext ?_)
  change Matrix.diagonal (fun _ ↦ (locIdele w x).val * star (locIdele w x)⁻¹.val) = _
  simp [ofSplitPlace, ← map_inv, singleGL, locIdele, ← diagonal_one, star_eq_conjTranspose]

/-- Let `f` be a form on `U(1)` whose weight is the power `κ` of the determinant. For `x` in `Eˣ`,
right translation by `x / star x` multiplies `f` by `∏ v, (star (Φ v x) / Φ v x) ^ κ v`, where
`Φ v` is the embedding of the CM type at the infinite place `v`. -/
lemma New.apply_mul_scalarFin_divStar_principalIdele {κ : InfinitePlace E → ℤ}
    {f : Gf E (Fin 1) → WeylIndex (Fin 1) (0 : InfinitePlace E → ℕ → ℕ) → ℂ}
    (hf : f ∈ (stdSpace E (Fin 1)).forms (0, κ)) (x : Eˣ) :
    (fun g : Gf E (Fin 1) ↦ f (g * scalarFin (Fin 1) (divStar (principalIdele x)))) =
      (∏ v : InfinitePlace E, (star (Φ v x.val) / Φ v x.val) ^ κ v) • f := by
  let γ : U (stdSpace E (Fin 1)).J :=
    U.of (by simp) ((x.val / star x.val) • 1) (by simp [smul_smul, field])
  funext g
  have h_comm : g * scalarFin (Fin 1) (divStar (principalIdele x)) = stdEmbFin γ * g := by
    refine Subtype.ext (Units.ext ?_)
    ext
    simp [γ, scalarFin, coe_divStar, Matrix.map_smul', mul_comm, div_eq_mul_inv]
  have h_law : f (stdEmbFin γ * g) = (stdSpace E (Fin 1)).weightRep 0 κ γ (f g) := hf.2 γ g
  rw [h_comm, h_law]
  -- compute the scalar by which `γ` acts on the representation of weight `κ`
  simp [γ, stdSpace_weightRep_apply, weylRep, Units.smul_def, schur_smul,
    starRingEnd_apply (R := E), Matrix.map_smul', smul_mulVec]

/-- If a function `f` on `U(1)` is spherical with Hecke polynomial `Q` at the split place `w`
(`HasHeckePolyAt`), then right translation by a uniformiser `ϖ` of `E_w`, embedded at `w`
(`ofSplitPlace`), multiplies `f` by the scalar `-Q(0)`. -/
lemma New.HasHeckePolyAt.rightRegular_ofSplitPlace_scalar {M : Type} {f : Gf E (Fin 1) → M → ℂ}
    {w : FinPlace E} {hw : w.IsSplit} {Q : Polynomial ℂ} (hQ : HasHeckePolyAt f w hw Q)
    {ϖ : (LocField w)ˣ} (hϖ : Valued.v ϖ.val = WithZero.exp (-1)) :
    rightRegular ℂ (Gf E (Fin 1)) (M → ℂ) (ofSplitPlace hw (.scalar (Fin 1) ϖ)) f = -Q.coeff 0 •
      f := by
  obtain ⟨h_sph, t, rfl, ht⟩ := hQ -- `t j` is the scalar of the `j`-th Hecke operator on `f`
  set π := rightRegular ℂ (Gf E (Fin 1)) (M → ℂ)
  -- `T_{w̄,0}` fixes `f`, which is spherical at `w̄` too
  have h_bar : f ∈ sphericalAt π (star w) := by rwa [sphericalAt, maxCompactAt, Gf.supportedOn_star]
  -- in rank one the scalar matrix `ϖ` carries `T_{w̄,0}`, the identity on `f`, to `T_{w,1}`
  calc π (ofSplitPlace hw (.scalar (Fin 1) ϖ)) f
      = π (ofSplitPlace hw (.scalar (Fin 1) ϖ)) (heckeSplit π hw.star 0 f) :=
        congrArg _ (heckeGL_zero ((mem_sphericalAt_iff hw.star).1 h_bar)).symm
    _ = heckeSplit π hw 1 f := heckeSplit_dual hw 0 1 h_sph hϖ (by simp)
    _ = -(heckePoly w.q (card (Fin 1)) t).coeff 0 • f := by simp [ht, coeff_heckePoly]

open scoped Classical in
/-- The algebraic Hecke character `θ` (character `θ.val.1` of the finite ideles, infinity type
`θ.val.2`) matches a function `f` on `U(1)` whose weight is the power `κ` of the determinant: its
infinity type is `± κ`, and at a split place `w` its value at `locIdele w x`, the idele with
component `x` at `w` and `1` elsewhere, is the scalar by which `x` acts on `f`, when there is
one. -/
structure New.IsRankOneCharacter (κ : InfinitePlace E → ℤ)
    (f : Gf E (Fin 1) → WeylIndex (Fin 1) (0 : InfinitePlace E → ℕ → ℕ) → ℂ)
    (θ : AlgHeckeChar E) : Prop where
  /-- The exponent at `σ` is `± κ v` for the place `v` of `σ`, with `+` when `σ` is the embedding
  `Φ v` of the CM type. -/
  type_eq (σ : E →+* ℂ) : θ.val.2.toAdd σ = (if σ = Φ (.mk σ) then 1 else -1) * κ (.mk σ)
  /-- If right translation by `x`, embedded at the split place `w`, multiplies `f` by `c`, then
  `θ_w(x) = c`. -/
  apply_locIdele {w : FinPlace E} (hw : w.IsSplit) (x : (LocField w)ˣ) {c : ℂ}
    (hc : (fun g : Gf E (Fin 1) ↦ f (g * ofSplitPlace hw (.scalar (Fin 1) x))) = c • f) :
    θ.val.1 (locIdele w x) = c
  /-- If `f` has the Hecke polynomial `Q` at the split place `w`, then `θ_w(x) = -Q(0)` for every
  uniformiser `x`. -/
  apply_uniformizer {w : FinPlace E} (hw : w.IsSplit) (x : (LocField w)ˣ)
    (hx : Valued.v x.val = WithZero.exp (-1)) {Q : Polynomial ℂ} (hQ : HasHeckePolyAt f w hw Q) :
    θ.val.1 (locIdele w x) = -Q.coeff 0

/-- Let `r` be attached to the Hecke polynomials `P` of an eigenform `f` on `U(1)` whose weight is
the power `κ` of the determinant (`Attached`: their characteristic polynomials approximate `ιℓ P`
at most Frobenius elements). Then `det r` is the `ℓ`-adic avatar (the associated Galois character)
of an algebraic Hecke character `θ` whose infinity type and values at split places are read off from
`κ` and `f` (`New.IsRankOneCharacter`). -/
lemma New.GaloisRep.Attached.exists_det_eq_avatar {E : Type} [Field E] [CMType E]
    {κ : InfinitePlace E → ℤ} {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] [Algebra E Ω]
    {f : Gf E (Fin 1) → WeylIndex (Fin 1) (0 : InfinitePlace E → ℕ → ℕ) → ℂ}
    {P : FinPlace E → Polynomial ℂ} {r : GalRep ℓ E (Fin 1)} (hr : Attached P r)
    (hf : f ∈ (stdSpace E (Fin 1)).forms (0, κ)) (hf_eig : IsEigenform f P) :
    ∃ θ : AlgHeckeChar E, IsRankOneCharacter κ f θ ∧
      ∀ g : Gal(Ω/E), (r g).val.det = θ.avatar g := by
  classical
  -- Let `χ` extend the scalars by which the elements `z x = x / star x` of `U(1)` act on `f`; it is
  -- the character of `θ`. On most Frobenius elements the avatar of `θ` is `-ιℓ ((P w)(0))`, which
  -- approximates the determinant.
  -- `h_hecke`: at almost all `w` of prime norm, `w` is split with Hecke polynomial `P w`
  obtain ⟨hf_ne, h_hecke⟩ := hf_eig
  let π := rightRegular ℂ (Gf E (Fin 1)) (WeylIndex (Fin 1) (0 : InfinitePlace E → ℕ → ℕ) → ℂ)
  let z : (𝔸f E)ˣ →* Gf E (Fin 1) := (scalarFin (E := E) (Fin 1)).comp divStar.toMonoidHom
  obtain ⟨χ, hχ⟩ : ∃ χ : (𝔸f E)ˣ →* ℂˣ, ∀ (x : (𝔸f E)ˣ) (c : ℂ), π (z x) f = c • f → χ x = c :=
    exists_character_of_eigenvalues (π.comp z) hf_ne
  -- The kernel of `χ` contains the open group of `x` for which `z x` fixes `f`.
  have h_ker : (rightStabilizer f).comap z ≤ χ.ker := fun x hx ↦
    Units.ext (hχ x 1 ((funext hx).trans (one_smul ℂ f).symm))
  have h_open : IsOpen (χ.ker : Set (𝔸f E)ˣ) :=
    Subgroup.isOpen_mono h_ker (hf.1.preimage continuous_scalarFin_divStar)
  let m (σ : E →+* ℂ) : ℤ := (if σ = Φ (.mk σ) then 1 else -1) * κ (.mk σ)
  have h_type (x : Eˣ) : χ (principalIdele x) = ∏ σ : E →+* ℂ, σ x.val ^ (-m σ) := by
    rw [hχ _ _ (apply_mul_scalarFin_divStar_principalIdele hf x),
      Variety.prod_embeddings_eq_prod_pairs]
    exact prod_congr rfl fun v _ ↦ by simp [m, div_eq_inv_mul, mul_zpow]
  let θ : AlgHeckeChar E := ⟨(χ, .ofAdd m), h_open, h_type⟩
  have h_loc {w : FinPlace E} (hw : w.IsSplit) (x : (LocField w)ˣ) {c : ℂ}
      (hc : π (ofSplitPlace hw (.scalar (Fin 1) x)) f = c • f) : χ (locIdele w x) = c :=
    hχ _ c (by rwa [← scalarFin_divStar_locIdele hw] at hc)
  have hθ : IsRankOneCharacter κ f θ :=
    ⟨fun _ ↦ rfl, h_loc, fun hw x hx _ hQ ↦ h_loc hw x (hQ.rightRegular_ofSplitPlace_scalar hx)⟩
  refine ⟨θ, hθ, fun g ↦ ?_⟩
  -- Along Frobenius elements tending to `g`, `-ιℓ ((P w)(0))` tends to both sides.
  have h_frob : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      (θ.avatar y.frob).val = -ιℓ ((P y.place).coeff 0) := by
    filter_upwards [eventually_mostFrobenii h_hecke fun y h ↦ h y.prime_q,
      θ.eventually_avatar_frob] with y ⟨hw, hQ⟩ h_av
    have h_coeff : heckeCoeff χ ∅ y.place = -(P y.place).coeff 0 := by
      simpa [heckeCoeff] using hθ.apply_uniformizer hw _ (v_uniformizer y.place) hQ
    rw [h_av, h_coeff, map_neg]
  have h_det : (r g).val.det = -(r g).val.charpoly.coeff 0 := by
    simpa using det_eq_sign_charpoly_coeff (r g).val
  have h_lim : Tendsto (fun y : FrobeniusDatum E ↦ -ιℓ ((P y.place).coeff 0)) (mostFrobeniiAt E g)
      (nhds (θ.avatar g).val) :=
    (tendsto_mostFrobeniiAt fun s ↦ (θ.avatar s).val).congr' (h_frob.filter_mono inf_le_left)
  rw [h_det]
  exact tendsto_nhds_unique (hr.tendsto_charpoly_coeff g 0).neg h_lim
