import Lib.General.NumberTheory.CoefficientRings
import Lib.PadicHodge.TateSen

/-!
# Semilinear forms of given weight: independence, finiteness, and jumps read off a basis

`New.Period.hodgeTateMaps ρ γ u` is the `PadicAlgCl p`-space of `γ`-semilinear maps `f : T → ℂ_[p]`
with `f (ρ g x) = χ(g) ^ (-u) • toGp g • f x` for `g` near `1`. Here `toGp` is the map to `Gp p`
given by the instance `[OverGp Γ p]`, and the instance `[ThePrime p]` fixes `p` as a prime. For
`toGp` of open image and `T` finite over `R`:
* `New.Period.hodgeTateMaps.mem_span_same_weight`: a map of weight `u` in the `ℂ_[p]`-span of maps
  `f i` of weights `k i` lies in the `PadicAlgCl p`-span of those with `k i = u`;
* `New.Period.finite_hodgeTateMaps`: each space has finite dimension;
* `New.Period.hasJumps_of_basis`: the weights of a `ℂ_[p]`-basis of such maps are the jumps
  (`New.Period.HasJumps`).

The input is that an element of `ℂ_[p]` fixed near `1` is algebraic, and is zero if it is fixed
after twisting by a nonzero power of `χ`.

Notions from other files:
* `New.Period.nearOne`: The filter 'near 1' on Γ: the pull-back along `toGp : Γ → G_p` of the filter
  of neighbourhoods of the identity.
* `New.cyclotomicGp`: The p-adic cyclotomic character χ of G_p = Gal(Q̄_p over Q_p) (`New.Gp`); for
  `g : Γ`, `χ g` means χ applied to `toGp g`.
* `New.Period.jump`, `New.Period.HasJumps`: the multiplicity of the jump u is the dimension over
  `PadicAlgCl p` of `hodgeTateMaps ρ γ u`; a multiset J of integers gives the jumps if each u occurs
  in J with that multiplicity.

## Relation to the literature

Known; see `Lib.PadicHodge.Crystalline.Regularity` for sources.
-/

namespace New.Period

open Filter Module Submodule LinearMap Fintype Finset Set RingHomClass FaithfulSMul

variable {p : ℕ} [ThePrime p] {Γ R T : Type*}
  {ι : Type*} [Group Γ] [CommRing R] [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R] [OverGp Γ p]
  {ρ : Representation R Γ T} {γ : R →ₐ[ℤ_[p]] ℂ_[p]}

/-- For an R-basis b of T indexed by ι, the C_p-linear isomorphism from γ-semilinear maps f: T →
C_p to C_p^ι sending f to its values f(b_i). -/
noncomputable def evalOnBasis (b : Basis ι R T) : (T →ₛₗ[toRingHom γ] ℂ_[p]) ≃ₗ[ℂ_[p]] ι → ℂ_[p] :=
  LinearEquiv.ofBijective (LinearMap.pi fun i ↦ LinearMap.id.flip (b i)) <| by
    refine ⟨fun f g hfg ↦ b.ext (congrFun hfg), fun c ↦ ?_⟩
    -- With `ℂ_[p]` an `R`-algebra through `γ`, semilinear maps are the `R`-linear ones.
    let := γ.toAlgebra
    exact ⟨⟨(b.constr ℕ c).toAddHom, (b.constr ℕ c).map_smul'⟩, funext (b.constr_basis ℕ c)⟩

/-- The algebraic closure `PadicAlgCl p` of `ℚ_p` is algebraic over `ℤ_[p]`. -/
instance : Algebra.IsAlgebraic ℤ_[p] (PadicAlgCl p) :=
  IsFractionRing.comap_isAlgebraic_iff.mpr (PadicAlgCl.isAlgebraic _)

variable (γ) in
/-- If R is algebraic over Z_p, every Z_p-algebra homomorphism γ: R → C_p factors through a
Z_p-algebra homomorphism δ: R → Q̄_p. -/
lemma exists_algHom_lift [Algebra.IsAlgebraic ℤ_[p] R] :
    ∃ δ : R →ₐ[ℤ_[p]] PadicAlgCl p, ∀ r : R, γ r = δ r := by
  -- The values of `γ` are algebraic over `ℤ_[p]`, so they lie in the algebraically closed subfield
  -- `PadicAlgCl p` of `ℂ_[p]`; restrict the codomain of `γ` to it.
  let incl : PadicAlgCl p →ₐ[ℤ_[p]] ℂ_[p] := IsScalarTower.toAlgHom ℤ_[p] (PadicAlgCl p) ℂ_[p]
  have h_range (r : R) : γ r ∈ incl.range := by
    have h_alg : IsAlgebraic (PadicAlgCl p) (γ r) := ((Algebra.IsAlgebraic.isAlgebraic r).algHom
      γ).extendScalars (algebraMap_injective ℤ_[p] (PadicAlgCl p))
    exact Variety.IsAbsIntegrallyClosed.mem_range_of_isIntegralElem h_alg.isIntegral
  let e : PadicAlgCl p ≃ₐ[ℤ_[p]] incl.range := AlgEquiv.ofInjectiveField incl
  exact ⟨e.symm.toAlgHom.comp (γ.codRestrict _ h_range),
    fun r ↦ (congrArg Subtype.val (e.apply_symm_apply ⟨γ r, h_range r⟩)).symm⟩

/-- Let R be algebraic over Z_p and let the s_i, for i in an index type ι, span T over R. If a
γ-semilinear f: T → C_p satisfies f(g s_i) = χ(g)^(−u)·g f(s_i) for g near 1, for each i, then f
lies in `New.Period.hodgeTateMaps` for u. -/
lemma mem_hodgeTateMaps_of_span [Algebra.IsAlgebraic ℤ_[p] R] {ι : Sort*} {s : ι → T}
    (hs : span R (Set.range s) = ⊤) {f : T →ₛₗ[toRingHom γ] ℂ_[p]} {u : ℤ}
    (h_gen : ∀ i : ι,
      ∀ᶠ g : Γ in nearOne Γ, f (ρ g (s i)) = (χ g ^ (-u)).val • toGp g • f (s i)) :
    f ∈ hodgeTateMaps ρ γ u := by
  show ∀ x : T, ∀ᶠ g : Γ in nearOne Γ, f (ρ g x) = (χ g ^ (-u)).val • toGp g • f x
  intro x
  obtain ⟨δ, hδ⟩ := exists_algHom_lift γ
  induction eq_top_iff'.mp hs x using span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact h_gen i
  | zero => simp
  | add y z _ _ hy hz => filter_upwards [hy, hz] with g hgy hgz using by simp [hgy, hgz]
  | smul r y _ hy =>
    -- the scalar `γ r = δ r` is algebraic, so it is fixed by `toGp g` for `g` near 1
    filter_upwards [hy, eventually_nearOne_apply_eq Γ (δ r)] with g hgy h_fix
    simp [hgy, hδ, smul_coe_Cp, h_fix]

variable [F : Module.Finite R T]

/-- If `T` is finite over `R`, the `γ`-semilinear maps `T → ℂ_[p]` form a finite-dimensional
`ℂ_[p]`-space. -/
instance : Module.Finite ℂ_[p] (T →ₛₗ[toRingHom γ] ℂ_[p]) := by
  -- a semilinear map is determined by its values on finitely many generators of `T`
  obtain ⟨n, x, hx⟩ := F.exists_fin
  exact .of_injective (pi fun i ↦ id.flip (x i)) fun f g hfg ↦ ext_on_range hx (congrFun hfg)

/-- Let `toGp` have open image (as the instance `OverGp Γ p` gives) and T be finite over R. Here
`hodgeTateMaps ρ γ k` is the Q̄_p-space of γ-semilinear maps f : T → ℂ_p with f(ρ g x) = χ(g)^(−k) •
toGp(g) • f(x) for g near 1, where χ is the cyclotomic character. If f_i lies in
`New.Period.hodgeTateMaps` for k_i, and φ in `New.Period.hodgeTateMaps` for u lies in the ℂ_p-span
of the f_i, then φ lies in the ℚ̄_p-span of the f_i with k_i = u. -/
lemma hodgeTateMaps.mem_span_same_weight {k : ι → ℤ} {f : ι → T →ₛₗ[toRingHom γ] ℂ_[p]}
    (hf : ∀ i : ι, f i ∈ hodgeTateMaps ρ γ (k i)) {u : ℤ} {φ : T →ₛₗ[toRingHom γ] ℂ_[p]}
    (hφ : φ ∈ hodgeTateMaps ρ γ u) (hφ_span : φ ∈ span ℂ_[p] (Set.range f)) :
    φ ∈ span (PadicAlgCl p) (f '' {i : ι | k i = u}) := by
  -- Write `φ = ∑ c i • f (a i)` with the `f (a i)` linearly independent. Comparing the actions on
  -- both sides gives `χ(g) ^ (k (a i) - u) • g • c i = c i` near `1`; so `c i` is algebraic if
  -- `k (a i) = u` (Ax–Sen–Tate), and zero otherwise (Tate's vanishing theorem).
  obtain ⟨n, x, hx⟩ : ∃ (n : ℕ) (x : Fin n → T), span R (Set.range x) = ⊤ := F.exists_fin
  obtain ⟨κ, a, -, h_span, h_indep⟩ := exists_linearIndependent' ℂ_[p] f
  have := h_indep.finite
  let := Fintype.ofFinite κ
  obtain ⟨c, rfl⟩ : ∃ c : κ → ℂ_[p], ∑ i, c i • (f ∘ a) i = φ :=
    (mem_span_range_iff_exists_fun ℂ_[p]).mp (h_span.ge hφ_span)
  have h_coeff : ∀ i : κ,
      ∀ᶠ g : Gp p in nhds 1, (cyclotomicGp g ^ (-u + k (a i))).val • g • c i = c i := by
    -- It suffices to prove this at `toGp g` for `g` near 1 in `Γ`.
    suffices h_near : ∀ᶠ g : Γ in nearOne Γ,
        ∀ i : κ, (χ g ^ (-u + k (a i))).val • toGp g • c i = c i from
      eventually_all.mp (nhds_one_le_map_nearOne Γ (mem_map.mpr h_near))
    filter_upwards [eventually_all.mpr fun l ↦ hφ (x l),
      eventually_all.mpr fun l ↦ eventually_all.mpr fun i ↦ hf (a i) (x l)] with g hgφ hgf
    -- The two combinations agree after composing with the surjection `ρ g`: test on generators.
    have h_eq : ∑ i, ((χ g ^ (-u + k (a i))).val • toGp g • c i) • (f ∘ a) i =
        ∑ i, c i • (f ∘ a) i := by
      refine (cancel_right (ρ.apply_bijective g).surjective).mp (ext_on_range hx fun l ↦ ?_)
      simpa [hgf, smul_sum, smul_smul, zpow_add] using (hgφ l).symm
    exact Fintype.linearIndependent_iffₛ.mp h_indep
      (fun i ↦ (χ g ^ (-u + k (a i))).val • toGp g • c i) c h_eq
  refine sum_mem fun i _ ↦ ?_
  by_cases hu : u = k (a i)
  · -- weight `u`: `c i` is fixed near `1`, hence algebraic (Ax–Sen–Tate)
    have h_fixed : ∀ᶠ g : Gp p in nhds 1, g • c i = c i := by simpa [hu] using h_coeff i
    obtain ⟨y, hy⟩ := exists_algebraic_of_fixed_near_one h_fixed
    rw [hy, PadicComplex.coe_eq, _root_.algebraMap_smul]
    exact smul_mem _ _ (subset_span ⟨a i, hu.symm, rfl⟩)
  · -- another weight: `c i` is fixed after a nonzero twist, hence zero (Tate)
    have h_twist : ∀ᶠ g : Gp p in nhds 1,
        (cyclotomicGp g ^ (-u + k (a i))).val • g • c i = (cyclotomicGp g ^ (0 : ℤ)).val • c i := by
      simpa using h_coeff i
    have hc_zero : c i = 0 := tate_eq_zero_of_cyclotomicGp_twist (neg_add_eq_zero.not.mpr hu)
      h_twist
    simp [hc_zero]

/-- If `toGp` has open image (as the instance `OverGp Γ p` gives) and T is finite over R, the
ℚ̄_p-space `New.Period.hodgeTateMaps` for γ and u is finite-dimensional, for every integer u. -/
instance finite_hodgeTateMaps (u : ℤ) : Module.Finite (PadicAlgCl p) (hodgeTateMaps ρ γ u) := by
  -- Finitely many `f i` in the space have the same span over `ℂ_[p]` as the space itself; by
  -- `hodgeTateMaps.mem_span_same_weight` they span it over `PadicAlgCl p`.
  obtain ⟨f, hf, h_span, -⟩ := exists_fun_fin_finrank_span_eq ℂ_[p]
    (hodgeTateMaps ρ γ u : Set (T →ₛₗ[toRingHom γ] ℂ_[p]))
  have h_le : hodgeTateMaps ρ γ u ≤ span (PadicAlgCl p) (f '' {i | u = u}) := fun φ hφ ↦
    hodgeTateMaps.mem_span_same_weight hf hφ (h_span.ge (subset_span hφ))
  exact .of_fg ((fg_span (toFinite _)).of_le h_le)

/-- Let `toGp` have open image (as the instance `OverGp Γ p` gives) and T be finite over R. If
a ℂ_p-basis b of the γ-semilinear maps has each `b i` in `New.Period.hodgeTateMaps` for `u i`, then
the `u i` are the jumps (`New.Period.HasJumps`). -/
lemma hasJumps_of_basis [Fintype ι] {u : ι → ℤ} {b : Basis ι ℂ_[p] (T →ₛₗ[toRingHom γ] ℂ_[p])}
    (hb_mem : ∀ i : ι, b i ∈ hodgeTateMaps ρ γ (u i)) :
    HasJumps ρ γ (univ.val.map u) := by
  intro v
  -- The space of weight `v` is spanned over `PadicAlgCl p` by the basis vectors with `u i = v`.
  have h_span : hodgeTateMaps ρ γ v = span (PadicAlgCl p) (b '' {i : ι | u i = v}) := by
    refine le_antisymm (fun φ hφ ↦ hodgeTateMaps.mem_span_same_weight hb_mem hφ (b.mem_span φ))
      (span_le.mpr ?_)
    rintro _ ⟨i, rfl, rfl⟩
    exact hb_mem i
  -- These vectors are independent, so the dimension is their number.
  have h_indep : LinearIndependent (PadicAlgCl p) fun i : {i : ι | u i = v} ↦ b i :=
    (b.linearIndependent.restrict_scalars' _).comp _ Subtype.val_injective
  rw [jump, h_span, image_eq_range, finrank_span_eq_card h_indep, Multiset.count_map]
  simp [eq_comm, Fintype.card_subtype, card_def]

end New.Period
