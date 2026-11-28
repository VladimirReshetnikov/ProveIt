import Lib.ClassField.GreenbergWiles.SelmerLevels

/-!
# Trivialised cocycles and power residue relations at split primes

Let `G` act on a discrete module `V`. A trivialised cocycle is a pair `(f, z)` of a continuous map
`z : G → V` vanishing on `I` and a map `f : X → V` with `g • f x = f (g • x) + z g`; when `X` is
nonempty, `z` is then a cocycle. At split primes off `N`, the values of such cocycles on tame
generators `γ i` of inertia satisfy linear relations.

## Main definitions and results

* `New.DiscreteModule.trivialisedCocycles`: pairs `(f, z)` of a continuous `z : G → V` vanishing on
  `I` and `f : X → V` with `g • f x = f (g • x) + z g`; so `z` is the coboundary of `f x` on the
  stabiliser of `x`.
* `New.DiscreteModule.trivialisedCocycles.exists_mem_of_orbit_reps`,
  `New.DiscreteModule.trivialisedCocycles.corestrict_mem`: such pairs are built from data at one
  point per orbit, and by corestriction.
* `New.DiscreteModule.trivialisedCocycles.hasFewCocycles_of_isShortExact`: the bound `(#V) ^ k` for
  the number of such pairs (`New.DiscreteModule.HasFewCocycles`) passes from the ends of a short
  exact sequence to the middle term.
* `New.IsLargeLevel.SplitPlaces.exists_powerResidueSymbols` (as one conjunction,
  `power_residue_reciprocity`): the `m`-th power residue symbols of the `N`-units of the field of
  `U` give linear relations among these values when `V` is trivial on `U`. If the field of `U` is
  totally complex, solutions of the relations give such cocycles.

Notions from other files:
* `New.DiscreteModule R G`: an `R`-module `V` with the discrete topology and a continuous `R`-linear
  action `ρ` of `G`; `New.DiscreteModule.restrictTo` restricts the action to a subgroup.
* `New.Z1`: the `R`-module of continuous 1-cocycles of `ρ`, that is, of continuous maps
  `f : G → M` with `f (g * h) = f g + ρ g (f h)`.
* `New.IsLargeLevel.SplitPlaces`: Split places for `U`. The subgroup `U` fixes the `m`-th roots of
  unity, and `m` divides `N`.
* `New.IsLargeLevel.fixedSUnits`: The N-units of the fixed field of U; `fixedSUnitsRep` is the
  action of G / U on them.
* `New.IsTameGeneratorFor`: γ lies in the inertia group of A, and γy/y is the root of unity
  `New.rootPowHom Ω m 1` for some m-th root y of some uniformiser π of K for A.

## Relation to the literature

Known; see `Lib.ClassField.GreenbergWiles.CocycleCounts` for sources.
-/

/-! ## Cocycles trivialised at places and corestriction -/

section TrivialisedCocycles

open Function QuotientGroup MulAction Quotient Set Nat AddSubgroup

namespace New.DiscreteModule

variable {R G : Type} [CommRing R] [Group G] [TopologicalSpace G] (X : Type) [MulAction G X]
  (I : Set G) (V : DiscreteModule R G) {A B C : DiscreteModule R G} {ι : A.Hom B} {π : B.Hom C}

/-- Trivialised cocycles: pairs of f : X → V and continuous z : G → V vanishing on I, with
g f(x) = f(gx) + z(g) for all g, x. -/
def trivialisedCocycles : AddSubgroup ((X → V) × (G → V)) :=
  AddSubgroup.ofSub
    {p : (X → V.V) × (G → V.V) | Continuous p.2 ∧
      (∀ (g : G) (x : X), V.ρ g (p.1 x) = p.1 (g • x) + p.2 g) ∧ ∀ g ∈ I, p.2 g = 0}
    ⟨0, continuous_zero, by simp, by simp⟩ <| by
    rintro p ⟨hp, hp_triv, hp_zero⟩ q ⟨hq, hq_triv, hq_zero⟩
    refine ⟨hp.add hq.neg, fun g x ↦ ?_, fun g hg ↦ by simp [hp_zero g hg, hq_zero g hg]⟩
    simp [hp_triv, hq_triv]
    abel

variable {X I V} in
/-- Membership in `New.DiscreteModule.trivialisedCocycles`, written out. -/
lemma mem_trivialisedCocycles {f : X → V} {z : G → V} :
    (f, z) ∈ V.trivialisedCocycles X I ↔
      Continuous z ∧ (∀ (g : G) (x : X), V.ρ g (f x) = f (g • x) + z g) ∧ ∀ g ∈ I, z g = 0 :=
  Iff.rfl

/-- There are finitely many trivialised cocycles, at least one and at most `#V ^ k`. -/
abbrev HasFewCocycles (k : ℕ) : Prop :=
  Nat.card (V.trivialisedCocycles X I) ∈ Ioc 0 (Nat.card V ^ k)

namespace trivialisedCocycles

/-- For an equivariant map u : A → B, the additive map between the groups
`New.DiscreteModule.trivialisedCocycles` of A and B that composes both components of a pair of
functions with u. -/
def map (u : A.Hom B) : A.trivialisedCocycles X I →+ B.trivialisedCocycles X I :=
  AddMonoidHom.mk'
    (fun p ↦ ⟨p.1.map (Function.comp u) (Function.comp u), by
      obtain ⟨⟨f, z⟩, h_cont, h_triv, h_zero⟩ := p
      refine ⟨by fun_prop, fun g x ↦ ?_, fun g hg ↦ ?_⟩
      · simpa [u.isIntertwining] using congrArg u (h_triv g x)
      · simpa using congrArg u (h_zero g hg)⟩)
    (by simp)

/-- For a discrete `G`-module `V` over `R`, a `G`-set `X` and `I ⊆ G`, the trivialised cocycles
`V.trivialisedCocycles X I` are pairs of a map `f : X → V` and a continuous `z : G → V` vanishing on
`I`, with `g • f x = f (g • x) + z g` for all `g`, `x`. For a short exact sequence
`0 → A → B → C → 0` of discrete `G`-modules with maps `ι`, `π`, the number of trivialised cocycles
of `B` equals the number for `A` times the size of the image of the map `map X I π` that `π` induces
into those of `C`. -/
lemma card_eq_of_isShortExact (h_ses : A.IsShortExact ι π) :
    Nat.card (B.trivialisedCocycles X I) =
      Nat.card (A.trivialisedCocycles X I) * Nat.card (map X I π).range := by
  obtain ⟨hι_inj, hι_exact, -⟩ := h_ses
  -- The maps induced on trivialised cocycles are again injective and exact in the middle.
  have h_inj : Injective (map X I ι) := by simp [Injective, map, hι_inj.comp_left.eq_iff]
  have h_exact : Exact (map X I ι) (map X I π) := by
    rintro ⟨⟨f, z⟩, h_cont, h_triv, h_zero⟩
    constructor
    · -- Choose preimages pointwise; the injective map `ι` reflects the three conditions.
      intro h_ker
      obtain ⟨hf_zero, hz_zero⟩ : π ∘ f = 0 ∧ π ∘ z = 0 :=
        Prod.ext_iff.mp (Subtype.ext_iff.mp h_ker)
      choose f' hf' using fun y : X ↦ (hι_exact (f y)).mp (congrFun hf_zero y)
      choose z' hz' using fun g : G ↦ (hι_exact (z g)).mp (congrFun hz_zero g)
      obtain rfl : ι ∘ f' = f := funext hf'
      obtain rfl : ι ∘ z' = z := funext hz'
      refine ⟨⟨(f', z'), ?_, fun g y ↦ hι_inj ?_, fun g hg ↦ hι_inj ?_⟩, rfl⟩
      · simpa [comp_def, leftInverse_invFun hι_inj _] using
          (continuous_of_discreteTopology (f := invFun ι)).comp h_cont
      · simpa [ι.isIntertwining] using h_triv g y
      · simpa using h_zero g hg
    · rintro ⟨p, hp⟩
      rw [← hp]
      ext y <;> exact hι_exact.apply_apply_eq_zero _
  rw [← card_top, card_eq_mul_of_exact _ _ h_inj h_exact]
  simp

variable {X I V} {k : ℕ}

/-- If `X` is nonempty, the second component `z` of a trivialised cocycle `(f, z)` is a continuous
1-cocycle. -/
lemma snd_mem_Z1 [Nonempty X] {p : (X → V) × (G → V)} (hp : p ∈ V.trivialisedCocycles X I) :
    p.2 ∈ Z1 V.ρ := by
  obtain ⟨f, z⟩ := p
  obtain ⟨h_cont, h_triv, -⟩ :
      Continuous z ∧ (∀ (g : G) (x : X), V.ρ g (f x) = f (g • x) + z g) ∧ ∀ g ∈ I, z g = 0 :=
    mem_trivialisedCocycles.mp hp
  show Continuous z ∧ ∀ g k : G, z (g * k) = z g + V.ρ g (z k)
  refine ⟨h_cont, fun g k ↦ ?_⟩
  -- Compute the action of `g * k` on the trivialisation at any point `y` in two ways.
  obtain ⟨y⟩ : Nonempty X := inferInstance
  have h_two_ways : f ((g * k) • y) + z (g * k) = f ((g * k) • y) + (z g + V.ρ g (z k)) := by
    rw [← h_triv, map_mul, Module.End.mul_apply, h_triv, map_add, h_triv, mul_smul, add_assoc]
  exact add_left_cancel h_two_ways

/-- Let the points `x i` represent the orbits of `G` on `X`, and let `z` be a cocycle that vanishes
on `I`. If `m i` trivialises `z` on the stabiliser of `x i` for each `i`, then `z` has a
trivialisation `f` on all of `X` with `f (x i) = m i`. -/
lemma exists_mem_of_orbit_reps {κ : Sort*} {x : κ → X}
    (hx : Bijective (Quotient.mk (orbitRel G X) ∘ x)) {z : G → V} (hz : z ∈ Z1 V.ρ)
    (hI : ∀ g ∈ I, z g = 0) (m : κ → V)
    (h_stab : ∀ (i : κ) (g : G), g • x i = x i → z g = V.ρ g (m i) - m i) :
    ∃ f : X → V, (f, z) ∈ V.trivialisedCocycles X I ∧ ∀ i : κ, f (x i) = m i := by
  -- Write each point as `y = s y • x (i y)` and transport: `f y = s y • m (i y) - z (s y)`.
  obtain ⟨hz_cont, hz_cocycle⟩ : Continuous z ∧ ∀ g h : G, z (g * h) = z g + V.ρ g (z h) := hz
  have index_unique (i j : κ) (g : G) (hg : g • x j = x i) : i = j := hx.injective (sound ⟨g, hg⟩)
  have exists_rep (y : X) : ∃ i : κ, ∃ g : G, g • x i = y :=
    (hx.surjective ⟦y⟧).imp fun i hi ↦ Quotient.exact hi.symm
  -- The value `a • m j - z a` depends only on the point `a • x j`.
  have h_well (j : κ) (a b : G) (hab : a • x j = b • x j) :
      V.ρ a (m j) - z a = V.ρ b (m j) - z b := by
    have h_fixes : (b⁻¹ * a) • x j = x j := by rw [mul_smul, hab, inv_smul_smul]
    have h_cocycle : z a = z b + V.ρ b (z (b⁻¹ * a)) := by rw [← hz_cocycle, mul_inv_cancel_left]
    rw [h_cocycle, h_stab j _ h_fixes, map_sub, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel_left]
    abel
  obtain ⟨i, s, hs⟩ : ∃ (i : X → κ) (s : X → G), ∀ y : X, s y • x (i y) = y := by
    simpa only [Classical.skolem] using exists_rep
  refine ⟨fun y ↦ V.ρ (s y) (m (i y)) - z (s y),
    mem_trivialisedCocycles.mpr ⟨hz_cont, fun g y ↦ ?_, hI⟩, fun j ↦ ?_⟩
  · have h_point : (g * s y) • x (i y) = g • y := by rw [mul_smul, hs]
    have h_index : i (g • y) = i y := index_unique _ _ ((s (g • y))⁻¹ * (g * s y)) <| by
      rw [mul_smul, h_point, inv_smul_eq_iff, hs]
    have h_same_point : s (g • y) • x (i y) = (g * s y) • x (i y) := by rw [h_point, ← h_index, hs]
    have h_value : V.ρ (s (g • y)) (m (i y)) - z (s (g • y)) =
        V.ρ (g * s y) (m (i y)) - z (g * s y) := h_well (i y) _ _ h_same_point
    simp only [h_index, h_value, hz_cocycle, map_mul, map_sub, Module.End.mul_apply]
    abel
  · have h_index : j = i (x j) := index_unique _ _ (s (x j)) (hs _)
    have h_fix : s (x j) • x j = x j := by simpa only [← h_index] using hs (x j)
    simp only [← h_index, h_stab j _ h_fix, sub_sub_cancel]

omit [TopologicalSpace G] in
/-- With `x.out` the chosen representative of a coset `x ∈ G / H`, the element
`x.out⁻¹ * g * (g⁻¹ • x).out` lies in `H`. -/
lemma out_inv_mul_mul_out_mem (H : Subgroup G) (g : G) (x : G ⧸ H) :
    x.out⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h_coset : (QuotientGroup.mk (g⁻¹ * x.out) : G ⧸ H) = QuotientGroup.mk (g⁻¹ • x).out := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, Quotient.mk_smul_out]
  simpa only [mul_inv_rev, inv_inv] using QuotientGroup.eq.mp h_coset

/-- Corestriction. Let `P` be an open subgroup of finite index that contains `I`, let `I` be
stable under conjugation, and let `(f, c)` be a trivialised cocycle for `P` and `I`.
With `s x = x.out` the chosen representative of the coset `x ∈ G / P`, the pair of
`y ↦ ∑ x, s x • f ((s x)⁻¹ • y)` and `g ↦ ∑ x, s x • c ((s x)⁻¹ * g * s (g⁻¹ • x))`
is a trivialised cocycle for `G` and `I`. -/
lemma corestrict_mem [IsTopologicalGroup G] (P : OpenSubgroup G) [Fintype (G ⧸ P.toSubgroup)]
    (hI : ∀ g ∈ I, g ∈ P ∧ ∀ s : G, s⁻¹ * g * s ∈ I)
    {f : X → V} {c : P.toSubgroup → V}
    (h_mem : (f, c) ∈ (V.restrictTo P).trivialisedCocycles X (Subtype.val ⁻¹' I)) :
    (fun y : X ↦ ∑ x : G ⧸ P.toSubgroup, V.ρ x.out (f (x.out⁻¹ • y)),
      fun g : G ↦ ∑ x : G ⧸ P.toSubgroup, V.ρ x.out
        (c ⟨x.out⁻¹ * g * (g⁻¹ • x).out, out_inv_mul_mul_out_mem P.toSubgroup g x⟩)) ∈
      V.trivialisedCocycles X I := by
  obtain ⟨h_cont, h_triv, h_zero⟩ :
      Continuous c ∧
        (∀ (u : P.toSubgroup) (y : X), (V.restrictTo P).ρ u (f y) = f (u • y) + c u) ∧
        ∀ u ∈ Subtype.val ⁻¹' I, c u = 0 :=
    mem_trivialisedCocycles.mp h_mem
  have hI_le (g : G) (hg : g ∈ I) : g ∈ P := (hI g hg).left
  have hI_conj (g : G) (hg : g ∈ I) (s : G) : s⁻¹ * g * s ∈ I := (hI g hg).right s
  refine mem_trivialisedCocycles.mpr ⟨?_, fun g y ↦ ?_, fun g hg ↦ ?_⟩
  · fun_prop
  · -- Match the term of the coset `g⁻¹ • x` on the left with the term of `x` on the right.
    simp only [map_sum, ← Finset.sum_add_distrib]
    refine (Fintype.sum_equiv (toPerm g⁻¹) _ _ fun x ↦ ?_).symm
    -- The trivialisation of `c` for `u = (s x)⁻¹ * g * s (g⁻¹ • x)` in `P`, moved by `s x`.
    have h_term : V.ρ (x.out⁻¹ * g * (g⁻¹ • x).out) (f ((g⁻¹ • x).out⁻¹ • y)) =
        f (x.out⁻¹ • g • y) +
          c ⟨x.out⁻¹ * g * (g⁻¹ • x).out, out_inv_mul_mul_out_mem P.toSubgroup g x⟩ := by
      have h_point : (x.out⁻¹ * g * (g⁻¹ • x).out) • (g⁻¹ • x).out⁻¹ • y = x.out⁻¹ • g • y := by
        simp [mul_smul]
      rw [← h_point]
      exact h_triv ⟨x.out⁻¹ * g * (g⁻¹ • x).out, out_inv_mul_mul_out_mem P.toSubgroup g x⟩
        ((g⁻¹ • x).out⁻¹ • y)
    rw [← map_add, ← h_term, ← Module.End.mul_apply, ← map_mul, mul_assoc,
      mul_inv_cancel_left, map_mul, Module.End.mul_apply, toPerm_apply]
  · -- All conjugates of `g` lie in `I`, hence in `P`: `g` fixes every coset and each term is `0`.
    have h_fix (x : G ⧸ P.toSubgroup) : g⁻¹ • x = x := by
      induction x using QuotientGroup.induction_on with
      | H s => simpa [QuotientGroup.eq] using hI_le _ (hI_conj g hg s)
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    have h_mem_I : x.out⁻¹ * g * (g⁻¹ • x).out ∈ I := by
      simpa [h_fix] using hI_conj g hg x.out
    have h_value :
        c ⟨x.out⁻¹ * g * (g⁻¹ • x).out, out_inv_mul_mul_out_mem P.toSubgroup g x⟩ = 0 :=
      h_zero _ h_mem_I
    rw [h_value, map_zero]

/-- Let `0 → A → B → C → 0` be a short exact sequence such that `A` and `C` have few trivialised
cocycles. Then so has `B`. If the count for `B` reaches its bound `#B ^ k`, then every trivialised
cocycle of `C` lifts to `B` and the count for `A` reaches its bound `#A ^ k`. -/
lemma hasFewCocycles_of_isShortExact (h_ses : A.IsShortExact ι π) (hA : A.HasFewCocycles X I k)
    (hC : C.HasFewCocycles X I k) :
    B.HasFewCocycles X I k ∧
      (Nat.card B ^ k ≤ Nat.card (B.trivialisedCocycles X I) →
        (map X I π).range = ⊤ ∧ Nat.card A ^ k ≤ Nat.card (A.trivialisedCocycles X I)) := by
  obtain ⟨hA_pos, hA_le⟩ := hA
  obtain ⟨hC_pos, hC_le⟩ := hC
  have hC_fin : Finite (C.trivialisedCocycles X I) := (Nat.card_pos_iff.mp hC_pos).right
  -- With `r` the size of the image in the trivialised cocycles of `C`, the count for `B` is the
  -- count for `A` times `r`, and `r` is at most the count for `C`; also `#B ^ k = #A ^ k * #C ^ k`.
  have image_le : Nat.card (map X I π).range ≤ Nat.card (C.trivialisedCocycles X I) :=
    (map X I π).range.card_le_card_addGroup
  rw [HasFewCocycles, card_eq_of_isShortExact X I h_ses, h_ses.card_eq_card_mul_card, mul_pow]
  refine ⟨⟨mul_pos hA_pos Nat.card_pos, mul_le_mul' hA_le (image_le.trans hC_le)⟩,
    fun h_attained ↦ ?_⟩
  -- If `#A ^ k * #C ^ k` is attained, neither factor can fall short of its bound.
  have h_image : Nat.card (C.trivialisedCocycles X I) ≤ Nat.card (map X I π).range := by
    nlinarith [hA_pos, hA_le, hC_le]
  exact ⟨eq_top_of_le_card _ h_image, by nlinarith [hC_pos, hC_le]⟩

end trivialisedCocycles

end New.DiscreteModule

end TrivialisedCocycles

/-!
## Power residue relations among values on inertia at split primes

Fix primes `s.v i` off `N` with places `s.valuationSubring i` of `Ω`, Frobenii `s.φ i` in the open
normal subgroup `U` of `G = Gal(Ω/K)`, and tame generators `γ i` of inertia at
`s.valuationSubring i`. We describe the values `z (γ i)` of cocycles `z` that are trivialised above
`N` and infinity and vanish on the inertia `I` at all other primes off `N`.

`New.DiscreteUnits Ω` is `Ωˣ` written additively (as the discrete module `unitsModule G`;
`(unitsModule G).H0` is its `G`-invariants, and `ofBase` maps the units of the fixed field onto
them), so `m • r = y` means `r ^ m = y`, `unitsRep g r - r` is `g r / r`, and `New.rootPowHom Ω m a`
is `ζ ^ a` for a fixed primitive `m`-th root of unity `ζ`, and `cyclotomicCharMod Ω m g` is the
`c : ZMod m` with `g ζ = ζ ^ c`.
-/

namespace New

variable {G K R : Type} [Group G] [TopologicalSpace G] [Field K] [EmbeddedNumberField K]
  [MulSemiringAction G Ω] [IsProGalois G K Ω] [CommRing R] {m N : ℕ} [NeZero m]
  {ι : Type} {U : OpenNormalSubgroup G} {A : ClosurePlace} {v : FinPlace K}
  {V : DiscreteModule R G} [Module (ZMod m) V]
  {I : Set G} (s : IsLargeLevel.SplitPlaces m N I U ι)

open NumberField DiscreteModule trivialisedCocycles Cohomology DiscreteUnits NeZero Subgroup
  QuotientGroup InfinitePlace QZChar QZ ZModModule

attribute [local instance low] Fintype.ofFinite

omit [IsProGalois G K Ω] in
/-- Let `G` act on `Ω` as the Galois group of `Ω` over a field `L`. An element `g` of `G` that fixes
an infinite place `u` of `Ω` is `1` or a complex conjugation. -/
lemma eq_one_or_isComplexConj {L : Type} [Field L] [Algebra L Ω] [hG : IsProGalois G L Ω]
    {g : G} {u : InfinitePlace Ω} (h_smul : MulSemiringAction.toAlgAut G ℚ Ω g • u = u) :
    g = 1 ∨ IsComplexConj g := by
  -- `g` fixes the embedding that defines `u`, or conjugates it
  have h_stab : MulSemiringAction.toAlgAut G ℚ Ω g ∈
      MulAction.stabilizer Gal(Ω/ℚ) (InfinitePlace.mk u.embedding) := by
    rwa [MulAction.mem_stabilizer_iff, u.mk_embedding]
  obtain h_fix | h_conj := (mem_stabilizer_mk_iff u.embedding _).mp h_stab
  · -- `g` acts trivially on `Ω`, and the action is faithful
    exact .inl (hG.faithful.eq_of_smul_eq_smul (by simpa [AlgEquiv.ext_iff] using h_fix))
  · exact .inr ⟨u.embedding, h_conj.eq⟩

/-- Let `A` lie over a prime `v` not dividing `m`, and let `γ` in the inertia group of `A` move an
`m`-th root of a uniformiser by the primitive root `ζ`. A locally constant map `f` to a group
killed by `m` that is additive on inertia takes there only multiples of `f γ`. -/
lemma IsTameGeneratorFor.exists_apply_eq_nsmul (h : IsPlaceOver A v) (hm : ↑m ∉ v.asIdeal) {γ τ : G}
    (hγ : IsTameGeneratorFor m A γ) (hτ : τ ∈ inertiaGroup G A) {V : Type*} [AddCommGroup V]
    [Module (ZMod m) V] (f : G → V) (hf : IsLocallyConstant f)
    (h_add : ∀ g ∈ inertiaGroup G A, ∀ k ∈ inertiaGroup G A, f (g * k) = f g + f k) :
    ∃ c : ℕ, f τ = c • f γ := by
  obtain ⟨hγ_ine, π, y, hπ, hy, hγy⟩ : γ ∈ inertiaGroup G A ∧ ∃ (π : Kˣ) (y : DiscreteUnits Ω),
      IsUniformiser A π.val ∧ m • y = ↑(DiscreteUnits.ofBase G Ω (Additive.ofMul π)) ∧
        unitsRep γ y - y = (rootPowHom Ω m).val 1 := hγ
  obtain ⟨h_local, -, h_unif⟩ := h.isLocalGalois_and_residueCard_eq_and_isUniformiser G
  let F : inertiaGroup (decompGroup G A) A →* Multiplicative V :=
    .mk' (fun g ↦ .ofAdd (f g)) fun g g' ↦ h_add _ g.prop _ g'.prop
  let γ' : inertiaGroup (decompGroup G A) A := ⟨⟨γ, hγ_ine.1⟩, hγ_ine⟩
  -- `γ` moves the root `y` of the uniformiser by a root of unity of order `m`.
  have h_prim : IsPrimitiveRoot (γ • (y.toMul : Ω) / y.toMul) m := by
    simpa [← hγy, ← IsPrimitiveRoot.coe_units_iff] using isPrimitiveRoot_rootPowHom_one Ω m
  -- So, by the tame theorem, every value of `F` is a power of its value at `γ`.
  obtain ⟨-, tame⟩ := h_local.tame_inertia (h_unif hπ) (h.valuation_natCast_eq_one_iff.2 hm)
    (congrArg Units.val hy) F (hf _).preimage_val.preimage_val fun g ↦ char_nsmul_eq_zero m (f g)
  have h_pow : ∀ g : inertiaGroup (decompGroup G A) A, ∃ c : ℕ, F g = F γ' ^ c :=
    (tame γ').left h_prim
  exact h_pow ⟨⟨τ, hτ.1⟩, hτ⟩

open Pointwise in
/-- Let `G` be the Galois group of the algebraic closure `Ω` over `K`, and let `V` be killed by `m`
and fixed by `U`. A cocycle that vanishes at a tame generator `γ` at `s.valuationSubring i`
vanishes on the inertia group of every place `A` of `Ω` over the prime `v = s.v i`. -/
lemma IsLargeLevel.SplitPlaces.apply_inertia_eq_zero (hA : IsPlaceOver A v) {i : ι} {γ τ : G}
    (hv : s.v i = v) (hγ : IsTameGeneratorFor m (s.valuationSubring i) γ) (z : Z1 V.ρ)
    (hU : V.TrivialOn U.toOpenSubgroup.toSubgroup) (hz : z.val γ = 0) (hτ : τ ∈ inertiaGroup G A) :
    z.val τ = 0 := by
  -- Move `τ` by conjugation into inertia at `s.valuationSubring i`, where `z` is additive, so that
  -- by tameness its value is a multiple of `z γ = 0`; then conjugate back.
  obtain ⟨hz_cont, hz_cocycle⟩ :
      Continuous z.val ∧ ∀ g k : G, z.val (g * k) = z.val g + V.ρ g (z.val k) := z.prop
  subst hv
  obtain ⟨g, hg⟩ : ∃ g : G, g • A = s.valuationSubring i := hA.exists_smul G (s.isPlaceOver i)
  have h_triv (σ : G) (hσ : σ ∈ inertiaGroup G (s.valuationSubring i)) (a : V.V) : V.ρ σ a = a :=
    hU σ (s.inertiaGroup_le (s.level_notMem i) (s.isPlaceOver i) hσ) a
  have h_conj : g * τ * g⁻¹ ∈ inertiaGroup G (s.valuationSubring i) := by
    rw [← hg]
    exact hτ.conj g
  have h_add (σ : G) (hσ : σ ∈ inertiaGroup G (s.valuationSubring i)) (σ' : G) :
      z.val (σ * σ') = z.val σ + z.val σ' := by rw [hz_cocycle, h_triv σ hσ]
  have hm : ↑m ∉ (s.v i).asIdeal := fun hm_mem ↦
    s.level_notMem i (Ideal.mem_of_dvd _ s.dvd_level.natCast hm_mem)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, z.val (g * τ * g⁻¹) = c • z.val γ :=
    hγ.exists_apply_eq_nsmul (s.isPlaceOver i) hm h_conj _
      (fun S ↦ hz_cont.isOpen_preimage S (isOpen_discrete S)) fun σ hσ σ' _ ↦ h_add σ hσ σ'
  have h_back : z.val (g⁻¹ * (g * τ * g⁻¹) * g⁻¹⁻¹) = V.ρ g⁻¹ (z.val (g * τ * g⁻¹)) :=
    cocycle_conj_eq_smul (a := V.ρ) hz_cocycle (h_triv _ h_conj _)
  simpa [← mul_assoc, hc, hz] using h_back

/-- The Kummer character `κ x` of an element `x` of valuation one vanishes on inertia at a place
that does not divide `m`. -/
lemma kummer_eq_zero_of_mem_inertiaGroup {κ : (unitsModule G).H0 →+ Z1 (Representation.trivial ℤ G
  (ZMod m))}
    (hκ : ∀ (x : ↥(unitsModule G).H0) (r : DiscreteUnits Ω), m • r = ↑x → ∀ g : G,
      (rootPowHom Ω m).val ((κ x).val g) = unitsRep g r - r)
    (h : IsPlaceOver A v) (hm : ↑m ∉ v.asIdeal) (x : ↥(unitsModule G).H0)
    (hx : A x.val.toMul.val = 1) {g : G} (hg : g ∈ inertiaGroup G A) :
    (κ x).val g = 0 := by
  obtain ⟨r, hr⟩ : ∃ r : DiscreteUnits Ω, m • r = x.val := exists_nsmul _ (NeZero.ne m)
  -- `r` is an `m`-th root of `x`, which `g` fixes, so `g` fixes `r`
  have h_fix : unitsRep g r = r :=
    ext (inertia_fixes_root_of_unit hg (h.valuation_natCast_eq_one_iff.mpr hm)
      (congrArg Units.val hr) hx (congrArg Units.val (x.prop g)))
  apply (rootPowHom Ω m).prop.left
  simp [hκ x r hr, h_fix]

open Pointwise in
/-- Let `γ` move an `m`-th root of a uniformiser at `A` by the fixed root of unity, and let `U`
contain the decomposition group of `g • A`. At `g γ g⁻¹` the Kummer character of an element `x` of
the fixed field of `U` is the order of `x` at the prime `u ∤ m` under `g • A`, times
`cyclotomicCharMod Ω m g`. -/
lemma IsTameGeneratorFor.kummer_apply_conj {γ : G} (hγ : IsTameGeneratorFor m A γ)
    {κ : (unitsModule U.toOpenSubgroup.toSubgroup).H0 →+
      Z1 (Representation.trivial ℤ U.toOpenSubgroup.toSubgroup (ZMod m))}
    (hκ : ∀ (x : ↥(unitsModule U.toOpenSubgroup.toSubgroup).H0) (r : DiscreteUnits Ω), m • r = ↑x →
      ∀ q : ↥U.toOpenSubgroup.toSubgroup, (rootPowHom Ω m).val ((κ x).val q) = unitsRep q r - r)
    (h : IsPlaceOver A v) (g : G) {u : FinPlace (fixedFieldOf U.toOpenSubgroup.toSubgroup)}
    (hu : IsPlaceOver (g • A) u) (hm : ↑m ∉ u.asIdeal)
    (h_dec : decompGroup G (g • A) ≤ U.toOpenSubgroup.toSubgroup)
    (h_mem : g * γ * g⁻¹ ∈ U.toOpenSubgroup.toSubgroup)
    (x : (fixedFieldOf U.toOpenSubgroup.toSubgroup)ˣ) :
    (κ (DiscreteUnits.ofBase U.toOpenSubgroup.toSubgroup Ω (Additive.ofMul x))).val
        ⟨g * γ * g⁻¹, h_mem⟩ =
      cyclotomicCharMod Ω m g *
        ↑(-(u.valuation (fixedFieldOf U.toOpenSubgroup.toSubgroup) x.val).log) := by
  obtain ⟨h_ine, π, y, hπ, hy, hγy⟩ := hγ
  let Q : Subgroup G := U.toOpenSubgroup.toSubgroup
  set c : ℤ := -(u.valuation (fixedFieldOf Q) x.val).log with hc
  -- The decomposition group lies in `U`, so `π` stays a uniformiser over the fixed field and `x`
  -- is `π ^ c` times a unit.
  have hA : IsPlaceOver (g • A) v := h.smul g
  have h_ord : ordRat (fixedFieldOf Q) (g • A) = ordRat K (g • A) :=
    ((hA.ramification_in_tower Q hu).left h_dec).right
  let z : (unitsModule Q).H0 := ⟨_, fun q ↦ (c • ofBase G Ω (.ofMul π)).prop q⟩
  have h_unit : ordRat K (g • A) (ofBase Q Ω (.ofMul x) - z).val = 0 := by
    have hx_ord : ordRat K (g • A) (ofBase Q Ω (.ofMul x)) = c := by
      rw [← h_ord, hu.ordRat_ofBase]
      simp [hc, Q]
    simp [z, hA.ordRat_ofBase, h.isUniformiser_iff.mp hπ, hx_ord]
  have h_zero : (κ (ofBase Q Ω (.ofMul x) - z)).val ⟨g * γ * g⁻¹, h_mem⟩ = 0 :=
    kummer_eq_zero_of_mem_inertiaGroup hκ hu hm _ (hA.ordRat_eq_zero_iff.mp h_unit) (h_ine.conj g)
  -- So `x` may be replaced by `z = π ^ c`, which has the `m`-th root `(g y) ^ c`.
  have hz_root : m • c • unitsRep g y = z := by
    simp [z, (ofBase G Ω _).prop _, smul_comm m, ← map_nsmul, hy]
  apply (rootPowHom Ω m).prop.left
  calc _ = (rootPowHom Ω m).val ((κ z).val ⟨_, h_mem⟩) :=
        congrArg _ (by simpa [sub_eq_zero] using h_zero)
    _ = unitsRep (g * γ * g⁻¹) (c • unitsRep g y) - c • unitsRep g y := hκ z _ hz_root _
    _ = unitsRep g ((rootPowHom Ω m).val c) := by simp [← zsmul_one, ← hγy, smul_sub, -zsmul_eq_mul]
    _ = _ := (map_cyclotomicCharMod_mul ..).symm

/-- If `K` contains the `m`-th roots of unity, every continuous character `χ : G → ℤ/m` is the
Kummer character of an element `x = r ^ m` of `K`. -/
lemma exists_kummer_root (h_cyc : ∀ g : G, cyclotomicCharMod Ω m g = 1) (χ : G → ZMod m)
    (hχ : Continuous χ) (h_add : ∀ g k : G, χ (g * k) = χ g + χ k) :
    ∃ (r : DiscreteUnits Ω) (x : Additive Kˣ),
      m • r = DiscreteUnits.ofBase G Ω x ∧
      ∀ g : G, (rootPowHom Ω m).val (χ g) = unitsRep g r - r := by
  -- By Hilbert 90, `ζ ^ χ g = g r / r` for some `r`; then `r ^ m` is fixed by `G`.
  obtain ⟨r, hr⟩ : ∃ r : DiscreteUnits Ω, ∀ g : G, (rootPowHom Ω m).val (χ g) = unitsRep g r - r :=
    hilbert90_unitsRep ⟨fun g ↦ (rootPowHom Ω m).val (χ g), by fun_prop,
      by simp [← map_cyclotomicCharMod_mul, h_add, h_cyc]⟩
  have hr_fix (g : G) : unitsRep g (m • r) = m • r := by
    simp [← add_eq_of_eq_sub (hr g), ← map_nsmul, ZMod.natCast_self]
  obtain ⟨x, hx⟩ := (ofBase_bijective G (K := K)).surjective ⟨m • r, hr_fix⟩
  exact ⟨r, x, (congrArg Subtype.val hx).symm, hr⟩

/-- A Kummer map for `U`: an additive map `κ` from the `U`-invariants of `Ωˣ` to the characters
`U → ℤ/m` with `ζ ^ κ x q = q r / r` whenever `r ^ m = x`. -/
private def IsKummerMap (κ : (unitsModule U.toOpenSubgroup.toSubgroup).H0 →+
      Z1 (Representation.trivial ℤ U.toOpenSubgroup.toSubgroup (ZMod m))) : Prop :=
  ∀ (x : ↥(unitsModule U.toOpenSubgroup.toSubgroup).H0) (r : DiscreteUnits Ω), m • r = ↑x →
    ∀ q : ↥U.toOpenSubgroup.toSubgroup, (rootPowHom Ω m).val ((κ x).val q) = unitsRep q r - r

/-- The split family `s` over the field of `U`: the index `(i, g)` names the place
`g⁻¹ • s.valuationSubring i`, the prime of the field of `U` below it, and the Frobenius
`g⁻¹ (s.φ i) g`, where `g` is the chosen representative of the coset. -/
private noncomputable abbrev liftToFixedField :
    IsLargeLevel.SplitPlaces m N ((↑) ⁻¹' I : Set U.toOpenSubgroup.toSubgroup) ⟨⊤, normal_top⟩
      (ι × G ⧸ U.toOpenSubgroup.toSubgroup) :=
  s.liftToSubgroup U.1 ⟨⊤, normal_top⟩ le_rfl le_top (fun g _ ↦ s.cyclotomicCharMod_eq_one _ g.2) _
    out_eq'

/-- For `θ = (i, g)`, the Kummer character of an element `x` of the field of `U` takes at
`g⁻¹ (γ i) g` the value `cyclotomicCharMod Ω m g⁻¹` times the order of `x` at the prime
`(liftToFixedField s).v θ`. -/
private lemma kummer_conj_liftToFixedField {γ : ι → G}
    (hγ : ∀ i : ι, IsTameGeneratorFor m (s.valuationSubring i) (γ i))
    {κ : (unitsModule U.toOpenSubgroup.toSubgroup).H0 →+
      Z1 (Representation.trivial ℤ U.toOpenSubgroup.toSubgroup (ZMod m))}
    (hκ : IsKummerMap κ) (θ : ι × G ⧸ U.toOpenSubgroup.toSubgroup)
    (h_mem : θ.snd.out⁻¹ * γ θ.fst * θ.snd.out⁻¹⁻¹ ∈ U.toOpenSubgroup.toSubgroup)
    (x : (fixedFieldOf U.toOpenSubgroup.toSubgroup)ˣ) :
    (κ (ofBase U.toOpenSubgroup.toSubgroup Ω (.ofMul x))).val ⟨_, h_mem⟩ =
      cyclotomicCharMod Ω m θ.snd.out⁻¹ *
        ↑(-(((liftToFixedField s).v θ).valuation (fixedFieldOf U.toOpenSubgroup.toSubgroup)
          x.val).log) := by
  -- `m` divides `N`, which lies in no prime of the family
  have hm : ↑m ∉ ((liftToFixedField s).v θ).asIdeal := fun hm_mem ↦
    (liftToFixedField s).level_notMem θ (Ideal.mem_of_dvd _ s.dvd_level.natCast hm_mem)
  exact (hγ θ.fst).kummer_apply_conj hκ (s.isPlaceOver _) _ ((liftToFixedField s).isPlaceOver θ) hm
    (s.decompGroup_le ((s.isPlaceOver _).smul _)) _ x

/-- For `θ = (i, g)`, the Kummer character of an `N`-unit `x` takes at the Frobenius
`(liftToFixedField s).φ θ` the value `cyclotomicCharMod Ω m g⁻¹` times the symbol `b` of `g x` at
`i`. -/
private lemma IsLargeLevel.SplitPlaces.kummer_frob_liftToFixedField
    {κ : (unitsModule U.toOpenSubgroup.toSubgroup).H0 →+
      Z1 (Representation.trivial ℤ U.toOpenSubgroup.toSubgroup (ZMod m))} (hκ : IsKummerMap κ)
    {b : IsLargeLevel.fixedSUnits N U →+ ι → ZMod m}
    (hb : ∀ (y : ↥(fixedSUnits N U)) (r : DiscreteUnits Ω), m • r = ↑y → ∀ i : ι,
      (rootPowHom Ω m).val (b y i) = unitsRep (s.φ i) r - r)
    (x : ↥(unitsModule U.toOpenSubgroup.toSubgroup).H0) (hx : x.val ∈ sUnits N)
    (θ : ι × G ⧸ U.toOpenSubgroup.toSubgroup) :
    (κ x).val ((liftToFixedField s).φ θ) =
      cyclotomicCharMod Ω m θ.snd.out⁻¹ * b (fixedSUnitsRep N U θ.snd.out ⟨x.val, hx, x.prop⟩)
        θ.fst := by
  obtain ⟨r, hr⟩ : ∃ r : DiscreteUnits Ω, m • r = x.val := exists_nsmul _ (NeZero.ne m)
  have h_smul : m • unitsRep θ.snd.out r = fixedSUnitsRep N U θ.snd.out ⟨x.val, hx, x.prop⟩ :=
    (map_nsmul ..).symm.trans (congrArg _ hr)
  rw [← (rootPowHom Ω m).prop.left.eq_iff, hκ x r hr, map_cyclotomicCharMod_mul, hb _ _ h_smul]
  ext
  simp [liftToFixedField, liftToSubgroup, mul_smul]

/-- A trivialised cocycle `(f, z)` for the places above `N` and infinity vanishes at each
element of `U` that fixes such a place, since `U` acts trivially on `V`. -/
private lemma snd_trivialisedCocycles_eq_zero_of_smul_eq
    (h_triv : V.TrivialOn U.toOpenSubgroup.toSubgroup)
    {P : (PlaceAboveLevel N → V) × (G → V)} (hP : P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I)
    (y : PlaceAboveLevel N) (q : U.toOpenSubgroup.toSubgroup) (h_fix : (q : G) • y = y) :
    P.snd q = 0 := by
  obtain ⟨-, hP_triv, -⟩ := mem_trivialisedCocycles.mp hP
  simpa [h_fix, h_triv _ q.prop] using hP_triv q y

/-- A trivialised cocycle `(f, z)` for the places above `N` and infinity vanishes at each complex
conjugation in `U`: it fixes the infinite place of `Ω` that it conjugates. -/
private lemma snd_trivialisedCocycles_eq_zero_of_isComplexConj
    (h_triv : V.TrivialOn U.toOpenSubgroup.toSubgroup)
    {P : (PlaceAboveLevel N → V) × (G → V)} (hP : P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I)
    (q : U.toOpenSubgroup.toSubgroup) (h_cc : IsComplexConj q) :
    P.snd q = 0 := by
  obtain ⟨φ, hφ⟩ := h_cc
  have h_stab : MulSemiringAction.toAlgAut G ℚ Ω q ∈
      MulAction.stabilizer Gal(Ω/ℚ) (InfinitePlace.mk φ) :=
    (mem_stabilizer_mk_iff φ _).mpr (.inr (RingHom.ext hφ).symm)
  exact snd_trivialisedCocycles_eq_zero_of_smul_eq h_triv hP (.inr (InfinitePlace.mk φ)) q
    (congrArg _ h_stab)

/-- A trivialised cocycle `(f, z)` for the places above `N` and infinity vanishes on the
decomposition groups in `U` of the primes above `N`. -/
private lemma snd_eq_zero_of_mem_decompGroup (h_triv : V.TrivialOn U.toOpenSubgroup.toSubgroup)
    {P : (PlaceAboveLevel N → V) × (G → V)} (hP : P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I)
    (u : FinPlace (fixedFieldOf (K := K) U.toOpenSubgroup.toSubgroup)) (hu : ↑N ∈ u.asIdeal)
    (q : U.toOpenSubgroup.toSubgroup)
    (hq : q ∈ decompGroup U.toOpenSubgroup.toSubgroup (placeOver u)) :
    P.snd q = 0 :=
  snd_trivialisedCocycles_eq_zero_of_smul_eq h_triv hP
    (.inl ⟨_, u.isPlaceOver_placeOver.valuation_natCast_lt_one_iff.mpr hu⟩) q
    (congrArg Sum.inl (Subtype.ext hq))

/-- Part (b) of `New.IsLargeLevel.SplitPlaces.power_residue_reciprocity`: a trivialised cocycle
`(f, z)` for the places above `N` and infinity, with `z` zero at all `γ i`, vanishes on `U`. -/
private lemma IsLargeLevel.SplitPlaces.snd_eq_zero_of_snd_generators_eq_zero {γ : ι → G}
    (hγ : ∀ i : ι, IsTameGeneratorFor m (s.valuationSubring i) (γ i))
    (h_triv : V.TrivialOn U.toOpenSubgroup.toSubgroup)
    {P : (PlaceAboveLevel N → V) × (G → V)} (hP : P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I)
    (h_zero : ∀ i : ι, P.snd (γ i) = 0) (g : G) (hg : g ∈ U) :
    P.snd g = 0 := by
  let Q : Subgroup G := U.toOpenSubgroup.toSubgroup
  let F : IntermediateField K Ω := fixedFieldOf Q
  have h_place (u : FinPlace F) : IsPlaceOver (placeOver u) u := u.isPlaceOver_placeOver
  have h_div : (principalIdele (K := F)).range ⊔ idelesUnitOff {u | ↑N ∈ u.asIdeal} = ⊤ :=
    s.principal_sup_idelesUnitOff F le_rfl
  obtain ⟨z_cts, z_mul⟩ : P.snd ∈ Z1 V.ρ := snd_mem_Z1 hP
  obtain ⟨-, -, hP_zero⟩ := mem_trivialisedCocycles.mp hP
  -- The character `z = P.snd` of `U` vanishes at the complex conjugations and on the decomposition
  -- groups above `N`, and is unramified off `N`, hence zero.
  refine eq_zero_of_unramified_off _ h_div
    ⟨fun q : Q ↦ P.snd q, by fun_prop, by simp [z_mul, h_triv _]⟩
    (snd_trivialisedCocycles_eq_zero_of_isComplexConj h_triv hP)
      (snd_eq_zero_of_mem_decompGroup h_triv hP)
    (fun u hu q hq ↦ ?_) ⟨g, hg⟩
  obtain ⟨i, hi⟩ | h_new := em (u.below K ∈ Set.range s.v)
  · exact s.apply_inertia_eq_zero (h_place u).isPlaceOver_below hi (hγ i) ⟨_, z_cts, z_mul⟩
      h_triv (h_zero i) hq
  · exact hP_zero _
      ((s.mem_inertia_iff _).2 ⟨_, by simpa, h_new, _, (h_place u).isPlaceOver_below, hq⟩)

/-- Artin's law for the character `χ = κ y / m` of an `N`-unit `y` of the field `F` of `U` and an
element `x` of `F` with an `m`-th root `r`. Let `r` be fixed by the complex conjugations in `U`, by
the decomposition groups above `N`, and by the elements of `U` in `I`. Then
`∑ θ, ord(x) • χ (S.φ θ) = 0`, where `S = liftToFixedField s` and the order is taken at `S.v θ`. -/
private lemma IsLargeLevel.SplitPlaces.sum_ord_smul_kummer_frob_eq_zero [Fintype ι]
    {κ : (unitsModule U.toOpenSubgroup.toSubgroup).H0 →+
      Z1 (Representation.trivial ℤ U.toOpenSubgroup.toSubgroup (ZMod m))} (hκ : IsKummerMap κ)
    (y : DiscreteUnits Ω) (y_unit : y ∈ sUnits N)
    (y_fix : y ∈ (unitsModule U.toOpenSubgroup.toSubgroup).H0) (r : DiscreteUnits Ω)
    (x : Additive (fixedFieldOf U.toOpenSubgroup.toSubgroup)ˣ)
    (hx : m • r = ofBase U.toOpenSubgroup.toSubgroup Ω x)
    (h_cc : ∀ q : U.toOpenSubgroup.toSubgroup, IsComplexConj q → unitsRep q r = r)
    (h_dec : ∀ u : FinPlace (fixedFieldOf U.toOpenSubgroup.toSubgroup), ↑N ∈ u.asIdeal →
      ∀ q ∈ decompGroup U.toOpenSubgroup.toSubgroup (placeOver u), unitsRep q r = r)
    (h_I : ∀ q : U.toOpenSubgroup.toSubgroup, ↑q ∈ I → unitsRep q r = r) :
    ∑ θ : ι × G ⧸ U.toOpenSubgroup.toSubgroup,
      -(((liftToFixedField s).v θ).valuation (fixedFieldOf U.toOpenSubgroup.toSubgroup)
        x.toMul.val).log •
        (ofZModCocycle m (κ ⟨y, y_fix⟩)).val ((liftToFixedField s).φ θ) = 0 := by
  let Q : Subgroup G := U.toOpenSubgroup.toSubgroup
  let F : IntermediateField K Ω := fixedFieldOf Q
  let S := liftToFixedField s
  have h_place (u : FinPlace F) : IsPlaceOver (placeOver u) u := u.isPlaceOver_placeOver
  -- The character `χ = κ y / m`, with values in `ℚ/ℤ`, is killed by `m` and unramified off `N`.
  let χ : QZChar Q := ofZModCocycle m (κ ⟨y, y_fix⟩)
  have χ_tors (q : Q) : m • χ.val q = 0 := by simp [χ, ← map_nsmul, ZMod.natCast_self]
  have χ_ine {B : ClosurePlace} {u : FinPlace F} (hB : IsPlaceOver B u) (hu : ↑N ∉ u.asIdeal)
      (q : Q) (hq : q ∈ inertiaGroup Q B) : χ.val q = 0 := by
    simp [χ, kummer_eq_zero_of_mem_inertiaGroup hκ hB
      (hu ∘ u.asIdeal.mem_of_dvd s.dvd_level.natCast)
      ⟨y, y_fix⟩ (y_unit _ (hB.valuation_natCast_eq_one_iff.mpr hu)) hq]
  -- Artin's law: the symbol `(χ, x)` dies on the stabiliser of `r`, which contains the complex
  -- conjugations.
  have h_artin : abelianLift χ (artinMap Q (principalIdele x.toMul)) = 1 :=
    artin_reciprocity ⟨_, IsProGalois.isOpen_stabilizer r.toMul.1⟩
      (fun q hq ↦ congrArg (fun z : DiscreteUnits Ω ↦ z.toMul.val) (h_cc q hq))
      (resH2_cyclicClass_eq_zero hx fun q ↦ ⟨ext q.2, χ_tors q⟩)
  refine sum_ord_smul_frob_eq_zero (n := m) (Subtype.ext (funext χ_tors)) h_artin S.v_injective
    S.isPlaceOver (fun θ ↦ (S.isFrob θ).left)
    (fun θ ↦ χ_ine (S.isPlaceOver θ) (S.level_notMem θ)) fun u hu ↦ ?_
  by_cases hN : ↑N ∈ u.asIdeal
  · -- above `N` the decomposition group fixes `r`
    exact .inl ((h_place u).abelianLift_artinAt_eq_one_iff.2
      (resH2_cyclicClass_eq_zero hx fun q ↦ ⟨h_dec u hN q q.prop, χ_tors q⟩))
  · -- at a prime off `N` that is no `S.v θ`, inertia lies in `I` and so fixes `r`
    have h_unit :
        placeOver u ((ofBase Q Ω (Additive.ofMul x.toMul)).val - m • r).toMul.val = 1 := by
      simp [hx]
    exact .inr ⟨⟨r, h_unit, fun q hq ↦
      h_I q ((S.mem_inertia_iff q).2 ⟨u, hN, hu, _, h_place u, hq⟩)⟩, χ_ine (h_place u) hN⟩

/-- Part (c) of `New.IsLargeLevel.SplitPlaces.power_residue_reciprocity`: for a trivialised
cocycle `(f, z)` for the places above `N` and infinity, each `N`-unit `y` gives the relation
`∑ b (g y) i • g⁻¹ z (γ i) = 0`, summed over `i` and `g ∈ G / U`. It is Artin's law for the
character `κ y` and the idele of an `x` in the field of `U` whose Kummer character is `l ∘ z`. -/
private lemma IsLargeLevel.SplitPlaces.sum_symbol_smul_snd_generators_eq_zero {γ : ι → G}
    (hγ : ∀ i : ι, IsTameGeneratorFor m (s.valuationSubring i) (γ i)) [Fintype ι]
    (h_triv : V.TrivialOn U.toOpenSubgroup.toSubgroup)
    {κ : (unitsModule U.toOpenSubgroup.toSubgroup).H0 →+
      Z1 (Representation.trivial ℤ U.toOpenSubgroup.toSubgroup (ZMod m))} (hκ : IsKummerMap κ)
    {b : IsLargeLevel.fixedSUnits N U →+ ι → ZMod m}
    (hb : ∀ (y : ↥(fixedSUnits N U)) (r : DiscreteUnits Ω), m • r = ↑y → ∀ i : ι,
      (rootPowHom Ω m).val (b y i) = unitsRep (s.φ i) r - r)
    {P : (PlaceAboveLevel N → V) × (G → V)} (hP : P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I)
    (y : ↥(fixedSUnits N U)) :
    ∑ θ : ι × G ⧸ U.toOpenSubgroup.toSubgroup,
      b (fixedSUnitsRep N U θ.snd y) θ.fst • V.ρ θ.snd.out⁻¹ (P.snd (γ θ.fst)) = 0 := by
  let Q : Subgroup G := U.toOpenSubgroup.toSubgroup
  let F : IntermediateField K Ω := fixedFieldOf Q
  let S := liftToFixedField s
  have h_inj : Function.Injective (rootPowHom Ω m).val := (rootPowHom Ω m).prop.left
  have hγ_mem (i : ι) : γ i ∈ Q := by
    obtain ⟨⟨hγ_dec, -⟩, -⟩ := hγ i
    exact s.decompGroup_le (s.isPlaceOver i) hγ_dec
  let γ' (θ : ι × G ⧸ Q) : Q :=
    ⟨θ.snd.out⁻¹ * γ θ.fst * θ.snd.out⁻¹⁻¹, U.isNormal'.conj_mem _ (hγ_mem θ.fst) _⟩
  have κ_φ (x : ↥(unitsModule Q).H0) (hx : x.val ∈ sUnits N) (θ : ι × G ⧸ Q) :
      (κ x).val (S.φ θ) =
        cyclotomicCharMod Ω m θ.snd.out⁻¹ * b (fixedSUnitsRep N U θ.snd.out ⟨_, hx, x.prop⟩)
          θ.fst :=
    kummer_frob_liftToFixedField s hκ hb x hx θ
  obtain ⟨z_cts, z_mul⟩ : P.snd ∈ Z1 V.ρ := snd_mem_Z1 hP
  obtain ⟨-, -, hP_zero⟩ := mem_trivialisedCocycles.mp hP
  obtain ⟨y, y_unit, y_fix⟩ := y
  -- The relation may be tested along additive maps `l : V → ℤ/m`. The character
  -- `l ∘ z` of `U` is `κ x` for some `x = r ^ m` in `F`.
  refine eq_zero_of_forall_hom_eq_zero
    ((bijective_ofZMod_comp (char_nsmul_eq_zero m)).surjective.forall.mpr fun l ↦ ?_)
  -- `l ∘ z` is additive on `U`, which acts trivially on `V`
  obtain ⟨r, x, hx, hr⟩ : ∃ (r : DiscreteUnits Ω) (x : Additive Fˣ), m • r = ofBase Q Ω x ∧
      ∀ q : Q, (rootPowHom Ω m).val (l (P.snd q)) = unitsRep q r - r :=
    exists_kummer_root (fun q ↦ S.cyclotomicCharMod_eq_one q ⟨⟩) _ (by fun_prop)
      fun g k ↦ by simp [z_mul, h_triv _]
  have r_fix (q : Q) (h : P.snd q = 0) : unitsRep q r = r := by simp [← sub_eq_zero, ← hr, h]
  -- `l ∘ z` and `κ x` have the same root of unity at each `γ' θ`
  have l_γ (θ : ι × G ⧸ Q) : l (V.ρ θ.snd.out⁻¹ (P.snd (γ θ.fst))) =
      cyclotomicCharMod Ω m θ.snd.out⁻¹ * ↑(-((S.v θ).valuation F x.toMul.val).log) :=
    calc _ = l (P.snd (γ' θ)) :=
        congrArg l (cocycle_conj_eq_smul (a := V.ρ) z_mul (h_triv _ (hγ_mem _) _)).symm
      _ = (κ (ofBase Q Ω x)).val (γ' θ) := h_inj (by rw [hr, hκ _ r hx])
      _ = _ := kummer_conj_liftToFixedField s hγ hκ θ _ x.toMul
  -- The character `χ = κ y / m`, with values in `ℚ/ℤ`, and Artin's law for `(χ, x)`: `r` is fixed
  -- wherever `z` vanishes, in particular at the complex conjugations and on the decomposition
  -- groups above `N`.
  let χ : QZChar Q := ofZModCocycle m (κ ⟨y, y_fix⟩)
  have h_sum : ∑ θ, -((S.v θ).valuation F x.toMul.val).log • χ.val (S.φ θ) = 0 :=
    s.sum_ord_smul_kummer_frob_eq_zero hκ y y_unit y_fix r x hx
      (fun q hq ↦ r_fix q (snd_trivialisedCocycles_eq_zero_of_isComplexConj h_triv hP q hq))
      (fun u hN q hq ↦ r_fix q (snd_eq_zero_of_mem_decompGroup h_triv hP u hN q hq))
      fun q hq ↦ r_fix q (hP_zero q hq)
  suffices h_goal : ∑ θ : ι × G ⧸ Q, b (fixedSUnitsRep N U θ.snd ⟨y, y_unit, y_fix⟩) θ.fst *
      l (V.ρ θ.snd.out⁻¹ (P.snd (γ θ.fst))) = 0 by
    simpa [ZMod.map_smul] using congrArg (ofZMod m) h_goal
  apply ofZMod_injective (n := m)
  -- By `l_γ` and `κ_φ` both sums have the terms `cyclotomicCharMod g⁻¹ * b (g y) i * ord x`.
  simpa [← map_zsmul, χ, ZMod.map_smul, l_γ, κ_φ ⟨y, y_fix⟩ y_unit, mul_comm (b _ _),
    mul_left_comm (Int.cast _), mul_assoc] using h_sum

variable [NeZero N]

/-- The cocycle of part (d) of `New.IsLargeLevel.SplitPlaces.power_residue_reciprocity`. Let `x` in
the field of `U` be a local `m`-th power above `N`, a unit at the other primes outside the lifted
family `liftToFixedField s`, and of order `cyclotomicCharMod Ω m g * f (i, g)` at its prime of index
`(i, g)`. Then `z = κ x • a` is trivialised at the places above `N` and infinity, and its
corestriction to `G` has the values `z (γ i) = ∑ g, g (f (i, g) • a)`. -/
private lemma IsLargeLevel.SplitPlaces.exists_mem_trivialisedCocycles_of_valuation {γ : ι → G}
    (hγ : ∀ i : ι, IsTameGeneratorFor m (s.valuationSubring i) (γ i)) [Fintype ι]
    (h_triv : V.TrivialOn U.toOpenSubgroup.toSubgroup)
    [IsTotallyComplex (fixedFieldOf U.toOpenSubgroup.toSubgroup)]
    {κ : (unitsModule U.toOpenSubgroup.toSubgroup).H0 →+
      Z1 (Representation.trivial ℤ U.toOpenSubgroup.toSubgroup (ZMod m))} (hκ : IsKummerMap κ)
    (f : ι × G ⧸ U.toOpenSubgroup.toSubgroup → ZMod m) (a : V.V)
    (x : (fixedFieldOf U.toOpenSubgroup.toSubgroup)ˣ)
    (hx_pow : ∀ u ∈ {u : FinPlace (fixedFieldOf U.toOpenSubgroup.toSubgroup) | ↑N ∈ u.asIdeal},
      ideleAt u (principalIdele x) ∈ (powMonoidHom m).range)
    (hx_unit : ∀ u : FinPlace (fixedFieldOf U.toOpenSubgroup.toSubgroup), ↑N ∉ u.asIdeal →
      u ∉ Set.range (liftToFixedField s).v →
        u.valuation (fixedFieldOf U.toOpenSubgroup.toSubgroup) x = 1)
    (hx_ord : ∀ θ : ι × G ⧸ U.toOpenSubgroup.toSubgroup,
      (((liftToFixedField s).v θ).valuation (fixedFieldOf U.toOpenSubgroup.toSubgroup) x.val).log =
        -((cyclotomicCharMod Ω m θ.snd.out * f θ).val : ℤ)) :
    ∃ P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I, ∀ i : ι,
      P.snd (γ i) = ∑ δ : G ⧸ (U.toOpenSubgroup : Subgroup G), V.ρ δ.out (f (i, δ) • a) := by
  let Q : Subgroup G := U.toOpenSubgroup.toSubgroup
  let F : IntermediateField K Ω := fixedFieldOf Q
  let S := liftToFixedField s
  have h_inj : Function.Injective (rootPowHom Ω m).val := (rootPowHom Ω m).prop.left
  have h_place (u : FinPlace F) : IsPlaceOver (placeOver u) u := u.isPlaceOver_placeOver
  have hγ_mem (i : ι) : γ i ∈ Q := by
    obtain ⟨⟨hγ_dec, -⟩, -⟩ := hγ i
    exact s.decompGroup_le (s.isPlaceOver i) hγ_dec
  choose root h_root using fun x : DiscreteUnits Ω ↦ exists_nsmul x (NeZero.ne m)
  have κ_fix (x : ↥(unitsModule Q).H0) (q : Q) (h : unitsRep q (root x.val) = root x.val) :
      (κ x).val q = 0 :=
    h_inj (by simp [hκ x _ (h_root _), h])
  let γ' (θ : ι × G ⧸ Q) : Q :=
    ⟨θ.snd.out⁻¹ * γ θ.fst * θ.snd.out⁻¹⁻¹, U.isNormal'.conj_mem _ (hγ_mem θ.fst) _⟩
  have κ_γ (θ : ι × G ⧸ Q) : (κ (ofBase Q Ω (.ofMul x))).val (γ' θ) =
      cyclotomicCharMod Ω m θ.snd.out⁻¹ * ↑(-((S.v θ).valuation F x.val).log) :=
    kummer_conj_liftToFixedField s hγ hκ θ _ x

  -- The cocycle `z = κ x • a` of `U` vanishes on `I` and on the stabilisers of the places above
  -- `N` and infinity, so it is trivialised by `0` at representatives of the orbits.
  let xFixed : ↥(unitsModule Q).H0 := ofBase Q Ω (.ofMul x)
  let z (q : Q) : V := (κ xFixed).val q • a
  obtain ⟨hκ_cont, hκ_cocycle⟩ := (κ xFixed).prop
  -- `using!`: the goal and `h_triv` agree only up to unfolding of definitions
  have hz : z ∈ Z1 (V.restrictTo Q).ρ :=
    ⟨(continuous_bot (f := fun c : ZMod m ↦ c • a)).comp hκ_cont,
      fun p q ↦ by simpa [z, hκ_cocycle, add_smul] using! (h_triv _ p.prop _).symm⟩
  have hz_I (q : Q) (hq : ↑q ∈ I) : z q = 0 := by
    obtain ⟨u, hN, h_new, B, hB, h_ine⟩ := (S.mem_inertia_iff q).mp hq
    simp [z, kummer_eq_zero_of_mem_inertiaGroup hκ hB
      (hN ∘ u.asIdeal.mem_of_dvd s.dvd_level.natCast) xFixed
      (hB.valuationVia_eq_one_iff.mpr (hx_unit u hN h_new)) h_ine]
  obtain ⟨trivialisation, h_trivialisation, -⟩ :=
    trivialisedCocycles.exists_mem_of_orbit_reps (I := Subtype.val ⁻¹' I)
        (PlaceAboveLevel.bijective_orbits Q N h_place) hz hz_I 0 <| by
    rintro (⟨u, hu⟩ | u) q hq
    · -- above `N`, `x` is a local `m`-th power, so the decomposition group fixes its roots
      have h_dec : q ∈ decompGroup Q (placeOver u) := congrArg Subtype.val (Sum.inl.inj hq)
      have h_root_val : (m • root xFixed.val).val = xFixed.val.val :=
        congrArg (fun y : DiscreteUnits Ω ↦ y.val) (h_root xFixed)
      have h_fix : unitsRep q (root xFixed.val) = root xFixed.val :=
        ext ((h_place u).smul_root_eq_of_local_pow (hx_pow u hu) h_root_val q
          h_dec (S.cyclotomicCharMod_eq_one q ⟨⟩))
      simp [z, κ_fix xFixed q h_fix]
    · -- `F` is totally complex, so `U` has no complex conjugation
      obtain rfl : q = 1 := (eq_one_or_isComplexConj (Sum.inr.inj hq)).resolve_right
        fun h_cc ↦ h_cc.false_of_isTotallyComplex
      simp [z, κ_fix]
  -- Corestrict to `G`; the value at `γ i` is the sum of the `δ • z (δ⁻¹ γ δ)`.
  refine ⟨_, corestrict_mem U.toOpenSubgroup s.mem_and_conj_mem h_trivialisation,
    fun i ↦ Finset.sum_congr rfl fun δ _ ↦ ?_⟩
  have h_ord : ((S.v (i, δ)).valuation F x.val).log =
      -((cyclotomicCharMod Ω m δ.out * f (i, δ)).val : ℤ) := hx_ord (i, δ)
  have h_value : z (γ' (i, δ)) = f (i, δ) • a := by simp [z, xFixed, κ_γ, h_ord]
  have h_coset : (γ i)⁻¹ • δ = δ := by
    induction δ using QuotientGroup.induction_on with
    | H g => simp [(eq_one_iff (N := Q) _).mpr, hγ_mem]
  simp [← h_value, γ', h_coset]

/-- Part (d) of `New.IsLargeLevel.SplitPlaces.power_residue_reciprocity`: let the field of `U` be
totally complex. A family `f` that satisfies the relations of the symbols `b` gives, for each
`a : V`, a trivialised cocycle with `z (γ i) = ∑ g, g (f (i, g) • a)`. The hypothesis `h_idele` is
the converse half of Kummer theory for `κ` (`New.exists_kummer_chars`) at the primes above `N`: an
idele whose Artin symbol is killed by `κ u` for all `N`-units `u` is principal times an `m`-th power
above `N` that is a unit off `N`. -/
private lemma IsLargeLevel.SplitPlaces.exists_mem_trivialisedCocycles_of_sum_symbol_mul_eq_zero
    {γ : ι → G} (hγ : ∀ i : ι, IsTameGeneratorFor m (s.valuationSubring i) (γ i)) [Fintype ι]
    (h_triv : V.TrivialOn U.toOpenSubgroup.toSubgroup)
    [IsTotallyComplex (fixedFieldOf U.toOpenSubgroup.toSubgroup)]
    {κ : (unitsModule U.toOpenSubgroup.toSubgroup).H0 →+
      Z1 (Representation.trivial ℤ U.toOpenSubgroup.toSubgroup (ZMod m))} (hκ : IsKummerMap κ)
    (h_idele : ∀ α : (𝔸f (fixedFieldOf U.toOpenSubgroup.toSubgroup))ˣ,
      (∀ u : Set.unit {u : FinPlace (fixedFieldOf U.toOpenSubgroup.toSubgroup) | ↑N ∈ u.asIdeal}
          (fixedFieldOf U.toOpenSubgroup.toSubgroup),
        abelianLift (ofZModCocycle m (κ (ofBase U.toOpenSubgroup.toSubgroup Ω (.ofMul u.val))))
          (artinMap U.toOpenSubgroup.toSubgroup α) = 1) →
      α ∈ principalIdele.range ⊔
        idelesPowAt {u : FinPlace (fixedFieldOf U.toOpenSubgroup.toSubgroup) | ↑N ∈ u.asIdeal} m ⊓
          idelesUnitOff {u : FinPlace (fixedFieldOf U.toOpenSubgroup.toSubgroup) | ↑N ∈ u.asIdeal})
    {b : IsLargeLevel.fixedSUnits N U →+ ι → ZMod m}
    (hb : ∀ (y : ↥(fixedSUnits N U)) (r : DiscreteUnits Ω), m • r = ↑y → ∀ i : ι,
      (rootPowHom Ω m).val (b y i) = unitsRep (s.φ i) r - r)
    (f : ι × G ⧸ U.toOpenSubgroup.toSubgroup → ZMod m)
    (hf : ∀ y : ↥(fixedSUnits N U), ∑ θ : ι × G ⧸ U.toOpenSubgroup.toSubgroup,
      b (fixedSUnitsRep N U θ.snd y) θ.fst * f θ = 0)
    (a : V.V) :
    ∃ P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I, ∀ i : ι,
      P.snd (γ i) = ∑ δ : G ⧸ (U.toOpenSubgroup : Subgroup G), V.ρ δ.out (f (i, δ) • a) := by
  -- Take local elements `ξ θ` of order one with Artin symbol `(S.φ θ)⁻¹`, and the idele
  -- `α` of order `e θ ≡ cyclotomicCharMod g * f θ` at `S.v θ`. The relations `hf` say that the
  -- Kummer characters of the `N`-units kill `α`, so for some `x` in `F` the idele `α / x` is an
  -- `m`-th power above `N` and a unit elsewhere.
  let Q : Subgroup G := U.toOpenSubgroup.toSubgroup
  let F : IntermediateField K Ω := fixedFieldOf Q
  let S := liftToFixedField s
  have κ_φ (x : ↥(unitsModule Q).H0) (hx : x.val ∈ sUnits N) (θ : ι × G ⧸ Q) :
      (κ x).val (S.φ θ) =
        cyclotomicCharMod Ω m θ.snd.out⁻¹ * b (fixedSUnitsRep N U θ.snd.out ⟨_, hx, x.prop⟩)
          θ.fst :=
    kummer_frob_liftToFixedField s hκ hb x hx θ
  choose ξ hξ_val hξ_art using fun θ : ι × G ⧸ Q ↦
    (S.isPlaceOver θ).exists_localArtin_eq_of_isFrob (Γ := Q) (g := (S.φ θ)⁻¹)
      (by simpa only [inv_inv] using (S.isFrob θ).left)
  let e (θ : ι × G ⧸ Q) : ℕ := (cyclotomicCharMod Ω m θ.snd.out * f θ).val
  let α : (𝔸f F)ˣ := ∏ θ, locIdele (S.v θ) (ξ θ) ^ e θ
  have hα (u : Set.unit {u : FinPlace F | ↑N ∈ u.asIdeal} F) :
      abelianLift (ofZModCocycle m (κ (ofBase Q Ω (.ofMul u.val)))) (artinMap Q α) = 1 := by
    simp [α, e, (S.isPlaceOver _).artinAt_eq_of_localArtin_eq (hξ_art _), ← toAdd_eq_zero,
      ← map_nsmul, ← map_sum,
      mul_comm (f _), mul_assoc, κ_φ (ofBase Q Ω (.ofMul u.val)) (ofBase_mem_sUnits.mpr u.prop), hf]
  obtain ⟨_, ⟨x, rfl⟩, β, ⟨h_pow, h_unit⟩, hβ⟩ := mem_sup.mp (h_idele α hα)
  obtain rfl : β = α / principalIdele x := eq_div_of_mul_eq'' hβ
  -- Off `N`, `x` has the valuations of `α`.
  have h_val : ∀ u : FinPlace F, ↑N ∉ u.asIdeal →
      ∏ θ, Valued.v ((locIdele (S.v θ) (ξ θ)).val u) ^ e θ = u.valuation F x := by
    simpa [α, idelesUnitOff, div_eq_one, Units.ext_iff, ideleAt] using h_unit
  have val_S (θ : ι × G ⧸ Q) : ((S.v θ).valuation F x.val).log = -e θ := by
    rw [← h_val _ (S.level_notMem θ), Fintype.prod_eq_single θ]
    · simp [hξ_val]
    · simp +contextual [S.v_injective.ne, eq_comm]
  -- So `x` is a local `m`-th power above `N` and a unit at the other primes outside the family.
  have hx_pow : ∀ u ∈ {u : FinPlace F | ↑N ∈ u.asIdeal},
      ideleAt u (principalIdele x) ∈ (powMonoidHom m).range :=
    fun u hu ↦ by simpa [α, hu.ne_of_notMem, S.level_notMem] using mem_iInf.1 h_pow ⟨u, hu⟩
  have hx_unit : ∀ u : FinPlace F, ↑N ∉ u.asIdeal → u ∉ Set.range S.v → u.valuation F x = 1 :=
    fun u hN h_new ↦ by simp [← h_val u hN, Ne.symm (h_new ⟨_, ·⟩)]
  exact s.exists_mem_trivialisedCocycles_of_valuation hγ h_triv hκ f a x hx_pow hx_unit val_S

/-- Power residue symbols `b` of the `N`-units of the field of `U` at the split primes of `s`, with
what they say about the values `z (γ i)` at tame generators `γ i` of the cocycles `z = P.snd` of
the pairs `P` trivialised above `N` and infinity. -/
structure IsLargeLevel.SplitPlaces.PowerResidueSymbols [Fintype ι] (γ : ι → G)
    (b : IsLargeLevel.fixedSUnits N U →+ ι → ZMod m) : Prop where
  /-- `ζ ^ b y i = s.φ i r / r` whenever `r ^ m = y`. -/
  rootPowHom_apply (y : ↥(fixedSUnits N U)) (r : DiscreteUnits Ω) (hr : m • r = ↑y) (i : ι) :
    (rootPowHom Ω m).val (b y i) = unitsRep (s.φ i) r - r
  /-- A trivialised cocycle that vanishes at every `γ i` vanishes on `U`. -/
  snd_eq_zero_of_forall_snd_eq_zero (P : (PlaceAboveLevel N → V) × (G → V))
    (hP : P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I) (h_zero : ∀ i : ι, P.snd (γ i) = 0)
    (g : G) (hg : g ∈ U) : P.snd g = 0
  /-- Each `N`-unit `y` gives the relation `∑ b (g y) i • g⁻¹ z (γ i) = 0`, over `i` and
  `g ∈ G / U`. -/
  sum_smul_eq_zero (P : (PlaceAboveLevel N → V) × (G → V))
    (hP : P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I) (y : ↥(fixedSUnits N U)) :
    ∑ θ : ι × G ⧸ U.toOpenSubgroup.toSubgroup,
      b (fixedSUnitsRep N U θ.snd y) θ.fst • V.ρ θ.snd.out⁻¹ (P.snd (γ θ.fst)) = 0
  /-- Over a totally complex field of `U`, a solution `f` of the relations gives, for each `a`, a
  trivialised cocycle with `z (γ i) = ∑ g, g (f (i, g) • a)`. -/
  exists_mem_trivialisedCocycles
    (h_complex : IsTotallyComplex (fixedFieldOf U.toOpenSubgroup.toSubgroup))
    (f : ι × G ⧸ U.toOpenSubgroup.toSubgroup → ZMod m)
    (hf : ∀ y : ↥(fixedSUnits N U), ∑ θ : ι × G ⧸ U.toOpenSubgroup.toSubgroup,
      b (fixedSUnitsRep N U θ.snd y) θ.fst * f θ = 0) (a : V.V) :
    ∃ P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I, ∀ i : ι,
      P.snd (γ i) = ∑ δ : G ⧸ (U.toOpenSubgroup : Subgroup G), V.ρ δ.out (f (i, δ) • a)

/-- Power residue reciprocity at split primes. Let `U` act trivially on the `ℤ/m`-module `V`, and
let `γ i` be tame generators of inertia at `s.valuationSubring i`. Then some power residue symbols
`b` have the properties of `New.IsLargeLevel.SplitPlaces.PowerResidueSymbols`. Cosets act on `V`
through their representatives `out`. The proof is by Kummer theory (`New.exists_kummer_chars`) and
Artin's law.

The Greenberg–Wiles bounds on cocycle counts in this development use this statement in place of
Poitou–Tate duality. -/
theorem IsLargeLevel.SplitPlaces.exists_powerResidueSymbols (γ : ι → G)
    (hγ : ∀ i : ι, IsTameGeneratorFor m (s.valuationSubring i) (γ i))
    [Fintype ι] (h_triv : V.TrivialOn U.toOpenSubgroup.toSubgroup) :
    ∃ b : IsLargeLevel.fixedSUnits N U →+ ι → ZMod m, s.PowerResidueSymbols (V := V) γ b := by
  -- Work over the fixed field `F` of `U`, which contains the `m`-th roots of unity, with the Kummer
  -- characters `κ x` of `U`. The relations are Artin's law for a symbol `(κ y, x)`
  -- (`sum_ord_smul_kummer_frob_eq_zero`); conversely a family `f` that satisfies them gives the
  -- orders of an idele that is principal up to powers and units.
  let Q : Subgroup G := U.toOpenSubgroup.toSubgroup
  let F : IntermediateField K Ω := fixedFieldOf Q
  -- `hκ`: `ζ ^ κ x q = q r / r` whenever `r ^ m = x`. `h_idele`: for `F` totally complex and a
  -- large set `T` of primes, an idele whose Artin symbol is killed by the `κ u` of all `T`-units
  -- `u` is principal times an idele that is an `m`-th power at `T` and a unit elsewhere.
  have h_cyc (q : Q) : cyclotomicCharMod Ω m q = 1 :=
    (liftToFixedField s).cyclotomicCharMod_eq_one q ⟨⟩
  obtain ⟨κ, hκ, h_idele⟩ := exists_kummer_chars (K := F) h_cyc
  -- The symbol `b y i` is the value of `κ y` at the Frobenius `s.φ i`.
  have h_fix (y : ↥(fixedSUnits N U)) : y.val ∈ (unitsModule Q).H0 :=
    (Submodule.mem_inf.mp y.prop).right
  let b : IsLargeLevel.fixedSUnits N U →+ ι → ZMod m :=
    .mk' (fun y i ↦ (κ ⟨y, h_fix y⟩).val ⟨s.φ i, (s.isFrob i).right⟩) fun y y' ↦ funext fun i ↦
      congrArg (fun c ↦ c.val ⟨s.φ i, (s.isFrob i).right⟩)
        (κ.map_add ⟨y, h_fix y⟩ ⟨y', h_fix y'⟩)
  have hb : ∀ (y : ↥(fixedSUnits N U)) (r : DiscreteUnits Ω), m • r = ↑y → ∀ i : ι,
      (rootPowHom Ω m).val (b y i) = unitsRep (s.φ i) r - r :=
    fun y r hr i ↦ hκ _ r hr _
  refine ⟨b, hb, fun P hP ↦ snd_eq_zero_of_snd_generators_eq_zero s hγ h_triv hP,
    fun P hP ↦ sum_symbol_smul_snd_generators_eq_zero s hγ h_triv hκ hb hP, fun h_complex ↦ ?_⟩
  exact exists_mem_trivialisedCocycles_of_sum_symbol_mul_eq_zero s hγ h_triv hκ
    (fun α hα ↦ h_idele (finite_natCast_mem _) (s.principal_sup_idelesUnitOff F le_rfl)
      (fun u ↦ u.asIdeal.mem_of_dvd s.dvd_level.natCast) α hα) hb

/-- `New.IsLargeLevel.SplitPlaces.exists_powerResidueSymbols` as one conjunction: its clauses
(a)–(d) are the four fields of `New.IsLargeLevel.SplitPlaces.PowerResidueSymbols`, in order. Here
`s.φ i` is a Frobenius element in `U` at a place over the `i`-th split prime. A pair `P` is a map
`f` on the places of `Ω` above `N` and infinity together with a continuous `z = P.snd` vanishing on
`I`, with `g f(x) = f(g x) + z g`.

Clauses (c) and (d) are an explicit substitute for the Poitou–Tate duality behind the
Greenberg–Wiles formula, for modules fixed by `U` at auxiliary split primes, pairing trivialised
cocycles with `N`-units by power residue symbols. -/
lemma IsLargeLevel.SplitPlaces.power_residue_reciprocity (γ : ι → G)
    (hγ : ∀ i : ι, IsTameGeneratorFor m (s.valuationSubring i) (γ i))
    [Fintype ι] (h_triv : V.TrivialOn U.toOpenSubgroup.toSubgroup) :
    ∃ b : IsLargeLevel.fixedSUnits N U →+ ι → ZMod m,
      -- (a) `b y i` is the `m`-th power residue symbol of the `N`-unit `y` at the `i`-th prime
      (∀ (y : ↥(fixedSUnits N U)) (r : DiscreteUnits Ω), m • r = ↑y → ∀ i : ι,
        (rootPowHom Ω m).val (b y i) = unitsRep (s.φ i) r - r) ∧
      (∀ P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I,
        -- (b) on `U`, a trivialised cocycle that vanishes at all `γ i` is zero
        ((∀ i : ι, P.snd (γ i) = 0) → ∀ g ∈ U, P.snd g = 0) ∧
        -- (c) each `N`-unit `y` gives a relation between the values at the `γ i`
        ∀ y : ↥(fixedSUnits N U), ∑ θ : ι × G ⧸ U.toOpenSubgroup.toSubgroup,
          b (fixedSUnitsRep N U θ.snd y) θ.fst • V.ρ θ.snd.out⁻¹ (P.snd (γ θ.fst)) = 0) ∧
      -- (d) over a totally complex field, a family `f` with these relations comes from a cocycle
      (IsTotallyComplex (fixedFieldOf U.toOpenSubgroup.toSubgroup) →
        ∀ f : ι × G ⧸ U.toOpenSubgroup.toSubgroup → ZMod m,
          (∀ y : ↥(fixedSUnits N U), ∑ θ : ι × G ⧸ U.toOpenSubgroup.toSubgroup,
            b (fixedSUnitsRep N U θ.snd y) θ.fst * f θ = 0) →
          ∀ a : V.V, ∃ P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I, ∀ i : ι,
            P.snd (γ i) = ∑ δ : G ⧸ (U.toOpenSubgroup : Subgroup G), V.ρ δ.out (f (i, δ) • a)) := by
  obtain ⟨b, h_symbols⟩ := s.exists_powerResidueSymbols γ hγ h_triv
  exact ⟨b, h_symbols.rootPowHom_apply,
    fun P hP ↦ ⟨h_symbols.snd_eq_zero_of_forall_snd_eq_zero P hP, h_symbols.sum_smul_eq_zero P hP⟩,
    fun h_complex f hf a ↦ h_symbols.exists_mem_trivialisedCocycles h_complex f hf a⟩

end New
