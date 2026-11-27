import New.Congruences.LocalLoss.CrystallineCocycles

/-!
# A bound for non-crystalline cocycles modulo `ℓ ^ m` by the Tate dual lattice

This file proves a local estimate at a place above `ℓ`, by Tate duality. The group `Γ` maps to the
absolute Galois group of `ℚ_ℓ` (`OverGp Γ ℓ`), `R` is the integer ring of a finite extension of
`ℚ_ℓ` (`PadicIntegerRing R ℓ`), and `L = R ^ d` is the lattice of a matrix representation of `Γ`
(`matrixLattice`). `QuotSpan a` is the ring `R / a`.

* `New.Selmer.ComesFromClass`: a map with values modulo `ℓ ^ m` is the image of a crystalline
  cocycle of a lattice of a given class.
* `New.Selmer.relLength_le_of_comesFromClass`: if the map of `Γ` to the Galois group is an open
  embedding and `L` lies in the class, a module of maps that come from the class, modulo the
  reductions of the crystalline cocycles of `L`, is at most as long as the crystalline cocycles of
  the Tate dual of `L` modulo those orthogonal to the class.
* `New.Selmer.comesFromClass_of_mem_ribetCocycles`: let `η : Γ →* G`, and let the lattices of all
  `u x ∘ η` lie in the class. Then the restriction along `η` of a cocycle in `ribetCocycles u ρ`
  comes from the class.
* `New.Selmer.relLength_ribetCocycles_le`: if the map of `Γ` to the Galois group is an open
  embedding and the lattices of `ρ ∘ η` and of all `u x ∘ η` lie in the class, the same bound holds
  for `ribetCocycles u ρ` modulo the cocycles whose restriction along `η` obeys the linear
  relations that hold on the crystalline cocycles of the lattice `L` of `ρ ∘ η`.

Notions from other files:
* `New.Lift.InClass F K U`: the class of `Γ`-lattices `Y` over `R` (`GalLattice R Γ`) with three
  properties: the periods of `Y` that are fixed by almost all elements of `Γ` near `1` and along the
  filter `F` on `Γ` span; at each algebra map `ι : R → ℂ_ℓ` the Hodge–Tate jumps of `Y` lie in the
  finite set `U ι`; and on the periods of `Y` the polynomial `Q` over `R`, evaluated at the action
  of an element `s` of `Γ`, is zero whenever `s` is in inertia and `K s Q` holds. Such lattices
  are potentially crystalline.
* `New.Period.crysCocycles`: the module `Z_f(T)` of maps `c : Γ → T` that become coboundaries in
  `Bmax ⊗ T`.
* `New.Lift.cupOrthogonal 𝒬 L`: the maps `c : Γ → L` whose cup product with every crystalline
  cocycle of every `Y` in `𝒬` is a coboundary, for every `k` and every pairing `Y × L → ℤ/ℓᵏ(1)`
  given by a `New.Lift.Pairing`.
* `New.Selmer.ribetCocycles u ρ a`: the cocycles for `ρ` with values modulo `a` that obey the
  linear relations among the families `(u x g - 1)_x`.

The estimate bounds the non-crystalline defect above `ℓ` of the cocycles used in
`New.Congruences.FirstOrder.RibetElement`.

## Relation to the literature

See `New.Congruences.FirstOrder.RibetElement` for related work.
-/

open New Matrix Period Lift Module Function Topology Submodule crysCocycles Ideal.Quotient
  NeZero LinearMap LE DistribSMul

/-- Let `Γ` be a group with a map to the absolute Galois group of `ℚ_ℓ` with open image
(`OverGp Γ ℓ`), let `R` be the integer ring of a finite extension of `ℚ_ℓ`, and let `Γ` act through
the matrix representation `σ` on vectors over `R / ℓ ^ m`. A map `s` from `Γ` to such vectors comes
from the class of lattices `𝒬` if `s = t ∘ a` for a lattice `Y` in `𝒬`, a `Γ`-equivariant `R`-linear
map `t : Y → (R / ℓ ^ m) ^ d` and a crystalline cocycle `a` of `Y` (a map `Γ → Y` that becomes a
coboundary after tensoring with `Bmax`). -/
def New.Selmer.ComesFromClass {ℓ : ℕ} [ThePrime ℓ] {R Γ d : Type} [CommRing R]
    [PadicIntegerRing R ℓ] [Group Γ] [Fintype d] [DecidableEq d] [OverGp Γ ℓ]
    (𝒬 : GalLattice R Γ → Prop) (σ : Γ →* Matrix d d R) (m : ℕ)
    (s : Γ → d → QuotSpan (ℓ ^ m : R)) : Prop :=
  ∃ Y : GalLattice R Γ, 𝒬 Y ∧ ∃ t : Y →ₗ[R] d → QuotSpan (ℓ ^ m : R),
    (∀ (g : Γ) (x : Y), t (Y.ρ g x) = σ g • t x) ∧ ∃ a ∈ crysCocycles Y.ρ, t ∘ a = s

/-- A vector over `R` reduces to `0` modulo `ℓ ^ m` exactly if it lies in `ℓ ^ m R ^ d`. -/
lemma New.Selmer.ker_compLeft_mkQ_eq_pPowMultiples {ℓ : ℕ} [ThePrime ℓ] {R d : Type} [CommRing R]
    [Algebra ℤ_[ℓ] R] (m : ℕ) :
    ((mkQ (R ∙ (ℓ : R) ^ m)).compLeft d).toAddMonoidHom.ker = Period.pPowMultiples (d → R) m := by
  ext x
  -- Both sides say that every coordinate of `x` is divisible by `ℓ ^ m`.
  change (mkQ (R ∙ (ℓ : R) ^ m)).compLeft d x = 0 ↔ ∃ y : d → R, (ℓ : ℤ_[ℓ]) ^ m • y = x
  simp [Algebra.smul_def, funext_iff, eq_zero_iff_mem, mem_span_singleton, Classical.skolem,
    mul_comm]

/-- Let `Y` and `L` be `R`-lattices with an action of `Γ`, and let the `R`-linear map `q : Y → L` be
equivariant modulo `ℓ ^ m L` (`pPowMultiples L m`). Let `ψ` be the form `y ⊗ φ ↦ φ (q y)` on
`Y ⊗ L^∨(1)`. Then the coboundary `g ↦ g ψ - ψ` is `ℓ ^ m` times a crystalline cocycle of the Tate
dual of `Y ⊗ L^∨(1)`. -/
lemma New.Selmer.exists_crysCocycles_pow_smul_eq_coboundary {ℓ : ℕ} [ThePrime ℓ] {R Γ : Type}
    [CommRing R] [PadicIntegerRing R ℓ] [Group Γ] [OverGp Γ ℓ] {Y L : GalLattice R Γ} {m : ℕ}
    {q : Y →ₗ[R] L} (hq : ∀ (g : Γ) (y : Y), L.ρ g (q y) - q (Y.ρ g y) ∈ Period.pPowMultiples L m) :
    let ψ : (Y.tensor L.tateDual).tateDual := TensorProduct.lift (Dual.eval R L ∘ₗ q)
    ∃ c ∈ crysCocycles (Y.tensor L.tateDual).tateDual.ρ,
      ∀ g : Γ, ℓ ^ m • c g = (Y.tensor L.tateDual).tateDual.ρ g ψ - ψ := by
  intro ψ
  -- Divide: `g q - q = ℓ ^ m δ g` for linear maps `δ g : Y → L`.
  let mul : L →ₗ[R] L := toLinearMap R L ((ℓ : ℤ_[ℓ]) ^ m)
  have exists_δ (g : Γ) : ∃ δ : Y →ₗ[R] L, ∀ y : Y, mul (δ y) = (Y.ρ.linHom L.ρ g q - q) y := by
    have h_range (y : Y) : (Y.ρ.linHom L.ρ g q - q) y ∈ LinearMap.range mul := by
      simpa [mul] using hq g (Y.ρ g⁻¹ y)
    exact ⟨_, codRestrictOfInjective_comp_apply _ mul (smul_right_injective L NeZero.out) h_range⟩
  choose δ hδ using exists_δ
  -- The forms `c g : y ⊗ φ ↦ φ (δ g y)` give the cocycle, as `crysCocycles` is saturated.
  let c (g : Γ) : (Y.tensor L.tateDual).tateDual := TensorProduct.lift (Dual.eval R L ∘ₗ δ g)
  have c_cob (g : Γ) : (ℓ : ℤ_[ℓ]) ^ m • c g = (Y.tensor L.tateDual).tateDual.ρ g ψ - ψ := by
    ext y φ
    simpa [c, ψ, mul] using congrArg φ (hδ g y)
  refine ⟨c, crysCocycles.mem_of_smul_mem (a := (ℓ : ℤ_[ℓ]) ^ m) NeZero.out ?_, mod_cast c_cob⟩
  rw [show (ℓ : ℤ_[ℓ]) ^ m • c = _ from funext c_cob]
  exact coboundary_mem ψ

/-- Let the map `𝒥.toGp` from `Γ` to the absolute Galois group of `ℚ_ℓ` be an open embedding, and
let `R` be the integer ring of a finite extension of `ℚ_ℓ`. Let `InClass F K U` be the class of
potentially crystalline `Γ`-lattices `Y` over `R` such that `Bmax ⊗ Y` is spanned by the periods
fixed near `1` and along the filter `F`, the Hodge–Tate jumps at each `ι : R → ℂ_ℓ` lie in `U ι`,
and `Q(s) = 0` on the periods for `s` in inertia with `K s Q`. Let the lattice `L = R ^ d` of
`σ` lie in the class. Let `N` be a module of maps `Γ → L / ℓ ^ m`, each of the form `t ∘ a` for a
crystalline cocycle `a` of a lattice `Y` of the class and a `Γ`-equivariant `R`-linear map
`t : Y → L / ℓ ^ m` (`ComesFromClass`). Then the length of `N` modulo the reductions of the
crystalline cocycles of `L` is at most the length of the crystalline cocycles of the Tate dual
`L^∨(1)` modulo those whose cup products with the crystalline cocycles of all lattices of the class
are coboundaries (`dualDefect`). Here `relLength S T` is the length of `S / (S ∩ T)`. -/
lemma New.Selmer.relLength_le_of_comesFromClass {ℓ : ℕ} [ThePrime ℓ] {R Γ d : Type} [CommRing R]
    [PadicIntegerRing R ℓ] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Fintype d]
    [DecidableEq d] [𝒥 : OverGp Γ ℓ] (h_emb : IsOpenEmbedding 𝒥.toGp) {σ : Γ →* Matrix d d R}
    {F : Filter Γ} {K : Γ → Polynomial R → Prop} {U : (R →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ}
    (hL : InClass F K U (matrixLattice σ)) {m : ℕ}
    {N : Submodule R (Γ → d → QuotSpan (ℓ ^ m : R))}
    (hN : ∀ s ∈ N, ComesFromClass (InClass F K U) σ m s) :
    relLength N ((crysCocycles (matrixLattice σ).ρ).map
        (((mkQ (R ∙ (ℓ : R) ^ m)).compLeft d).compLeft Γ)) ≤
      dualDefect (InClass F K U) (matrixLattice σ).tateDual := by
  -- Apply local duality modulo `ℓ ^ m`. Each member of `N`, like each reduction of a crystalline
  -- cocycle of `L`, comes from the class, so it is orthogonal to `cupOrthogonal`.
  let L : GalLattice R Γ := matrixLattice σ
  -- `f` turns the evaluation pairing of the dual and `L` into a perfect pairing `b` over `ℤ_[ℓ]`.
  obtain ⟨f, hf⟩ : ∃ f : Dual ℤ_[ℓ] R, Bijective ((restrictScalarsₗ ℤ_[ℓ] R L R ℤ_[ℓ]).compr₂ f) :=
    exists_perfect_pairing
  let b : L.tateDual ≃ₗ[ℤ_[ℓ]] Dual ℤ_[ℓ] L := .ofBijective _ hf
  let : TopologicalSpace (QuotSpan (ℓ ^ m : R)) := ⊥
  have : DiscreteTopology (QuotSpan (ℓ ^ m : R)) := discreteTopology_bot _
  -- The reduction `τ` modulo `ℓ ^ m` is onto, has the kernel `ℓ ^ m L` and is equivariant.
  let τ : (d → R) →ₗ[R] d → QuotSpan (ℓ ^ m : R) := (mkQ (R ∙ (ℓ : R) ^ m)).compLeft d
  have τ_surj : Surjective τ := mk_surjective.comp_left
  have τ_ker : τ.toAddMonoidHom.ker = Period.pPowMultiples L m :=
    ker_compLeft_mkQ_eq_pPowMultiples m
  have τ_equiv (g : Γ) (x : L) : τ (L.ρ g x) = σ g • τ x :=
    funext fun i ↦ map_sum (mkQ (R ∙ (ℓ : R) ^ m)) (fun j : d ↦ σ g i j * x j) Finset.univ
  -- A crystalline cocycle of a lattice of the class, mapped to `L / ℓ ^ m`, is continuous.
  have cont_red {Y : GalLattice R Γ} (hY : InClass F K U Y) (q : Y →ₗ[R] L) {a : Γ → Y}
      (ha : a ∈ crysCocycles Y.ρ) : Continuous ((τ ∘ₗ q) ∘ a) :=
    continuous_comp h_emb hY.isPotentiallyCrystalline (τ ∘ₗ q).toAddMonoidHom
      (fun y ↦ funext fun i ↦ nsmul_quot_eq_zero dvd_rfl (τ (q y) i)) ha
  -- So `L / ℓ ^ m` is a discrete `Γ`-module: `g ↦ g • τ x` is a coboundary plus a constant.
  let V : DiscreteModule ℤ_[ℓ] Γ := .of (actionRep ℤ_[ℓ] (d → QuotSpan (ℓ ^ m : R)) σ) <| by
    suffices ∀ x : L, Continuous fun g : Γ ↦ σ g • τ x by
      simpa [τ_surj.forall, continuous_prod_of_discrete_right]
    intro x
    simpa [τ_equiv] using (cont_red (Y := L) hL .id (coboundary_mem x)).add_const (τ x)
  let A : Submodule R (Γ → d → QuotSpan (ℓ ^ m : R)) := (crysCocycles L.ρ).map (τ.compLeft Γ)
  let H : Submodule R (Γ → L.tateDual) := cupOrthogonal (InClass F K U) L.tateDual
  -- A map that comes from the class is a continuous cocycle, and its cup products with the members
  -- of `H` are coboundaries.
  have orthogonal (s : Γ → V) (hs : ComesFromClass (InClass F K U) σ m s) :
      IsCupOrthogonal b m (V := V) (τ.restrictScalars ℤ_[ℓ]) H.toAddSubgroup s := by
    obtain ⟨Y, hY, t, t_equiv, a, ha, rfl⟩ := hs
    -- Lift `t` to a linear map `q : Y → L`, which is equivariant modulo `ℓ ^ m`.
    obtain ⟨q, rfl⟩ := projective_lifting_property τ t τ_surj
    have q_equiv (g : Γ) (y : Y) : τ (q (Y.ρ g y)) = σ g • τ (q y) := t_equiv g y
    -- The pairing `(y, φ) ↦ f (φ (q y))` modulo `ℓ ^ m` is one of those tested in `cupOrthogonal`.
    obtain ⟨c, hc, c_cob⟩ := exists_crysCocycles_pow_smul_eq_coboundary (q := q) (m := m)
      fun g y ↦ τ_ker.le (by simp [τ_equiv, q_equiv])
    let P : Pairing Y L.tateDual :=
      { exponent := m, integralForm := TensorProduct.lift (Dual.eval R L ∘ₗ q), toZp := f,
        cocycle := ⟨c, hc⟩, pow_smul_cocycle := c_cob }
    have cocycle_eq (g h : Γ) : τ (q (a (g * h))) = τ (q (a g)) + σ g • τ (q (a h)) := by
      rw [apply_mul ha, map_add, map_add, q_equiv]
    -- The cup product of `q ∘ a` and `z` under `b` is that of `a` and `z` under `P`.
    exact ⟨⟨cont_red hY q ha, cocycle_eq⟩, q ∘ a, rfl, fun z hz ↦ hz Y P hY a ha⟩
  -- Local duality: `[N : N ∩ A]` divides the index of `H ∩ Z` in the crystalline cocycles `Z` of
  -- the dual. The reduction of a crystalline cocycle of `L` comes from the class by `τ` itself.
  have index_dvd : A.toAddSubgroup.relIndex N.toAddSubgroup ∣
      H.toAddSubgroup.relIndex (crysCocycles L.tateDual.ρ).toAddSubgroup :=
    IsPotentiallyCrystalline.relIndex_dvd_of_orthogonal h_emb hL.isPotentiallyCrystalline
      hL.dual.isPotentiallyCrystalline b
      (by simp [b, ← map_mul]) (V := V) (q := τ.restrictScalars ℤ_[ℓ]) τ_equiv τ_surj τ_ker
      (fun z hz ↦ orthogonal (τ ∘ z) ⟨L, hL, τ, τ_equiv, z, hz, rfl⟩)
      fun s hs ↦ orthogonal s (hN s hs)
  -- A relative index is the cardinality of the quotient whose length is `relLength`.
  change relLength N A ≤ relLength (crysCocycles L.tateDual.ρ) H
  exact length_le_of_card_dvd ℓ index_dvd

/-- Let `Γ` be a group with a map to the absolute Galois group of `ℚ_ℓ` with open image
(`OverGp Γ ℓ`), and let `R` be the integer ring of a finite extension of `ℚ_ℓ`. Let `InClass F K U`
be the class of potentially crystalline `Γ`-lattices `Y` over `R` such that `Bmax ⊗ Y` is spanned by
the periods fixed near `1` and along the filter `F`, the Hodge–Tate jumps at each `ι : R → ℂ_ℓ` lie
in `U ι`, and `Q(s) = 0` on the periods for `s` in inertia with `K s Q`. Let `η : Γ →* G`, let `u x`
be matrix representations of `G` of size `n`, and let the lattices `R ^ n` of all `u x ∘ η` lie in
the class. Let `w` be a cocycle of `G` for the matrix representation `ρ`, with values in
`(R / ℓ ^ m) ^ d`, that obeys the linear relations among the families `(u x g - 1)_x`
(`ribetCocycles`). Then `w ∘ η` is the image of a crystalline cocycle of a lattice `Y` of the class
under an `R`-linear map `Y → (R / ℓ ^ m) ^ d` that is equivariant for `ρ ∘ η` (`ComesFromClass`). -/
lemma New.Selmer.comesFromClass_of_mem_ribetCocycles {ℓ : ℕ} [ThePrime ℓ] {X n R Γ G d : Type}
    [Fintype X] [Fintype n] [DecidableEq n] [CommRing R] [PadicIntegerRing R ℓ] [Group Γ] [Group G]
    [Fintype d] [DecidableEq d] [OverGp Γ ℓ] {η : Γ →* G} {u : X → G →* Matrix n n R}
    {ρ : G →* Matrix d d R} {F : Filter Γ} {K : Γ → Polynomial R → Prop}
    {U : (R →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ}
    (hu : ∀ x : X, InClass F K U (matrixLattice ((u x).comp η))) {m : ℕ}
    {w : G → d → QuotSpan (ℓ ^ m : R)} (hw : w ∈ ribetCocycles u ρ (ℓ ^ m)) :
    ComesFromClass (InClass F K U) (ρ.comp η) m (w ∘ η) := by
  -- `Y` is a subrepresentation of (families of matrices) × (values), determined by its first
  -- component (`Y_inj`), that contains all `(u g - 1 + (ℓ ^ m) ^ k • v, w g)` (`hY`).
  obtain ⟨k, Y, Y_inj, hY⟩ : ∃ (k : ℕ) (Y : Subrepresentation
        ((actionRep R (X → Matrix n n R) (MonoidHom.pi u)).prod
          (actionRep R (d → QuotSpan (ℓ ^ m : R)) ρ))),
      Injective (fun y : Y.toSubmodule ↦ y.val.fst) ∧ ∀ (g : G) (v : X → Matrix n n R),
        ((fun x : X ↦ u x g - 1) + (ℓ ^ m : R) ^ k • v, w g) ∈ Y :=
    ribetCocycles.exists_graph_subrepresentation u ρ hw
  have : IsTorsionFree R Y.toSubmodule := Y_inj.moduleIsTorsionFree _ fun _ _ ↦ rfl
  let Y' : GalLattice R Γ := ⟨Y.toSubmodule, Y.toRepresentation.comp η⟩
  -- The second component `t` is equivariant and maps `a` to the restriction of `w`.
  let t : Y' →ₗ[R] d → QuotSpan (ℓ ^ m : R) :=
    LinearMap.snd R (X → Matrix n n R) (d → QuotSpan (ℓ ^ m : R)) ∘ₗ Y.toSubmodule.subtype
  let a : Γ → Y' := fun g ↦ ⟨((fun x ↦ u x (η g) - 1) + (ℓ ^ m : R) ^ k • 0, w (η g)), hY (η g) 0⟩
  refine ⟨Y', ?_, t, fun _ _ ↦ rfl, a, ?_, rfl⟩
  · -- The columns of the first component embed `Y'` in a sum of the lattices of the `u x ∘ η`.
    let col (c : X × n) : Y' →ₗ[R] matrixLattice ((u c.1).comp η) :=
      { toFun y i := y.val.fst c.1 i c.2, map_add' _ _ := rfl, map_smul' _ _ := rfl }
    refine .of_jointly_injective (fun c : X × n ↦ hu c.1) col (fun _ _ _ ↦ rfl) fun y hy ↦ Y_inj ?_
    exact funext fun x ↦ Matrix.ext fun i j ↦ congrFun (hy (x, j)) i
  · -- `(ℓ ^ m) ^ k • a` is the coboundary of `y₀`, whose first component equals
    -- `(ℓ ^ m) ^ k • 1` as `u x 1 = 1`, and `crysCocycles` is saturated.
    let y₀ : Y' := ⟨((fun x ↦ u x 1 - 1) + (ℓ ^ m : R) ^ k • 1, w 1), hY 1 1⟩
    have cob_eq : (fun g : Γ ↦ Y'.ρ g y₀ - y₀) = ((ℓ : ℤ_[ℓ]) ^ m) ^ k • a := by
      refine funext fun g ↦ Y_inj (funext fun x ↦ ?_)
      change u x (η g) * (u x 1 - 1 + (ℓ ^ m : R) ^ k • 1) - (u x 1 - 1 + (ℓ ^ m : R) ^ k • 1) =
        ((ℓ : ℤ_[ℓ]) ^ m) ^ k • (u x (η g) - 1 + (ℓ ^ m : R) ^ k • 0)
      rw [← algebraMap_smul R (((ℓ : ℤ_[ℓ]) ^ m) ^ k)]
      simp [smul_sub]
    refine crysCocycles.mem_of_smul_mem (a := ((ℓ : ℤ_[ℓ]) ^ m) ^ k) NeZero.out ?_
    rw [← cob_eq]
    exact coboundary_mem y₀

/-- Let the map `𝒥.toGp` from `Γ` to the absolute Galois group of `ℚ_ℓ` be an open embedding, let
`R` be the integer ring of a finite extension of `ℚ_ℓ`, and let `η : Γ →* G`. Let `u x` (`x : X`)
and `ρ` be matrix representations of `G` over `R` of sizes `n` and `d`. Let the lattices of all
`u x ∘ η` and the lattice `L` of `ρ ∘ η` lie in `InClass F K U`, the class of potentially
crystalline `Γ`-lattices `Y` such that `Bmax ⊗ Y` is spanned by the periods fixed near `1` and along
the filter `F`, the Hodge–Tate jumps at each `ι : R → ℂ_ℓ` lie in `U ι`, and `Q(s) = 0` on the
periods for `s` in inertia with `K s Q`. Take the cocycles of `G` for `ρ` with values modulo `ℓ ^ m`
that obey the linear relations among the families `(u x g - 1)_x` (`ribetCocycles`), modulo those
whose restriction along `η` obeys (`obeying`) all linear relations that hold on the crystalline
cocycles of `L` (`relationsOn`). The length of this quotient is at most that of the crystalline
cocycles of the Tate dual `L^∨(1)` modulo those whose cup products with the crystalline cocycles of
all lattices of the class are coboundaries (`dualDefect`). -/
lemma New.Selmer.relLength_ribetCocycles_le {ℓ : ℕ} [ThePrime ℓ] {X n R Γ G d : Type} [Fintype X]
    [Fintype n] [DecidableEq n] [CommRing R] [PadicIntegerRing R ℓ] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [Group G] [Fintype d] [DecidableEq d] [𝒥 : OverGp Γ ℓ]
    (h_emb : IsOpenEmbedding 𝒥.toGp) {η : Γ →* G} {u : X → G →* Matrix n n R}
    {ρ : G →* Matrix d d R}
    {F : Filter Γ} {K : Γ → Polynomial R → Prop} {U : (R →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ}
    (hu : ∀ x : X, InClass F K U (matrixLattice ((u x).comp η))) (m : ℕ)
    (hL : InClass F K U (matrixLattice (ρ.comp η))) :
    relLength (ribetCocycles u ρ (ℓ ^ m))
        ((obeying (relationsOn (crysCocycles (matrixLattice (ρ.comp η)).ρ))
          (QuotSpan (ℓ ^ m : R))).comap (LinearMap.funLeft R (d → QuotSpan (ℓ ^ m : R)) η)) ≤
      dualDefect (InClass F K U) (matrixLattice (ρ.comp η)).tateDual := by
  let L : GalLattice R Γ := matrixLattice (ρ.comp η)
  let restrict : (G → d → QuotSpan (ℓ ^ m : R)) →ₗ[R] Γ → d → QuotSpan (ℓ ^ m : R) :=
    LinearMap.funLeft R (d → QuotSpan (ℓ ^ m : R)) η
  -- `N` holds the restrictions along `η`, `A` the reductions of the crystalline cocycles of `L`,
  -- and `B` the maps that obey the linear relations that hold on these cocycles.
  let N : Submodule R (Γ → d → QuotSpan (ℓ ^ m : R)) := (ribetCocycles u ρ (ℓ ^ m)).map restrict
  let A : Submodule R (Γ → d → QuotSpan (ℓ ^ m : R)) :=
    (crysCocycles L.ρ).map (((mkQ (R ∙ (ℓ : R) ^ m)).compLeft d).compLeft Γ)
  let B : Submodule R (Γ → d → QuotSpan (ℓ ^ m : R)) :=
    obeying (relationsOn (crysCocycles L.ρ)) (QuotSpan (ℓ ^ m : R))
  have hN : ∀ s ∈ N, ComesFromClass (InClass F K U) (ρ.comp η) m s :=
    Set.forall_mem_image.2 fun w hw ↦ comesFromClass_of_mem_ribetCocycles hu hw
  calc relLength (ribetCocycles u ρ (ℓ ^ m)) (B.comap restrict)
      = relLength N B := relLength_comap (ribetCocycles u ρ (ℓ ^ m)) restrict
    _ ≤ relLength N A := relLength_mono le_rfl (map_le_iff_le_comap.2 mkQ_mem_obeying_relationsOn)
    _ ≤ dualDefect (InClass F K U) L.tateDual := relLength_le_of_comesFromClass h_emb hL hN
