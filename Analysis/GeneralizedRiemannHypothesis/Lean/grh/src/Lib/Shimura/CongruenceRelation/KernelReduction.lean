import Lib.Shimura.HeckeTower.Model

/-!
# Reduction of isogeny kernels: Cartier density, the tangent line and torsion sections

The file studies how kernels of isogenies of abelian schemes in a family `X : New.ThetaFamily D Z τ`
reduce from a valuation subring of `ℂ` to a field. The file records what goodness of the PEL data
gives at the kernel of a map to a field. It also finds the line of tangent vectors on which `𝓞 E`
acts through `x.baseHom`. From this line it gets a function that detects tangent vectors, and from
that function a parameter `t` whose powers are local equations for the torsion sections.

## Main definitions and results

* `New.Variety.cartier`: a function on a finite flat subgroup scheme (or coset) of a commutative
  group scheme that vanishes at all `K`-points is zero, for `K` an algebraically closed field of
  characteristic zero containing the base ring.
* `New.Variety.ker_factors_of_points`: over a valuation ring with fraction field `ℂ`, a closed
  condition that holds for the torsion complex points of the kernel of a finite flat homomorphism
  holds for all points of the kernel.
* `New.Variety.placeTorsion`: the points of `x.groupScheme` with values in a `k`-algebra `C` that
  are killed by the kernel of `x.baseHom`.
* `New.Variety.ker_factors_of_torsionPoint`: the torsion sections are dense in the kernel of an
  isogeny.
* `New.Variety.exists_isLieLine`: the line of tangent vectors on which `𝓞 E` acts through
  `x.baseHom`.
* `New.Variety.exists_isLocalEquation_pow_sectionCount`: at a local point `z` of the special fibre
  killed by a power of `β - b`, the power `t ^ N` of a parameter `t` is a local equation for a
  family of torsion sections, `N` of which pass through the closed point of `z`.
* `New.Variety.exists_param_pow_card_eq_zero`: the resulting parameter at a point killed by
  `ker x.baseHom`, and a nonzero torsion section that reduces to zero.

Notions from other files:
* `New.ThetaObject`: An object of the family X over a scheme T: a morphism x from T to the base of
  X; `x.groupScheme` is the pull-back of the abelian scheme along it.
* `New.ThetaObject.baseHom`: For an object x over Spec R, the ring homomorphism O_E → R induced by x
  and the structure morphism of the base of the family to Spec O_E.
* `New.AddObj`: A commutative group object.
* `New.specOver`: The spectrum of an R-algebra B, as a scheme over Spec R.
* `New.ValuativeArc`: A valuation ring O with fraction field ℂ, with its generic point Spec ℂ → Spec
  O.

## Relation to the literature

Known; see `Lib.Shimura.AbelianScheme.IsogenyFlatness`,
`Lib.Shimura.CongruenceRelation.HeckeNeighbours`, `Lib.Shimura.Deformation.TangentBound` and
`Lib.Shimura.ThetaModuli.UniversalFamily` for sources.
-/

/-!
## Cartier's theorem on density of characteristic zero points

Over a subring `V` of an algebraically closed field `K` of characteristic `0`, the `K`-points of a
finite flat subgroup scheme of a fixed commutative group scheme are schematically dense in it.
-/

namespace New.Variety

open CategoryTheory AlgebraicGeometry TrivSqZeroExt DualNumber Algebra TensorProduct specOver Over
  Module

variable {V : Type} [CommRing V] {A B : Over (Spec ⟨V⟩)} [AddObj A] [AddObj B]

/-- In characteristic `0`, a derivation of a finite `K`-algebra (given as a section `ρ` of
`R[ε] → R`) takes values in the kernel of every `K`-point `c`. -/
lemma point_snd_eq_zero_of_section {K R : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
    [Module.Finite K R] (c : R →ₐ[K] K) (ρ : R →ₐ[K] R[ε]) (hρ : ∀ r : R, (ρ r).fst = r) (f : R) :
    c (ρ f).snd = 0 := by
  -- `g` has the same derivative as `f` and vanishes at `c`. By induction on `n`, whatever kills
  -- `g ^ n` sends the derivative of `g` into the kernel of `c`.
  let g : R := f - c f • 1
  have h_ann_snd (n : ℕ) (s : R) (hs : s * g ^ n = 0) : c (s * (ρ g).snd) = 0 := by
    induction n generalizing s with
    | zero => simp_all
    | succ n ih =>
      -- Differentiate `s * g ^ (n + 1) = 0` and multiply by `s` to remove the term `(ρ s).snd`.
      have h_der : s * ((n + 1) • (g ^ n * (ρ g).snd)) + (ρ s).snd * g ^ (n + 1) = 0 := by
        simpa [hρ] using congrArg (fun r ↦ (ρ r).snd) hs
      have h_ann : (n + 1) • s * s * (ρ g).snd * g ^ n = 0 := by
        linear_combination s * h_der - (ρ s).snd * hs
      -- By induction `(n + 1) * c (s * (ρ g).snd) ^ 2 = 0`, and the characteristic is `0`.
      have h_sq : ((n + 1 : ℕ) : K) * c (s * (ρ g).snd) ^ 2 = 0 := by
        rw [← ih _ h_ann, nsmul_eq_mul]
        simp only [map_mul, map_natCast]
        ring
      simpa [Nat.cast_add_one_ne_zero] using h_sq
  -- `R` is Artinian, so `g ^ n` is killed by an element `1 - g * y`, which is `1` at `c`.
  obtain ⟨n, y, hy⟩ : ∃ (n : ℕ) (y : R), g ^ (n + 1) * y = g ^ n * 1 :=
    (IsArtinianRing.of_finite K R).exists_pow_succ_smul_dvd g (1 : R)
  have h_at_c : c ((1 - g * y) * (ρ g).snd) = 0 := h_ann_snd n _ (by linear_combination -hy)
  -- `g` and `f` differ by a constant, and `g` vanishes at `c`.
  simpa [g] using h_at_c

/-- **Cartier's theorem.** Let `V` embed in an algebraically closed field `K` of characteristic
`0`, let `S` be a finite flat `V`-algebra and `ι : Spec S ⟶ A` a monomorphism to a commutative
group scheme whose points are stable under `(x, y, z) ↦ x - y + z` (a subgroup or a coset).
Then every nonzero `s : S` is nonzero at some `V`-algebra map `S → K`. -/
lemma cartier (K : Type) [Field.{0} K] [IsAlgClosed K] [CharZero K] [Algebra V K] [FaithfulSMul V K]
    {S : Type} [CommRing S] [Algebra V S] [Module.Finite V S] [Flat V S] {ι : specOver V S ⟶ A}
    (hι_mono : Mono ι)
    (h_coset : ∀ {T : Over (Spec (CommRingCat.of V))} (x y z : T ⟶ specOver V S),
      ∃ w : T ⟶ specOver V S, w ≫ ι = x ≫ ι - y ≫ ι + z ≫ ι)
    {s : S} (hs : s ≠ 0) :
    ∃ o : S →ₐ[V] K, o s ≠ 0 := by
  -- Work on `R = K ⊗[V] S`, where `1 ⊗ s ≠ 0` by flatness. Choose a `K`-point `c` that kills the
  -- annihilator of `1 ⊗ s`. Translation extends a tangent vector at `c` to a derivation of `R`,
  -- which must vanish at `c`; by Nakayama `ker c` is then killed by some `b` with `c b ≠ 0`, so
  -- `1 ⊗ s ∉ ker c`.
  have h_ann : Ideal.torsionOf (K ⊗[V] S) (K ⊗[V] S) (includeRight s) ≠ ⊤ := by
    simpa using (includeRight_injective (FaithfulSMul.algebraMap_injective V K)).ne hs
  obtain ⟨c, hc⟩ : ∃ c : K ⊗[V] S →ₐ[K] K,
      Ideal.torsionOf (K ⊗[V] S) (K ⊗[V] S) (includeRight s) ≤ RingHom.ker c :=
    nullstellensatz_exists_le_ker h_ann
  have no_tangent (v : K ⊗[V] S →ₐ[K] K[ε]) (hv : ∀ r : K ⊗[V] S, (v r).fst = c r)
      (f : K ⊗[V] S) : (v f).snd = 0 := by
    -- `K`-algebra maps `R → R[ε]` are the `R[ε]`-points of `Spec S`.
    let pt : (K ⊗[V] S →ₐ[K] (K ⊗[V] S)[ε]) ≃ (specOver V (K ⊗[V] S)[ε] ⟶ specOver V S) :=
      (AlgHom.liftEquiv ..).symm.trans (.ofBijective _ map_bijective)
    -- `μ` is evaluation at `c` and `ν` the structure map, both extended by `ε ↦ ε`.
    let μ : (K ⊗[V] S)[ε] →ₐ[K] K[ε] := DualNumber.lift ⟨((ofId K K[ε]).comp c, ε), by
      simp [Commute.all]⟩
    let ν : K[ε] →ₐ[K] (K ⊗[V] S)[ε] := DualNumber.lift ⟨(ofId .., ε), by simp [Commute.all]⟩
    -- `ρ` is the universal point minus `c` plus `v`.
    obtain ⟨ρ, hρ⟩ : ∃ ρ : K ⊗[V] S →ₐ[K] (K ⊗[V] S)[ε],
        pt ρ ≫ ι = pt (inlAlgHom ..) ≫ ι - pt ((ofId ..).comp c) ≫ ι + pt (ν.comp v) ≫ ι :=
      pt.surjective.exists.mp (h_coset ..)
    -- Modulo `ε`, `c` and `v` cancel; at `c` (that is, along `μ`) the first two terms cancel.
    have h_mod_ε := specOver.map (fstHom V (K ⊗[V] S) (K ⊗[V] S)) ≫= hρ.trans (sub_add ..)
    have h_along_μ := specOver.map (μ.restrictScalars V) ≫= hρ
    -- `TensorProduct.algebraMap_apply` stays out: with it the call no longer reduces `h_along_μ`.
    simp +zetaDelta [sub_eq_zero_of_eq, cancel_mono, map_bijective.injective.eq_iff,
      AlgHom.ext_iff, hv, -TensorProduct.algebraMap_apply, map_comp_assoc, algebraMap_eq_inl',
      lift_apply_apply, AddGrpObj.comp_sub, comp_add] at h_mod_ε h_along_μ
    have h_fst : ∀ x : S, (ρ (1 ⊗ₜ[V] x)).fst = 1 ⊗ₜ[V] x := h_mod_ε
    have h_at_c : ∀ x : S, inl (c (ρ (1 ⊗ₜ[V] x)).fst) + inl (c (ρ (1 ⊗ₜ[V] x)).snd) * ε =
        inl (c (1 ⊗ₜ[V] x)) + inl (v (1 ⊗ₜ[V] x)).snd * ε := h_along_μ
    -- `ι` is a monomorphism, so these are identities on the elements `1 ⊗ x`: `ρ` is a section of
    -- `R[ε] → R`, and its value at `c` is `v`.
    have h_section : (fstHom ..).comp ρ = 1 := ext_ring (AlgHom.ext h_fst)
    have hv_eq : v = μ.comp ρ := ext_ring (AlgHom.ext fun x ↦ by
      simp [μ, h_at_c, hv, TrivSqZeroExt.ext_iff, lift_apply_apply, algebraMap_eq_inl'])
    -- `(v f).snd = c (ρ f).snd`, as `v = μ ∘ ρ`
    simpa [hv_eq, μ, lift_apply_apply, algebraMap_eq_inl'] using
      point_snd_eq_zero_of_section c ρ (AlgHom.congr_fun h_section) f
  refine ⟨(AlgHom.liftEquiv ..).symm c, fun hcs ↦ ?_⟩
  obtain ⟨b, hb, hcb⟩ : ∃ b ∈ (⊥ : Ideal (K ⊗[V] S)).colon (RingHom.ker c), c b ≠ 0 :=
    exists_mem_colon_of_tangent (x := c) rfl bot_le fun v hv _ ↦ no_tangent v hv
  -- If `1 ⊗ s ∈ ker c`, then `b` kills it, so `b` lies in its annihilator and `c b = 0`.
  exact hcb (hc ((Ideal.mem_torsionOf_iff _ _).mpr
    ((Submodule.mem_bot _).mp (Submodule.mem_colon.mp hb (includeRight s) hcs))))

/-- Let `V` be a valuation ring with fraction field `ℂ` (a `ValuativeArc`) and `ψ : A ⟶ B` a finite
flat homomorphism of commutative group schemes over `V`, with `B` separated. Let `r : A.left ⟶ Y`
be a morphism of schemes and `j : Z ⟶ Y` a closed immersion. If `r` maps every torsion `ℂ`-point of
the kernel of `ψ` into `Z`, then it maps every point `z : T ⟶ A` of the kernel into `Z`. -/
lemma ker_factors_of_points [ValuativeArc V] [IsSeparated B.hom] (ψ : A ⟶ B) [IsAdditive ψ]
    [IsFinite ψ.left] [Flat ψ.left] {Y Z : Scheme} {j : Z ⟶ Y}
    [IsClosedImmersion (X := Z) (Y := Y) j]
    (r : A.left ⟶ Y) (hr : ∀ s : specOver V ℂ ⟶ A,
      IsOfFinAddOrder s → s ≫ ψ = 0 → ∃ l : (specOver V ℂ).left ⟶ Z, l ≫ j = s.left ≫ r)
    ⦃T : Over (Spec (CommRingCat.of V))⦄ (z : T ⟶ A) (hz : z ≫ ψ = 0) :
    ∃ l : T.left ⟶ Z, l ≫ j = z.left ≫ r := by
  -- The kernel of `ψ` is `Spec S` with `S` finite flat. The ideal `I` of the locus where `r` maps
  -- into `Z` vanishes at all `ℂ`-points, so is zero by Cartier's theorem.
  obtain ⟨S, ι, hS_finite, hS_flat, hι_closed, hι, h_ker⟩ :=
    exists_finite_kernel_ring (f := ψ) inferInstance
  obtain ⟨z', hz'⟩ := h_ker z hz
  -- `hI`: a ring map `γ` out of `S` kills `I` iff `ι ≫ r` maps the point `Spec γ` into `Z`.
  obtain ⟨I, -, hI⟩ := exists_ideal_le_ker_iff_factors j (ι.left ≫ r)
  have h_coset {T : Over (Spec (CommRingCat.of V))} (x y w : T ⟶ specOver V S) :
      ∃ u : T ⟶ specOver V S, u ≫ ι = x ≫ ι - y ≫ ι + w ≫ ι :=
    h_ker _ (by simp [hι, add_comp, AddGrpObj.sub_comp])
  have h_pts (o : S →ₐ[V] ℂ) : I ≤ RingHom.ker o := by
    -- The multiples of the point `o` are among the finitely many `ℂ`-points of the kernel.
    have h_fin : IsOfFinAddOrder (specOver.map o ≫ ι) := by
      refine finite_multiples.mp
        ((Set.finite_range fun o' : S →ₐ[V] ℂ ↦ specOver.map o' ≫ ι).subset ?_)
      rintro _ ⟨m, rfl⟩
      obtain ⟨u, hu⟩ := h_ker (m • (specOver.map o ≫ ι)) (by simp [hι, nsmul_comp])
      -- every `ℂ`-point of `Spec S` comes from a `V`-algebra map `S → ℂ`
      obtain ⟨o', rfl⟩ := map_bijective.surjective u
      exact ⟨o', hu⟩
    exact (hI o.toRingHom).mpr (hr _ h_fin (by simp [hι]))
  have hI_zero : I ≤ RingHom.ker (RingHom.id S) := fun s hs ↦ by
    by_contra hs_ne
    obtain ⟨o, ho⟩ := cartier ℂ (mono_of_mono_left ι) h_coset hs_ne
    exact ho (h_pts o hs)
  obtain ⟨l, hl⟩ := (hI _).mp hI_zero
  exact ⟨z'.left ≫ l, by simp [hl, ← hz']⟩

end New.Variety

/-!
## Goodness of the PEL data at the kernel of a map to a field

`New.Variety.ringChar_prime_and_exists_isCoprime_of_isGoodAt_ker` states what `New.PEL.IsGoodAt`
gives when the ideal is the kernel of a map `ρ` from `𝓞 E` to a field, in the form used by the
deformation arguments. `D.β` is an element with `star D.β = 1 - D.β`, and `D.level` is the level of
the PEL data `D`.
-/

section GoodPrimeArithmetic

open Ideal CharP RingHom Pointwise

/-- Let `D` be PEL data over the CM field `E` with distinguished element `D.β` and level `D.level`,
and let `ρ : 𝓞 E → k` be a map to a field whose kernel `𝔭` is good for `D` in the sense of
`PEL.IsGoodAt`. Then (a) the characteristic `p` of `k` is a prime; (b) `𝔭 ≠ 0`, and there are
`c ≠ 0` in `𝔭` and `t ≡ 1` modulo `𝔭` with `t 𝔭 ⊆ (c)`; (c) for some integer `b`, `β - b` lies in
`𝔭`, the elements `β - b` and `star β - b` are coprime, and the ideal `(D.level)` together with
`𝔭 · (p, star β - b)` generates the unit ideal. -/
lemma New.Variety.ringChar_prime_and_exists_isCoprime_of_isGoodAt_ker {E : Type} [Field E]
    [CMBase E] {D : PEL E} {k : Type*}
    [Field k] {ρ : NumberField.RingOfIntegers E →+* k} (h_good : D.IsGoodAt (ker ρ)) :
    -- (a)
    Fact (ringChar k).Prime ∧
    -- (b)
    (ker ρ ≠ ⊥ ∧
     ∃ c : NumberField.RingOfIntegers E,
       ρ c = 0 ∧ c ≠ 0 ∧ ∃ t : NumberField.RingOfIntegers E, t - 1 ∈ ker ρ ∧ t • ker ρ ≤ span {c}) ∧
    -- (c)
    ∃ b : ℤ,
      ρ (D.β - b) = 0 ∧
      IsCoprime (D.β - b) (star D.β - b) ∧
      span {D.level} ⊔ ker ρ * span {↑(ringChar k), star D.β - b} = ⊤ := by
  -- `D.IsGoodAt (ker ρ)` gives a prime `p` and an integer `b` with `p` and `β - b` in `ker ρ`.
  obtain ⟨-, p, b, hp, hp_mem, hβ_mem, h_coprime, h_level, -⟩ := h_good
  have char_eq : ringChar k = p := ringChar_of_prime_eq_zero hp (by simpa using hp_mem)
  subst char_eq
  have ker_ne_bot : ker ρ ≠ ⊥ := fun h_bot ↦ hp.ne_zero (by simpa [h_bot] using hp_mem)
  refine ⟨⟨hp⟩, ⟨ker_ne_bot, ?_⟩, b, hβ_mem, h_coprime, h_level⟩
  -- `c` is a uniformiser: it generates `ker ρ` modulo its square.
  obtain ⟨c, hc⟩ : ∃ c : NumberField.RingOfIntegers E, ker ρ • ker ρ ⊔ span {c} = ker ρ :=
    IsDedekindDomain.exists_sup_span_eq (ker ρ).smul_le_right (by simpa using ker_ne_bot)
  have hc_ne_zero : c ≠ 0 := by
    rintro rfl
    simp_all [ker_ne_top]
  refine ⟨c, hc.le (mem_sup_right (mem_span_singleton_self c)), hc_ne_zero, ?_⟩
  -- Nakayama: some `t ≡ 1` modulo `ker ρ` multiplies `ker ρ` into `(c)`.
  exact Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup .of_finite le_rfl (by order)

end GoodPrimeArithmetic

/-!
## Torsion sections, the tangent line and local equations

This section studies how kernels of isogenies of the abelian schemes of a family
`X : New.ThetaFamily D Z τ` reduce. In the statements about torsion sections, `y` is an object over
a valuation subring `V` of `ℂ` with a full structure `e : y.FullLevelStructure`, which gives
sections `e.torsionPoint s` of `y.groupScheme` over `V`. These are injective and `𝓞 E`-linear in
`s : AdelicTorsion E D.Index`, and over `ℂ` every torsion point is one of them. In the statements
about reduction, the object `x` over the field `k` is the pull-back of `y` along `φ : V →+* k`, and
`w` in the docstrings, except that of `torsionReduction_eq_iff`, stands for the ideal
`ker x.baseHom` of `𝓞 E`. The lemmas on tangent vectors allow a local base ring `R` with a map to
`k`.

The idea: the tangent vectors at a point of the kernel of an element `d` of `𝓞 E` that is coprime to
`star β - b` and zero in `k` lie on one line, so a single function detects them. For
`d = (β - b) ^ (M + 1)` this function gives a local equation for the torsion sections through the
point.
-/

namespace New.Variety

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory NumberField Over Category Submodule
  CommRingCat RingHom Finset TrivSqZeroExt DualNumber AddMonObj Module specOver
  Matrix

attribute [local instance low] Fintype.ofFinite

variable {E : Type} [Field E] [CMBase E]
  {D : PEL E} {V : ValuationSubring ℂ} {k : Type} [Field k]
  {φ : V →+* k} {Z : Scheme} {τ : Z ⟶ Spec (CommRingCat.of (𝓞 E))} {X : ThetaFamily D Z τ}
  {x : ThetaObject X (Spec (CommRingCat.of k))}
  {y : ThetaObject X (Spec (CommRingCat.of V))} (e : y.FullLevelStructure)
  {C C' : Type} [CommRing C] [Algebra k C] [CommRing C'] [Algebra k C'] (G : C →ₐ[k] C')

variable (x C) in
/-- For an object `x` over a field `k` and a `k`-algebra `C`, the `𝓞 E`-module of `C`-points of
`x.groupScheme` killed by the kernel of `x.baseHom`. -/
noncomputable abbrev placeTorsion : Submodule (𝓞 E) (specOver k C ⟶ x.groupScheme) :=
  torsionBySet (𝓞 E) (specOver k C ⟶ x.groupScheme) (ker x.baseHom)

/-- The map from `placeTorsion x C` to `placeTorsion x C'` induced by a homomorphism `G : C → C'` of
`k`-algebras: a point `Spec C ⟶ x.groupScheme` is composed with `Spec G : Spec C' ⟶ Spec C`. -/
noncomputable def placeTorsionMap : placeTorsion x C →ₗ[𝓞 E] placeTorsion x C' where
  toFun := fun ⟨y, hy⟩ ↦ ⟨specOver.map G ≫ y, by simp_all [← ModuleObj.comp_smul]⟩
  map_add' := by simp [comp_add]
  map_smul' := by simp

@[simp]
lemma placeTorsionMap_comp {C'' : Type} [CommRing C''] [Algebra k C''] (ψ : C'' →ₐ[k] C)
    (y : placeTorsion x C'') :
    placeTorsionMap (G.comp ψ) y = placeTorsionMap G (placeTorsionMap ψ y) :=
  Subtype.ext (map_comp_assoc ..).symm

/-- The torsion sections `e.torsionPoint s` of the object `y` over the valuation subring `V` of `ℂ`
(with full structure `e`) are dense in the kernel of an isogeny `ψ`: if `r` maps each of them that
lies in the kernel into the closed subscheme `j : W ⟶ Y.left`, then it maps every point `z` of the
kernel into it. -/
lemma ker_factors_of_torsionPoint {A : Over (Spec (.of V))} [IsAbelianScheme A]
    (ψ : y.groupScheme ⟶ A) [IsIsogeny ψ] {Y : Over (Spec (.of V))} {W : Scheme} {j : W ⟶ Y.left}
    (r : y.groupScheme ⟶ Y) [IsClosedImmersion j]
    (hr : ∀ s : AdelicTorsion E D.Index, e.torsionPoint s ≫ ψ = 0 →
      ∃ l : Spec (.of V) ⟶ W, l ≫ j = (e.torsionPoint s ≫ r).left)
    ⦃T : Over (Spec (.of V))⦄ (z : T ⟶ y.groupScheme) (hz : z ≫ ψ = 0) :
    ∃ l : T.left ⟶ W, l ≫ j = (z ≫ r).left := by
  -- It suffices to treat torsion points over `ℂ`; by counting, they come from the sections
  -- `e.torsionPoint t`.
  refine ker_factors_of_points ψ r.left (fun s hs_tors hs ↦ ?_) z hz
  -- `x_gen` is the object over `ℂ` obtained from `y` along the generic point of `Spec V`.
  obtain ⟨x_gen, hx_gen⟩ := y.exists_isPullbackAlong ValuativeArc.genericPt
  -- `p` identifies `ℂ`-points of `x_gen.groupScheme` with points of `y.groupScheme` over `ℂ`
  let p : (Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ x_gen.groupScheme) ≃ₗ[𝓞 E]
      ((Over.map ValuativeArc.genericPt).obj (Over.mk (𝟙 _)) ⟶ y.groupScheme) :=
    hx_gen.isGroupBaseChange.pointEquiv (T := Over.mk (𝟙 _))
  have h_inj : Function.Injective (hx_gen.isGroupBaseChange.pullSection ∘ₗ e.torsionPoint) :=
    p.symm.injective.comp (bijective_restrict_genericPt.injective.comp e.injective)
  obtain ⟨m, hm, hms⟩ := hs_tors.exists_nsmul_eq_zero
  have h_tors : m • p.symm s = 0 :=
    calc m • p.symm s = p.symm (m • s) := (map_nsmul p.symm m s).symm
      _ = p.symm 0 := congrArg p.symm hms
      _ = 0 := map_zero p.symm
  obtain ⟨t, ht⟩ := x_gen.exists_apply_eq_of_torsion h_inj (p.symm s) ⟨m, hm.ne', h_tors⟩
  -- `p.symm` is injective, so `s` is the section `e.torsionPoint t` read over `ℂ`
  obtain rfl : toUnit _ ≫ e.torsionPoint t = s := p.symm.injective ht
  obtain ⟨l, hl⟩ := hr t (bijective_restrict_genericPt.injective hs)
  exact ⟨ValuativeArc.genericPt ≫ l, by simp [hl, ValuativeArc.genericPt_eq]⟩

/-- Let `x` be an object over `R` and `k` an `R`-algebra. A tangent vector at `0` is a point of
`x.groupScheme` over `k[ε]` that reduces to `0` over `k`. The map `L` is a line of tangent vectors
on which `𝓞 E` acts through `ρ`, and into which `star β - b` maps all tangent vectors. Here `β` is
`D.β` and `b` is an integer; in `exists_isLieLine`, `ρ` is `x.baseHom` followed by `R → k`, with
`ρ (D.β - b) = 0`. -/
structure IsLieLine {R : Type} [CommRing R] [Algebra R k] (x : ThetaObject X (Spec (.of R)))
    (ρ : 𝓞 E →+* k) (b : ℤ) (L : k →+ (specOver R k[ε] ⟶ x.groupScheme)) : Prop where
  /-- The generator `L 1` is not zero. -/
  apply_one_ne_zero : L 1 ≠ 0
  /-- Each `L m` is a tangent vector at `0`. -/
  fstHom_comp (m : k) : specOver.map (fstHom R k k) ≫ L m = 0
  /-- The ring `𝓞 E` acts on the line through `ρ`. -/
  smul_apply (a : 𝓞 E) (m : k) : a • L m = L (ρ a * m)
  /-- The substitution `ε ↦ m ε` takes `L 1` to `L m`. -/
  scale_comp (m : k) :
    specOver.map ((TrivSqZeroExt.map (m • LinearMap.id)).restrictScalars R) ≫ L 1 = L m
  /-- The element `star β - b` maps every tangent vector at `0` into the line. -/
  exists_smul_eq (v : specOver R k[ε] ⟶ x.groupScheme)
    (hv : specOver.map (fstHom R k k) ≫ v = 0) : ∃ m : k, (star D.β - b) • v = L m

/-- Let `x` be a theta object of the family `X` over a local ring `R`, that is, a point of the base
of `X`. Its group scheme `x.groupScheme` is the pulled-back abelian scheme with its `𝓞 E`-action,
and `k` is an `R`-algebra that is a field. Let `ρ : 𝓞 E → k` be the composite of `x.baseHom` with
`R → k`, and let `b` be an integer with `ρ (D.β - b) = 0`, where `D.β` is the element `β` of the PEL
datum `D`. Then there is an additive map `L` from `k` to the tangent vectors at `0` of
`x.groupScheme` over `k` (points over `k[ε]` reducing to `0`) that is a line on which `𝓞 E` acts
through `ρ` and into which `star β - b` maps all tangent vectors. -/
lemma exists_isLieLine {R : Type} [CommRing R] [IsLocalRing R] [Algebra R k]
    (x : ThetaObject X (Spec (.of R))) {ρ : 𝓞 E →+* k} (hρ : ρ = (algebraMap R k).comp x.baseHom)
    {b : ℤ} (hb : ρ (D.β - b) = 0) :
    ∃ L : k →+ (specOver R k[ε] ⟶ x.groupScheme), IsLieLine x ρ b L := by
  -- By the signature condition of the family there are coordinates `z` at `0` in which `a` acts on
  -- tangent vectors by the matrix `m a`. The vector `Y` is a common eigenvector with a unit
  -- coordinate `Y l`, and `m (star β - b) - (β - b) = Y ⊗ ξ` has its image on the line spanned by
  -- `Y`, which is the line asked for.
  obtain ⟨V, z, m, ⟨h_chart, h_jac⟩, Y, ξ, l, hY_unit, hY_eigen, h_rank⟩ := X.signature b x
  let r : specOver R k ⟶ specOver R k[ε] := specOver.map (fstHom R k k)
  let p := x.isGroupBaseChange.pointEquiv (T := specOver R k[ε])
  have h_tiny {v : specOver R k[ε] ⟶ x.groupScheme} :
      IsInfinitesimal (ofHom (fstHom k k k).toRingHom) (p v) ↔ r ≫ v = 0 :=
    .trans (x.isGroupBaseChange.pointEquiv.map_eq_zero_iff : _ ↔ IsInfinitesimal _ v)
      (eq_zero_iff_factors_zero_section.trans (.symm eq_zero_iff_factors_zero_section))
  -- `h_lin`: on tangent vectors the coordinates are additive and turn `a • ·` into `m a`
  obtain ⟨h_zero, h_lin⟩ := h_jac (φ := ofHom (algebraMap R k[ε])) rfl
  have : IsSqZeroExt (ofHom (fstHom k k k).toRingHom) := isSqZeroExt_fstHom
  replace h_lin := h_lin (ψ := ofHom (fstHom k k k).toRingHom)
  -- `Z a` is the unique tangent vector with coordinates `a Y ε`
  have h_exu (a : k) : ∃! v, r ≫ v = 0 ∧ tangentCoords z (p v) = (Y · • inr a) := by
    simpa only [h_tiny] using p.bijective.existsUnique_iff.1
      (h_chart.existsUnique_tangentCoords_eq h_zero isSqZeroExt_fstHom (Y · • inr a) (by simp))
  choose Z hZ_tan hZ_dv hZ_uniq using by simpa only [ExistsUnique, and_assoc, and_imp] using h_exu
  have hZ_add (a c : k) : Z a + Z c = Z (a + c) := by
    refine hZ_uniq _ _ (by simp [hZ_tan, comp_add]) (funext fun i ↦ ?_)
    simp [(h_lin (h_tiny.2 (hZ_tan a))).2 _ (h_tiny.2 (hZ_tan c)), hZ_dv, TrivSqZeroExt.ext_iff]
  refine ⟨.mk' Z fun a c ↦ (hZ_add a c).symm, ?_, hZ_tan, fun c a ↦ ?_, fun a ↦ ?_, fun v hv ↦ ?_⟩
  · -- the `l`-th coordinate of `Z 1` is a unit times `ε`
    exact ne_of_apply_ne (fun v ↦ tangentCoords z (p v) l) (by simp [hZ_dv, hY_unit,
      TrivSqZeroExt.ext_iff])
  · -- `Y` is an eigenvector of `m c` with eigenvalue `x.baseHom c`
    refine hZ_uniq _ _ (by simp [hZ_tan]) (funext fun i ↦ ?_)
    simpa [h_lin (h_tiny.2 (hZ_tan a)), hZ_dv, hρ, smul_smul, sum_smul, map_smul, mul_comm (Y _),
      mul_comm a, dotProduct, mulVec, ← Algebra.smul_def, TrivSqZeroExt.ext_iff, fst_sum,
      snd_sum] using! congrArg (· • a) (congrFun (hY_eigen c) i)
  · -- the substitution `ε ↦ a ε` fixes the point over `k` and multiplies the coordinates by `a`
    refine hZ_uniq _ _ (.trans ?_ (hZ_tan 1)) (funext fun i ↦ ?_)
    · exact (assoc ..).symm.trans (eq_whisker (by simp [r, OverMorphism.ext_iff, specOver.map,
        ← Spec.map_comp, Spec.map_inj, CommRingCat.hom_ext_iff, RingHom.ext_iff]) _)
    · erw [IsEtaleChart.tangentCoords_comp (z := z) h_zero (h_tiny.2 (hZ_tan 1))
        ((map x).map (specOver.map _)) rfl]
      simp [hZ_dv, TrivSqZeroExt.ext_iff]
  · -- `β - b` vanishes in `k`, so `star β - b` acts on coordinates as `u ↦ ⟨ξ, u⟩ Y`
    refine ⟨∑ j, ξ j • snd (tangentCoords z (p v) j),
      hZ_uniq _ _ (by simp [r, hv]) (funext fun i ↦ ?_)⟩
    have h_fst : ∀ j, fst (tangentCoords z (p v) j) = 0 :=
      h_chart.map_tangentCoords_eq_zero h_zero (h_tiny.2 hv)
    have hb_zero : algebraMap R k ((Spec.preimage (x ≫ τ)).hom (D.β - b)) = 0 := by
      simpa only [hρ, ThetaObject.baseHom] using! hb
    simp [h_lin (h_tiny.2 hv), map_smul, smul_sum, h_fst, eq_add_of_sub_eq h_rank,
      -map_sub, hb_zero, vecMulVec, dotProduct, mulVec, algebraMap_eq_inl', ← Algebra.smul_def,
      TrivSqZeroExt.ext_iff, fst_sum, snd_sum]

/-- Let `x` be a theta object over a ring `R`, let `k` be an `R`-algebra that is a field, and let
`ρ : 𝓞 E → k` and an integer `b` be such that `L` is a line of tangent vectors at `0` of
`x.groupScheme` over `k` on which `𝓞 E` acts through `ρ` and into which `star D.β - b` maps all
tangent vectors. Let `d` in `𝓞 E` satisfy `ρ d = 0` and be coprime to `star D.β - b`, and let
`ι : Spec S ⟶ x.groupScheme` be the kernel of `d`: a monomorphism over `Spec R` that is killed by
`d` and through which every point killed by `d` factors. Then at each `k`-point `o` of `Spec S`
there is a function `T` in `S` such that every tangent vector at `o` (a `k[ε]`-point reducing to
`o`) along which `T` has zero derivative is itself zero. -/
lemma IsLieLine.exists_detects_tangent {R : Type} [CommRing R] [Algebra R k]
    {x : ThetaObject X (Spec (.of R))} {ρ : 𝓞 E →+* k} {b : ℤ}
    {L : k →+ (specOver R k[ε] ⟶ x.groupScheme)} (hL : IsLieLine x ρ b L) {d : 𝓞 E} (hd : ρ d = 0)
    (h_coprime : IsCoprime d (star D.β - b)) {S : Type} [CommRing S] [Algebra R S]
    (ι : specOver R S ⟶ x.groupScheme) [Mono ι.left] (h_ker : d • ι = 0)
    (h_lift : ∀ ⦃W : Over (Spec (.of R))⦄ (w : W ⟶ x.groupScheme), d • w = 0 →
      ∃ u : W ⟶ specOver R S, u ≫ ι = w)
    (o : S →ₐ[R] k) :
    ∃ T : S, ∀ v : S →ₐ[R] k[ε],
      (∀ a : S, (v a).fst = o a) → (v T).snd = 0 → ∀ a : S, (v a).snd = 0 := by
  -- Every tangent vector of `Spec S` at `o` is a multiple of one vector `v₀`.
  obtain ⟨r, c, hc⟩ : ∃ r c : 𝓞 E, r * d + c * (star D.β - b) = 1 := h_coprime
  have h_tors (W : Over (Spec (.of R))) (w : W ⟶ specOver R S) : d • w ≫ ι = 0 := by
    simpa using w ≫= h_ker
  -- `p` is the zero tangent vector at `o`, and `v₀` its translate by the generator `L 1`.
  let p : specOver R k[ε] ⟶ x.groupScheme := specOver.map ((inlAlgHom R k k).comp o) ≫ ι
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : S →ₐ[R] k[ε], specOver.map v₀ ≫ ι = L 1 + p :=
    specOver.map_bijective.surjective.exists.mp
      (h_lift (L 1 + p) (by simp [p, hL.smul_apply, hd, h_tors]))
  -- `T` is any function with nonzero derivative along `v₀`, if there is one
  obtain ⟨T, hT⟩ : ∃ T : S, (v₀ T).snd = 0 → ∀ a : S, (v₀ a).snd = 0 := by
    by_cases h_all : ∀ a : S, (v₀ a).snd = 0
    · exact ⟨0, fun _ ↦ h_all⟩
    · obtain ⟨T, hT_ne⟩ := not_forall.mp h_all
      exact ⟨T, fun hT_zero ↦ absurd hT_zero hT_ne⟩
  refine ⟨T, fun v hv hvT a ↦ ?_⟩
  -- As `c * (star β - b) = 1` on points of `Spec S`, `v - p = L m` for some `m`: `v = m • v₀`.
  -- (The calls below leave out `Spec.map_comp`: with `← Spec.map_comp_assoc` it makes simp loop.)
  have h_tangent : specOver.map (fstHom R k k) ≫ (c • (specOver.map v ≫ ι - p)) = 0 := by
    simp [p, hv, specOver.map, OverMorphism.ext_iff, cancel_mono, Spec.map_inj,
      CommRingCat.hom_ext_iff, RingHom.ext_iff, AddGrpObj.comp_sub, ← Spec.map_comp_assoc,
      sub_eq_zero_of_eq, -Spec.map_comp]
  obtain ⟨m, hm⟩ := hL.exists_smul_eq (c • (specOver.map v ≫ ι - p)) h_tangent
  -- With `σ` the substitution `ε ↦ m ε`, `hm` says `(1 - r d) • (v - p) + σ ≫ p = σ ≫ v₀` on `ι`.
  have h_v_eq : (1 - r * d) • (specOver.map v ≫ ι - p) +
        specOver.map ((TrivSqZeroExt.map (m • LinearMap.id)).restrictScalars R) ≫ p =
      specOver.map ((TrivSqZeroExt.map (m • LinearMap.id)).restrictScalars R) ≫
        specOver.map v₀ ≫ ι := by
    rw [← hL.scale_comp, smul_smul, mul_comm, eq_sub_of_add_eq' hc, ← add_left_inj, ← comp_add,
      ← hv₀] at hm
    exact hm
  have h_scale : ∀ a : S, (v a).fst = (v₀ a).fst ∧ (v a).snd = m * (v₀ a).snd := by
    simpa [sub_smul, mul_smul, smul_sub, h_tors, p, sub_add, specOver.map, OverMorphism.ext_iff,
      cancel_mono, Spec.map_inj, CommRingCat.hom_ext_iff, RingHom.ext_iff, TrivSqZeroExt.ext_iff,
      ← Spec.map_comp_assoc, sub_eq_zero_of_eq, -Spec.map_comp] using h_v_eq
  -- `m * (v₀ T).snd = 0`, so either `m = 0` or `v₀` is the zero tangent vector
  obtain ⟨-, hT_snd⟩ := h_scale T
  obtain ⟨-, ha_snd⟩ := h_scale a
  rw [hT_snd, mul_eq_zero] at hvT
  rw [ha_snd, mul_eq_zero]
  exact hvT.imp_right fun h ↦ hT h a

/-- Let `y` be an object over a local ring `R`, and let `ρ : 𝓞 E → k` be `y.baseHom` followed by
`R → k`. Let `ρ` send `β` to the integer `b`, with `β - b` coprime to `star β - b`. Let
`ι : Spec S → y.groupScheme` be the kernel of `(β - b) ^ (M + 1)`: a closed immersion killed by it,
through which every point that it kills factors. Let `o` be a `k`-point of `Spec S`. Some function
`T` on `Spec S` has nonzero derivative along every nonzero tangent vector at `o`. -/
lemma exists_detecting_tangent_vectors {R S : Type} [CommRing R] [IsLocalRing R] [Algebra R k]
    [CommRing S] [Algebra R S] (y : ThetaObject X (Spec (.of R))) {ρ : 𝓞 E →+* k}
    (hρ : ρ = (algebraMap R k).comp y.baseHom) {b : ℤ} (hb : ρ (D.β - b) = 0)
    (h_coprime : IsCoprime (D.β - b) (star D.β - b)) {M : ℕ} {ι : specOver R S ⟶ y.groupScheme}
    [IsClosedImmersion ι.left] (ι_ker : ι ≫ ((D.β - b) ^ (M + 1) • 𝟙 y.groupScheme) = 0)
    (ι_lift : ∀ ⦃W : Over (Spec (.of R))⦄ (w : W ⟶ y.groupScheme),
      w ≫ ((D.β - b) ^ (M + 1) • 𝟙 y.groupScheme) = 0 → ∃ u : W ⟶ specOver R S, u ≫ ι = w)
    (o : S →ₐ[R] k) :
    ∃ T : S, ∀ v : S →ₐ[R] k[ε],
      (∀ a : S, (v a).fst = o a) → (v T).snd = 0 → ∀ a : S, (v a).snd = 0 := by
  obtain ⟨L, hL⟩ := exists_isLieLine y hρ hb
  have h_pow : ρ ((D.β - b) ^ (M + 1)) = 0 := by simp [pow_succ, hb]
  exact hL.exists_detects_tangent h_pow h_coprime.pow_left ι (by simpa using ι_ker)
    (fun W w hw ↦ ι_lift w (by simp [hw])) o

/-- A point `p` of a group scheme `A` over `R`, with values in a ring `B`, vanishes along the ring
map `G : B →+* B'`: the point of `A` with values in `B'` induced by `G` is zero. -/
def VanishesAlong {R B B' : Type} [CommRing R] [CommRing B] [CommRing B']
    {A : Over (Spec (.of R))} [AddObj A] {s : Spec (.of B) ⟶ Spec (.of R)} (p : Over.mk s ⟶ A)
    (G : B →+* B') : Prop :=
  (homMk (specMap G) : Over.mk (specMap G ≫ s) ⟶ Over.mk s) ≫ p = 0

/-- Vanishing along `G` may be tested on any morphism `a` over `R` given by `G`. -/
lemma vanishesAlong_iff {R B B' : Type} [CommRing R] [CommRing B] [CommRing B']
    {A : Over (Spec (.of R))} [AddObj A] {s : Spec (.of B) ⟶ Spec (.of R)}
    {s' : Spec (.of B') ⟶ Spec (.of R)} {p : Over.mk s ⟶ A} {G : B →+* B'}
    (a : Over.mk s' ⟶ Over.mk s) (ha : a.left = specMap G) :
    VanishesAlong p G ↔ a ≫ p = 0 := by
  simp [VanishesAlong, eq_zero_iff_factors_zero_section, ha]

/-- For a full structure `e` on the object `y` over `V`, a family `c` of torsion vectors and a
point `p` of `y.groupScheme`, the number of indices `i` for which the torsion section
`e.torsionPoint (c i)` passes through `p`. -/
noncomputable def sectionCount {J : Type} (c : J → AdelicTorsion E D.Index)
    {T : Over (Spec (.of V))} (p : T ⟶ y.groupScheme) : ℕ :=
  Nat.card {i : J // toUnit T ≫ e.torsionPoint (c i) = p}

/-- Let `e` be a full structure on the object `y` over `V` and `z` a point of `y.groupScheme` with
values in a ring `B`. The element `f` of `B` is a local equation at `z` for the closure of the
torsion sections `e.torsionPoint (c i)`, as seen by isogenies `ψ` out of `y.groupScheme` and ring
maps `G` out of `B`. -/
structure IsLocalEquation {J : Type} (c : J → AdelicTorsion E D.Index) {B : Type} [CommRing B]
    {s : Spec (.of B) ⟶ Spec (.of V)} (z : Over.mk s ⟶ y.groupScheme) (f : B) : Prop where
  /-- If `υ` maps `u` to `z` and the torsion of `ker ψ` into the family `c`, and `ψ u` vanishes
  along `G`, then `G f = 0`. -/
  map_eq_zero {A : Over (Spec (.of V))} [IsAbelianScheme A] (ψ : y.groupScheme ⟶ A) [IsIsogeny ψ]
    {υ : 𝓞 E} {u : Over.mk s ⟶ y.groupScheme} (hu : υ • u = z)
    (hυ : ∀ t : AdelicTorsion E D.Index, e.torsionPoint t ≫ ψ = 0 → υ • t ∈ Set.range c)
    {B' : Type} [CommRing B'] {G : B →+* B'} (hG : VanishesAlong (u ≫ ψ) G) : G f = 0
  /-- If `ψ` kills the sections `e.torsionPoint (c i)` and `G f = 0`, then `ψ z` vanishes along
  `G`. -/
  vanishesAlong {A : Over (Spec (.of V))} [IsAbelianScheme A] (ψ : y.groupScheme ⟶ A)
    [IsIsogeny ψ] (hψ : ∀ i : J, e.torsionPoint (c i) ≫ ψ = 0) {B' : Type} [CommRing B']
    {G : B →+* B'} (hG : G f = 0) : VanishesAlong (z ≫ ψ) G

/-- Let `O` be a domain and `θ j` distinct sections of a finite type `O`-algebra `S` through a point
`o`, and let `T` have nonzero derivative along every nonzero tangent vector at `o`. Let `χ` send the
elements not vanishing at `o` to units, and let `g` divide each `χ (θ j T - T)`. If `a` vanishes
along the `θ j`, `j ∈ s`, then `g ^ #s` divides `χ a`. -/
lemma pow_card_dvd_of_sections {O S B J : Type*} [CommRing O] [IsDomain O] [CommRing S]
    [Algebra O S] [Algebra.FiniteType O S] [Algebra O k] [CommRing B] {o : S →ₐ[O] k} {T : S}
    (hT : ∀ v : S →ₐ[O] k[ε], (∀ a : S, (v a).fst = o a) → (v T).snd = 0 → ∀ a : S, (v a).snd = 0)
    {θ : J → S →ₐ[O] O} (hθ : θ.Injective) (hθo : ∀ (j : J) (a : S), algebraMap O k (θ j a) = o a)
    {χ : S →+* B} (hχ : ∀ a : S, o a ≠ 0 → IsUnit (χ a)) {g : B}
    (hg : ∀ j : J, g ∣ χ (algebraMap O S (θ j T) - T)) (s : Finset J) (a : S)
    (ha : ∀ j ∈ s, θ j a = 0) :
    g ^ #s ∣ χ a := by
  classical
  induction s using Finset.induction_on generalizing a with
  | empty => simp
  | insert j s hj ih =>
    -- By Nakayama, `ϖ` generates `ker (θ j)` near `o`: some `ρ` with `o ρ ≠ 0` multiplies
    -- `ker (θ j)` into `(ϖ)`.
    set ϖ : S := algebraMap O S (θ j T) - T with hϖ
    obtain ⟨ρ, hρ, hρo⟩ : ∃ ρ ∈ (Ideal.span {ϖ}).colon (ker (θ j)), o ρ ≠ 0 := by
      refine exists_mem_colon_of_tangent (AlgHom.ext (hθo j)) ?_ fun v hv h_ker ↦ hT v hv ?_
      · show Ideal.span {ϖ} ≤ ker (θ j)
        simp [hϖ]
      · show TrivSqZeroExt.snd (v T) = 0
        have hv_zero : v ϖ = 0 := h_ker (Ideal.mem_span_singleton_self ϖ)
        simpa [hϖ, algebraMap_eq_inl'] using congrArg TrivSqZeroExt.snd hv_zero
    replace hρ : ∀ c : S, θ j c = 0 → ϖ ∣ ρ * c := by
      simpa [mem_colon, Ideal.mem_span_singleton] using hρ
    obtain ⟨b, hb⟩ : ϖ ∣ ρ * a := hρ a (ha j (mem_insert_self j s))
    -- The other sections do not kill `ϖ`: else they would kill `ker (θ j)` and equal `θ j`.
    have hρ_ne (i : J) : θ i ρ ≠ 0 := fun h_zero ↦ hρo (by rw [← hθo i, h_zero, map_zero])
    have hϖ_ne (i : J) (hi : i ∈ s) : θ i ϖ ≠ 0 := by
      intro hϖ_zero
      suffices h_eq : θ j = θ i from hj (by rwa [hθ h_eq])
      ext c
      have h_dvd : θ i ϖ ∣ θ i (ρ * (algebraMap O S (θ j c) - c)) :=
        map_dvd (θ i) (hρ _ (by simp))
      simpa [hϖ_zero, hρ_ne, sub_eq_zero] using h_dvd
    have hb_zero (i : J) (hi : i ∈ s) : θ i b = 0 := by
      simpa [ha i (mem_insert_of_mem hi), hϖ_ne i hi] using congrArg (θ i) hb
    -- `χ ρ` is a unit, and `χ (ρ a) = χ ϖ * χ b` with `g ∣ χ ϖ` and `g ^ #s ∣ χ b`.
    have h_ρa : χ ρ * χ a = χ ϖ * χ b := by rw [← map_mul, hb, map_mul]
    rw [card_insert_of_notMem hj, pow_succ', ← (hχ ρ hρo).dvd_mul_left, h_ρa]
    exact mul_dvd_mul (hg j) (ih b hb_zero)

/-- Let `θ j` be finitely many sections of an `O`-algebra `S`, `o` a `k`-point of `S` and `T` an
element of `S`. Let `χ` send the elements not vanishing at `o` to units, and let `χ (θ j T - T)`
divide `g` for each `θ j` through `o`. Some `F` vanishes along all `θ j`, and `χ F` divides
`g ^ N`, where `N` is the number of sections through `o`. -/
lemma exists_dvd_pow_card_of_sections {O S B J : Type*} [CommRing O] [CommRing S]
    [Algebra O S] [Algebra O k] [CommRing B] [Finite J] {o : S →ₐ[O] k} {T : S}
    (θ : J → S →ₐ[O] O) {χ : S →+* B} (hχ : ∀ a : S, o a ≠ 0 → IsUnit (χ a)) {g : B}
    (hg : ∀ j : J, (∀ a : S, algebraMap O k (θ j a) = o a) →
      χ (algebraMap O S (θ j T) - T) ∣ g) :
    ∃ F : S, (∀ j : J, θ j F = 0) ∧
      χ F ∣ g ^ Nat.card {j : J // ∀ a : S, algebraMap O k (θ j a) = o a} := by
  classical
  -- `F` is a product of `f j` vanishing along `θ j`, whose image divides `g`, or `1` if `θ j`
  -- misses `o`.
  have h_factor (j : J) : ∃ f : S, θ j f = 0 ∧
      χ f ∣ if ∀ a : S, algebraMap O k (θ j a) = o a then g else 1 := by
    split_ifs with hj
    · exact ⟨algebraMap O S (θ j T) - T, by simp, hg j hj⟩
    · obtain ⟨a, ha⟩ := not_forall.mp hj
      exact ⟨algebraMap O S (θ j a) - a, by simp, (hχ _ (by simpa [sub_eq_zero] using ha)).dvd⟩
  choose f hf_zero hf_dvd using h_factor
  refine ⟨∏ j, f j, fun j ↦ ?_, ?_⟩
  · exact (map_prod (θ j) f univ).trans (prod_eq_zero (mem_univ j) (hf_zero j))
  · calc χ (∏ j, f j) = ∏ j, χ (f j) := map_prod χ f univ
      _ ∣ ∏ j, if ∀ a : S, algebraMap O k (θ j a) = o a then g else 1 :=
        univ.prod_dvd_prod_of_dvd _ _ fun j _ ↦ hf_dvd j
      _ = _ := by simp [prod_ite, Fintype.card_subtype]

/-- Density of the torsion sections, read on functions on `Spec S`. Let each section
`e.torsionPoint (κ i)` factor through the closed immersion `ι : Spec S ⟶ y.groupScheme` as the point
`θ i`, and let `υ` carry each torsion vector whose section the isogeny `ψ` kills into `κ`. If
`υ • u` is the point `z'` given by `γ : S → B`, `ψ u` vanishes along `G`, and `F` vanishes at every
`θ i`, then `G (γ F) = 0`. -/
private lemma map_eq_zero_of_vanishesAlong_of_sections {J : Type} {κ : J → AdelicTorsion E D.Index}
    {S : CommAlgCat V} {ι : specOver V S ⟶ y.groupScheme} [IsClosedImmersion ι.left]
    {θ : J → S →ₐ[V] V}
    (hθ : ∀ i : J, Spec.map (ofHom (θ i)) ≫ ι.left = (e.torsionPoint (κ i)).left)
    {A : Over (Spec (.of V))} [IsAbelianScheme A] (ψ : y.groupScheme ⟶ A) [IsIsogeny ψ] {υ : 𝓞 E}
    (h_sec : ∀ s : AdelicTorsion E D.Index, e.torsionPoint s ≫ ψ = 0 → υ • s ∈ Set.range κ)
    {B : Type} [CommRing B] {s : Spec (.of B) ⟶ Spec (.of V)} {u : Over.mk s ⟶ y.groupScheme}
    {z' : Over.mk s ⟶ specOver V S} {γ : of S ⟶ of B} (hz' : z'.left = Spec.map γ)
    (hu : υ • u = z' ≫ ι) {B' : Type} [CommRing B'] {G : B →+* B'}
    (h_zero : VanishesAlong (u ≫ ψ) G) {F : S} (hF_zero : ∀ i : J, θ i F = 0) :
    G (γ.hom F) = 0 := by
  -- Each torsion section killed by `ψ`, moved by `υ`, lies in the zero set of `F`; by density
  -- (`ker_factors_of_torsionPoint`) so does the point `υ • u` along `G`.
  let I : Ideal S := .span {F}
  have hI_closed : IsClosedImmersion (Spec.map (ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := .of S) I
  have h_fac (s : AdelicTorsion E D.Index) (hs : e.torsionPoint s ≫ ψ = 0) :
      ∃ l : Spec (.of V) ⟶ Spec (.of (S ⧸ I)),
        l ≫ Spec.map (ofHom (Ideal.Quotient.mk I)) ≫ ι.left =
          (e.torsionPoint s ≫ (υ • 𝟙 y.groupScheme)).left := by
    obtain ⟨i, hi⟩ := h_sec s hs
    have h_le : I ≤ ker (θ i : S →+* V) := by simpa [I] using hF_zero i
    obtain ⟨l, hl⟩ := le_ker_iff_factors.mp h_le
    exact ⟨l, by simp [← assoc, map_smul, hl, hθ, hi]⟩
  have h_ker : ((homMk (specMap G) : Over.mk (specMap G ≫ s) ⟶ Over.mk s) ≫ u) ≫ ψ = 0 :=
    (Category.assoc ..).trans h_zero
  have h_kill : I ≤ ker (G.comp γ.hom) := by
    obtain ⟨l, hl⟩ := ker_factors_of_torsionPoint e ψ (υ • 𝟙 y.groupScheme) h_fac _ h_ker
    refine le_ker_iff_factors.mpr ⟨l, (cancel_mono ι.left).mp ?_⟩
    -- `Spec.map_comp` is left out: with `← Spec.map_comp_assoc` it loops.
    simpa [hz', hu, specMap, ← Spec.map_comp_assoc, -Spec.map_comp] using hl
  exact h_kill (mem_span_singleton_self F)

/-- A torsion section of `y.groupScheme` that `d` kills factors through any
`ι : Spec S → y.groupScheme` through which every point killed by `d` factors: it is given by a
`V`-point `θ` of `Spec S`. -/
private lemma exists_spec_map_comp_eq_torsionPoint_of_smul_eq_zero {S : CommAlgCat V}
    {ι : specOver V S ⟶ y.groupScheme} {d : 𝓞 E}
    (ι_lift : ∀ ⦃W : Over (Spec (.of V))⦄ (w : W ⟶ y.groupScheme),
      w ≫ (d • 𝟙 y.groupScheme) = 0 → ∃ u : W ⟶ specOver V S, u ≫ ι = w)
    {s : AdelicTorsion E D.Index} (hs : d • s = 0) :
    ∃ θ : S →ₐ[V] V, Spec.map (ofHom θ) ≫ ι.left = (e.torsionPoint s).left := by
  obtain ⟨θ, hθ⟩ : ∃ θ : S →ₐ[V] V,
      specOver.map θ ≫ ι = toUnit (specOver V V) ≫ e.torsionPoint s :=
    specOver.map_bijective.surjective.exists.mp (ι_lift _ (by simp [hs, ← map_smul]))
  exact ⟨θ, by simpa [specOver.map, OverMorphism.ext_iff] using hθ⟩

/-- Let the sections `e.torsionPoint (κ i)` factor through the closed immersion `ι` as distinct
points `θ i` of `Spec S`, `S` finite over `V`, let `T` have nonzero derivative along each nonzero
tangent vector at the `k`-point `o`, and let `γ : S → B` give `z'`, invert the elements nonzero at
`o` and send `θ i T - T` to `t` for each `θ i` through `o`. If `ψ` kills each `e.torsionPoint (κ i)`
and `G` kills `t ^ N`, `N` the number of `θ i` through `o`, then `ψ (ι z')` vanishes along `G`. -/
private lemma vanishesAlong_of_map_pow_card_eq_zero [Algebra V k] {J : Type} [Finite J]
    {κ : J → AdelicTorsion E D.Index} {S : CommAlgCat V} [Module.Finite V S]
    {ι : specOver V S ⟶ y.groupScheme} [IsClosedImmersion ι.left] {θ : J → S →ₐ[V] V}
    (hθ : ∀ i : J, Spec.map (ofHom (θ i)) ≫ ι.left = (e.torsionPoint (κ i)).left)
    (θ_inj : θ.Injective) {o : S →ₐ[V] k} {T : S}
    (hT : ∀ v : S →ₐ[V] k[ε], (∀ a : S, (v a).fst = o a) → (v T).snd = 0 → ∀ a : S, (v a).snd = 0)
    {B : Type} [CommRing B] {s : Spec (.of B) ⟶ Spec (.of V)} {z' : Over.mk s ⟶ specOver V S}
    {γ : of S ⟶ of B} (hz' : z'.left = Spec.map γ)
    (γ_unit : ∀ a : S, o a ≠ 0 → IsUnit (γ.hom a)) {t : B}
    (γ_t : ∀ i : J, (∀ a : S, algebraMap V k (θ i a) = o a) →
      γ.hom (algebraMap V S (θ i T) - T) = t)
    {A : Over (Spec (.of V))} [IsAbelianScheme A] (ψ : y.groupScheme ⟶ A)
    (h_ker : ∀ i : J, e.torsionPoint (κ i) ≫ ψ = 0) {B' : Type} [CommRing B'] {G : B →+* B'}
    (h_pow : G (t ^ Nat.card {i : J // ∀ a : S, algebraMap V k (θ i a) = o a}) = 0) :
    VanishesAlong ((z' ≫ ι) ≫ ψ) G := by
  -- The ideal `I` of `ker ψ` in `Spec S` vanishes at every `θ i`, so `t ^ N` divides its image
  -- under `γ`, and `G ∘ γ` kills it.
  obtain ⟨I, -, hI⟩ := exists_ideal_le_ker_iff_factors ζ[A].left (ι ≫ ψ).left
  have h_le (i : J) : I ≤ ker (θ i : S →+* V) := by
    simpa [hI, ← hθ, eq_zero_iff_factors_zero_section] using h_ker i
  have h_kill : I ≤ ker (G.comp γ.hom) := by
    intro a ha
    have h_dvd : t ^ Nat.card {i : J // ∀ a : S, algebraMap V k (θ i a) = o a} ∣ γ.hom a := by
      rw [Nat.card_eq_fintype_card]
      exact pow_card_dvd_of_sections hT (θ_inj.comp Subtype.val_injective) Subtype.prop γ_unit
        (fun i ↦ (γ_t i.val i.property).symm.dvd) univ a fun i _ ↦ h_le i.val ha
    exact zero_dvd_iff.mp (h_pow.symm.dvd.trans (map_dvd G h_dvd))
  simpa [VanishesAlong, eq_zero_iff_factors_zero_section, hz'] using (hI _).mp h_kill

/-- A local equation for the closure of torsion sections. Let `x` over `k` be the pull-back of `y`
(`ho`), let `β - b ∈ w = ker x.baseHom` be coprime to `star β - b`, and let `z` be a point of
`y.groupScheme` killed by `(β - b) ^ M` over a local `k`-algebra `B` with `k`-point `π`. Some
`t ∈ ker π` makes `t ^ N` a local equation at `z` for the sections of any injective family `c` of
`w`-torsion vectors, `N` the number of them through the closed point of `z`. -/
lemma exists_isLocalEquation_pow_sectionCount (e : y.FullLevelStructure)
    (ho : x.IsPullbackAlong (specMap φ) y) {b : ℤ} (hb : x.baseHom (D.β - b) = 0)
    (h_coprime : IsCoprime (D.β - b) (star D.β - b)) (M : ℕ) {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra k B] (z : (Over.map (specMap φ)).obj (specOver k B) ⟶ y.groupScheme)
    (hz : (D.β - b) ^ M • z = 0) (π : B →ₐ[k] k) :
    ∃ t : B, π t = 0 ∧ ∀ ⦃J : Type⦄ (c : J → AdelicTorsion E D.Index), c.Injective →
      (∀ i : J, c i ∈ torsionBySet (𝓞 E) (AdelicTorsion E D.Index) (ker x.baseHom)) →
      IsLocalEquation e c z
        (t ^ sectionCount e c ((Over.map (specMap φ)).map (specOver.map π) ≫ z)) := by
  -- Let `Spec S` be the kernel of `(β - b) ^ (M + 1)` and `o` the closed point of `z` on it. Its
  -- tangent space at `o` is at most a line, so one function `T` detects tangent vectors; `t` is
  -- `o T - T` read on `z`.
  algebraize [φ]
  -- if `β = b` then `star β = b` too, against coprimality
  have h_ne : D.β - b ≠ 0 := by
    intro h_eq
    have h_star : star D.β - b = 0 := by simp [sub_eq_zero.mp h_eq]
    exact not_isCoprime_zero_zero (by rwa [h_eq, h_star] at h_coprime)
  have h_isog : IsIsogeny ((D.β - b) ^ (M + 1) • 𝟙 y.groupScheme) :=
    y.isIsogeny_smul_id (pow_ne_zero (M + 1) h_ne)
  obtain ⟨S, ι, hS_finite, hS_flat, hι_closed, ι_ker, ι_lift⟩ :=
    exists_finite_kernel_ring (f := (D.β - b) ^ (M + 1) • 𝟙 y.groupScheme) inferInstance
  obtain ⟨z', rfl⟩ := ι_lift z (by simp [mul_smul, hz, pow_succ'])
  -- The point `z'` is `Spec` of a ring map `γ` compatible with `φ`, as is every point of `Spec S`.
  obtain ⟨γ, hγ, hz'⟩ : ∃ γ : of S ⟶ of B,
      (∀ a : V, γ.hom (algebraMap V S a) = algebraMap k B (φ a)) ∧ z'.left = Spec.map γ := by
    simpa [Spec.map_surjective.exists, OverMorphism.ext_iff, ← Spec.map_comp, Spec.map_inj,
      CommRingCat.hom_ext_iff, RingHom.ext_iff] using homMk_surjective z'
  -- Now `z` is given by a ring map `γ : S → B`, and `o = π ∘ γ`.
  let o : S →ₐ[V] k := ⟨.comp π γ.hom, by simp [hγ, algebraMap_toAlgebra]⟩
  obtain ⟨T, hT⟩ :=
    exists_detecting_tangent_vectors y ho.baseHom_eq_comp hb h_coprime ι_ker ι_lift o
  let t : B := algebraMap k B (o T) - γ T
  refine ⟨t, by simp [t, o], fun J c c_inj c_mem ↦ ?_⟩
  -- The sections `e.torsionPoint (c i)` lie in `Spec S`; they are the distinct algebra maps `θ i`.
  have h_sections (i : J) :
      ∃ θ : S →ₐ[V] V, Spec.map (ofHom θ) ≫ ι.left = (e.torsionPoint (c i)).left := by
    have h_killed : (D.β - b) ^ (M + 1) • c i = 0 := by
      rw [pow_succ, mul_smul, (mem_torsionBySet_iff _ _).mp (c_mem i) ⟨_, hb⟩, smul_zero]
    exact exists_spec_map_comp_eq_torsionPoint_of_smul_eq_zero e ι_lift h_killed
  choose θ hθ using h_sections
  have θ_inj : θ.Injective := fun i j h_eq ↦
    c_inj (e.injective (by simp [← hθ, h_eq, OverMorphism.ext_iff]))
  -- there are finitely many, as `S` is finite and flat, so free, over the local ring `V`
  have hS_free : Module.Free V S := free_of_flat_of_isLocalRing
  have hJ_finite : Finite J := .of_injective θ θ_inj
  have h_count : sectionCount e c ((Over.map (specMap φ)).map (specOver.map π) ≫ z' ≫ ι) =
      Nat.card {i : J // ∀ a : S, φ (θ i a) = o a} := by
    -- `Spec.map_comp` is left out: with `← Spec.map_comp_assoc` it loops.
    simp [sectionCount, o, ← hθ, hz', specOver.map, OverMorphism.ext_iff, ← Spec.map_comp_assoc,
      cancel_mono, Spec.map_inj, CommRingCat.hom_ext_iff, RingHom.ext_iff, -Spec.map_comp]
  rw [h_count]
  have hπ_local : IsLocalHom (π : B →+* k) :=
    .of_surjective π fun r : k ↦ ⟨algebraMap k B r, π.commutes r⟩
  have γ_unit (a : S) (ha : o a ≠ 0) : IsUnit (γ.hom a) := hπ_local.map_nonunit (γ a) ha.isUnit
  have γ_t (i : J) (hi : ∀ a : S, φ (θ i a) = o a) : γ.hom (algebraMap V S (θ i T) - T) = t := by
    simp [t, hγ, hi]
  constructor
  · -- `map_eq_zero`: some `F` vanishes at all `θ i` and divides `t ^ N` on `z`; by density of
    -- the torsion sections in `ker ψ`, `G` kills it.
    intro A hA ψ hψ υ u hu h_sec B' hB' G h_van
    obtain ⟨F, hF_zero, hF_dvd⟩ :=
      exists_dvd_pow_card_of_sections θ γ_unit fun i hi ↦ (γ_t i hi).dvd
    have hF_kill : G (γ.hom F) = 0 :=
      map_eq_zero_of_vanishesAlong_of_sections e hθ ψ h_sec hz' hu h_van hF_zero
    exact zero_dvd_iff.mp (hF_kill.symm.dvd.trans (map_dvd G hF_dvd))
  · -- `vanishesAlong`: the equations of `ker ψ` are multiples of `t ^ N` on `z`.
    intro A hA ψ hψ h_ker B' hB' G h_pow
    exact vanishesAlong_of_map_pow_card_eq_zero e hθ θ_inj hT hz' γ_unit γ_t ψ h_ker h_pow

/-- Reduction of torsion sections. Let `x` over `k` be the pull-back of `y` over `V` along `φ`
(`ho`), and let `e` be a full structure on `y`. A `w`-torsion vector `s`, for `w = ker x.baseHom`,
goes to the `w`-torsion `k`-point of `x` that corresponds to the section `e.torsionPoint s`. -/
private noncomputable def torsionReduction (e : y.FullLevelStructure)
    (ho : x.IsPullbackAlong (specMap φ) y) :
    torsionBySet (𝓞 E) (AdelicTorsion E D.Index) (ker x.baseHom) →+ placeTorsion x k :=
  .mk' (fun s ↦ ⟨ho.isGroupBaseChange.pointEquiv.symm
      (toUnit ((Over.map (specMap φ)).obj (specOver k k)) ≫ e.torsionPoint s), by
    refine (mem_torsionBySet_iff _ _).2 fun a ↦ ?_
    simp [← ModuleObj.comp_smul, (mem_torsionBySet_iff _ _).1 s.property a, ← map_smul]⟩)
    (by simp [comp_add])

/-- The reduction of the torsion vector `s` is the point `w` exactly when the section
`e.torsionPoint s` is, read over `k` via `φ`, the point of `y.groupScheme` that
`ho.isGroupBaseChange.pointEquiv` matches with the `k`-point `w` of `x.groupScheme`. -/
private lemma torsionReduction_eq_iff (e : y.FullLevelStructure)
    (ho : x.IsPullbackAlong (specMap φ) y)
    (s : torsionBySet (𝓞 E) (AdelicTorsion E D.Index) (ker x.baseHom)) (w : placeTorsion x k) :
    torsionReduction e ho s = w ↔
      toUnit ((Over.map (specMap φ)).obj (specOver k k)) ≫ e.torsionPoint s =
        ho.isGroupBaseChange.pointEquiv w.val := by
  simp [torsionReduction, Subtype.ext_iff, LinearEquiv.symm_apply_eq]

open Pointwise in
/-- Let `c` and `t` be elements of `𝓞 E` with `t w ⊆ (c)`, for `w = ker x.baseHom`. If the full
structure `e` sends the torsion vector `s` to a section that `c` kills, then `t • s` is
`w`-torsion. -/
private lemma smul_mem_torsionBySet_of_comp_smul_eq_zero (e : y.FullLevelStructure) {c t : 𝓞 E}
    (h_dvd : t • ker x.baseHom ≤ Ideal.span {c}) {s : AdelicTorsion E D.Index}
    (hs : e.torsionPoint s ≫ (c • 𝟙 y.groupScheme) = 0) :
    t • s ∈ torsionBySet (𝓞 E) (AdelicTorsion E D.Index) (ker x.baseHom) := by
  have hc_tors : c • s = 0 := e.injective (by simpa [map_smul] using hs)
  -- `a * t` lies in `t w ⊆ (c)`, and `c` kills `s`.
  have h_mem (a : 𝓞 E) (ha : a ∈ ker x.baseHom) :
      a * t ∈ Ideal.torsionOf (𝓞 E) (AdelicTorsion E D.Index) s :=
    (Ideal.span_singleton_le_iff_mem _).mpr hc_tors (h_dvd ⟨a, ha, mul_comm t a⟩)
  simpa [mul_smul] using h_mem

open Pointwise in
/-- Let `x` over `k` be the reduction of `y` (`ho`) and `w = ker x.baseHom` good for `D` (`hw`).
Some nonzero `w`-torsion vector `s` has section `e.torsionPoint s` equal to `0` read over `k` via
`φ`; some additive map `ν` from `w`-torsion vectors to `w`-torsion `k`-points of `x` is such that,
for a `w`-torsion point `z` over a local `k`-algebra `B` with `k`-point `π`, some `t ∈ ker π` has
`t ^ N = 0`, `N` the size of the fibre of `ν` over the closed point `placeTorsionMap π z` of `z`; if
that point is `0`, `z` vanishes along every algebra map that kills `t`. -/
lemma exists_param_pow_card_eq_zero (hw : D.IsGoodAt (ker x.baseHom))
    {y : ThetaObject X (Spec (CommRingCat.of V))} (e : y.FullLevelStructure)
    (ho : x.IsPullbackAlong (specMap φ) y) :
    let T : Submodule (𝓞 E) (AdelicTorsion E D.Index) :=
      torsionBySet (𝓞 E) (AdelicTorsion E D.Index) (ker x.baseHom)
    ∃ ν : T →+ placeTorsion x k,
      (∃ s ∈ T, s ≠ 0 ∧
        toUnit ((Over.map (specMap φ)).obj (specOver k k)) ≫ e.torsionPoint s = 0) ∧
      ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra k B] (z : placeTorsion x B)
        (π : B →ₐ[k] k), ∃ t : B,
        π t = 0 ∧
        t ^ Nat.card {s : T // ν s = placeTorsionMap π z} = 0 ∧
        (placeTorsionMap π z = 0 → ∀ (C : Type) [CommRing C] [Algebra k C] (G : B →ₐ[k] C),
          G t = 0 → placeTorsionMap G z = 0) := by
  -- `ν` is reduction of torsion sections. The claims on the parameter `u` are those of
  -- `exists_isLocalEquation_pow_sectionCount` with `M = 1`; applied to the tangent vector `L 1`,
  -- they give the section that reduces to `0`. Goodness of `w = ker x.baseHom` gives `c ≠ 0` in
  -- `w`, `t ≡ 1` modulo `w` with `t w ⊆ (c)`, and `b` with `β - b ∈ w`.
  intro T
  obtain ⟨-, ⟨-, c, hc, hc₀, t, ht, h_dvd⟩, b, hb, h_coprime, -⟩ :=
    ringChar_prime_and_exists_isCoprime_of_isGoodAt_ker hw
  have h_isog : IsIsogeny (c • 𝟙 y.groupScheme) := y.isIsogeny_smul_id hc₀
  have hq : IsGroupBaseChange (specMap φ) ho.schemeMap := ho.isGroupBaseChange
  let ν : T →+ placeTorsion x k := torsionReduction e ho
  have ν_eq (s : T) (w : placeTorsion x k) : ν s = w ↔
      toUnit ((Over.map (specMap φ)).obj (specOver k k)) ≫ e.torsionPoint s = hq.pointEquiv w.val :=
    torsionReduction_eq_iff e ho s w
  -- The claim on points over every `B`, proved second below, implies the first claim: a nonzero
  -- section that reduces to `0`.
  refine ⟨ν, (and_iff_right_of_imp fun h_main ↦ ?_).mpr ?_⟩
  · -- If only the section `0` reduced to `0`, then `u = u ^ 1 = 0` for `z = L 1`, so `L 1 = 0`.
    obtain ⟨L, hL⟩ := exists_isLieLine x rfl hb
    let z : placeTorsion x k[ε] := ⟨L 1, by simp +contextual [hL.smul_apply]⟩
    obtain ⟨u, -, h_pow, h_zero⟩ := h_main k[ε] z (fstHom k k k)
    by_contra h_none
    have h_card : Nat.card {s // ν s = 0} = 1 :=
      Nat.card_eq_one_iff_exists.mpr
        ⟨⟨0, map_zero ν⟩, by simpa [ν_eq, not_imp_not] using h_none⟩
    have h_fst : placeTorsionMap (fstHom k k k) z = 0 := Subtype.ext (hL.fstHom_comp 1)
    rw [h_fst, h_card, pow_one] at h_pow
    have h_L : L 1 = 0 := by
      simpa [placeTorsionMap, z] using h_zero h_fst k[ε] (.id k k[ε]) h_pow
    exact hL.apply_one_ne_zero h_L
  · rintro B hB_ring hB_local hB_alg ⟨z, hz⟩ π
    replace hz : ∀ a : 𝓞 E, x.baseHom a = 0 → a • z = 0 := by simpa using hz
    have hz_ker : (D.β - b) ^ 1 • hq.pointEquiv z = 0 := by simp [← map_smul, hz _ hb]
    obtain ⟨u, hu, h_ker⟩ := exists_isLocalEquation_pow_sectionCount e ho hb h_coprime 1
      (hq.pointEquiv z) hz_ker π
    refine ⟨u, hu, ?_, ?_⟩
    · -- `map_eq_zero` for `ψ = c`, the family of all `w`-torsion vectors, and `υ = t`: as
      -- `c ∣ t * a` for `a ∈ w`, multiplying by `t` carries `c`-torsion into `w`-torsion; it fixes
      -- `z` because `t - 1 ∈ w`.
      have h_fix : t • hq.pointEquiv z = hq.pointEquiv z := by
        simpa [sub_smul, ← map_smul, sub_eq_zero] using hz _ ht
      have h_van : VanishesAlong (hq.pointEquiv z ≫ (c • 𝟙 y.groupScheme)) (.id B) :=
        (vanishesAlong_iff (𝟙 _) (by simp [specMap])).mpr (by simp [← map_smul, hz c hc])
      have h_zero : RingHom.id B (u ^ sectionCount e (Subtype.val : T → AdelicTorsion E D.Index)
          ((Over.map (specMap φ)).map (specOver.map π) ≫ hq.pointEquiv z)) = 0 :=
        (h_ker (J := T) Subtype.val Subtype.val_injective Subtype.prop).map_eq_zero
          (c • 𝟙 y.groupScheme) h_fix
          (fun s hs ↦ ⟨⟨t • s, smul_mem_torsionBySet_of_comp_smul_eq_zero e h_dvd hs⟩, rfl⟩) h_van
      have h_point : hq.pointEquiv (specOver.map π ≫ z) =
          (Over.map (specMap φ)).map (specOver.map π) ≫ hq.pointEquiv z := by
        simp [hq.pointEquiv_apply]
      simpa [sectionCount, ν_eq, placeTorsionMap, h_point] using h_zero
    · -- `vanishesAlong` for `ψ = 𝟙` and the single section `0`, which passes through the closed
      -- point of `z`.
      intro h_pt C hC_ring hC_alg G hG
      replace h_pt : specOver.map π ≫ z = 0 := congrArg Subtype.val h_pt
      have h_count : G ((u ^ sectionCount e (fun _ : Unit ↦ 0)
          ((Over.map (specMap φ)).map (specOver.map π) ≫ hq.pointEquiv z))) = 0 := by
        simp [sectionCount, ← hq.linear.map_zero, IsGroupBaseChange.pointEquiv, ← h_pt, hG]
      have h_van : VanishesAlong (hq.pointEquiv z ≫ 𝟙 y.groupScheme) (G : B →+* C) :=
        (h_ker (fun _ : Unit ↦ 0) (Function.injective_of_subsingleton _)
          fun _ ↦ zero_mem _).vanishesAlong (𝟙 _) (by simp) h_count
      rw [vanishesAlong_iff ((Over.map (specMap φ)).map (specOver.map G)) rfl] at h_van
      exact Subtype.ext (hq.pointEquiv.map_eq_zero_iff.mp h_van)

end New.Variety
