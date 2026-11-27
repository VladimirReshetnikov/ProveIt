import Lib.PadicComparison.Crystalline.ComparisonMap
import Lib.PadicComparison.HodgeTate.PeriodMap

/-!
# Crystallinity of p-adic cohomology of charted proper schemes and Frobenius congruences

The `p`-adic cohomology `New.Variety.ellAdicCohom` of a proper scheme `Y` is crystalline when `Y` is
charted (`New.Variety.IsCharted`) over a noetherian ring `R` that maps into the valuation ring of a
`p`-adic place of `Ω`, and over `Ω`. A congruence relation Σ n_i [Frob^{a_i} u_i(x)] = 0 between
maps of proper schemes (`New.Variety.CongruenceRelation`) gives the same relation between the
operators on `New.Period.Bmax ⊗ Vⁿ(Y)`.

## Overview of this theory

Let `R` be a commutative ring and `Ω` a fixed algebraic closure of `ℚ` that is an `R`-algebra. Call
a scheme charted over a ring if it is built from charts étale over tori (`New.Variety.IsCharted`).
Let `Vⁿ(Y)` be `New.Variety.ellAdicCohom` for `ℓ = p`, that is, `ℚ_p ⊗ Hⁿ(Y_Ω, ℤ_p)`. A place above
`p` is given by a valuation ring `A` of `Ω` containing the image of `R`.

* `New.Variety.finite_and_primitive_comparison`: let `Y` be proper over `R` and charted over an
  algebraically closed field `Ω` mapping to `ℂ_p`. Let `M` be a module over the tilt `O♭` of
  `O_{ℂ_p}`, with `B ↦ B ⊗ M` acyclic along tilting at perfect `O♭`-algebras. Then the cohomology of
  `Y_Ω` commutes with flat extension of coefficients, and each `Hⁿ(Y_Ω, 𝔽_p)` is finite. If also `R`
  maps compatibly to `O_{ℂ_p}`, the cohomology of `Y_Ω` with coefficients (locally constant `O♭`)
  `⊗ M` maps bijectively to that of `S ↦ Y(S)`. Here `S` runs over the `p`-adic test rings
  (`New.Variety.PadicTest`), with coefficients `S♭ ⊗ M`.
* `New.Variety.exists_period_map`: let `R` map to `O_{ℂ_p}` compatibly with an embedding `Ω → ℚ̄_p`.
  Let `S` be a `p`-torsion-free, `p`-adically complete `A_inf`-algebra and `K` a flat `S`-algebra
  over `ℚ_p`, as in `IsPeriodRingPair`. There are `K`-linear maps from `K ⊗ Vⁿ(Y)` to `Hⁿ` of
  `T ↦ Y(T)` on test rings `T`, with coefficients built from `K` and `W(T♭)`. These maps are natural
  and Galois-compatible. They are bijective when `Y` is proper and charted over `Ω`.
* `New.Variety.ellAdicCohom.isCrystalline_and_linearFrob_rel`: let `R` be noetherian, `K` a field,
  and `Y` proper and charted over `R` and over `Ω`. Then the decomposition group of `A` over `K`
  acts crystallinely on `Vⁿ(Y)`. Let `W` be proper and charted over `Ω`, with maps `uᵢ : W ⟶ Y`.
  Suppose that `∑ mᵢ [Frob^{aᵢ}(uᵢ x)] = 0` at the field-valued points `x` of the special fibre of
  `W`. Suppose also that each `γᵢ` in the decomposition group acts on the residue field as
  `x ↦ x ^ (1/p^aᵢ)`. Then `∑ mᵢ uᵢ^* ∘ linearFrob(γᵢ, aᵢ) = 0` on `Bmax ⊗ Vⁿ(Y)`.
* `New.Variety.exists_hasHodgeTateWeight`: let `Y` be proper, smooth of relative dimension `d` and
  charted over `Ω`. Let `E` be a field between `R` and `Ω`, and let `E → k → ℚ̄_p` be compatible,
  with a section `ε` of `k → ℚ̄_p`. Fix `h`, a proper `W`, and a class `x` in degree-`q` Hodge
  cohomology of `Y` over `E`. Then there are `v` in `ℂ_p ⊗ V^(q+h)(Y)` and an `ε`-semilinear map `Θ`
  with two properties. First, `v` has Hodge–Tate weight `h` for the decomposition group over `E`.
  Second, `hodgeTateMap h (u^* x) = Θ(u^* v)` for every `u : W ⟶ Y`.

These replace the primitive, crystalline and Hodge–Tate comparison theorems (Faltings, Scholze,
Bhatt–Morrow–Scholze) as used in `Lib.Shimura.Eigenspace`. There is no integral form, no Hodge–Tate
decomposition, and no identification with étale or crystalline cohomology.

`Descent` defines the test rings and proves acyclicity for almost coefficients. `Duality` on powers
of `ℙ¹`, with `Lib.Cohomology.SmoothBaseChange`, extends the comparison from a point to `Y`.
`Primitive` deduces the first result and lifts it to periods by `Completion`; the map is in
`HodgeTate.PeriodMap`. `Crystalline` uses `ToricTower` (roots of one unit at a time) for the
crystalline statement, and `CrystallineFrobenius` treats Frobenius. `HodgeTate` builds the
Hodge–Tate map.

## Main definitions and results

* `New.Variety.exists_cancels_frobPow_locally`: if p divides a power of z and a fixed power of z
  divides the image of 𝔴, then near each maximal ideal of a test the relation holds modulo z.

Notions from other files:
* `New.Variety.Cancels`: the integers m_i add up to zero on every fibre of a family v_i, that is, Σ
  m_i [v_i] = 0 in the free abelian group on the v_i.
* `New.Variety.CongruenceRelation`: Σ m_i [F_i u_i(x)] = 0 (`New.Variety.Cancels`) for every point x
  of W in a field of characteristic p that kills 𝔴, where F_i is the a_i-th iterate of Frobenius.
* `New.Period.Bmax`: The period ring B = B^+[1/μ] (Colmez's B_max, not Fontaine's B_cris), over
  which crystalline representations are defined.
* `New.Period.linearFrob`: β_{s,m}: a chosen B-linear endomorphism of B⊗T agreeing with φ^m
  j(s) ⊗ ρ(s) on D_pcris(T), if one exists (arbitrary otherwise).

## Relation to the literature

Known result: Congruence relation for the crystalline Frobenius. In the literature, characteristic
polynomials are compared through cycle classes. Here a relation among Frobenius twists of maps,
given on points of the special fibre, is carried directly to a relation among operators on
crystalline invariants. Source: Scholl, Motives for modular forms, 1990, Invent. Math. 100, §4.2.3,
through Katz–Messing, Some consequences of the Riemann hypothesis for varieties over finite fields,
1974, Invent. Math. 23, Thm 2(2); for the ramified base, Berthelot–Ogus, F-isocrystals and de Rham
cohomology I, 1983, Invent. Math. 72.
-/

/-!
## A Frobenius relation on p-adic tests modulo an element of O_C

A congruence relation Σ n_i [Frob^{a_i} u_i(x)] = 0 between maps u_i : W → Y of proper R-schemes,
known at points x in fields that kill an ideal 𝔴 (`New.Variety.CongruenceRelation`), is carried over
to points with values in p-adic tests (`New.Variety.PadicTest`), modulo an element z of O_C.
-/

section DenseRelation

open CategoryTheory AlgebraicGeometry Ideal CommRingCat Finset Quotient Spec ULift Fact Pi

/-- Let `φ` map `T` to a valuation ring, and let `x` be neither zero nor a unit. If the product of
`n` ideals `𝔮 l` lies in `α` and `x ^ (n + 1)` divides `φ α`, then `x` divides `φ (𝔮 l)` for
some `l`. -/
lemma New.Variety.exists_factor_forall_dvd {T V J : Type*} [CommRing T] [CommRing V] [IsDomain V]
    [ValuationRing V] [Fintype J] (φ : T →+* V) {α : Ideal T} {𝔮 : J → Ideal T}
    (h𝔮 : ∏ l : J, 𝔮 l ≤ α) {x : V} (hx_ne : x ≠ 0) (hx_nonunit : ¬IsUnit x)
    (hα : ∀ r ∈ α, x ^ (Fintype.card J + 1) ∣ φ r) :
    ∃ l : J, ∀ r ∈ 𝔮 l, x ∣ φ r := by
  -- Otherwise pick `r l ∈ 𝔮 l` with `φ (r l)` not divisible by `x`, hence dividing `x`. Then
  -- `x ^ (card J + 1)` divides `φ (∏ l, r l)`, which divides `x ^ card J`.
  by_contra! h_none : ∀ l : J, ∃ r ∈ 𝔮 l, ¬x ∣ φ r
  choose r hr_mem hr_ndvd using h_none
  have h_prod_dvd : φ (∏ l, r l) ∣ x ^ Fintype.card J := by
    rw [map_prod, ← Finset.card_univ, ← Finset.prod_const]
    exact prod_dvd_prod_of_dvd _ _ fun l _ ↦
      (ValuationRing.dvd_total ..).resolve_left (hr_ndvd l)
  have pow_succ_dvd : x ^ (Fintype.card J + 1) ∣ x ^ Fintype.card J :=
    (hα _ (h𝔮 (prod_mem_prod fun l _ ↦ hr_mem l))).trans h_prod_dvd
  exact Nat.not_succ_le_self _ ((pow_dvd_pow_iff hx_ne hx_nonunit).mp pow_succ_dvd)

/-- In a noetherian ring `T`, every ideal `α` contains a product of finitely many primes, each
containing `α`. -/
lemma New.Variety.exists_primes_over_prod_le {T : Type} [CommRing T] [IsNoetherianRing T]
    (α : Ideal T) :
    ∃ (J : Type) (_ : Fintype J) (𝔮 : J → Ideal T),
      (∀ l : J, (𝔮 l).IsPrime) ∧ (∀ l : J, α ≤ 𝔮 l) ∧ ∏ l : J, 𝔮 l ≤ α := by
  classical
  -- Pull back primes of `T ⧸ α` whose product is zero.
  obtain ⟨Z, hZ⟩ : ∃ Z : Multiset (PrimeSpectrum (T ⧸ α)), (Multiset.map PrimeSpectrum.asIdeal
    Z).prod ≤ ⊥ := PrimeSpectrum.exists_primeSpectrum_prod_le (T ⧸ α) ⊥
  refine ⟨Z, inferInstance, fun l ↦ l.fst.asIdeal.comap (Ideal.Quotient.mk α),
    fun l ↦ inferInstance, fun l ↦ mk_ker.ge.trans (ker_le_comap _), ?_⟩
  rw [← Z.map_univ, ← prod_eq_multiset_prod] at hZ
  refine le_trans (le_comap_of_map_le ?_) ((comap_mono hZ).trans mk_ker.le)
  exact (map_prod (mapHom _) ..).trans_le (prod_le_prod fun _ _ ↦ map_comap_le)

/-- Let `Y` be proper over `Spec R`, and let `u i : W ⟶ Y` be maps over `Spec R` with integers `n i`
and exponents `a i`. Assume `CongruenceRelation n 𝔴 p a u`: at every field-valued point of `W` of
characteristic `p` killing `𝔴`, the points `u i` twisted by `Frob^(a i)` satisfy `∑ n i • [·] = 0`.
Then the same holds over `T ⧸ 𝔭`: for any point `t : Spec T ⟶ W.left` and prime `𝔭` of `T` that
contains the image of `𝔴` under `R → T` and has `p = 0` in `T ⧸ 𝔭`, the morphisms
`Spec (T ⧸ 𝔭) ⟶ Y.left` given by `u i ∘ t`, precomposed with the quotient `T → T ⧸ 𝔭` followed by
`frobPow` with exponent `a i` (the map `x ↦ x ^ p ^ a i`), satisfy `Cancels n`, that is,
`∑ n i • [·] = 0` in the free abelian group on such morphisms. -/
lemma New.Variety.cancels_quotient_of_congruenceRelation {p : ℕ} [ThePrime p] {R : CommRingCat.{0}}
    {W Y : Over (Spec R)} {I : Type*} [Fintype I] {n : I → ℤ} {a : I → ℕ} {u : I → (W ⟶ Y)}
    [IsProper Y.hom] {𝔴 : Ideal R} (h_cong : CongruenceRelation n 𝔴 p a u) {T : CommRingCat.{0}}
    (t : Spec T ⟶ W.left) (𝔭 : Ideal T) [𝔭.IsPrime] (h𝔴 : 𝔴.map (Spec.preimage (t ≫ W.hom)).hom ≤ 𝔭)
    (hp : (p : T ⧸ 𝔭) = 0) :
    Cancels n fun i : I ↦
      Spec.map (ofHom ((frobPow hp (a i)).comp (Ideal.Quotient.mk 𝔭))) ≫ t ≫ (u i).left := by
  -- The relation holds in the fraction field `K` of `T ⧸ 𝔭`.
  let K : Type := 𝔭.ResidueField
  have h_charP : CharP K p :=
    (CharP.charP_iff_prime_eq_zero out).mpr (natCast_eq_zero_of_algebra hp _)
  -- The point of `W` in `K` kills the image of `𝔴`, so the relation holds there.
  have h_kills (r : R) (hr : r ∈ 𝔴) :
      (Spec.preimage ((Spec.map (ofHom (algebraMap T K)) ≫ t) ≫ W.hom)).hom r = 0 := by
    simpa [K] using le_comap_of_map_le h𝔴 hr
  have h_cancels_residue : Cancels n fun i : I ↦ Spec.map (ofHom (iterateFrobenius K p (a i))) ≫
      (Spec.map (ofHom (algebraMap T K)) ≫ t) ≫ (u i).left := h_cong K _ h_kills
  -- Points of the separated `Y` in `T ⧸ 𝔭` that agree in `K` are equal.
  have h_residue_injective : ∀ a : T ⧸ 𝔭, algebraMap (T ⧸ 𝔭) 𝔭.ResidueField a = 0 → a = 0 :=
    (injective_iff_map_eq_zero _).mp 𝔭.injective_algebraMap_quotient_residueField
  refine h_cancels_residue.mono fun i i' heq ↦ up_injective ?_
  refine (isProperOver_pointsToBase Y.hom).ext_of_jointly_injective
    ![ofHom (algebraMap (T ⧸ 𝔭) K)] (fun c hc ↦ h_residue_injective c (hc 0)) fun _ ↦ ?_
  apply up_inj.mpr
  -- Frobenius commutes with the map to `K`, on both sides of `heq`.
  have frob_comm (l : I) :
      Spec.map (ofHom (algebraMap (T ⧸ 𝔭) K)) ≫
          Spec.map (ofHom ((frobPow hp (a l)).comp (Ideal.Quotient.mk 𝔭))) =
        Spec.map (ofHom (iterateFrobenius K p (a l))) ≫ Spec.map (ofHom (algebraMap T K)) := by
    rw [← map_comp, ← map_comp]
    congr 1 with _
    simp [K, iterateFrobenius_def]
  -- `-ofHom_comp` keeps the two `Spec.map` factors apart, so that `frob_comm` applies.
  simpa [reassoc_of% frob_comm, -ofHom_comp] using heq

/-- Let `Y` be proper and let the relation `CongruenceRelation` hold. Let `t : Spec T ⟶ W` be a
point and `𝔮` a prime of `T` that contains `p` and the image of `𝔴`. Let a point `x` of `W` in `S`
factor as `Spec β ≫ t`, and let `ρ : S → D`, with `p = 0` in `D`, kill `β 𝔮`. Then the relation
holds (`New.Variety.Cancels`) at the points `Frob^{a_i} ∘ ρ` of `u_i(x)`. -/
lemma New.Variety.cancels_frobPow_comp_of_spec_map_comp_eq {p : ℕ} [ThePrime p]
    {R : CommRingCat.{0}} {W Y : Over (Spec R)} {I : Type*} [Fintype I] {n : I → ℤ} {a : I → ℕ}
    {u : I → (W ⟶ Y)} [IsProper Y.hom] {𝔴 : Ideal R} (h_cong : CongruenceRelation n 𝔴 p a u)
    {T S : CommRingCat.{0}} (t : Spec T ⟶ W.left) (𝔮 : Ideal T) [𝔮.IsPrime]
    (h𝔴 : 𝔴.map (Spec.preimage (t ≫ W.hom)).hom ≤ 𝔮) (hp𝔮 : (p : T ⧸ 𝔮) = 0) (β : T ⟶ S)
    {x : Spec S ⟶ W.left} (hβ : Spec.map β ≫ t = x) {D : Type} [CommRing D] (hpD : (p : D) = 0)
    (ρ : S →+* D) (h_ρβ_eq_zero : ∀ r ∈ 𝔮, ρ.comp β.hom r = 0) :
    Cancels n fun i : I ↦ Spec.map (ofHom ((frobPow hpD (a i)).comp ρ)) ≫ x ≫ (u i).left := by
  -- Both sides below are `Spec` of `r ↦ ρ (β r) ^ (p ^ a i)`, followed by `t ≫ (u i).left`.
  have h_point (i : I) :
      Spec.map (ofHom ((frobPow hpD (a i)).comp ρ)) ≫ x ≫ (u i).left =
        Spec.map (ofHom (Ideal.Quotient.lift 𝔮 (ρ.comp β.hom) h_ρβ_eq_zero)) ≫
          Spec.map (ofHom ((frobPow hp𝔮 (a i)).comp (Ideal.Quotient.mk 𝔮))) ≫ t ≫ (u i).left := by
    have h_ring_eq : β ≫ ofHom ((frobPow hpD (a i)).comp ρ) =
        ofHom ((frobPow hp𝔮 (a i)).comp (Ideal.Quotient.mk 𝔮)) ≫
          ofHom (Ideal.Quotient.lift 𝔮 (ρ.comp β.hom) h_ρβ_eq_zero) := by
      ext r
      -- Both ring maps send `r` to `ρ (β r) ^ p ^ a i`.
      aesop
    rw [← hβ]
    simp only [Category.assoc, ← Spec.map_comp_assoc, h_ring_eq]
  simp_rw [h_point]
  exact (cancels_quotient_of_congruenceRelation h_cong t 𝔮 h𝔴 hp𝔮).mono fun _ _ ↦
    (Spec.map (ofHom (Ideal.Quotient.lift 𝔮 (ρ.comp β.hom) h_ρβ_eq_zero)) ≫= ·)

/-- Let R be a noetherian ring with a map to O_C, W and Y proper over R, `u i : W ⟶ Y` maps with
integer weights `n i`, and p ∈ 𝔴. Suppose `∑ n i [u i(x) ∘ F^{a i}] = 0` as a formal sum of points
whenever x is a point of W over a field of characteristic p that kills 𝔴, with F the p-th power map
(`New.Variety.CongruenceRelation`). Then there is an M for which the following holds, for every z in
O_C such that (a) p divides a power of z and (b) z^{M+1} divides the image of every element of 𝔴.
For every point x of W in a p-adic test (a product of cells `c.Cell i`, which are valuation rings in
which p ≠ 0, with a map from O_C = `OC`, the valuation ring of ℂ_p) and every maximal ideal m of its
ring, there is b ∉ m with the following property. For every ring D in which p = 0 and every ring map
ρ to D that inverts b and kills the image of z, `∑ n i [u i ∘ x ∘ Spec(F^{a i} ∘ ρ)] = 0`
(`New.Variety.Cancels`). -/
lemma New.Variety.exists_cancels_frobPow_locally {p : ℕ} [ThePrime p] {R : Type} [CommRing R]
    [Algebra R OC] {W Y : Over (Spec ⟨R⟩)} {I : Type*} [Fintype I] (n : I → ℤ) (a : I → ℕ)
    (u : I → (W ⟶ Y)) [IsNoetherianRing R] [IsProper Y.hom] [IsProper W.hom] (𝔴 : Ideal R)
    (hp : ↑p ∈ 𝔴) (h_cong : CongruenceRelation n 𝔴 p a u) :
    ∃ M : ℕ, ∀ (z : OC) (j : ℕ), (p : OC) ∣ z ^ j →
      (∀ r ∈ 𝔴, z ^ (M + 1) ∣ algebraMap R OC r) →
      ∀ (c : PadicTest) (x : (testPoints.obj W).obj c)
        (m : Ideal ((PadicTest.algFunctor ⋙ restrictAlg (of R) OC).obj c)), IsMaximal m → ∃ b ∉ m,
        ∀ (D : Type) [CommRing D] (hpD : (p : D) = 0)
          (ρ : (PadicTest.algFunctor ⋙ restrictAlg (of R) OC).obj c →+* D),
          IsUnit (ρ b) → ρ (c.structureMap z) = 0 →
        Cancels n fun i : I ↦
          Spec.map (ofHom ((frobPow hpD (a i)).comp ρ)) ≫ x.down.left ≫ (u i).left := by
  classical
  -- All points of `W` in tests lift to one `t : Spec T ⟶ W` with `T` noetherian. The ideal
  -- `α = 𝔴 T` contains a product of primes `𝔮 l ⊇ α`. A point `β` of `T` in a test sends, on each
  -- factor, some `𝔮 l` into `(z)`; partition the factors by this `l`: where `z` dies, `β` factors
  -- through `T ⧸ 𝔮 l`.
  obtain ⟨T, t, h_finiteType, lift_pt⟩ := exists_locallyOfFiniteType_forall_factors W.hom
  have h_noetherian : IsNoetherianRing T :=
    isLocallyNoetherian_Spec.mp (LocallyOfFiniteType.isLocallyNoetherian (t ≫ W.hom))
  let α : Ideal T := 𝔴.map (preimage (t ≫ W.hom)).hom
  obtain ⟨J, h_fintype, 𝔮, h_prime, le_𝔮, prod_le⟩ := exists_primes_over_prod_le α
  refine ⟨Fintype.card J, fun z j hj hz c x m _ ↦ ?_⟩
  obtain ⟨β, hβ⟩ : ∃ β, map β ≫ t = x.down.left := lift_pt _ c.isTest.isComparableRing _
  -- `β` is a map of `R`-algebras, as `x` is a point over `R`: both ring maps from `R` below give
  -- the structure map of the test to `Spec R`.
  have h_over : (Spec.map β ≫ t) ≫ W.hom =
      (Opposite.unop ((specAlg (of R) (of R)).obj
        ((PadicTest.algFunctor ⋙ restrictAlg (of R) OC).obj c))).hom := (hβ =≫ W.hom).trans x.down.w
  have h_spec_preimage : Spec.map (preimage (t ≫ W.hom) ≫ β) = (Spec.map β ≫ t) ≫ W.hom := by simp
  have β_comm (r : R) : β ((preimage (t ≫ W.hom)).hom r) = c.structureMap (algebraMap R _ r) :=
    ConcreteCategory.congr_hom (map_injective (h_spec_preimage.trans h_over)) r
  have exists_prime (i : c.Index) : ∃ l, ∀ r ∈ 𝔮 l, c.structureMap z i ∣ β r i := by
    let σ : OC →+* c.Cell i := (evalRingHom _ i).comp c.structureMap
    let φ : T →+* c.Cell i := (evalRingHom _ i).comp β.hom
    refine exists_factor_forall_dvd φ prod_le (fun hz0 ↦ ?_) (fun hz1 ↦ ?_) fun r hr ↦ ?_
    · -- A power of `z` divides `p ≠ 0`.
      simpa [σ, hz0, IsCell.p_ne_zero] using map_dvd σ (hz _ hp)
    · -- The non-unit `p` divides a power of `z`.
      have h_p_dvd : (p : c.Cell i) ∣ σ z ^ j := by simpa using map_dvd σ hj
      exact mt (isUnit_of_dvd_unit h_p_dvd) out (hz1.pow j)
    · -- It suffices to treat the generators of `α`, which come from `𝔴`.
      have α_le : α ≤ comap φ (span {σ z ^ (Fintype.card J + 1)}) := by
        refine map_le_of_le_comap fun r hr ↦ mem_span_singleton.mpr ?_
        rw [← map_pow]
        exact (map_dvd σ (hz r hr)).trans (congrFun (β_comm r) i).symm.dvd
      exact mem_span_singleton.mp (α_le hr)
  choose τ hτ using exists_prime
  -- The idempotents `ε l` of the factors with `τ i = l` add up to `1`, so one is outside `m`.
  let ε (l : J) : c.ProdRing := fun i ↦ if τ i = l then 1 else 0
  have sum_ε : ∑ l, ε l = 1 := funext fun i ↦ by simp [ε]
  obtain ⟨l, hl⟩ : ∃ l, ε l ∉ m := by
    by_contra! h_all_mem
    have h_sum_mem : ∑ l, ε l ∈ m := sum_mem fun l _ ↦ h_all_mem l
    rw [sum_ε] at h_sum_mem
    exact m.one_notMem h_sum_mem
  refine ⟨ε l, hl, fun D _ hpD ρ hunit hρ ↦ ?_⟩
  have hp𝔮 : (p : T ⧸ 𝔮 l) = 0 := by simpa using eq_zero_iff_mem.mpr (le_𝔮 l (mem_map_of_mem _ hp))
  -- `z` divides `ε l` times the image of `𝔮 l`; as `ρ (ε l)` is a unit and `ρ` kills `z`, it
  -- kills that image.
  have h_ρβ_eq_zero (r : T) (hr : r ∈ 𝔮 l) : ρ.comp β.hom r = 0 := by
    let b : c.ProdRing := β r
    have dvd_ε_mul : c.structureMap z ∣ ε l * b := by
      refine pi_dvd_iff.mpr fun i ↦ ?_
      rw [Pi.mul_apply]
      by_cases hi : τ i = l
      · simpa [ε, hi, b] using hτ i r (by rwa [hi])
      · simp [ε, hi]
    have dvd_ρ : ρ (c.structureMap z) ∣ ρ b :=
      hunit.dvd_mul_left.mp ((map_dvd ρ dvd_ε_mul).trans (map_mul ..).dvd)
    rwa [hρ, zero_dvd_iff] at dvd_ρ
  -- Pull the relation over `T ⧸ 𝔮 l` back along `T ⧸ 𝔮 l → D`.
  exact cancels_frobPow_comp_of_spec_map_comp_eq h_cong t (𝔮 l) (le_𝔮 l) hp𝔮 β hβ hpD ρ h_ρβ_eq_zero

end DenseRelation

/-!
## Crystallinity and the Frobenius congruence relation

The period map of `New.Variety.exists_period_map` identifies `Bmax ⊗ Vⁿ(Y)` with cohomology on
`p`-adic tests. The classes that come from points over the period ring modulo its ideal
`New.Variety.pdIdeal` span it (`New.Variety.span_range_crysComparison_pull_eq_top`). On such classes
an operator is determined by how it moves those points. The trivial relation `[y] - [y] = 0` gives
Galois invariance.
-/

namespace New.Variety

open CategoryTheory AlgebraicGeometry TensorProduct Ideal WittVector Period Fact CharP Comparison
  Algebra.TensorProduct ConcreteCategory PadicTest ModuleCat.Algebra MulSemiringAction Function
  ULift Set

/-- Let `σ` on `S` and a natural family `s` of ring maps both lie over `τ : A →+* A`. Then `σ ⊗ s`
is a natural family of ring maps between the base changes to `S`. -/
lemma exists_tensor_twist {C : Type*} {A S : Type} [Category C] [CommRing A] [CommRing S]
    [Algebra A S] {ψ : C ⥤ C} {Θ : C ⥤ CommAlg A} {τ : A →+* A} (σ : S →+* S)
    (hσ : ∀ a : A, σ (algebraMap A S a) = algebraMap A S (τ a))
    (s : ψ ⋙ Θ ⋙ forget₂ (CommAlg A) CommRingCat ⟶ Θ ⋙ forget₂ (CommAlg A) CommRingCat)
    (hs : ∀ (c : C) (a : A),
      s.app c (algebraMap A (Θ.obj (ψ.obj c)) a) = algebraMap A (Θ.obj c) (τ a)) :
    ∃ t :
          ψ ⋙ (Θ ⋙ algBaseChange S) ⋙ forget₂ (CommAlg S) CommRingCat ⟶
            (Θ ⋙ algBaseChange S) ⋙ forget₂ (CommAlg S) CommRingCat,
      ∀ (c : C) (a : S) (x : Θ.obj (ψ.obj c)),
      t.app c (a ⊗ₜ x) = σ a ⊗ₜ show Θ.obj c from s.app c x := by
  let t (c : C) : S ⊗[A] Θ.obj (ψ.obj c) →+* S ⊗[A] Θ.obj c :=
    mapRingHom (T := Θ.obj (ψ.obj c)) (T' := Θ.obj c) τ σ (s.app c).hom
      (RingHom.ext hσ) (RingHom.ext (hs c))
  have ht (c : C) (a : S) (x : Θ.obj (ψ.obj c)) :
      t c (a ⊗ₜ x) = σ a ⊗ₜ show Θ.obj c from s.app c x := mapRingHom_tmul ..
  refine ⟨⟨fun c ↦ CommRingCat.ofHom (t c), fun c d f ↦
    CommRingCat.hom_ext (tmul_ext fun a x ↦ ?_)⟩, ht⟩
  -- Naturality is checked on pure tensors, where it is the naturality of `s`; the base change of a
  -- map acts on `a ⊗ x` by `a ⊗ f x`.
  change t d (a ⊗ₜ[A] (Θ.map (ψ.map f)).hom x) = lTensor S (Θ.map f).hom (t c (a ⊗ₜ[A] x))
  rw [ht, ht]
  exact congrArg (σ a ⊗ₜ[A] ·) (s.naturality_apply f x)

/-- A domain in which `z ^ q = z` for every `z`, for some `q > 1`, is finite: every element is a
root of the nonzero polynomial `X ^ q - X`. -/
lemma finite_of_forall_pow_eq {k : Type*} [CommRing k] [IsDomain k] {q : ℕ} (hq : 1 < q)
    (h_pow_eq : ∀ z : k, z ^ q = z) :
    Finite k := by
  -- Otherwise the monic polynomial `X ^ q - X` would be zero.
  refine .of_not_infinite fun _ ↦ ?_
  have h_ne : (.X ^ q - .X : Polynomial k) ≠ 0 :=
    (Polynomial.monic_X_pow_sub (by simpa using hq)).ne_zero
  exact h_ne (Polynomial.funext fun z ↦ by simp [h_pow_eq z])

/-- Suppose the structure map `hP.algebraMap : Ainf → Amax` commutes with the action of
`(a, σ) ∈ FrobGal`. Then there is a natural transformation `τ` from the σ-twisted period sheaf to
the untwisted one. These are the functors from p-adic tests to commutative rings sending a test `c`
to the p-adic completion of `Amax ⊗ W(c^♭)`, with the tilt taken of `PadicTest.twist σ c` for the
twisted sheaf. `τ` sends the class of `b ⊗ w` to `((a, σ) • b) ⊗ W(Frob^a)(w)`, and modulo the
divided-power ideal (`pdQuotientMap`) it sends `testToPdReduction y` to
`(testToPdReduction y) ^ p ^ a` for every `y` in the ring `c.ProdRing` of the test. -/
lemma exists_period_twist {p : ℕ} [ThePrime p] [hP : CrysPeriodAlgebra] (a : ℕ) (σ : Gp p)
    (h_smul : ∀ z : Ainf,
      ((.ofAdd a, σ) : FrobGal) • hP.algebraMap z = hP.algebraMap (((.ofAdd a, σ) : FrobGal) • z)) :
    ∃ τ :
          PadicTest.twist σ ⋙ (tilt ⋙ periodAlg Amax) ⋙ forget₂ (CommAlg Amax) CommRingCat ⟶
            (tilt ⋙ periodAlg Amax) ⋙ forget₂ (CommAlg Amax) CommRingCat,
      (∀ {c : PadicTest} {b b' : Amax} {w w' : WittVector p c.TiltRing},
        toRingHom FrobGal Amax (.ofAdd a, σ) b = b' →
        WittVector.map (iterateFrobenius c.TiltRing p a) w = w' →
        τ.app c (AdicCompletion.of _ _ (b ⊗ₜ w)) = .of _ _ (b' ⊗ₜ w')) ∧
      ∀ (c : PadicTest) (y : c.ProdRing),
        pdQuotientMap (τ.app c).hom (testToPdReduction.app ((PadicTest.twist σ).obj c) y) =
          testToPdReduction.app c y ^ p ^ a := by
  -- The action `t` on `Amax ⊗ W(c♭)` passes to the completion.
  let F : Amax →+* Amax := toRingHom FrobGal Amax (.ofAdd a, σ)
  obtain ⟨t, ht⟩ := exists_tensor_twist (ψ := PadicTest.twist σ) (Θ := tilt ⋙ wittFunctor) F h_smul
    ⟨fun c ↦ CommRingCat.ofHom (WittVector.map (iterateFrobenius c.TiltRing p a)),
      fun _ _ _ ↦ ext_apply fun _ ↦ ext fun _ ↦ (map_pow ..).symm⟩
    fun _ _ ↦ ext fun _ ↦ (congrArg (fun x ↦ x ^ p ^ a) (tiltMap_comp ..)).trans (map_pow ..).symm
  let τ :
      PadicTest.twist σ ⋙ (tilt ⋙ periodAlg Amax) ⋙ forget₂ .. ⟶
        (tilt ⋙ periodAlg Amax) ⋙ forget₂ .. :=
    (Functor.whiskerRight t
      (.mk _ (CommAlgCat.ofHom ·.hom.toIntAlgHom) ⋙ algCompletion ℤ p ⋙ forget₂ _ CommRingCat) :)
  have hτ {c b b' w w'} (hb : F b = b')
      (hw : WittVector.map (iterateFrobenius c.TiltRing p a) w = w') :
      τ.app c (.of _ _ (b ⊗ₜ w)) = .of _ _ (b' ⊗ₜ w') :=
    (adicMap_algebraMap ..).trans (congrArg _ ((ht ..).trans (congrArg₂ _ hb hw)))
  refine ⟨τ, hτ, fun c y ↦ ?_⟩
  -- Untilts exhaust the test, and `τ` raises a Teichmüller element to the power `p ^ a`.
  obtain ⟨b, rfl⟩ := untilt_surjective_of_isAbsIntegrallyClosed (p := p) y
  rw [← fontaineTheta_teichmuller]
  refine (congrArg (pdQuotientMap (τ.app c).hom) (testToPdReduction_theta ..)).trans ?_
  refine (congrArg _ (hτ (map_one _) (map_teichmuller ..))).trans ?_
  refine (testToPdReduction_theta c
    (teichmuller p (iterateFrobenius c.TiltRing p a b))).symm.trans ?_
  rw [fontaineTheta_teichmuller, fontaineTheta_teichmuller, iterateFrobenius_def, map_pow]
  exact map_pow (testToPdReduction.app c).hom _ _

/-- Let `R` be noetherian with a ring map `σ` to `O_C`, and let the image of the ideal `𝔭` of `R`
lie in the maximal ideal. For every `M` there are `x` in `O_C` and `N` such that `p` divides
`x ^ N` and `x ^ (M + 1)` divides the image of every element of `𝔭`. -/
private lemma exists_dvd_pow_and_pow_dvd {p : ℕ} [ThePrime p] {R : Type} [CommRing R]
    [IsNoetherianRing R] (σ : R →+* OC) (𝔭 : Ideal R)
    (h𝔭 : 𝔭 ≤ (IsLocalRing.maximalIdeal OC).comap σ) (M : ℕ) :
    ∃ (x : OC) (N : ℕ), (p : OC) ∣ x ^ N ∧ ∀ r ∈ 𝔭, x ^ (M + 1) ∣ σ r := by
  -- `O_C` is a Bézout ring in which every element has an `(M + 1)`-th root: take `x ^ (M + 1)`
  -- generating the image of `𝔭`. It is not a unit, so `p` divides a power of `x`.
  obtain ⟨y, hy⟩ := IsBezout.isPrincipal_of_FG _ (𝔭.fg_of_isNoetherianRing.map σ)
  obtain ⟨x, rfl⟩ := IsAbsIntegrallyClosed.exists_pow_eq (M + 1) y
  have hx_nonunit : ¬IsUnit x := fun hx ↦
    map_le_of_le_comap h𝔭 (hy.ge (subset_span rfl)) (hx.pow _)
  obtain ⟨N, hN⟩ := OC.exists_dvd_pow hx_nonunit (NeZero.ne (p : OC))
  exact ⟨x, N, hN, fun r hr ↦ mem_span_singleton.mp (hy.le (mem_map_of_mem σ hr))⟩

/-- Let `e` embed `Ω` in `ℚ̄_p` and carry `R` into the integers (`hR`), compatibly with the actions
of `Γ` through `toGp` (`hj`), and let `𝔭` be the ideal of the elements of `R` whose image has norm
`< 1` (`h𝔭`). If `s` fixes `R` and `(toGp s, f)` is a Weil pair, then `z ^ p ^ f = z` on `R ⧸ 𝔭`. -/
private lemma pow_pow_eq_of_isWeilPair {p : ℕ} [ThePrime p] {R : CommRingCat} [Algebra R Ω]
    {e : Ω →+* PadicAlgCl p} (hR : ∀ r : R, algebraMap R Ω r ∈ (intQpBar p).comap e)
    {Γ : Type} [Group Γ] [OverGp Γ p] [MulSemiringAction Γ Ω] [SMulCommClass Γ R Ω]
    (hj : ∀ (g : Γ) (x : Ω), toGp g (e x) = e (g • x)) {𝔭 : Ideal R}
    (h𝔭 : ∀ r : R, r ∈ 𝔭 ↔ ‖e (algebraMap R Ω r)‖ < 1) {s : Γ} {f : ℕ}
    (hs : IsWeilPair (toGp s) f) (z : R ⧸ 𝔭) :
    z ^ p ^ f = z := by
  -- `s` fixes `r`, and `s⁻¹`, a Frobenius for `p ^ f`, moves `r` to `r ^ p ^ f` modulo `𝔭`.
  obtain ⟨r⟩ := z
  refine Ideal.Quotient.eq.mpr ?_
  simpa [← map_inv, h𝔭, hj, norm_sub_rev] using
    hs.2 _ ((New.intQpBar p).valuation_le_one ⟨_, hR r⟩)

/-- Let `k` be a perfect domain of characteristic `p` and `πk : R →+* k`. The ring map
`R → W(k) ⧸ pdIdeal W(k)` that sends `z` to the class of the Teichmüller lift of `πk z`. -/
private noncomputable def teichReduction {p : ℕ} [ThePrime p] {R k : Type} [CommRing R]
    [CommRing k] [IsDomain k] [CharP k p] [PerfectRing k p] (πk : R →+* k) :
    R →+* WittVector p k ⧸ pdIdeal (WittVector p k) :=
  (constantCoeff.liftOfRightInverse (teichmuller p) .refl
    ⟨pdQuotientMk _, by simp [IsCompleteTorsionFree.p_mem_pdIdeal,
      isReductionMod_constantCoeff_and_isCompleteTorsionFree k]⟩).comp πk

/-- The coefficients `Bmax ⊗ A` of the period maps on `p`-adic tests, where `A` is the completion of
`Amax ⊗ W(c♭)` at the test `c`. -/
private noncomputable abbrev periodCoeff {p : ℕ} [ThePrime p] [CrysPeriodAlgebra] :
    AbFunctor PadicTest := moduleCoeff (asModules (tilt ⋙ periodAlg Amax) ⋙ tensorWith Bmax Bmax)

/-- Degree-`n` cohomology of the points of `V` in `B ⧸ pdIdeal B`, where `B` runs over the
`p`-torsion-free, `p`-adically complete `W(k)`-algebras and `R` acts through `teichReduction πk`,
with coefficients `B`. The periods `C z` of `map_J_tensorAction_eq_pull` and
`sum_linearFrob_apply_eq_zero` are indexed by its elements `z`. -/
private noncomputable abbrev crysClasses (p : ℕ) [ThePrime p] {R : CommRingCat} {k : Type}
    [CommRing k] [IsDomain k] [CharP k p] [PerfectRing k p] (πk : R →+* k) {Y : Over (Spec R)}
    (V : Subfunctor (algPointsOf R R Y)) (n : ℕ) : Type 2 :=
  H (freeAb.obj (pdReduction (teichReduction (p := p) πk) ⋙ V.toFunctor))
    (moduleCoeff (asModules (ObjectProperty.ι fun A : CommAlg (WittVector p k) ↦
      IsCompleteTorsionFree A))) n

/-- Let `z ^ p ^ a = z` on `k`, and let `W(k) → A_max` agree with `integersToPdQuotient` on the
Teichmüller lifts of the image of `R` (`hr`). Then `x ↦ x ^ p ^ a` on `B ⧸ pdIdeal B`, for the
crystalline tests `B`, is a map of `R`-algebras from the structure through `integersToPdQuotient` to
the structure through `teichReduction πk`. -/
private noncomputable def frobPowHom {p : ℕ} [ThePrime p] [CrysPeriodAlgebra] {R : CommRingCat}
    [Algebra R OC] {k : Type} [CommRing k] [IsDomain k] [CharP k p] [PerfectRing k p]
    [Algebra (WittVector p k) Amax] (πk : R →+* k)
    (hr : ∀ z : R, pdQuotientMk Amax (algebraMap (WittVector p k) Amax (teichmuller p (πk z))) =
      integersToPdQuotient (algebraMap R OC z))
    (a : ℕ) (ha : ∀ z : k, z ^ p ^ a = z) :
    pdReduction integersToPdQuotient ⋙ restrictAlg R OC ⟶
      CrysTest.restrictScalars (WittVector p k) ⋙ pdReduction (teichReduction (p := p) πk) where
  app B := CommAlg.homOfRingHom (frobPow B.p_eq_zero_mod_pdIdeal a) fun z ↦ by
    -- `z ^ p ^ a` and `z` have the same image in `k`.
    have hz : pdQuotientMk Amax (algebraMap (WittVector p k) Amax (teichmuller p (πk z))) =
        integersToPdQuotient (algebraMap R OC z) ^ p ^ a := by
      rw [← map_pow, ← map_pow, ← hr, map_pow πk, ha (πk z)]
    exact ((congrArg (pdQuotientMap _) hz).trans (map_pow ..)).symm
  naturality _ _ _ := by
    ext
    exact (map_pow ..).symm

/-- For `a = 0` the map `frobPowHom` is `x ↦ x ^ p ^ 0 = x`, so it is bijective at every test. -/
private lemma bijective_frobPowHom_zero_app {p : ℕ} [ThePrime p] [CrysPeriodAlgebra]
    {R : CommRingCat} [Algebra R OC] {k : Type} [CommRing k] [IsDomain k] [CharP k p]
    [PerfectRing k p] [Algebra (WittVector p k) Amax] (πk : R →+* k)
    (hr : ∀ z : R, pdQuotientMk Amax (algebraMap (WittVector p k) Amax (teichmuller p (πk z))) =
      integersToPdQuotient (algebraMap R OC z))
    (B : CrysTest Amax) :
    Bijective ((frobPowHom πk hr 0 pow_one).app B) := by
  have h_id : ⇑((frobPowHom πk hr 0 pow_one).app B) = id := funext pow_one
  rw [h_id]
  exact bijective_id

/-- Let `algebraMap : W(k) → A_max` be the unique lift of `ℓ : k → A_max ⧸ pdIdeal A_max` (`h_lift`,
`h_lift_unique`), where `ℓ` comes from `integersToPdQuotient` on `R` (`hℓ`). If `z ^ p ^ a = z` on
`k`, then the pair `(a, toGp s)` fixes the image of `W(k)` in `A_max`. -/
private lemma toRingHom_algebraMap_witt_eq {p : ℕ} [ThePrime p] {R : CommRingCat} [Algebra R Ω]
    [Algebra R OC] {e : Ω →+* PadicAlgCl p}
    (he_algebraMap : ∀ r : R, (e (algebraMap R Ω r) : ℂ_[p]) = algebraMap R OC r)
    {Γ : Type} [Group Γ] [OverGp Γ p] [MulSemiringAction Γ Ω] [SMulCommClass Γ R Ω]
    (he_smul : ∀ (g : Γ) (x : Ω), toGp g (e x) = e (g • x)) [CrysPeriodAlgebra]
    (h_smul : ∀ (μ : FrobGal) (b : Ainf), μ • algebraMap Ainf Amax b = algebraMap Ainf Amax (μ • b))
    {k : Type} [CommRing k] (πk : R →+* k) (hπk : Surjective πk) (ℓ : k →+* Amax ⧸ pdIdeal Amax)
    (hℓ : ∀ z : R, ℓ (πk z) = integersToPdQuotient (algebraMap R OC z))
    [Algebra (WittVector p k) Amax]
    (h_lift : ∀ w : WittVector p k,
      pdQuotientMk Amax (algebraMap (WittVector p k) Amax w) = ℓ (w.coeff 0))
    (h_lift_unique : ∀ g' : WittVector p k →+* Amax,
      (∀ w : WittVector p k, pdQuotientMk Amax (g' w) = ℓ (w.coeff 0)) →
        g' = algebraMap (WittVector p k) Amax)
    (a : ℕ) (ha : ∀ z : k, z ^ p ^ a = z) (s : Γ) (w : WittVector p k) :
    toRingHom FrobGal Amax ((.ofAdd a, toGp s) : FrobGal) (algebraMap (WittVector p k) Amax w) =
      algebraMap (WittVector p k) Amax w := by
  let μ : FrobGal := (.ofAdd a, toGp s)
  let F : Amax →+* Amax := toRingHom FrobGal Amax μ
  -- By `ha`, the map `F ∘ algebraMap` lifts the same map `ℓ` as `algebraMap`.
  refine RingHom.congr_fun (h_lift_unique (F.comp (algebraMap (WittVector p k) Amax)) fun w ↦ ?_) w
  obtain ⟨y, hy⟩ := hπk (w.coeff 0)
  obtain ⟨b : OFlat, hb⟩ := untilt_surjective_of_isAbsIntegrallyClosed (p := p) (algebraMap R OC y)
  have h_inv : μ.2 • algebraMap R OC y = algebraMap R OC y :=
    Subtype.ext (by simp [μ, ← he_algebraMap, he_smul])
  calc
    _ = pdQuotientMap F (integersToPdQuotient (algebraMap R OC y)) :=
      congrArg (pdQuotientMap F) ((h_lift w).trans (by rw [← hℓ, hy]))
    _ = integersToPdQuotient (μ • b).untilt := by
      rw [← hb, integersToPdQuotient_untilt, integersToPdQuotient_untilt, ← smul_teichmuller,
        ← h_smul]
      rfl
    _ = integersToPdQuotient ((μ.2 • b.untilt) ^ p ^ a) := congrArg _ (untilt_frobGal_smul μ b)
    _ = ℓ (w.coeff 0) := by rw [hb, h_inv, ← map_pow (algebraMap R OC), ← hℓ, map_pow, ha, hy]

/-- The main step of `ellAdicCohom.isCrystalline_and_linearFrob_rel`, for a period map `J` and a
subfunctor `V` of the points of `Y`. Let `C z` restrict on `V` to the pull-back of the crystalline
class `z` along the reduction of points (`hC`), and let every pair `(a, toGp s)` with
`z ^ p ^ a = z` on `k` fix `W(k)` in `A_max`. If `z ^ p ^ a = z` on `k`, then `(a, toGp s)` acting
on `Bmax`, with `s` acting on the cohomology, sends `C z` to a period that restricts to the
pull-back of `z` along the reduction of points followed by `Frob ^ a`. -/
private lemma map_J_tensorAction_eq_pull {p : ℕ} [ThePrime p] {R : CommRingCat} [Algebra R Ω]
    [Algebra R OC] {e : Ω →+* PadicAlgCl p}
    (he_algebraMap : ∀ r : R, (e (algebraMap R Ω r) : ℂ_[p]) = algebraMap R OC r)
    {Γ : Type} [Group Γ] [OverGp Γ p] [MulSemiringAction Γ Ω] [SMulCommClass Γ R Ω]
    (he_smul : ∀ (g : Γ) (x : Ω), toGp g (e x) = e (g • x)) [CrysPeriodAlgebra]
    (h_smul : ∀ (μ : FrobGal) (b : Ainf), μ • algebraMap Ainf Amax b = algebraMap Ainf Amax (μ • b))
    {k : Type} [CommRing k] [IsDomain k] [CharP k p] [PerfectRing k p] (πk : R →+* k)
    [Algebra (WittVector p k) Amax]
    (h_witt_fixed : ∀ a : ℕ, (∀ z : k, z ^ p ^ a = z) → ∀ (s : Γ) (w : WittVector p k),
      toRingHom FrobGal Amax ((.ofAdd a, toGp s) : FrobGal) (algebraMap (WittVector p k) Amax w) =
        algebraMap (WittVector p k) Amax w)
    (h_teichmuller : ∀ z : R,
      pdQuotientMk Amax (algebraMap (WittVector p k) Amax (teichmuller p (πk z))) =
        integersToPdQuotient (algebraMap R OC z))
    {Y : Over (Spec R)} (V : Subfunctor (algPointsOf R R Y)) (n : ℕ)
    {J : ∀ Y : Over (Spec R), Bmax ⊗[ℤ_[p]] (ellAdicCohom (ℓ := p) R Ω n).obj ⟨Y⟩ →ₗ[Bmax]
      H (freeAb.obj (testPoints.obj Y)) (periodCoeff (p := p)) n}
    (hJ : IsPadicPeriodMap he_algebraMap (Iso.refl _) he_smul J)
    (C : crysClasses p πk V n → Bmax ⊗[ℤ_[p]] (ellAdicCohom (ℓ := p) R Ω n).obj ⟨Y⟩)
    (hC : ∀ z : crysClasses p πk V n, H.map (periodCoeff (p := p))
        (freeAb.map (V.whisker (algFunctor ⋙ restrictAlg R OC)).ι) n (J Y (C z)) =
      crysComparison.pull (freeAbMap (toCrysPoints V (frobPowHom πk h_teichmuller 0 pow_one))) n z)
    (a : ℕ) (ha : ∀ z : k, z ^ p ^ a = z) (s : Γ) (z : crysClasses p πk V n) :
    H.map (periodCoeff (p := p)) (freeAb.map (V.whisker (algFunctor ⋙ restrictAlg R OC)).ι) n
        (J Y (tensorAction Bmax ((.ofAdd a, toGp s) : FrobGal)
          (ellAdicCohom.galoisAction R Ω Γ Y n s) (C z))) =
      crysComparison.pull (freeAbMap (toCrysPoints V (frobPowHom πk h_teichmuller a ha))) n z := by
  let Ψ : AbFunctor PadicTest := periodCoeff (p := p)
  let μ : FrobGal := (.ofAdd a, toGp s)
  let F : Amax →+* Amax := toRingHom FrobGal Amax μ
  -- `μ` acts on the period sheaves: by `τ` over `Amax` and by `β` over `Bmax`.
  obtain ⟨τ, hτ, h_eta⟩ := exists_period_twist a (toGp s) (h_smul μ)
  obtain ⟨β, hβ⟩ := exists_tensor_twist (τ := F) (toRingHom FrobGal Bmax μ) (by simp [F]) τ
    fun _ _ ↦ hτ rfl (map_one _)
  let cmp : Comparison Ψ Ψ := ⟨PadicTest.twist (toGp s),
    (Functor.whiskerRight β (liftCoeff (forget₂ _ RingCat ⋙ forget₂ ..)) :)⟩
  -- `F` fixes the image of `W(k)` (`h_witt_fixed`), so `τ` is a map `κ` of algebras over `W(k)`.
  let κ : PadicTest.twist (toGp s) ⋙ crysComparison.functor ⟶ crysComparison.functor :=
    { app c := ⟨ofHom ⟨(τ.app c).hom, fun _ ↦ hτ (h_witt_fixed a ha s _) (map_one _)⟩⟩
      naturality _ _ _ := by
        ext
        apply τ.naturality_apply }
  -- `incl` includes the points of `V`, `δ` twists them by `s`, and `red a ha` reduces them and
  -- composes with `Frob ^ a`.
  let incl := freeAb.map (V.whisker (algFunctor ⋙ restrictAlg R OC)).ι
  let δ := Functor.whiskerRight (toTwistAlg he_algebraMap he_smul s) (freeAb V.toFunctor)
  let red (a : ℕ) (ha : ∀ z : k, z ^ p ^ a = z) :=
    freeAbMap (toCrysPoints V (frobPowHom πk h_teichmuller a ha))
  let Zcr := freeAb (pdReduction (teichReduction (p := p) πk) ⋙ V.toFunctor)
  let α : _ ⟶ (crysComparison.trans cmp).functor ⋙ Zcr :=
    δ ≫ (PadicTest.twist (toGp s)).whiskerLeft (red 0 pow_one)
  -- Moving the reduced points by `κ` is composing them with `Frob ^ a`.
  have h_points : α ≫ Functor.whiskerRight κ Zcr = red a ha := by
    ext c : 2
    let ZV := freeAb V.toFunctor
    refine ((ZV.map_comp ..).trans ((ZV.map_comp ..) =≫ _)).symm.trans
      (congrArg _ (ext_apply fun y ↦ ?_))
    -- `x ^ p ^ 0 = x`, then `h_eta`
    exact (congrArg (pdQuotientMap (τ.app c).hom) (pow_one _)).trans (h_eta c y)
  -- Twisting the coefficients by `β` is moving the period ring by `κ`: both give `1 ⊗ τ x`.
  have h_coeff : (crysComparison.trans cmp).coeffHom =
      Functor.whiskerRight κ _ ≫ crysComparison.coeffHom := by
    ext
    -- `hβ` at `1 ⊗ x`, with `μ 1 = 1`.
    exact congrArg up ((hβ ..).trans (congrArg (· ⊗ₜ _) (toRingHom FrobGal Bmax μ).map_one))
  have h_pull : (crysComparison.trans cmp).pull α n = crysComparison.pull (red a ha) n :=
    (congrArg (pull ⟨_, ·⟩ _ n) h_coeff).trans
      ((pull_whiskerRight κ crysComparison.coeffHom _).trans
        (congrArg (crysComparison.pull · n) h_points))
  -- `J` turns the action of `μ` and `s` into the comparison `cmp`, because `β` acts by `μ` on
  -- `Bmax` and fixes the Witt vectors with coefficients in the prime field.
  have h_twist : J Y (tensorAction Bmax μ (ellAdicCohom.galoisAction R Ω Γ Y n s) (C z)) =
      cmp.pull (freeAbMap (toTwistPoints he_algebraMap he_smul s Y)) n (J Y (C z)) :=
    hJ.equivariant Y s _ cmp.coeffHom (fun c b w hw ↦
      -- The coordinates of `w` are fixed by Frobenius, so `Frob ^ a` fixes `w`.
      have h_frob_w : WittVector.map (iterateFrobenius c.TiltRing p a) w = w :=
        ext fun i ↦ (congrFun (pow_iterate ..) _).symm.trans (iterate_fixed (hw i) _)
      congrArg up ((hβ ..).trans (congrArg _ (hτ (map_one _) h_frob_w)))) _
  -- Twisting points by `s` commutes with the inclusion of the points of `V`.
  have h_square : incl ≫ freeAbMap (toTwistPoints he_algebraMap he_smul s Y) =
      δ ≫ cmp.functor.whiskerLeft incl :=
    freeAb.hom_ext fun _ _ ↦ rfl
  refine .trans ?_ ((pull_trans z).trans (DFunLike.congr_fun h_pull z))
  calc
    _ = cmp.pull δ n (H.map Ψ incl n (J Y (C z))) :=
      (congrArg (H.map Ψ incl n) h_twist).trans (map_pull_eq_pull_map h_square n _)
    _ = cmp.pull δ n (crysComparison.pull (red 0 pow_one) n z) := congrArg _ (hC z)

/-- The congruence relation of `ellAdicCohom.isCrystalline_and_linearFrob_rel` on one period `C z`.
Let `periodCoeff` have Zariski descent (`h_zar`), let `V` be cohomologically dense (`hV_dense`), and
let the periods be fixed by `Γ` (`h_fixed`) and moved by the Weil pairs as in `h_action`. If the
relation of the points `Frob ^ a i (u i x)` holds near every closed point of a test once `p` and
`x₀` vanish (`h_rel_loc`), and `integersToPdQuotient` kills `x₀`, then
`∑ m i • (u i)^* ∘ linearFrob (γ i) (a i)` kills `C z`. -/
private lemma sum_linearFrob_apply_eq_zero {p : ℕ} [ThePrime p] {R : CommRingCat} [Algebra R Ω]
    [Algebra R OC] {e : Ω →+* PadicAlgCl p}
    (he_algebraMap : ∀ r : R, (e (algebraMap R Ω r) : ℂ_[p]) = algebraMap R OC r)
    {Γ : Type} [Group Γ] [OverGp Γ p] [MulSemiringAction Γ Ω] [SMulCommClass Γ R Ω]
    (he_smul : ∀ (g : Γ) (x : Ω), toGp g (e x) = e (g • x)) [CrysPeriodAlgebra]
    {k : Type} [CommRing k] [IsDomain k] [CharP k p] [PerfectRing k p] (πk : R →+* k)
    [Algebra (WittVector p k) Amax]
    (h_teichmuller : ∀ z : R,
      pdQuotientMk Amax (algebraMap (WittVector p k) Amax (teichmuller p (πk z))) =
        integersToPdQuotient (algebraMap R OC z))
    {W Y : Over (Spec R)} [IsProper W.hom] [IsCharted W Ω] (V : Subfunctor (algPointsOf R R Y))
    (n : ℕ) {J : ∀ Y : Over (Spec R), Bmax ⊗[ℤ_[p]] (ellAdicCohom (ℓ := p) R Ω n).obj ⟨Y⟩ →ₗ[Bmax]
      H (freeAb.obj (testPoints.obj Y)) (periodCoeff (p := p)) n}
    (hJ : IsPadicPeriodMap he_algebraMap (Iso.refl _) he_smul J)
    (h_zar : HasZariskiDescent PadicTest.ringFunctor (periodCoeff (p := p)))
    (hV_dense : IsCohomDense (periodCoeff (p := p)) (V.whisker (algFunctor ⋙ restrictAlg R OC)))
    (C : crysClasses p πk V n → Bmax ⊗[ℤ_[p]] (ellAdicCohom (ℓ := p) R Ω n).obj ⟨Y⟩)
    (h_crys : IsCrystalline (ellAdicCohom.galoisAction R Ω Γ Y n))
    (h_fixed : ∀ {𝓕 : Filter Γ} (z : crysClasses p πk V n),
      C z ∈ fixedPeriods (ellAdicCohom.galoisAction R Ω Γ Y n) Bmax 𝓕)
    (h_action : ∀ (a : ℕ) (ha : ∀ z : k, z ^ p ^ a = z) (s : Γ) (z : crysClasses p πk V n),
      H.map (periodCoeff (p := p)) (freeAb.map (V.whisker (algFunctor ⋙ restrictAlg R OC)).ι) n
          (J Y (tensorAction Bmax ((.ofAdd a, toGp s) : FrobGal)
            (ellAdicCohom.galoisAction R Ω Γ Y n s) (C z))) =
        crysComparison.pull (freeAbMap (toCrysPoints V (frobPowHom πk h_teichmuller a ha))) n z)
    (h_pow : ∀ {s : Γ} {f : ℕ}, IsWeilPair (toGp s) f → ∀ z : k, z ^ p ^ f = z)
    {ι : Type} [Fintype ι] (u : ι → (W ⟶ Y)) (a : ι → ℕ) (γ : ι → Γ) (m : ι → ℤ)
    (hW : ∀ i : ι, IsWeilPair (toGp (γ i)) (a i)) (x₀ : OC) (hx_zero : integersToPdQuotient x₀ = 0)
    (h_rel_loc : ∀ (c : PadicTest) (x : (testPoints.obj W).obj c)
      (𝔪 : Ideal ((algFunctor ⋙ restrictAlg R OC).obj c)), 𝔪.IsMaximal →
      ∃ b ∉ 𝔪, ∀ (D : Type) [CommRing D] (hpD : (p : D) = 0)
        (ρ : (algFunctor ⋙ restrictAlg R OC).obj c →+* D),
        IsUnit (ρ b) → ρ (c.structureMap x₀) = 0 →
          Cancels m fun i : ι ↦ Spec.map (CommRingCat.ofHom ((frobPow hpD (a i)).comp ρ)) ≫
            x.down.left ≫ (u i).left)
    (z : crysClasses p πk V n) :
    (∑ i : ι,
      m i • (((ellAdicCohom R Ω n).map (u i).op).hom.restrictScalars ℤ_[p]).baseChange Bmax ∘ₗ
        linearFrob (ellAdicCohom.galoisAction R Ω Γ Y n) (γ i) (a i)) (C z) = 0 := by
  let Ψ : AbFunctor PadicTest := periodCoeff (p := p)
  let V' := V.whisker (algFunctor ⋙ restrictAlg R OC)
  -- It suffices to work on the dense set `T` of points of `W` that every `u i` sends into `V`.
  let T := ⨅ i, V'.preimage (testPoints.map (u i))
  have hT : IsCohomDense Ψ T := InfClosed.iInf_mem (s := IsCohomDense Ψ) (fun _ hU _ ↦ hU.inf)
    (.of_top_le le_rfl) fun _ ↦ hV_dense.preimage _
  refine (hJ.bijective W).injective ((hT.isCohomEquiv n).1 ?_)
  -- `linearFrob` acts on the fixed period `C z` as the Weil pair, giving the class `y i`, and `J`
  -- commutes with pull-backs.
  let y (i : ι) : H (freeAb.obj (testPoints.obj Y)) Ψ n :=
    J Y (tensorAction Bmax ((.ofAdd (a i), toGp (γ i)) : FrobGal)
      (ellAdicCohom.galoisAction R Ω Γ Y n (γ i)) (C z))
  simp [linearFrob_apply h_crys.isPotentiallyCrystalline (hW _), h_fixed, hJ.natural, Ψ, H.map_map]
  show ∑ i, m i • H.map Ψ (freeAb.map T.ι ≫ freeAb.map (testPoints.map (u i))) n (y i) = 0
  -- `δ i` takes a point `w` of `T` to `u i w`; `red i` takes it on to the point over the period
  -- ring modulo divided powers, composed with `Frob ^ a i`.
  let δ (i : ι) : T.toFunctor ⟶ V'.toFunctor := T.homOfLe (iInf_le _ i) ≫ Subfunctor.fromPreimage ..
  let red (i : ι) := toCrysPoints V (frobPowHom πk h_teichmuller (a i) (h_pow (hW i)))
  let v (i : ι) := δ i ≫ red i
  -- On `T` the `i`-th term is the pull-back of the crystalline class `z` along `v i`.
  have h_term (i : ι) : H.map Ψ (freeAb.map T.ι ≫ freeAb.map (testPoints.map (u i))) n (y i) =
      crysComparison.pull (freeAbMap (v i)) n z :=
    calc
      _ = H.map Ψ (freeAb.map (δ i)) n (H.map Ψ (freeAb.map V'.ι) n (y i)) :=
        (congrArg (H.map Ψ · n (y i)) freeAb.hom_ext).trans (H.map_comp ..)
      _ = H.map Ψ (freeAb.map (δ i)) n (crysComparison.pull (freeAbMap (red i)) n z) :=
        congrArg _ (h_action _ (h_pow (hW i)) _ z)
      _ = _ := H.map_map (δ i) (red i) _
  -- So it remains to see that the locus where `∑ m i [v i w] = 0` is locally everything in `T`.
  suffices h_loc : IsZariskiLocallyTop PadicTest.ringFunctor (relationLocus m v) from
    (Finset.sum_congr rfl fun i _ ↦ congrArg (m i • ·) (h_term i)).trans
      (H.sum_map_eq_zero_of_relationLocus m v (h_zar h_loc).isCohomEquiv _)
  intro c w 𝔪 h𝔪
  obtain ⟨b, hb, h_rel⟩ := h_rel_loc c (T.ι.app c w) 𝔪 h𝔪
  refine ⟨b, hb, fun B f hf ↦ ?_⟩
  -- Apply `h_rel` in the period ring of `B` modulo divided powers, where `p` and `x₀` vanish.
  let π := (testToPdReduction.app B).hom.comp f
  have h_cancel : Cancels m fun i ↦ Spec.map (CommRingCat.ofHom
      ((frobPow (crysThickening.obj B).p_eq_zero_mod_pdIdeal (a i)).comp π.toRingHom)) ≫
        (T.ι.app c w).down.left ≫ (u i).left :=
    h_rel _ _ π.toRingHom (hf.map (testToPdReduction.app B).hom)
      ((π.commutes x₀).trans ((congrArg (pdQuotientMap _) hx_zero).trans (map_zero _)))
  refine ((congrArg _ (funext fun i ↦ ?_)).mpr h_cancel).mono fun _ _ he ↦
    Subtype.ext (down_injective (Over.OverMorphism.ext he))
  -- The point `v i` of the image of `w` in `B` is `Frob ^ a i (u i w)`, read through `π`.
  exact (_ ≫= Category.assoc ..).trans (Spec.map_comp_assoc ..).symm

/-- Let `R` be a noetherian ring and `K` a field. Let `Ω` be an algebraic closure of `ℚ` that is an
algebra over `R` and over `K`, compatibly with a map `R → K`. Let `A` be the valuation ring of a
`p`-adic place of `Ω` over `K` (`GaloisRep.PadicPlaceEmbedding`), with `R` mapping into `A`. Let
`Y`, `W` be proper over `R`, charted over `Ω`, and `Y` also charted over `R`. Suppose
`∑ m i [Frob ^ a i (u i x)] = 0` at the field-valued points `x` of `W` that kill the prime of `R` of
elements whose valuation in `A` is `< 1`. Let each `γ i` lie in the decomposition group of `A` in
the Galois group of `Ω` over `K` (`decompGroup`). Suppose its image in `G_p` forms an `IsWeilPair`
with `a i`. (a) The representation of this decomposition group on `Vⁿ(Y)` is crystalline. (b)
`∑ m i • (u i)^* ∘ β i = 0` on `Bmax ⊗ Vⁿ(Y)`, where `β i` is `linearFrob` of this representation
at `γ i` and `a i`. -/
lemma ellAdicCohom.isCrystalline_and_linearFrob_rel {p : ℕ} [ThePrime p] {R : CommRingCat}
    (K : Type) [Field K] [Algebra R Ω] [Algebra K Ω] [Algebra R K] [IsScalarTower R K Ω]
    {A : ClosurePlace} [I : GaloisRep.PadicPlaceEmbedding K A p]
    (hR : ∀ r : R, algebraMap R Ω r ∈ A) {W Y : Over (Spec R)} [IsNoetherianRing R]
    [hY_charted : IsCharted Y R] [IsCharted Y Ω] [IsProper Y.hom] (n : ℕ) [IsProper W.hom]
    [IsCharted W Ω] {ι : Type} [Fintype.{0} ι] (u : ι → (W ⟶ Y)) (a : ι → ℕ)
    (γ : ι → decompGroup Gal(Ω/K) A) (m : ι → ℤ)
    (h_cong : CongruenceRelation m {r : R | A.valuation (algebraMap R Ω r) < 1} p a u)
    (hW : ∀ i : ι, IsWeilPair (I.toGp (γ i)) (a i)) :
    let ρ : Representation ℚ_[p] (decompGroup Gal(Ω/K) A) ((ellAdicCohom R Ω n).obj (.op Y)) :=
      galoisAction R Ω (decompGroup Gal(Ω/K) A) Y n
    -- (a) the cohomology is crystalline
    IsCrystalline ρ ∧
    -- (b) the congruence relation holds for the operators `linearFrob` of the Weil pairs
    ∑ i : ι,
      m i • (((ellAdicCohom R Ω n).map (u i).op).hom.restrictScalars ℤ_[p]).baseChange Bmax ∘ₗ
        linearFrob ρ (γ i) (a i) = 0 := by
  -- The crystalline classes `z` on `Y` give periods `C z` that span. A Weil pair `(toGp s, a)` acts
  -- on `C z` as the pull-back along `Frob ^ a` on points (`h_action`). The case `a = 0` shows that
  -- they are fixed; the relation between the points `Frob ^ a i (u i x)` gives the congruence
  -- relation.
  intro ρ
  -- `φ` is a Frobenius element of the decomposition group; the place `A` is the one induced by `e`.
  obtain ⟨kc, -, -, -, _, ⟨φ, rfl⟩, hφ⟩ := Lift.exists_kummerChart (decompGroup Gal(Ω/K) A)
  -- `I` gives the map `toGp`, the embedding `e`, the equation `(intQpBar p).comap e = A` (which
  -- replaces `A`), the equivariance `hj` of `e`, and `h_completion` (`toGp` is an open embedding).
  obtain @⟨I, e, ⟨rfl, hj⟩, h_completion⟩ := I
  -- The embedding `e` maps `R` into the integers of `ℂ_[p]`; `k` is the residue ring of `R` at the
  -- prime `𝔭` under the maximal ideal.
  let σ : R →+* valRingCp p :=
    ((algebraMap ..).comp (e.comp (algebraMap R Ω))).codRestrict (valRingCp p) (by simpa)
  have hσ (r : R) : (e (algebraMap R Ω r) : ℂ_[p]) = σ r := rfl
  let h_algebra : Algebra R OC := σ.toAlgebra
  let 𝔭 : Ideal R := (IsLocalRing.maximalIdeal _).comap σ
  let k : Type := R ⧸ 𝔭
  have h𝔭 (r : R) : r ∈ 𝔭 ↔ ‖e (algebraMap R Ω r)‖ < 1 := by
    simp [𝔭, valRingCp.dvd_iff_norm_le, isUnit_iff_dvd_one, ← hσ]
  have hp : (p : R) ∈ 𝔭 := by simp [𝔭, out]
  -- The decomposition group fixes `R`, so a Weil pair `(toGp s, f)` forces `z ^ p ^ f = z` on `k`.
  have h_pow {s} {f : ℕ} : IsWeilPair (I.toGp s) f → ∀ z : k, z ^ p ^ f = z :=
    pow_pow_eq_of_isWeilPair hR hj h𝔭
  -- The inverse of `φ` gives a Weil pair with `0 < f`, so the domain `k` is finite: a finite
  -- field of characteristic `p`.
  have hφ' : IsWeilPair (I.toGp φ⁻¹) kc.f := by simpa
  have h_finite : Finite k := finite_of_forall_pow_eq (by simp [one_lt_pow₀, out]) (h_pow hφ')
  let h_field : Field k := (Finite.isField_of_domain k).toField
  have h_charP : CharP k p :=
    (CharP.charP_iff_prime_eq_zero out).mpr (Quotient.eq_zero_iff_mem.mpr hp)
  -- `V` is locally everything in `Y` and is built from pieces étale over tori.
  obtain ⟨V, hV⟩ := hY_charted.exists_isCharting
  -- Choose `x` with `x ^ (M + 1)` dividing the image of `𝔭` and `N` with `p ∣ x ^ N`. By `hM`
  -- the given relation then holds modulo `(p, x)` near every closed point of a test.
  obtain ⟨M, hM⟩ := exists_cancels_frobPow_locally m a u 𝔭 hp
    (by simpa [← h𝔭, comap_apply_lt_one_iff] using h_cong)
  obtain ⟨x, N, hN, hx_dvd⟩ := exists_dvd_pow_and_pow_dvd σ 𝔭 le_rfl M
  -- An `Ainf`-algebra structure on `Amax` for which `integersToPdQuotient` kills `x`, hence `σ 𝔭`.
  -- So `integersToPdQuotient` induces a map `k → Amax ⧸ pdIdeal Amax`, with exactly one lift
  -- `g : W(k) → Amax`.
  obtain ⟨hP, _, h_smul, hx_zero⟩ := exists_crysPeriodAlgebra hN
  have h_ker (r : R) (hr : r ∈ 𝔭) : integersToPdQuotient.comp σ r = 0 := by
    simpa [hx_zero] using map_dvd integersToPdQuotient (hx_dvd r hr)
  let ℓ : k →+* Amax ⧸ pdIdeal Amax := Ideal.Quotient.lift 𝔭 (integersToPdQuotient.comp σ) h_ker
  obtain ⟨g, hg, hg_unique⟩ := hP.existsUnique_witt_lift (cast_eq_zero k p) ℓ
  algebraize [g]
  -- `g` agrees with `integersToPdQuotient` on the Teichmüller lifts of the image of `R`.
  have hr (z : R) : pdQuotientMk Amax (g (teichmuller p (⟦z⟧ : k))) = integersToPdQuotient (σ z) :=
    hg _
  -- The period maps `J` to the cohomology on `p`-adic tests with coefficients `Ψ`: natural in the
  -- scheme, compatible with twists, and bijective on proper charted schemes.
  let Ψ : AbFunctor PadicTest := periodCoeff (p := p)
  choose J hJ using fun n : ℕ ↦ exists_period_map hσ Bmax (.refl _) n hj hP.toIsPeriodRingPair
  -- `Ψ` has Zariski descent, so `V` is dense and `J` followed by restriction to `V` is bijective.
  have h_zar : HasZariskiDescent _ Ψ := (hasPartitions_periodAlg (S := Amax) Bmax
    (.refl _)).hasZariskiDescent (𝟙 _) (by simp) (·.isTest.isComparableRing)
  let V' := V.whisker (algFunctor ⋙ restrictAlg R OC)
  have hV_dense : IsCohomDense Ψ V' := h_zar (hV.1.whisker _)
  let periodEquiv (n : ℕ) :
      Bmax ⊗[ℤ_[p]] (ellAdicCohom R Ω n).obj ⟨Y⟩ ≃ₗ[Bmax] H (freeAb.obj V'.toFunctor) Ψ n :=
    .ofBijective (H.mapₗ .. ∘ₗ J n Y) ((hV_dense.isCohomEquiv n).comp ((hJ n).bijective Y))
  -- `pullFrob a ha z` is the pull-back of a crystalline class `z` along the reduction of points
  -- followed by `Frob ^ a` (`frobPowHom`); `C z` is the period with
  -- `periodEquiv n (C z) = pullFrob 0 _ z`.
  let pullFrob (a : ℕ) (ha : ∀ z : k, z ^ p ^ a = z) :=
    crysComparison.pull (freeAbMap (toCrysPoints V (frobPowHom (algebraMap R k) hr a ha))) n
  choose C hC using fun z ↦ (periodEquiv n).surjective (pullFrob 0 pow_one z)
  -- The main step (`map_J_tensorAction_eq_pull`): `(a, toGp s)` together with `ρ s` sends `C z`
  -- to the preimage of `pullFrob a ha z`.
  have h_action (a : ℕ) (ha : ∀ z : k, z ^ p ^ a = z) s z :
      periodEquiv n (tensorAction Bmax ((.ofAdd a, toGp s) : FrobGal) (ρ s) (C z)) =
        pullFrob a ha z :=
    map_J_tensorAction_eq_pull hσ hj h_smul (algebraMap R k)
      (toRingHom_algebraMap_witt_eq hσ hj h_smul (algebraMap R k) Ideal.Quotient.mk_surjective ℓ
        (fun _ ↦ rfl) hg hg_unique) hr V n (hJ n) C hC a ha s z
  -- The classes `pullFrob 0 _ z` span, since `frobPowHom _ _ 0 _` is an isomorphism; so the
  -- periods `C z` span.
  have h_span : Submodule.span Bmax (.range C) = ⊤ := by
    have h_range : Submodule.span Bmax (.range (pullFrob 0 pow_one)) = ⊤ :=
      span_range_crysComparison_pull_eq_top V _
        (isoOfAppBijective _ (bijective_frobPowHom_zero_app (algebraMap R k) hr)).isIso_hom
        (isCompleteTorsionFree_wittVector k k) hV (irreducible p)
        (fun n ↦ .equiv (equivOfCompatibleSMul _ ℚ_[p] .. ≪≫ₗ periodEquiv n)) n
    -- `using!`: the groups of `pullFrob 0 _` and of `periodEquiv n` agree only after unfolding.
    simpa [← Submodule.map_eq_top_iff (e := periodEquiv n), Submodule.map_span, ← range_comp', hC]
      using! h_range
  -- The case `a = 0` of `h_action` says that every `s` fixes `C z`.
  have h_fixed {𝓕 : Filter _} z : C z ∈ fixedPeriods ρ Bmax 𝓕 :=
    .of_forall fun s ↦ (periodEquiv n).injective ((h_action 0 pow_one s z).trans (hC z).symm)
  have h_crys : IsCrystalline ρ :=
    eq_top_mono (Submodule.span_mono (range_subset_iff.mpr h_fixed)) h_span
  -- The relation on each period `C z` (`sum_linearFrob_apply_eq_zero`).
  exact ⟨h_crys, LinearMap.ext_on_range h_span fun z ↦
    sum_linearFrob_apply_eq_zero hσ hj (algebraMap R k) hr V n (hJ n) h_zar hV_dense C h_crys
      h_fixed h_action h_pow u a γ m hW x hx_zero (hM x N hN hx_dvd) z⟩

end New.Variety
