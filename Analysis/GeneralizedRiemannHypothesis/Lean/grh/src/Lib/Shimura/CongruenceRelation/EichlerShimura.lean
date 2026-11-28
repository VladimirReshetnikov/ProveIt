import Lib.Cohomology.SmoothBaseChange

/-!
# The congruence relation and the trivial action of inertia on ℓ-adic cohomology

The Eichler–Shimura argument: a relation between Frobenius twists of points in characteristic p
gives a relation between pull-backs and Galois action on ℓ-adic cohomology.

* `New.Variety.ellAdicCohom.ellAdicPull_frobEnd`: the absolute Frobenius acts trivially on
  cohomology.
* `New.Variety.ellAdicCohom.congruence_relation`: the congruence relation
  `New.Variety.CongruenceRelation` on points gives ∑ mᵢ uᵢ^* g^(−eᵢ) = 0 on Vⁿ(Y), for a Frobenius
  element g.
* `New.Variety.ellAdicCohom.galoisAction_eq_one_of_inertia`: inertia acts trivially (the case q = 1
  of the relation).

The idea: extend classes from Ω to the valuation ring A, then restrict to the special fibre.
`New.Variety.ellAdicCohom` is X ↦ Vⁿ(X) = ℚ_ℓ ⊗ Hⁿ(X_Ω, ℤ_ℓ), with the action
`New.Variety.ellAdicCohom.galoisAction` of Γ; `New.Variety.ellAdicPull` is the pull-back along a map
of free abelian functors (`freeAb` sends a functor to its pointwise free abelian group);
`New.Variety.IsCharted` is the hypothesis on Y that stands in for smoothness: it gives smooth base
change, so that pull-back from A to Ω is bijective on the cohomology of Y.

Notions from other files:
* `New.IsFrob`: σ stabilises the valuation subring A and σx ≡ x^q modulo the maximal ideal for all x
  in A; for q = 1 this is membership in the inertia group.
* `New.Variety.mapOnTests`: For a map u: X → Y of set-valued functors on rings, its restriction to a
  map of functors on test rings.
* `New.Variety.ellAdicCoeff`: The coefficient `ℤ_ℓ`: a test ring `A` goes to the Witt vectors of the
  ring of locally constant functions `Spec A → 𝔽_ℓ`.

## Relation to the literature

Known result: Smooth proper reduction gives unramified ℓ-adic cohomology, and Frobenius relations
pass to it. Here the base is the valuation ring of a place. Source: Stacks project, Tags 0GKD (SGA4
XVI 2.2) and 03SN (SGA5 XV); Deligne, Formes modulaires et représentations ℓ-adiques, Sém. Bourbaki
355 (1969).
-/

namespace New.Variety.ellAdicCohom

open CategoryTheory AlgebraicGeometry CommRingCat ellAdicPull Comparison

variable {ℓ : ℕ} [ThePrime ℓ]
  {R : CommRingCat} [Algebra R Ω]
  {Γ : Type*} [Group Γ] [MulSemiringAction Γ Ω] [SMulCommClass Γ R Ω]
  {A : ClosurePlace} (hR : ∀ r : R, algebraMap R Ω r ∈ A) (hℓ : IsUnit (ℓ : A))
  {W Y : Over (Spec R)} [IsCharted Y R] [IsProper Y.hom]
  {n p f : ℕ} [Fact p.Prime] (hp : A.valuation p < 1)
  {U : PointFunctor} (hU_char : ∀ B : CommRingCat, U B → (p : B) = 0) (j : ℕ)

/-- For a functor U on rings with points only in rings where p = 0, the endomorphism sending x
in U(B) to its image under b ↦ b^(p^j). -/
def frobEnd : U ⟶ U where
  app B := ↾fun x ↦ U.map (ofHom (frobPow (hU_char B x) j)) x
  naturality := by
    intros
    ext
    dsimp
    simp_rw [← U.map_comp_apply]
    congr 3
    aesop

/-- The value of `New.Variety.ellAdicCohom.frobEnd` at a point x ∈ U(B): the image of x under the
ring map b ↦ b^(p^j) of B. -/
lemma frobEnd_app (hU_char : ∀ B : CommRingCat, U B → (p : B) = 0) (j : ℕ) (B : CommRingCat)
    (x : U B) :
    (frobEnd hU_char j).app B x = U.map (ofHom (frobPow (hU_char B x) j)) x :=
  rfl

/-- The absolute Frobenius acts trivially on ℓ-adic cohomology. Let p = 0 in every ring B in which
U has a point (`hU_char`). Then the endomorphism `New.Variety.ellAdicCohom.frobEnd` of U, which
moves a point x ∈ U(B) along the ring map b ↦ b^(p^j) of B, pulls back to the identity of
ℚ_ℓ ⊗ Hⁿ(U, ℤ_ℓ). -/
lemma ellAdicPull_frobEnd (hU_char : ∀ B : CommRingCat, U B → (p : B) = 0) (j : ℕ) :
    ellAdicPull n (freeAb.map (mapOnTests (frobEnd hU_char j))) = 1 := by
  ext x
  refine congrArg (1 ⊗ₜ ·) ?_
  -- Frobenius as an endomorphism `η` of the functor `(A, x) ↦ A` on the category of points of `U`
  let η : elementsProj (testIncl ⋙ U) ⟶ elementsProj (testIncl ⋙ U) :=
    { app A := ⟨ofHom (frobPow (hU_char _ A.val) j)⟩
      naturality _ _ _ := by
        ext
        exact (map_pow ..).symm }
  -- it acts trivially on the coefficients, since it fixes every prime ideal
  have h_coef : Functor.whiskerRight η (ellAdicCoeff (ℓ := ℓ)) ≫ 𝟙 _ = 𝟙 _ := by
    ext A ⟨⟨y⟩⟩
    -- the coefficients at `A` are functions on `Spec A`, moved along `comap` of `η`
    congrm ⟨⟨fun i ↦ ⟨_ ∘ ?_, _⟩⟩⟩
    show PrimeSpectrum.comap (Hom.hom (testIncl.map (η.app A))) = fun q ↦ q
    ext q
    simp [η, q.isPrime.pow_mem_iff_mem, NeZero.pos]
  -- pulling back to the category of points along the tautological point is injective
  refine (hasUniversalPoints_elements.isBijective n).injective ?_
  -- `frobEnd` moves the tautological point as `η` does
  have h_square : 𝟙 (freeAb.obj (onePointFunctor (testIncl ⋙ U).Elements)) ≫
      freeAbMap tautologicalSection ≫ Functor.whiskerRight η (freeAb.obj (testIncl ⋙ U)) =
        freeAbMap tautologicalSection ≫ (restrict (elementsProj (testIncl ⋙ U))
          ellAdicCoeff).functor.whiskerLeft (freeAb.map (mapOnTests (frobEnd hU_char j))) :=
    rfl
  calc
    _ = (Comparison.restrict (elementsProj _) ellAdicCoeff).pull
      (freeAbMap tautologicalSection ≫ Functor.whiskerRight η _) n x :=
      (map_pull_eq_pull_map h_square n x).symm.trans (H.map_id _)
    -- `η` can be moved from the point to the coefficients, where it is trivial
    _ = pull ⟨_, Functor.whiskerRight η ellAdicCoeff ≫ 𝟙 _⟩ (freeAbMap tautologicalSection) n x :=
      (DFunLike.congr_fun (pull_whiskerRight η ..) x).symm
    _ = _ := congrArg (fun c ↦ pull ⟨_, c⟩ (freeAbMap tautologicalSection) n x) h_coef

include hR hℓ hp

/-- The Eichler–Shimura relation. Let A ⊂ Ω (an algebraic closure of ℚ) be a valuation ring
containing the image of R (`hR`), with p in its maximal ideal (`hp`) and ℓ a unit (`hℓ`); let Γ act
on Ω by R-algebra automorphisms, and let g ∈ Γ be a Frobenius for p^f at A, i.e. g stabilises A and
acts as x ↦ x^(p^f) modulo its maximal ideal. Let W, Y be proper over R with Y charted over R
(`New.Variety.IsCharted`); if uᵢ : W → Y satisfy ∑ mᵢ [Frob_(p^(f eᵢ)) uᵢ(w)] = 0 (in the sense of
`Cancels`; Frob_q composes a k-point with Spec of the map x ↦ x^q of k) at the field points w of W
of characteristic p killing the preimage in R of A's maximal ideal
(`New.Variety.CongruenceRelation`), then ∑ mᵢ uᵢ^*(g^(−eᵢ) x) = 0 for every x in Vⁿ(Y) = ℚ_ℓ ⊗ Hⁿ(Y
×_R Ω, ℤ_ℓ), with Γ acting through Ω. -/
lemma congruence_relation [IsProper W.hom] {g : Γ} (hg : IsFrob A (p ^ f) g) {I : Type} [Fintype I]
    (u : I → (W ⟶ Y)) (e : I → ℕ) (m : I → ℤ)
    (h_cong : CongruenceRelation m (algebraMap R Ω ⁻¹' A.nonunits) p (fun i : I ↦ e i * f) u)
    (x : (ellAdicCohom R Ω n).obj (Opposite.op Y)) :
    ∑ i : I,
      m i • (ellAdicCohom R Ω n).map (u i).op (galoisAction R Ω Γ Y n (g⁻¹ ^ e i) x) = 0 := by
  -- Lift `x` to a class `y` over the valuation ring `A`, restrict to the special fibre `U₀`, where
  -- `g⁻¹ ^ e i` is undone by Frobenius, and use the relation at geometric points of `U₀`.
  algebraize [RingHom.codRestrict _ A hR]
  -- smooth base change: pull-back from `A` to `Ω` is bijective on the cohomology of `Y`
  obtain ⟨y, rfl⟩ := (isTestCohomEquiv_baseChangeTransition hp hℓ
    Y).bijective_ellAdicPull.surjective x
  -- `σ i` is `g⁻¹ ^ e i` on `A`, and `μ i` sends `(x, ω)` to `(u i x, ω ∘ σ i)`
  let σ (i : I) : A →+* A := (MulSemiringAction.toRingHom ..).restrict A A fun a ↦
    (mem_decompGroup_iff.mp (pow_mem (inv_mem hg.left) (e i)) a).mpr
  -- `σ i` fixes the image of `R`
  have h_σ_alg (i : I) : ofHom (algebraMap R A) ≫ ofHom (σ i) = ofHom (algebraMap R A) :=
    CommRingCat.hom_ext <| RingHom.ext fun r ↦ Subtype.ext <| smul_algebraMap _ r
  let μ (i : I) : geomPoints R A W ⟶ geomPoints R A Y :=
    (geomPoints R A).map (u i) ≫ baseChangeTransition _ (ofHom (σ i)) (h_σ_alg i)
  -- it suffices that the sum vanishes over `A`, before passing to `Ω`
  suffices h_sum : ∑ i, m i • ellAdicPull n (freeAb.map (mapOnTests (μ i))) y = 0 by
    let toA :
        testIncl ⋙ baseChangeOf (pointsToBase W.hom) (ofHom (algebraMap R A) ≫ ofHom A.subtype) ⟶
          testIncl ⋙ geomPoints R A W :=
      mapOnTests (Y := geomPoints R A W) (baseChangeTransition _ (ofHom A.subtype) rfl)
    -- each term is the pull-back along `toA` of the matching term over `A`; `erw`, since the
    -- terms match these lemmas only up to unfolding definitions
    conv_lhs =>
      enter [2, i]
      erw [comp, ← freeAb.map_comp, comp, ← freeAb.map_comp, freeAb.map_comp toA (mapOnTests (μ i)),
        ← comp, ← map_zsmul]
    erw [← map_sum, h_sum, map_zero]
    rfl
  -- the special fibre: the points that kill the maximal ideal of `A`; they have characteristic `p`
  let s₀ : geomPoints R A W ⟶ reprBy (of A) :=
    fibreProd.snd (pointsToBase W.hom) (reprMap (ofHom (algebraMap R A)))
  let U₀ : Subfunctor (geomPoints R A W) := zeroPoints s₀ (A.valuation · < 1)
  have h_char (B : CommRingCat) (x : U₀.toFunctor.obj B) : (p : B) = 0 := by
    simpa using x.property p hp
  -- restriction to `U₀` is injective by proper base change
  have h_res : IsCohomEquiv (locConstCoeff ⟨ZMod ℓ⟩) (freeAb.map (mapOnTests U₀.ι)) := by
    have h_max : (IsLocalRing.maximalIdeal A : Set A) = fun a : A ↦ A.valuation a < 1 :=
      Set.ext A.valuation_lt_one_iff
    unfold U₀
    rw [← h_max]
    exact ((isProperOver_pointsToBase _).baseChange _).proper_base_change hℓ
  refine h_res.bijective_ellAdicPull.injective ?_
  -- `F i` is `μ i` after the Frobenius of exponent `p ^ (e i * f)` on `U₀`, which acts trivially
  let F (i : I) : U₀.toFunctor ⟶ geomPoints R A Y := frobEnd h_char (e i * f) ≫ U₀.ι ≫ μ i
  trans ellAdicPull n (∑ i, m i • freeAb.map (mapOnTests (F i))) y
  · simp [F, ← comp, ellAdicPull_frobEnd]
  · -- the sum vanishes on the locus where the points `F i x` cancel; it is enough that this locus
    -- is dense
    suffices h_dense : IsCohomDense (locConstCoeff ⟨ZMod ℓ⟩)
      (relationLocus m fun i ↦ mapOnTests (F i)) by
      refine h_dense.isCohomEquiv.bijective_ellAdicPull.injective ((comp ..).trans ?_)
      simp [relationLocus_sum_eq_zero]
    -- by properness it is enough to treat points `x` at which the `F i` coincide whenever they do
    -- at some geometric point `z` (`h_coinc`)
    refine ((isProperOver_pointsToBase _).baseChange _).isCohomDense_of_coincidences F
      fun {k} hk_field hk_closed z B x h_coinc ↦ ?_
    -- at `z = (w, ω)`, with `w` the `W`-component `z.val.val.fst`:
    -- `ω a = ω (σ i a) ^ p ^ (e i * f)`, as `g` is a Frobenius
    let ω : of A ⟶ of k := baseRingMap s₀ z.val
    have h_frob (i : I) (a : A) : ω a = ω (σ i a) ^ p ^ (e i * f) := by
      have h_val : A.valuation ((a : Ω) - (σ i a : Ω) ^ (p ^ f) ^ e i) < 1 := by
        simpa [σ] using (hg.pow (e i)).right (σ i a) (by simp)
      have h_zero : ω (a - σ i a ^ (p ^ f) ^ e i) = 0 := z.property _ <| by
        show A.valuation ((a : Ω) - ((σ i a ^ (p ^ f) ^ e i : A) : Ω)) < 1
        simpa using h_val
      simpa [sub_eq_zero, ← pow_mul'] using h_zero
    -- so `F i z = (Frob (u i w), ω)`, and these points cancel by the congruence relation
    have hk_char : CharP k p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr (h_char _ z)
    have h_cancel : Cancels m fun i ↦
        Spec.map (ofHom (iterateFrobenius k p (e i * f))) ≫ z.val.val.fst.down ≫ (u i).left :=
      h_cong k _ fun r hr ↦
        (congrArg (fun t ↦ t.down.hom r) z.val.property).trans (z.property _ hr)
    refine h_cancel.mono fun i i' hij ↦
      h_coinc i i' (baseChangeOf.ext (congrArg ULift.up hij) fun a ↦ ?_)
    -- the ring map of `F i z` is `ω ∘ σ i` followed by the Frobenius of exponent `p ^ (e i * f)`
    show ω (σ i a) ^ p ^ (e i * f) = ω (σ i' a) ^ p ^ (e i' * f)
    rw [← h_frob i, ← h_frob i']

/-- Inertia acts trivially. Let Ω be an algebraic closure of ℚ and an R-algebra, A ⊂ Ω a valuation
ring that contains the image of R (`hR`), with a prime p in its maximal ideal (`hp`) and ℓ a unit
(`hℓ`). For Y proper over R and as in `New.Variety.IsCharted`, the inertia group of A acts
trivially on Vⁿ(Y). -/
lemma galoisAction_eq_one_of_inertia {g : Γ} (hg : g ∈ inertiaGroup Γ A) :
    galoisAction R Ω Γ Y n g = 1 := by
  ext x
  -- apply `congruence_relation` to `g⁻¹`, a Frobenius for `p ^ 0`: the relation on points reads
  -- `-[y] + [y] = 0`
  have h_cong : CongruenceRelation ![-1, 1] (algebraMap R Ω ⁻¹' A.nonunits) p
      (fun i : Fin 2 ↦ i * 0) ![𝟙 Y, 𝟙 Y] := by simp [CongruenceRelation, Cancels]
  simpa [neg_add_eq_iff_eq_add] using
    congruence_relation hR hℓ hp (f := 0) (inv_mem hg) ![𝟙 Y, 𝟙 Y] Fin.val ![-1, 1] h_cong x

end New.Variety.ellAdicCohom
