import Lib.General.Geometry.GeometricPoints
import Lib.LocalGL.Green.TauFunctions
import Lib.Shimura.Uniformisation.HolomorphicFamilies

/-!
# Complex points over countable rings, Zariski generic members and Galois coverings

This file collects tools for passing between points of schemes over a countable ring and complex
points, and for building Galois coverings from complex points: extensions of embeddings of countable
rings into ℂ, an injective character of the algebraic closure of a finite field, Zariski generic
members of holomorphic families, reduced closures of families of complex points, and criteria for
coverings to be étale or smooth.

## Main definitions and results

* `New.exists_ringEquiv_extend`: two embeddings of a countable ring, into `ℂ` and into an
  algebraically closed field of the same cardinality, are matched by an isomorphism of the fields
  (Steinitz's classification, relative to the ring).
* `New.exists_ringHom_complex_extend` lets one view a point over a field of cardinality at most that
  of ℂ as a complex point, compatibly with given embeddings of a countable base ring in the field
  and in ℂ.
* `New.Variety.exists_generic_member`: if `X` is locally of finite type over a countable ring and
  `φ` is a holomorphic family of complex points of `X` on a connected open set `U`, some `φ b`
  specialises, in the Zariski topology, to every `φ c`.
* `New.Variety.ReducedClosure`: the reduced closure in a finite product of schemes over `S` of a
  family of complex points; `New.Variety.ReducedClosure.exists_lift` constructs maps between two
  such closures.
* `New.Variety.isGaloisCovering_of_complex_points`: over a countable domain whose maps to fields of
  characteristic 0 are injective, a surjective map from a proper to a separated scheme, with a
  finite group acting simply transitively on its fibres of complex points, is a Galois covering.
* `New.Variety.IsGaloisCovering.smoothOfRelativeDimension_baseChange`: for a Galois covering
  `W → Z` over a domain `R`, with `W` proper and reduced and `Z` separated and smooth, the base
  change of `W` to a field of characteristic 0 containing `R` is smooth.

Notions from other files:
* `New.Variety.IsGaloisCovering`: Δ is a finite group of automorphisms of W over c : W → Z, c is
  surjective, and Δ acts simply transitively on the fibres of c on points with values in fields of
  characteristic 0.
* `New.LandsIn t U`: the morphism t lands in the open U, that is, the preimage of U is everything.
* `New.HolomorphicAt φ w`: for every function regular on an open set containing φ w, the nearby
  members of the family φ land in that open set and the function pulls back to one analytic at w.
  The parameter space is a finite-dimensional complex normed space (`FinComplexSpace`).
* `New.IsSeparatingFamily ξ`: the scheme is reduced and the complex points ξ z are dense in it.

## Relation to the literature

The isomorphisms of fields come from Steinitz's theorem, and the étaleness criterion is that of
Chase–Harrison–Rosenberg.
-/

noncomputable section

/-! ## Steinitz's theorem relative to a countable ring -/

section ExtendEmbedding

open Cardinal IsAlgClosed

/-- Let `K` be a countable ring, `L` an algebraically closed field with the cardinality of `ℂ`, and
`f : K → ℂ`, `g : K → L` injective ring maps. Then some isomorphism `σ : ℂ ≃+* L` satisfies
`σ ∘ f = g`.

A form of Steinitz's theorem (characteristic and cardinality determine an uncountable algebraically
closed field up to isomorphism), refined so that the isomorphism respects the given embeddings. -/
lemma New.exists_ringEquiv_extend {L : Type} {K : Type*} [Field L] [IsAlgClosed L] [CommRing K]
    [Countable K] (h_mk : #ℂ = #L) (f : K →+* ℂ) (g : K →+* L)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : ℂ ≃+* L, ∀ a : K, σ (f a) = g a := by
  -- Both fields are algebraic closures of `K` adjoined a transcendence basis, and, `K` being
  -- countable, the two bases have the cardinality of the uncountable fields.
  algebraize [f, g]
  have : FaithfulSMul K ℂ := (faithfulSMul_iff_algebraMap_injective K ℂ).2 hf
  have : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 hg
  have : Nontrivial K := f.domain_nontrivial
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K ℂ
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K L
  have h_uncountable : ℵ₀ < #ℂ := by simp [aleph0_lt_continuum]
  have hs_card : #ℂ = #s := by
    simpa using cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs mk_le_aleph0
      h_uncountable
  have ht_card : #L = #t := by
    simpa using cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht mk_le_aleph0
      (h_uncountable.trans_eq h_mk)
  obtain ⟨e⟩ : Nonempty (s ≃ t) := Cardinal.eq.1 (by rw [← hs_card, ← ht_card, h_mk])
  -- The bijection of the bases gives a `K`-algebra isomorphism `K[s] ≃ K[t]`, which extends to
  -- the algebraic closures.
  let Ks : Subalgebra K ℂ := Algebra.adjoin K (Set.range (Subtype.val : s → ℂ))
  let Kt : Subalgebra K L := Algebra.adjoin K (Set.range (Subtype.val : t → L))
  let φ : Ks ≃ₐ[K] Kt :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv K e).trans ht.1.aevalEquiv)
  have : IsAlgClosure Ks ℂ := isAlgClosure_of_transcendence_basis Subtype.val hs
  have : IsAlgClosure Kt L := isAlgClosure_of_transcendence_basis Subtype.val ht
  refine ⟨IsAlgClosure.equivOfEquiv ℂ L φ.toRingEquiv, fun a ↦ ?_⟩
  -- `f` and `g` are the structure maps of the `K`-algebras `ℂ` and `L`
  calc _ = algebraMap Kt L (φ (algebraMap K Ks a)) :=
      IsAlgClosure.equivOfEquiv_algebraMap ℂ L φ.toRingEquiv (algebraMap K Ks a)
    _ = g a := by rw [φ.commutes]; rfl

end ExtendEmbedding

/-! ## Extension of embeddings of a countable ring into ℂ -/

section ComplexExtension

open Cardinal

/-- Let `D` be a countable ring, `K` a field with `#K ≤ #ℂ`, and `f : D → K`, `φ : D → ℂ`
injective ring maps. Then `φ` extends along `f` to a ring map `ψ : K → ℂ`. -/
lemma New.exists_ringHom_complex_extend {D : Type*} {K : Type} [CommRing D] [Countable D] [Field K]
    {f : D →+* K} {φ : D →+* ℂ} (hf : Function.Injective f) (hφ : Function.Injective φ)
    (h_le : #K ≤ #ℂ) :
    ∃ ψ : K →+* ℂ, ψ.comp f = φ := by
  -- The algebraic closure `L` of `K(X_z : z ∈ ℂ)` contains `K` and has the cardinality of `ℂ`, so
  -- some isomorphism `σ : ℂ ≃ L` is compatible with the two embeddings of the countable ring `D`.
  let F : Type := FractionRing (MvPolynomial ℂ K)
  let L : Type := AlgebraicClosure F
  -- a fraction field has the cardinality of the ring, which is `max (max #ℂ #K) ℵ₀`
  have hF : #F = #ℂ := by simp [F, aleph0_le_continuum, h_le.trans_eq mk_complex]
  have h_card : #ℂ = #L := by
    rw [← hF]
    refine le_antisymm (by simpa using mk_le_of_module F L) ?_
    simpa [hF, aleph0_le_continuum] using Algebra.IsAlgebraic.cardinalMk_le_max F L
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_extend h_card φ ((algebraMap K L).comp f) hφ
    ((algebraMap K L).injective.comp hf)
  exact ⟨(σ.symm : L →+* ℂ).comp (algebraMap K L),
    RingHom.ext fun a ↦ σ.symm_apply_eq.2 (hσ a).symm⟩

end ComplexExtension

/-!
## A faithful character of the units of the algebraic closure of a finite field

`New.faithfulChar k` is chosen among the injective multiplicative characters from the algebraic
closure of the finite field `k` to `ℂ`. `New.exists_injective_mulChar` shows that such a character
exists, using Teichmüller lifts to Witt vectors, so the chosen character is injective
(`New.faithfulChar_injective`).
-/

section FaithfulChar

open WittVector Algebra IsIntegral Function RingHom

/-- The algebraic closure of a finite field has an injective multiplicative character to `ℂ`. -/
theorem New.exists_injective_mulChar (k : Type*) [Field k] [Finite k] :
    ∃ T : MulChar (AlgebraicClosure k) ℂ, Injective T := by
  -- Teichmüller lifts are integral over `ℤ`, and the ring `R` of Witt vectors integral over
  -- `ℤ` is a domain of characteristic zero, so it embeds in `ℂ`.
  have : CharZero (WittVector (ringChar k) (AlgebraicClosure k)) :=
    -- it contains the Witt vectors of the prime field, which are the `p`-adic integers
    (charZero_iff (map_injective _ (ZMod.castHom_injective (AlgebraicClosure k)))).1
      (toPadicInt (ringChar k)).charZero
  let R := integralClosure ℤ (WittVector (ringChar k) (AlgebraicClosure k))
  have h_int (x : AlgebraicClosure k) : teichmuller (ringChar k) x ∈ R := by
    -- `k[x]` is finite, so its monoid algebra is integral over `ℤ`; map it to the Witt vectors.
    have : Finite k[x] :=
      Module.finite_iff_finite.1 (finite_adjoin_simple_of_isIntegral (R := k) (isIntegral x))
    let x' : k[x] := ⟨x, self_mem_adjoin_singleton k x⟩
    let toWitt : MonoidAlgebra ℤ k[x] →ₐ[ℤ] WittVector (ringChar k) (AlgebraicClosure k) :=
      MonoidAlgebra.lift ℤ _ _ ((teichmuller (ringChar k)).domRestrict k[x])
    have h_apply : toWitt (MonoidAlgebra.single x' 1) = teichmuller (ringChar k) x := by
      simp [toWitt, x']
    have h_single : _root_.IsIntegral ℤ (MonoidAlgebra.single x' (1 : ℤ)) := isIntegral _
    rw [← h_apply]
    exact h_single.map toWitt
  let lift : MulChar (AlgebraicClosure k) R :=
    { (teichmuller (ringChar k)).codRestrict R h_int with
      map_nonunit' := by simp [Subtype.ext_iff] }
  let emb : R →ₐ[ℤ] ℂ := IsAlgClosed.lift
  -- The kernel of `emb` is a prime of `R` lying over `(0)`, and `R` is integral over `ℤ`.
  have h_emb : Injective emb :=
    (injective_iff_ker_eq_bot emb).2 (Ideal.eq_bot_of_liesOver_bot ℤ (Ideal.comap emb ⊥))
  refine ⟨lift.ringHomComp emb.toRingHom, fun x y h ↦ ?_⟩
  -- The coefficient `0` of the Teichmüller lift of `x` is `x`.
  have h_lift : lift x = lift y := h_emb h
  have h_coeff : (teichmuller (ringChar k) x).coeff 0 = (teichmuller (ringChar k) y).coeff 0 :=
    congrArg (fun w : R ↦ (w : WittVector (ringChar k) (AlgebraicClosure k)).coeff 0) h_lift
  simpa only [teichmuller_coeff_zero] using h_coeff

/-- For a finite field `k` the character `faithfulChar k`, chosen among the multiplicative
characters from the algebraic closure of `k` to `ℂ`, is injective, so it is faithful
(`IsFaithfulMulChar`). -/
instance New.faithfulChar_injective {k : Type*} [Field k] [Finite k] :
    IsFaithfulMulChar (AlgebraicClosure k) (faithfulChar k) where
  injective := Classical.epsilon_spec (exists_injective_mulChar k)

end FaithfulChar

namespace New.Variety

/-!
## Zariski generic members of holomorphic families of complex points

Idea: over a countable base, an affine open of finite type has countably many functions, so Baire's
theorem and the identity theorem give a `b` at which no function vanishes unless it vanishes along
all of `φ` nearby.
-/

section GenericPoint

open CategoryTheory AlgebraicGeometry IsLocalRing PointFn Algebra Spec

/-- If `X` is locally of finite type over a countable ring, the ring of sections of `X` over an
affine open `W` is countable. -/
lemma countable_sections {X : Scheme} {R : CommRingCat} (s : X ⟶ Spec R) [Countable R]
    [LocallyOfFiniteType s] {W : X.Opens} (h : IsAffineOpen W) : Countable Γ(X, W) := by
  -- The ring of sections is of finite type over `R`, so a quotient of a polynomial ring in finitely
  -- many variables, whose elements are finitely supported families of coefficients.
  have h_ring : (preimage (h.fromSpec ≫ s)).hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), map_preimage]
    infer_instance
  algebraize [(preimage (h.fromSpec ≫ s)).hom]
  obtain ⟨n, f, hf⟩ := FiniteType.iff_quotient_mvPolynomial''.1 h_ring
  have := (MvPolynomial.basisMonomials (Fin n) R).repr.injective.countable
  exact hf.countable

/-- Let `X` be locally of finite type over a countable ring. Every point `t : Spec K ⟶ X` with
values in a field `K` factors through the residue field of a point `z` of `X`, as `Spec` of a ring
map `φ` (written `specMap φ`) followed by the canonical map to `X`, and this residue field is
countable. -/
lemma exists_countable_residue_point {X : Scheme} {R : CommRingCat} (s : X ⟶ Spec R) [Countable R]
    [LocallyOfFiniteType s] {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ X) :
    ∃ᵉ (z : X) (φ : X.residueField z →+* K),
      specMap φ ≫ X.fromSpecResidueField z = t ∧ Countable (X.residueField z) := by
  let z : X := t (closedPoint K)
  refine ⟨z, (X.SpecToEquivOfField K t).2.hom, (X.SpecToEquivOfField K).left_inv t, ?_⟩
  -- The stalk at the image `z` of `t` is a localisation of the countable ring of sections over an
  -- affine open `W ∋ z`, and it surjects onto the residue field.
  obtain ⟨W, hW, ht⟩ := exists_isAffineOpen_landsIn t
  have : Countable Γ(X, W) := countable_sections s hW
  let z' : W := ⟨z, landsIn_iff_mem.1 ht⟩
  let := X.presheaf.algebra_section_stalk z'
  have : Countable (X.presheaf.stalk z) := (hW.isLocalization_stalk z').mk'_surjective.countable
  exact (residue_surjective (R := X.presheaf.stalk z)).countable

/-- For countably many analytic functions on a connected open set `N` and an open set `V` meeting
`N`, some point of `N ∩ V` is a zero only of those functions that vanish on all of `N`. -/
lemma exists_mem_forall_ne_zero_of_analyticOnNhd {P : Type} [FinComplexSpace P] {ι : Type*}
    [Countable ι] (g : ι → P → ℂ) {N V : Set P} (hN_open : IsOpen N) (hN_conn : IsPreconnected N)
    (hg : ∀ i : ι, AnalyticOnNhd ℂ (g i) N) (hV : IsOpen V) (h_nonempty : (N ∩ V).Nonempty) :
    ∃ b ∈ N, b ∈ V ∧ ∀ i : ι, ∀ e ∈ N, g i e ≠ 0 → g i b ≠ 0 := by
  -- Each non-vanishing set `Z i` is open, so agrees with its closure on a residual set.
  let Z (i : ι) : Set P := N ∩ g i ⁻¹' {x : ℂ | x ≠ 0}
  have hZ (i : ι) : closure (Z i) =ᶠ[residual P] Z i := closure_residualEq
    ((hg i).continuousOn.isOpen_inter_preimage hN_open isOpen_ne).isLocallyClosed
  -- Baire: there are countably many `i`, so some `b ∈ N ∩ V` is good for all of them.
  have h_dense : Dense {e : P | ∀ i : ι, (e ∈ closure (Z i)) = (e ∈ Z i)} :=
    dense_of_mem_residual (eventually_countable_forall.2 hZ)
  obtain ⟨b, hb_gen, hbN, hbV⟩ := h_dense.exists_mem_open (hN_open.inter hV) h_nonempty
  refine ⟨b, hbN, hbV, fun i e he hne ↦ ?_⟩
  -- By the identity theorem `g i` is non-zero arbitrarily near `b`, hence at `b`.
  have h_freq : ∃ᶠ x in nhds b, g i x ≠ 0 := Filter.not_eventually.1 fun h_zero ↦
    hne ((hg i).eqOn_zero_of_preconnected_of_eventuallyEq_zero hN_conn hbN h_zero he)
  exact ((hb_gen i).mp (hN_open.inter_closure ⟨hbN, h_freq.mem_closure⟩ : b ∈ closure (Z i))).2

/-- Let `X` be locally of finite type over a countable ring and `φ` a family of complex points of
`X`, parametrised by a finite-dimensional complex space and holomorphic on the open set `U`
(`HolomorphicAt`: regular functions pull back to analytic ones). If `c ∈ U` lies in the closure of
an open set `V`, there is `b ∈ V` such that the image point of `φ b` specialises to that of `φ e`
for all `e` near `c`. -/
lemma exists_mem_eventually_specializes {P : Type} [FinComplexSpace P] {U : Set P} {X : Scheme}
    {R : CommRingCat} (s : X ⟶ Spec R) [Countable R] [LocallyOfFiniteType s]
    {φ : P → (Spec (CommRingCat.of ℂ) ⟶ X)} (hU : IsOpen U) (hφ : ∀ b ∈ U, HolomorphicAt φ b)
    {V : Set P} (hV : IsOpen V) {c : P} (hcV : c ∈ closure V) (hcU : c ∈ U) :
    ∃ b ∈ V, ∀ᶠ e in nhds c, φ b (closedPoint ℂ) ⤳ φ e (closedPoint ℂ) := by
  -- Baire's theorem gives a `b` at which no section over an affine open around `φ c` vanishes,
  -- unless it vanishes identically along `φ` near `c`.
  obtain ⟨W, hW, hcW⟩ := exists_isAffineOpen_landsIn (φ c)
  have : Countable Γ(X, W) := countable_sections s hW
  let val (f : Γ(X, W)) (e : P) : ℂ := PointFn.ofSection f _ (φ e)
  -- A connected open neighbourhood `N ⊆ U` of `c` that `φ` maps into the affine open `W`.
  obtain ⟨N, ⟨hN_open, hcN, hN_conn⟩, hN⟩ : ∃ N : Set P,
      (IsOpen N ∧ c ∈ N ∧ _root_.IsConnected N) ∧ ∀ e ∈ N, e ∈ U ∧ LandsIn (φ e) W :=
    -- holomorphy, applied to any section over `W`, says that `φ e` lands in `W` for `e` near `c`
    (LocallyConnectedSpace.open_connected_basis c).mem_iff.1
      ((hU.eventually_mem hcU).and (hφ c hcU (isRegularOn_ofSection 0) hcW).1)
  have h_an (f : Γ(X, W)) : AnalyticOnNhd ℂ (val f) N := fun e he ↦ by
    obtain ⟨heU, heW⟩ := hN e he
    exact (hφ e heU (isRegularOn_ofSection f) heW).2
  obtain ⟨b, hbN, hbV, h_ne⟩ : ∃ b ∈ N,
      b ∈ V ∧ ∀ f : Γ(X, W), ∀ e ∈ N, val f e ≠ 0 → val f b ≠ 0 :=
    exists_mem_forall_ne_zero_of_analyticOnNhd val hN_open hN_conn.isPreconnected h_an hV
      (mem_closure_iff.1 hcV N hN_open hcN)
  -- Test the specialisation on basic opens of `W`: a point lies in the basic open of `f` exactly
  -- when the value of `f` there is a unit (`landsIn_basicOpen`).
  refine ⟨b, hbV, (hN_open.eventually_mem hcN).mono fun e he ↦
    specializes_iff_forall_open.2 fun O hO heO ↦ ?_⟩
  obtain ⟨-, heW⟩ := hN e he
  obtain ⟨f, hfO, hef⟩ := hW.exists_basicOpen_le (V := ⟨O, hO⟩) ⟨_, heO⟩ (landsIn_iff_mem.1 heW)
  have hfe : val f e ≠ 0 := ((landsIn_basicOpen heW f).1 (landsIn_iff_mem.2 hef)).ne_zero
  have hb_lands : LandsIn (φ b) (X.basicOpen f) :=
    (landsIn_basicOpen (hN b hbN).2 f).2 (h_ne f e he hfe).isUnit
  exact hfO (landsIn_iff_mem.1 hb_lands)

/-- Let `X` be locally of finite type over a countable ring and `φ` a family of complex points of
`X`, parametrised by a finite-dimensional complex space and holomorphic (regular functions pull back
to analytic ones) on a connected open set `U`. There is `b ∈ U` such that the image point of
`φ b` specialises to the image point of `φ c` for every `c ∈ U`. -/
lemma exists_generic_member {P : Type} [FinComplexSpace P] {U : Set P} {X : Scheme}
    {R : CommRingCat} (s : X ⟶ Spec R) [Countable R] [LocallyOfFiniteType s]
    {φ : P → (Spec (CommRingCat.of ℂ) ⟶ X)} (hU : IsOpen U)
    (h_conn : IsConnected U) (hφ : ∀ b ∈ U, HolomorphicAt φ b) :
    ∃ b ∈ U, ∀ c ∈ U, φ b (closedPoint ℂ) ⤳ φ c (closedPoint ℂ) := by
  -- Locally there is a `b` such that `φ b` specialises to all nearby `φ e`
  -- (`exists_mem_eventually_specializes`). Connectedness spreads this over `U`.
  obtain ⟨c, hc⟩ := h_conn.nonempty
  obtain ⟨b, hb, hbc⟩ := exists_mem_eventually_specializes s hU hφ hU (subset_closure hc) hc
  -- The set of points near which `φ b` specialises to `φ e` is open, and closed in `U`.
  let G : Set P := {x : P | ∀ᶠ e in nhds x, φ b (closedPoint ℂ) ⤳ φ e (closedPoint ℂ)}
  have hG : IsOpen G := isOpen_setOfPred_eventually_nhds
  have h_all : U ⊆ G := by
    refine h_conn.isPreconnected.subset_of_closure_inter_subset hG ⟨c, hc, hbc⟩ fun x hx ↦ ?_
    obtain ⟨d, hdG, hdx⟩ := exists_mem_eventually_specializes s hU hφ hG hx.1 hx.2
    exact hdx.mono fun e hde ↦ hdG.self_of_nhds.trans hde
  exact ⟨b, hb, fun e he ↦ (h_all he).self_of_nhds⟩

end GenericPoint

/-! ## Reduced closures in products and Galois coverings -/

section GaloisCovers

open CategoryTheory AlgebraicGeometry Limits RingHom Over Set Scheme IsArtinianRing Pi pullback
  CommRingCat Ideal Quotient Algebra TensorProduct Function Finset Module Spec OverMorphism
  FormallyUnramified LocallyQuasiFinite IsOpenImmersion IsLocalization IsIntegralClosure

attribute [local instance low] Fintype.ofFinite

/-- Let `b` be a complex point of a scheme `S`, let `Z j` be finitely many schemes over `S`, and let
`F j a` be a complex point of `Z j` over `b` for each `a : A`. A reduced closure of the tuples
`(F j a)_j` is a reduced closed subscheme `W` (the field `scheme`) of the product of the `Z j` over
`S`, with a dense family of complex points that lift these tuples. -/
structure ReducedClosure {S : Scheme} {b : Spec (of ℂ) ⟶ S} {J A : Type} [Finite J]
    {Z : J → Over S} (F : (j : J) → A → (Over.mk b ⟶ Z j)) where
  /-- The closure, a scheme over `S`. -/
  scheme : Over S
  /-- The inclusion of `scheme` in the product of the `Z j`. -/
  incl : scheme ⟶ ∏ᶜ Z
  /-- The complex point of `scheme` indexed by `a`. -/
  point (a : A) : Over.mk b ⟶ scheme
  /-- The point `point a` lies over the point `(F j a)_j` of the product. -/
  point_incl (a : A) : point a ≫ incl = Pi.lift fun j : J ↦ F j a
  /-- `incl` is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion incl.left
  /-- `scheme` is reduced and its points `point a` are dense in it. -/
  isSeparatingFamily : IsSeparatingFamily fun a : A ↦ (point a).left

attribute [instance] ReducedClosure.isClosedImmersion

-- `S` is the base scheme, `b` a complex point of it, and `F j a` a complex point of the factor
-- `Z j` over `b`, for `j` in the finite set `J` and `a` in the index set `A`.
variable {S : Scheme} {b : Spec (of ℂ) ⟶ S} {J A : Type} [Finite J] {Z : J → Over S}
  {F : (j : J) → A → (Over.mk b ⟶ Z j)}

/-- A reduced closure is a reduced scheme. -/
instance (C : ReducedClosure F) : AlgebraicGeometry.IsReduced C.scheme.left :=
  C.isSeparatingFamily.1

/-- The morphism from the closure `C.scheme` to the factor `Z j`: the inclusion into the product
followed by the `j`-th projection. -/
def ReducedClosure.proj (C : ReducedClosure F) (j : J) : C.scheme ⟶ Z j := C.incl ≫ Pi.π Z j

@[simp]
lemma ReducedClosure.point_comp_proj (C : ReducedClosure F) (a : A) (j : J) :
    C.point a ≫ C.proj j = F j a := by
  simp [proj, reassoc_of% point_incl]

/-- Every family of tuples of complex points has a reduced closure. -/
instance : Nonempty (ReducedClosure F) := by
  obtain ⟨Y, i, e, h_closed, he, h_sep⟩ :=
    exists_reduced_closure fun a : A ↦ (Pi.lift fun j : J ↦ F j a).left
  exact ⟨{ scheme := .mk (i ≫ (∏ᶜ Z).hom), incl := homMk i
           point a := homMk (e a) (by simp [reassoc_of% he])
           point_incl a := ext (he a)
           isClosedImmersion := h_closed, isSeparatingFamily := h_sep }⟩

/-- Two morphisms over `S` to a reduced closure `C.scheme` agree as soon as their composites with
all projections `C.proj j` to the factors agree. -/
lemma ReducedClosure.hom_ext (C : ReducedClosure F) {T : Over S} {f g : T ⟶ C.scheme}
    (h : ∀ j : J, f ≫ C.proj j = g ≫ C.proj j) : f = g :=
  (mono_of_mono_left C.incl).right_cancellation f g (Pi.hom_ext _ _ h)

/-- Let `C` and `C'` be reduced closures (reduced closed subschemes of `∏ᶜ Z` and `∏ᶜ Z'` over `S`
with dense complex points) of families `F` and `F'` of complex points indexed by the
same set `A`. Maps `f j` from `C'` to the factors `Z j` that send the point `a` of `C'` to
`F j (σ a)` come from a map `g` to the closure `C`, and `g` sends the point `a` to the point
`σ a`. Here `S` is the base scheme and `F j a` is a complex point of `Z j` over the fixed complex
point `b` of `S`, with `j` in the finite set `J` and `a` in `A`. -/
lemma ReducedClosure.exists_lift (C : ReducedClosure F) {J' : Type} [Finite J'] {Z' : J' → Over S}
    {F' : (j : J') → A → (Over.mk b ⟶ Z' j)} {C' : ReducedClosure F'}
    (σ : A → A) (f : (j : J) → (C'.scheme ⟶ Z j))
    (h : ∀ (a : A) (j : J), C'.point a ≫ f j = F j (σ a)) :
    ∃ g : C'.scheme ⟶ C.scheme,
      (∀ j : J, g ≫ C.proj j = f j) ∧ ∀ a : A, C'.point a ≫ g = C.point (σ a) := by
  -- The map `Pi.lift f` sends the dense points of the reduced scheme `C'.scheme` into the closed
  -- subscheme `C.scheme`, so it factors through it.
  have h_pt (a : A) : C.point (σ a) ≫ C.incl = C'.point a ≫ Pi.lift f :=
    (C.point_incl (σ a)).trans (Pi.hom_ext _ _ fun j ↦ by simp [h])
  obtain ⟨g, hg⟩ := exists_lift_of_dense_preimage C.incl.left (Pi.lift f).left <|
    C'.isSeparatingFamily.2.mono <| range_subset_iff.2 fun a ↦
      ⟨(C.point (σ a)).left (IsLocalRing.closedPoint ℂ),
        congrArg (fun y ↦ y.left (IsLocalRing.closedPoint ℂ)) (h_pt a)⟩
  let g' : C'.scheme ⟶ C.scheme := homMk g (by simpa using hg =≫ hom _)
  have h_incl : g' ≫ C.incl = Pi.lift f := ext hg
  have h_proj (j : J) : g' ≫ C.proj j = f j := by simp [proj, reassoc_of% h_incl]
  exact ⟨g', h_proj, fun a ↦ C.hom_ext fun j ↦ by simp [h_proj, h]⟩

/-- Chase–Harrison–Rosenberg. Let `B` be a finite `A`-algebra with `A → B` injective and `G` a
finite group. Assume: (a) `σ` is a right action of `G` on `B` by `A`-algebra maps, that is
`σ 1 = id` and `σ (g * h) = σ h ∘ σ g`; (b) for every field `k` over `A` and any two `A`-algebra
maps `x y : B → k` there is exactly one `g` with `x ∘ σ g = y`; (c) every element of `B` fixed
by all `σ g` comes from `A`. Then `B` is étale over `A`. -/
lemma etale_of_simply_transitive {A : Type*} {B : Type} {G : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] [Group G] [Finite G]
    (h_inj : Function.Injective (algebraMap A B)) (σ : G →* (B →ₐ[A] B)ᵐᵒᵖ)
    (h_points : ∀ (k : Type) [Field k] [Algebra A k] (x y : B →ₐ[A] k),
      ∃! g : G, ∀ b : B, x ((σ g).unop b) = y b)
    (h_invariant : ∀ s : B, (∀ g : G, (σ g).unop s = s) → ∃ a : A, algebraMap A B a = s) :
    Algebra.Etale A B := by
  classical
  -- Find `x i`, `y i` in `B` with `∑ i, σ g (y i) * x i = if g = 1 then 1 else 0`. With the trace
  -- `t` they form a dual basis, so `B` is projective; and `∑ i, y i ⊗ x i` is a separability
  -- element, so `B` is unramified.
  let tr : B →ₗ[A] B := ∑ g : G, (σ g).unop.toLinearMap
  let t : B →ₗ[A] A := tr.codRestrictOfInjective (Algebra.linearMap A B) h_inj fun s ↦
    h_invariant (tr s) fun g ↦ by
      simpa [tr] using Equiv.sum_comp (.mulRight g) fun h ↦ (σ h).unop s
  have ht (s : B) : algebraMap A B (t s) = ∑ g : G, (σ g).unop s := by
    simpa [tr] using tr.codRestrictOfInjective_comp_apply (Algebra.linearMap A B) h_inj _ s
  -- The kernels of the maps `b ⊗ b' ↦ σ g b * b'` are pairwise coprime: a maximal ideal over two
  -- of them gives two points of `B` in its residue field, related by both group elements.
  let 𝔞 (g : G) : Ideal (B ⊗[A] B) := ker (productMap (σ g).unop (.id A B))
  have h_coprime : Pairwise (IsCoprime on 𝔞) := by
    refine fun g g' h_ne ↦ isCoprime_iff_sup_eq.2 (by_contra fun h_sup ↦ h_ne ?_)
    obtain ⟨𝔪, h𝔪, h_le⟩ := exists_le_maximal _ h_sup
    let : Field (B ⊗[A] B ⧸ 𝔪) := Quotient.field 𝔪
    let left : B →ₐ[A] B ⊗[A] B ⧸ 𝔪 := (mkₐ A 𝔪).comp includeLeft
    let right : B →ₐ[A] B ⊗[A] B ⧸ 𝔪 := (mkₐ A 𝔪).comp includeRight
    have h_rel (g : G) (hg : 𝔞 g ≤ 𝔪) (b : B) : right ((σ g).unop b) = left b :=
      Ideal.Quotient.eq.2 (hg (show 1 ⊗ₜ[A] (σ g).unop b - b ⊗ₜ[A] 1 ∈ 𝔞 g by simp [𝔞]))
    exact (h_points _ right left).unique (h_rel g (le_sup_left.trans h_le))
      (h_rel g' (le_sup_right.trans h_le))
  -- Chinese remainder theorem: `u = ∑ i, y i ⊗ x i` is `1` modulo `𝔞 1` and `0` modulo the others.
  obtain ⟨u, hu⟩ : ∃ u : B ⊗[A] B, ∀ g : G, u - Pi.single (M := fun _ ↦ B ⊗[A] B) 1 1 g ∈ 𝔞 g :=
    exists_forall_sub_mem_ideal h_coprime _
  obtain ⟨r, y, x, rfl⟩ := exists_sum_tmul_eq u
  have h_delta (g : G) : ∑ i, (σ g).unop (y i) * x i = if g = 1 then 1 else 0 := by
    simpa [𝔞, sub_eq_zero, single_apply, apply_ite] using hu g
  have h_dual (z : B) : ∑ i, t (z * y i) • x i = z :=
    calc ∑ i, t (z * y i) • x i
      _ = ∑ g : G, (σ g).unop z * ∑ i, (σ g).unop (y i) * x i := by
        simp [Algebra.smul_def, ht, sum_mul, mul_sum, sum_comm (s := univ (α := G)), mul_assoc]
      _ = z := by simp [h_delta]
  -- Expand both sides in the dual basis and move the scalars across `⊗`.
  have h_swap (s : B) : ∑ i, (s * y i) ⊗ₜ[A] x i = ∑ i, x i ⊗ₜ[A] (s * y i) :=
    calc ∑ j, (s * y j) ⊗ₜ[A] x j
      _ = ∑ j, (∑ i, t (s * y j * y i) • x i) ⊗ₜ[A] x j := by simp only [h_dual]
      _ = ∑ i, x i ⊗ₜ[A] ∑ j, t (s * y i * y j) • x j := by
        simp only [sum_tmul, tmul_sum, smul_tmul]
        exact sum_comm.trans (by simp only [mul_right_comm])
      _ = ∑ i, x i ⊗ₜ[A] (s * y i) := by simp only [h_dual]
  have h_unramified : FormallyUnramified A B := by
    refine iff_exists_tensorProduct.2 ⟨∑ i, y i ⊗ₜ x i, fun s ↦ ?_, by simpa using h_delta 1⟩
    have h_symm : ∑ i, y i ⊗ₜ[A] x i = ∑ i, x i ⊗ₜ[A] y i := by simpa using h_swap 1
    rw [sub_mul, sub_eq_zero]
    calc (1 : B) ⊗ₜ[A] s * ∑ i, y i ⊗ₜ[A] x i
      _ = (1 : B) ⊗ₜ[A] s * ∑ i, x i ⊗ₜ[A] y i := by rw [h_symm]
      _ = s ⊗ₜ[A] (1 : B) * ∑ i, y i ⊗ₜ[A] x i := by simp [mul_sum, h_swap]
  have h_projective : Projective A B :=
    .of_split (.pi fun i ↦ t.comp (.mulRight A (y i))) (Fintype.linearCombination A x)
      (LinearMap.ext h_dual)
  -- finite and projective, hence flat and finitely presented
  have : Module.FinitePresentation A B := finitePresentation_of_projective A B
  exact .of_formallyUnramified_of_flat

/-- Let `R` be a countable domain, with a given map to `ℂ`, all of whose ring maps to fields of
characteristic 0 are injective. Let `W` be proper over `R`, `Z` separated, and `c : W ⟶ Z`
surjective and invariant under an action `s` of a finite group `Δ` on `W` that is simply transitive
on the fibres of `c` on complex points (`specOver R ℂ` is `Spec ℂ` over `Spec R`). Then `c` is a
Galois covering with group `Δ` in the sense of `New.Variety.IsGaloisCovering`: simple transitivity
holds for points with values in any field of characteristic 0. -/
lemma isGaloisCovering_of_complex_points {R : CommRingCat} [IsDomain R] {W Z : Over (Spec R)}
    [IsProper W.hom] [IsSeparated Z.hom] {c : W ⟶ Z} {Δ : FiniteGrp}
    {s : Δ →* CategoryTheory.End W} [Countable R] [Algebra R ℂ]
    (hR : ∀ (k : Type) [Field k] [CharZero k] (f : R →+* k), Function.Injective f)
    (h_inv : ∀ g : Δ.toGrp, (s g).asHom ≫ c = c) (hc : AlgebraicGeometry.Surjective c.left)
    (h_orbit : ∀ y z : specOver R ℂ ⟶ W, y ≫ c = z ≫ c → ∃! g : Δ.toGrp, y ≫ (s g).asHom = z) :
    IsGaloisCovering c s := by
  refine ⟨h_inv, hc, fun k _ _ y y' hy ↦ ?_⟩
  -- The pair `(y, y')` is a point of `W ×_Z W`. It factors through the residue field of its image
  -- `z`, which is countable and so embeds in `ℂ` over `R`.
  let p₁ : pullback c.left c.left ⟶ W.left := fst c.left c.left
  let p₂ : pullback c.left c.left ⟶ W.left := snd c.left c.left
  obtain ⟨x, rfl, rfl⟩ : ∃ x, x ≫ p₁ = y ∧ x ≫ p₂ = y' :=
    ⟨lift y y' hy, lift_fst y y' hy, lift_snd y y' hy⟩
  obtain ⟨z, φ, rfl, h_countable⟩ := exists_countable_residue_point (p₁ ≫ W.hom) x
  set j : Spec (residueField _ z) ⟶ pullback c.left c.left := fromSpecResidueField _ z
  have : CharZero (residueField _ z) := φ.charZero
  -- `R` maps injectively to the countable residue field and to `ℂ`, so `ψ` exists.
  obtain ⟨ψ, hψ⟩ : ∃ ψ : residueField _ z →+* ℂ,
      ψ.comp (Spec.preimage (j ≫ p₁ ≫ W.hom)).hom = algebraMap R ℂ :=
    exists_ringHom_complex_extend (hR _ _) (hR ℂ _) (by simp [Cardinal.aleph0_le_continuum.trans'])
  -- Both projections of `specMap ψ ≫ j` are complex points over `R` with the same image in `Z`.
  have h_fibre : p₁ ≫ c.left = p₂ ≫ c.left := condition
  have h₁ : (specMap ψ ≫ j ≫ p₁) ≫ W.hom = (specOver R ℂ).hom := by simp [← hψ]
  let y₁ : specOver R ℂ ⟶ W := homMk (specMap ψ ≫ j ≫ p₁) h₁
  let y₂ : specOver R ℂ ⟶ W :=
    homMk (specMap ψ ≫ j ≫ p₂) <| by
      rw [← h₁, ← c.w]
      simp only [Category.assoc, reassoc_of% h_fibre]
  have h_complex : ∃! g : Δ, y₁ ≫ (s g).asHom = y₂ :=
    h_orbit y₁ y₂ (OverMorphism.ext (by simp [y₁, y₂, h_fibre]))
  -- The maps `specMap φ` and `specMap ψ` between spectra of fields are epi, so they cancel.
  simpa [y₁, y₂, OverMorphism.ext_iff, cancel_epi] using h_complex

/-- Let `c : W ⟶ Z` be a Galois covering with group `Δ` acting through `s`, and `π : T ⟶ Z` a map
from a scheme whose field-valued points have characteristic zero. If `p : X ⟶ W` lies over
`r : X ⟶ T`, then two points of `X` with the same image under `r` have images under `p` in the
same `Δ`-orbit. -/
lemma IsGaloisCovering.exists_apply_eq_of_apply_eq.{u} {R : CommRingCat.{u}} {W Z : Over (Spec R)}
    {c : W ⟶ Z} {Δ : FiniteGrp} {s : Δ →* CategoryTheory.End W} (hG : IsGaloisCovering c s)
    {T X : Scheme} {π : T ⟶ Z.left}
    (h_char : ∀ (K : Type u) [Field K], (Spec (of K) ⟶ T) → CharZero K)
    {p : X ⟶ W.left} (r : X ⟶ T) (hr : p ≫ c.left = r ≫ π) (w v : X) (hv : r v = r w) :
    ∃ g : Δ, (s g).asHom.left (p w) = p v := by
  -- Lift `(v, w)` to a point `t` of the fibre product and use its residue field.
  obtain ⟨t, rfl, rfl⟩ := Pullback.exists_preimage_pullback v w hv
  let j : Spec (residueField _ t) ⟶ pullback r r := fromSpecResidueField _ t
  have : CharZero (residueField _ t) := h_char _ (j ≫ fst r r ≫ r)
  have h_fibre : (j ≫ snd r r ≫ p) ≫ c.left = (j ≫ fst r r ≫ p) ≫ c.left := by
    simp [hr, condition_assoc]
  obtain ⟨g, hg, -⟩ : ∃! g : Δ, (j ≫ snd r r ≫ p) ≫ (s g).asHom.left = j ≫ fst r r ≫ p :=
    hG.torsor (residueField _ t) _ _ h_fibre
  refine ⟨g, ?_⟩
  simpa [j] using congrArg (fun y ↦ y default) hg

/-- Let `c : W ⟶ Z` be a Galois covering with group `Δ`, let `π : T ⟶ Z` be a map from a scheme
whose field-valued points have characteristic zero, and let `p : X ⟶ W`, injective on points, lie
over `r : X ⟶ T`. Then the fibres of `r` are finite. -/
lemma IsGaloisCovering.finite_preimage_singleton.{u} {R : CommRingCat.{u}} {W Z : Over (Spec R)}
    {c : W ⟶ Z} {Δ : FiniteGrp} {s : Δ →* CategoryTheory.End W} (hG : IsGaloisCovering c s)
    {T X : Scheme} {π : T ⟶ Z.left}
    (h_char : ∀ (K : Type u) [Field K], (Spec (of K) ⟶ T) → CharZero K)
    {p : X ⟶ W.left} (hp : Function.Injective p) (r : X ⟶ T) (hr : p ≫ c.left = r ≫ π) (x : X) :
    (r ⁻¹' {r x}).Finite :=
  -- each fibre lies in the preimage of a `Δ`-orbit
  have h_orbit : r ⁻¹' {r x} ⊆ p ⁻¹' range fun g : Δ ↦ (s g).asHom.left (p x) :=
    hG.exists_apply_eq_of_apply_eq h_char r hr x
  ((finite_range _).preimage hp.injOn).subset h_orbit

/-- Let `Spec B` be the pull-back of `c : W ⟶ Z` along `u : Spec A ⟶ Z`, with projection `p` to
`W`. A point `y` of `W` with values in an `A`-algebra `K` that lies over the point
`Spec K ⟶ Spec A ⟶ Z` comes from an `A`-algebra map `B → K`. Here `specMap φ` is the morphism
of spectra induced by a ring map `φ`. -/
lemma exists_algHom_specMap_comp_eq {W Z : Scheme} {c : W ⟶ Z} {A B : Type} [CommRing A]
    [CommRing B] [Algebra A B] {p : Spec (of B) ⟶ W} {u : Spec (of A) ⟶ Z}
    (hp : IsPullback p (specMap (algebraMap A B)) c u) (K : Type) [CommRing K] [Algebra A K]
    (y : Spec (of K) ⟶ W) (hy : y ≫ c = specMap (algebraMap A K) ≫ u) :
    ∃ χ : B →ₐ[A] K, specMap χ ≫ p = y := by
  let l : specOver A K ⟶ specOver A B := homMk (hp.lift y _ hy) (hp.lift_snd y _ hy)
  obtain ⟨χ, hχ⟩ := specOver.map_bijective.surjective l
  have h_left : specMap (χ : B →+* K) = hp.lift y _ hy := congrArg Hom.left hχ
  exact ⟨χ, by rw [h_left, hp.lift_fst]⟩

/-- Let `c : W ⟶ Z` be a Galois covering with group `Δ` acting through `s`, and let `Spec B` be its
pull-back along `u : Spec A ⟶ Z`, where the field-valued points of `A` have characteristic zero and
the projection `p : Spec B ⟶ W` is a monomorphism. Then `Δ` acts on the `A`-algebra `B` from the
right, compatibly with `s` and simply transitively on the field-valued points of `B` over `A`.
(Galois covering: `c` is surjective and `Δ` is simply transitive on its fibres of points in fields
of characteristic zero; `specMap φ` is the morphism of spectra induced by `φ`.) -/
lemma IsGaloisCovering.exists_simply_transitive_action {R : CommRingCat} {W Z : Over (Spec R)}
    {c : W ⟶ Z} {Δ : FiniteGrp} {s : Δ →* CategoryTheory.End W} (hG : IsGaloisCovering c s)
    {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (h_char : ∀ (K : Type) [Field K], (Spec (of K) ⟶ Spec (of A)) → CharZero K)
    {p : Spec (of B) ⟶ W.left} {u : Spec (of A) ⟶ Z.left} [Mono p]
    (hp : IsPullback p (specMap (algebraMap A B)) c.left u) :
    ∃ σ : Δ →* (B →ₐ[A] B)ᵐᵒᵖ,
      (∀ g : Δ, specMap (σ g).unop ≫ p = p ≫ (s g).asHom.left) ∧
      ∀ (K : Type) [Field K] [Algebra A K] (x y : B →ₐ[A] K),
        ∃! g : Δ, ∀ b : B, x ((σ g).unop b) = y b := by
  have h_exists (g : Δ) : ∃ χ : B →ₐ[A] B, specMap χ ≫ p = p ≫ (s g).asHom.left :=
    exists_algHom_specMap_comp_eq hp B (p ≫ (s g).asHom.left)
      (by simp [← comp_left, hG.comp_eq, hp.w])
  choose act h_act using h_exists
  -- As `p` is mono, identities between points of `W` are identities between ring maps.
  have h_cancel {K : Type} [CommRing K] [Algebra A K] (x y : B →ₐ[A] K) :
      specMap (x : B →+* K) ≫ p = specMap (y : B →+* K) ≫ p ↔ x = y := by
    simp [cancel_mono, Spec.map_inj, ConcreteCategory.hom_ext_iff, AlgHom.ext_iff]
  have h_comp {K : Type} [CommRing K] [Algebra A K] (x : B →ₐ[A] K) (g : Δ) :
      specMap (x.comp (act g) : B →+* K) ≫ p = (specMap (x : B →+* K) ≫ p) ≫ (s g).asHom.left := by
    rw [Category.assoc, ← h_act, ← Spec.map_comp_assoc]
    rfl
  have h_id : specMap (RingHom.id B) = 𝟙 (Spec (of B)) := Spec.map_id _
  have h_one : act 1 = .id A B := (h_cancel _ _).1 (by simp [h_act, h_id])
  have h_mul (g h : Δ) : act (g * h) = (act h).comp (act g) :=
    (h_cancel _ _).1 (by simp [h_comp, h_act])
  let σ : Δ →* (B →ₐ[A] B)ᵐᵒᵖ :=
    { toFun g := .op (act g)
      map_one' := congrArg MulOpposite.op h_one
      map_mul' g h := congrArg MulOpposite.op (h_mul g h) }
  refine ⟨σ, h_act, fun K _ _ x y ↦ ?_⟩
  have : CharZero K := h_char K (specMap (algebraMap A K))
  have h_fibre :
      (specMap (x : B →+* K) ≫ p) ≫ c.left = (specMap (y : B →+* K) ≫ p) ≫ c.left := by
    simp [hp.w, ← Spec.map_comp_assoc, ← ofHom_comp]
  simpa [σ, ← h_comp, h_cancel, AlgHom.ext_iff] using hG.torsor K _ _ h_fibre

section ProductOfFields

-- `Ω m` is an algebra over the residue field of the reduced Artinian ring `N` at `m`.
variable {N : Type*} [CommRing N] [IsArtinianRing N] [IsReduced N] {Ω : MaximalSpectrum N → Type*}
  [∀ m, CommRing (Ω m)] [∀ m, Algebra N (Ω m)] [∀ m, Algebra (N ⧸ m.asIdeal) (Ω m)]
  [∀ m, IsScalarTower N (N ⧸ m.asIdeal) (Ω m)]

/-- A reduced Artinian ring `N` embeds in any product over its maximal ideals `m` of faithful
algebras over the residue fields `N ⧸ m`. -/
lemma algebraMap_pi_injective
    (hΩ : ∀ m : MaximalSpectrum N, Function.Injective (algebraMap (N ⧸ m.asIdeal) (Ω m))) :
    Function.Injective (algebraMap N (∀ m : MaximalSpectrum N, Ω m)) := fun x y h_eq ↦
  (equivPi N).injective <| funext fun m ↦ hΩ m <| by
    simpa [IsScalarTower.algebraMap_apply N (N ⧸ m.asIdeal) (Ω m)] using congrFun h_eq m

/-- An element of the product of the `Ω m` whose components all come from the residue fields of
the reduced Artinian ring `N` comes from `N`. -/
lemma exists_algebraMap_pi_eq {z : ∀ m : MaximalSpectrum N, Ω m}
    (hz : ∀ m : MaximalSpectrum N, z m ∈ Set.range (algebraMap (N ⧸ m.asIdeal) (Ω m))) :
    ∃ v : N, algebraMap N (∀ m : MaximalSpectrum N, Ω m) v = z := by
  choose w hw using hz
  obtain ⟨v, rfl⟩ := (equivPi N).surjective w
  exact ⟨v, funext fun m ↦ (IsScalarTower.algebraMap_apply _ _ _ _).trans (hw m)⟩

end ProductOfFields

/-- If `A` is a smooth algebra over a normal domain `P`, then `A` is integrally closed in
`A ⊗[P] Frac P`. -/
lemma exists_algebraMap_eq_of_isIntegral_of_smooth {P A : Type} [CommRing P] [IsDomain P]
    [IsIntegrallyClosed P] [CommRing A] [Algebra P A] [Algebra.Smooth P A]
    {v : A ⊗[P] FractionRing P} (hv : IsIntegral A v) :
    ∃ x : A, algebraMap A (A ⊗[P] FractionRing P) x = v := by
  -- Integral closure commutes with smooth base change, and `P` is its own integral closure.
  let F : Type := FractionRing P
  have h_normal : Function.Surjective (algebraMap P (integralClosure P F)) :=
    fun z ↦ (isIntegral_iff.mp z.prop).imp fun _ ↦ Subtype.ext
  obtain ⟨w, hw⟩ : ∃ w : A ⊗[P] integralClosure P F, toIntegralClosure P A F w = ⟨v, hv⟩ :=
    toIntegralClosure_bijective_of_smooth.surjective _
  obtain ⟨x, rfl⟩ := includeLeft_surjective A A h_normal w
  exact ⟨x, congrArg Subtype.val hw⟩

/-- Let `Spec B` be the pull-back of a Galois covering `c : W ⟶ Z` with group `Δ` along
`u : Spec A ⟶ Z`, where `A` has field-valued points of characteristic zero, `B` is integral over `A`
and `p : Spec B ⟶ W` is a monomorphism. Let `σ` be the action of `Δ` on `B` compatible with the
action `s` on `W` (`specMap f` is the morphism of spectra induced by `f`). If an ideal `I` of `B`
contains the image of no nonzero element of `A` and contains all the conjugates `σ g b`, then `b` is
nilpotent. -/
lemma IsGaloisCovering.isNilpotent_of_forall_mem {R : CommRingCat} {W Z : Over (Spec R)}
    {c : W ⟶ Z} {Δ : FiniteGrp} {s : Δ →* CategoryTheory.End W} (hG : IsGaloisCovering c s)
    {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (h_char : ∀ (K : Type) [Field K], (Spec (of K) ⟶ Spec (of A)) → CharZero K)
    {p : Spec (of B) ⟶ W.left} {u : Spec (of A) ⟶ Z.left} [Mono p]
    (hp : IsPullback p (specMap (algebraMap A B)) c.left u) {σ : Δ →* (B →ₐ[A] B)ᵐᵒᵖ}
    (hσ : ∀ g : Δ, specMap (σ g).unop ≫ p = p ≫ (s g).asHom.left) {I : Ideal B}
    (hI : I.comap (algebraMap A B) = ⊥) {b : B} (hb : ∀ g : Δ, (σ g).unop b ∈ I) :
    IsNilpotent b := by
  -- Every prime of `B` is conjugate to one containing `I`.
  refine nilpotent_iff_mem_prime.mpr fun 𝔮 h𝔮 ↦ ?_
  obtain ⟨Q, hQ, hQ_prime, h_under⟩ :
      ∃ Q ≥ I, Q.IsPrime ∧ Q.comap (algebraMap A B) = 𝔮.under A :=
    exists_ideal_over_prime_of_isIntegral (𝔮.under A) I (hI.trans_le bot_le)
  let Q' : Spec (of B) := ⟨Q, hQ_prime⟩
  let 𝔮' : Spec (of B) := ⟨𝔮, h𝔮⟩
  obtain ⟨g, hg⟩ : ∃ g : Δ, (s g).asHom.left (p Q') = p 𝔮' :=
    hG.exists_apply_eq_of_apply_eq h_char _ hp.w Q' 𝔮' (PrimeSpectrum.ext h_under.symm)
  -- `p` is injective on points, so `g` moves `Q` to `𝔮` already in `Spec B`.
  have h_move : specMap ((σ g).unop : B →+* B) Q' = 𝔮' :=
    p.injective ((congrArg (fun f ↦ f Q') (hσ g)).trans hg)
  have h_comap : Q.comap (σ g).unop = 𝔮 := congrArg PrimeSpectrum.asIdeal h_move
  exact h_comap.le (hQ (hb g))

/-- Let `Ω` be a Galois extension of a field `K`, both algebras over `A`. If all `A`-algebra maps
`B → Ω` take the same value at `z`, this value lies in `K`. -/
lemma mem_range_algebraMap_of_forall_apply_eq {A B K Ω : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [Algebra A K] [Algebra A Ω]
    [IsScalarTower A K Ω] (χ : B →ₐ[A] Ω) {z : B} (hz : ∀ x : B →ₐ[A] Ω, x z = χ z) :
    χ z ∈ Set.range (algebraMap K Ω) :=
  (InfiniteGalois.mem_bot_iff_fixed _).mpr fun τ ↦ hz ((τ.restrictScalars A).toAlgHom.comp χ)

/-- Let `c : W ⟶ Z` be a Galois covering with group `Δ`, with `W` proper and `Z` separated over
`R`. Let `A` be étale over a normal domain `P`, with field-valued points of characteristic zero, and
let `Spec B` be the pull-back of `c` along `u : Spec A ⟶ Z`. If `B` is reduced and finite over `A`
and the projection `p : Spec B ⟶ W` is a monomorphism, then `B` is étale over `A`.
(Galois covering: `c` is surjective and `Δ`, acting through `s`, is simply transitive on its fibres
of points in fields of characteristic zero; `specMap f` is the morphism of spectra induced by the
ring map `f`.) -/
lemma IsGaloisCovering.etale_of_isPullback {R : CommRingCat} {W Z : Over (Spec R)} [IsProper W.hom]
    [IsSeparated Z.hom] {c : W ⟶ Z} {Δ : FiniteGrp} {s : Δ →* CategoryTheory.End W}
    (hG : IsGaloisCovering c s) (P : Type) [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    {A B : Type} [CommRing A] [Algebra P A] [Algebra.Etale P A]
    [CommRing B] [IsReduced B] [Algebra A B] [Module.Finite A B]
    (h_char : ∀ (K : Type) [Field K], (Spec (of K) ⟶ Spec (of A)) → CharZero K)
    {p : Spec (of B) ⟶ W.left} {u : Spec (of A) ⟶ Z.left} [Mono p]
    (hp : IsPullback p (specMap (algebraMap A B)) c.left u) :
    Algebra.Etale A B := by
  -- The group `Δ` acts on `B`, simply transitively on field-valued points. By
  -- `etale_of_simply_transitive` it remains to see that `A → B` is injective with image `B^Δ`.
  obtain ⟨σ, hσ, h_points⟩ := hG.exists_simply_transitive_action h_char hp
  have h_charA {K : Type} [Field K] [Algebra A K] : CharZero K :=
    h_char K (specMap (algebraMap A K))
  -- `N = A ⊗ Frac P` is a finite product of fields. Choose a point of `B` over an algebraic
  -- closure of each factor; together they form `χ`, which is injective on `A`.
  let F : Type := FractionRing P
  let N : Type := A ⊗[P] F
  let : Algebra F N := rightAlgebra
  have : Algebra.Etale F N := .of_equiv (commRight P F A)
  have : IsReduced N := isReduced_of_field F N
  have : Module.Finite F N := finite_of_free F N
  have : IsArtinianRing N := of_finite F N
  let (m : MaximalSpectrum N) : Field (N ⧸ m.asIdeal) := Quotient.field m.asIdeal
  let Ω (m : MaximalSpectrum N) : Type := AlgebraicClosure (N ⧸ m.asIdeal)
  have hN_inj : Function.Injective (algebraMap N (∀ m : MaximalSpectrum N, Ω m)) :=
    algebraMap_pi_injective fun _ ↦ RingHom.injective _
  have h_point (m : MaximalSpectrum N) : Nonempty (B →ₐ[A] Ω m) := by
    obtain ⟨y, hy⟩ : ∃ y : Spec (of (Ω m)) ⟶ W.left,
        y ≫ c.left = specMap (algebraMap A (Ω m)) ≫ u :=
      exists_point_over c.left (hG.surjective.surj _)
    exact (exists_algHom_specMap_comp_eq hp (Ω m) y hy).nonempty
  let χ : B →ₐ[A] ∀ m : MaximalSpectrum N, Ω m := .pi fun m ↦ (h_point m).some
  have hχ (x : A) : χ (algebraMap A B x) = algebraMap N _ (algebraMap A N x) := χ.commutes x
  have hA_inj : Function.Injective ((χ : B →+* ∀ m, Ω m).comp (algebraMap A B)) :=
    fun x x' h ↦ includeLeft_injective (S := P) (IsFractionRing.injective P F)
      (hN_inj ((hχ x).symm.trans (h.trans (hχ x'))))
  refine etale_of_simply_transitive (.of_comp (f := χ) hA_inj) σ h_points fun z hz ↦ ?_
  -- All points of `B` in a component `Ω m` agree on the invariant `z`, so `χ z` lies in `N`.
  have h_mem (m : MaximalSpectrum N) : χ z m ∈ Set.range (algebraMap (N ⧸ m.asIdeal) (Ω m)) := by
    let χₘ : B →ₐ[A] Ω m := (evalAlgHom _ _ m).comp χ
    refine mem_range_algebraMap_of_forall_apply_eq χₘ fun x ↦ ?_
    obtain ⟨g, hg, -⟩ := h_points (Ω m) x χₘ
    simpa [hz] using hg z
  obtain ⟨v, hv⟩ : ∃ v : N, algebraMap N (∀ m : MaximalSpectrum N, Ω m) v = χ z :=
    exists_algebraMap_pi_eq h_mem
  -- `v` is integral over `A`, and `A` is integrally closed in `N`, being smooth over normal `P`.
  have hχz_int : IsIntegral A (χ z) := .map χ (.of_finite A z)
  have hv_int : IsIntegral A v := .tower_bot hN_inj (by rwa [hv])
  obtain ⟨x, rfl⟩ : ∃ x : A, algebraMap A N x = v :=
    exists_algebraMap_eq_of_isIntegral_of_smooth hv_int
  -- The invariant `x - z` and its conjugates lie in `ker χ`, so it is nilpotent, hence zero.
  have h_ker (g : Δ) : (σ g).unop (algebraMap A B x - z) ∈ RingHom.ker χ := by
    rw [map_sub, AlgHom.commutes, hz, mem_ker, map_sub, hχ, hv, sub_self]
  have h_bot : (RingHom.ker χ).comap (algebraMap A B) = ⊥ := comap_bot_of_injective _ hA_inj
  exact ⟨x, sub_eq_zero.mp (hG.isNilpotent_of_forall_mem h_char hp hσ h_bot h_ker).eq_zero⟩

/-- The base change of a reduced scheme along a flat preimmersion is reduced: its stalks are those
of the scheme. -/
lemma isReduced_pullback_of_flat {X Y T : Scheme} (f : X ⟶ T) (g : Y ⟶ T)
    [IsReduced X] [Flat g] [IsPreimmersion g] : IsReduced (pullback f g) := by
  have (x : ↥(pullback f g)) : IsReduced ((pullback f g).presheaf.stalk x) := ⟨fun a ha ↦ by
    obtain ⟨b, rfl⟩ := (fst f g).stalkMap_surjective x a
    simp [((IsNilpotent.map_iff (stalkMap_injective_of_flat _ _)).1 ha).eq_zero]⟩
  exact isReduced_of_isReduced_stalk _

/-- If the base change of `c : W ⟶ Z` to the fibre product `Z ×_T E` is smooth of relative dimension
`0` and `Z ×_T E ⟶ E` of relative dimension `d`, then the base change of `c ≫ f : W ⟶ T` along any
map factoring through `i : E ⟶ T` is smooth of relative dimension `d`. -/
lemma smoothOfRelativeDimension_pullback_snd_comp (d : ℕ) {W Z T E K : Scheme} (c : W ⟶ Z)
    (f : Z ⟶ T) (i : E ⟶ T) (ψ : K ⟶ E) [SmoothOfRelativeDimension d (snd f i)]
    [SmoothOfRelativeDimension 0 (snd c (fst f i))] :
    SmoothOfRelativeDimension d (snd (c ≫ f) (ψ ≫ i)) := by
  have h_comp : SmoothOfRelativeDimension d (snd c (fst f i) ≫ snd f i) := by
    simpa using smoothOfRelativeDimension_comp 0 d (snd c (fst f i)) (snd f i)
  have h_square : IsPullback (fst c (fst f i)) (snd c (fst f i) ≫ snd f i) (c ≫ f) i :=
    .paste_vert (.of_hasPullback _ _) (.of_hasPullback _ _)
  exact (smoothOfRelativeDimension_isStableUnderBaseChange d).1
    ((IsPullback.of_hasPullback (c ≫ f) (ψ ≫ i)).of_right' h_square) h_comp

/-- Let `c : W ⟶ Z` be a Galois covering over `Spec R` for a domain `R`: `c` is surjective, and a
finite group `Δ` acts on `W` over `Z` through `s`, simply transitively on the fibres over points
with values in fields of characteristic 0. Suppose `W` is proper and reduced and `Z` is separated
and smooth of relative dimension `d`. Then for any field `k` of characteristic 0 into which `R`
injects, the base change of `W` to `k` is smooth of relative dimension `d` over `Spec k`
(`specMap f` is the morphism of spectra induced by the ring map `f`). -/
lemma IsGaloisCovering.smoothOfRelativeDimension_baseChange {R : CommRingCat} [IsDomain R]
    {W Z : Over (Spec R)} [IsProper W.hom] [IsSeparated Z.hom] {c : W ⟶ Z} {Δ : FiniteGrp}
    {s : Δ →* CategoryTheory.End W} (hG : IsGaloisCovering c s) (d : ℕ)
    [IsReduced W.left] [SmoothOfRelativeDimension d Z.hom] (k : Type) [Field k] [CharZero k]
    [Algebra R k] [FaithfulSMul R k] :
    SmoothOfRelativeDimension d (pullback.snd W.hom (specMap (algebraMap R k))) := by
  -- Pass to the function field of `R`, through which `R → k` factors. There `c` becomes a finite
  -- map `q` from a reduced scheme to a smooth one, and `q` is étale by `etale_of_isPullback`.
  let E : Type := (Spec R).functionField
  let ι : Spec (of E) ⟶ Spec R := (Spec R).fromSpecStalk (genericPoint (Spec R))
  have hι : ι = specMap (algebraMap R E) := fromSpecStalk_eq R _
  let ψ : E →+* k := IsFractionRing.lift (FaithfulSMul.algebraMap_injective R k)
  have hψ : specMap ψ ≫ ι = specMap (algebraMap R k) := by
    have h_comp : ψ.comp (algebraMap R E) = algebraMap R k := lift_comp _
    rw [hι, ← h_comp, ← Spec.map_comp, ← ofHom_comp]
  -- The generic fibre of `Z`, and the pull-back `q` of `c` to it.
  let π : pullback Z.hom ι ⟶ Z.left := fst Z.hom ι
  let q : pullback c.left π ⟶ pullback Z.hom ι := snd c.left π
  have h_char (K : Type) [Field K] (y : Spec (of K) ⟶ pullback Z.hom ι) : CharZero K :=
    (charZero_iff (Spec.preimage (y ≫ snd Z.hom ι)).hom.injective).1 ψ.charZero
  -- The generic fibre of `W` is reduced, and `q` has finite fibres.
  have : IsReduced (pullback c.left π) := isReduced_pullback_of_flat c.left π
  have : AlgebraicGeometry.Surjective c.left := hG.surjective
  have h_fibre (x : ↥(pullback c.left π)) : (q ⁻¹' {q x}).Finite :=
    hG.finite_preimage_singleton h_char (fst c.left π).injective q condition x
  have : LocallyQuasiFinite q := of_finite_preimage_singleton q (q.surjective.forall.2 h_fibre)
  have : IsFinite q := .of_isProper_of_locallyQuasiFinite q
  -- By base change along `ψ` it suffices that `q` is smooth of relative dimension `0`.
  suffices h_zero : SmoothOfRelativeDimension 0 q by
    rw [← hψ, ← c.w]
    exact smoothOfRelativeDimension_pullback_snd_comp d c.left Z.hom ι (specMap ψ)
  refine ⟨fun x ↦ ?_⟩
  -- Near `q x`, over an affine open `V`, the generic fibre of `Z` is étale over a polynomial ring
  -- over the function field; apply `etale_of_isPullback` with this ring as `P`.
  obtain ⟨U, -, V, hV, hx, hVU, h_smooth⟩ :=
    (smoothOfRelativeDimension_iff d (snd Z.hom ι)).1 inferInstance (q x)
  have hU : U ≠ ⊥ := fun h ↦ by simpa [h] using hVU hx
  obtain rfl : U = ⊤ := U.eq_bot_or_top.resolve_left hU
  have hV' : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
  refine ⟨V, hV, q ⁻¹ᵁ V, hV', hx, le_rfl, etale_iff_isStandardSmoothOfRelativeDimension_zero.1 ?_⟩
  let P : Type := MvPolynomial (Fin d) Γ(Spec (of E), ⊤)
  obtain ⟨f, hf_etale⟩ : ∃ f : P →+* Γ(pullback Z.hom ι, V), f.Etale :=
    h_smooth.exists_etale_mvPolynomial.imp fun _ ↦ And.right
  have h_finite : (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom.Finite := by
    simpa only [← q.app_eq_appLE] using q.finite_app V hV
  have h_affine : IsPullback (Spec.map (q.appLE V (q ⁻¹ᵁ V) le_rfl)) hV'.fromSpec hV.fromSpec q :=
    isPullback _ _ _ _ (hV.SpecMap_appLE_fromSpec q hV' le_rfl).symm (by simp)
  -- `hf_etale` and `h_finite` become instances for the algebra structures given by the two maps
  algebraize [f, (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom]
  exact hG.etale_of_isPullback P (fun K _ y ↦ h_char K (y ≫ hV.fromSpec))
    (h_affine.flip.paste_horiz (.of_hasPullback c.left π))

end GaloisCovers

end New.Variety

end
