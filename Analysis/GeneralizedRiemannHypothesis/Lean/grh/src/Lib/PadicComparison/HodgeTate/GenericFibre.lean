import Lib.PadicComparison.Completion
import Lib.PadicComparison.Descent.TestCovers
import Lib.PadicHodge.PeriodRings.CrystallineRings

/-!
# The ring R[1/p] of a p-adic test and the square-zero extension W(R♭)[1/p]/(ker θ)²

Let `c` be a p-adic test with ring R = `c.ProdRing`, a product of valuation rings over O_C. Put K =
R[1/p] (`New.Variety.PadicTest.GenericRing`) and B = W(R♭)[1/p]/(ker θ)², where θ is Fontaine's map.
Since p is not a zero divisor in R, the map R → K is injective. B is a square-zero extension of K by
K, and the map ℚ̄_p → K lifts uniquely to B over ℤ_p. Both constructions are functorial in `c`.

## Main definitions and results

* `New.Variety.genericOver`, `New.Variety.thickeningOver`: `c ↦ K` and `c ↦ B` as functors to
  `k`-algebras.
* `New.Variety.thickeningOver.exact_mulMu_proj`: `0 → K → B → K → 0` is exact; the first map comes
  from multiplication by `μ` (`New.Period.mu`).
* `New.Variety.exists_periodAlg_iso_genericAlg`, `New.Variety.hasZariskiDescent_genericOver`: `K` as
  a completed tensor product; Zariski descent.

Notions from other files:
* `New.Variety.PadicTest.TiltRing`: The tilt R♭, the inverse limit of R/p along Frobenius.
* `New.Period.Ainf`: The ring A_inf of p-typical Witt vectors over the tilt O♭ of O_C.

## Relation to the literature

Known; see `Lib.PadicComparison.HodgeTate.PeriodMap` for sources.
-/

noncomputable section

/-! ## The ring R[1/p] and injectivity of R → R[1/p] -/

namespace New.Variety.PadicTest

variable {p : ℕ} [ThePrime p] (c : PadicTest)

/-- The ring R[1/p] obtained by inverting p in the ring R of a p-adic test. -/
abbrev GenericRing : Type := Localization.Away (p : c.ProdRing)

/-- The map `R → R[1/p]` is injective: an element of the ring `R` of a p-adic test that becomes
zero in `R[1/p]` is zero, since `p` is not a zero divisor in `R`. -/
lemma eq_zero_of_algebraMap_genericRing (x : c.ProdRing)
    (hx : algebraMap c.ProdRing c.GenericRing x = 0) :
    x = 0 := by
  -- A power of `p` kills `x`, and `p` is not a zero divisor of `c.ProdRing`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (p : c.ProdRing) ^ n * x = p ^ n * 0 :=
    IsLocalization.Away.exists_of_eq (p : c.ProdRing) (hx.trans (map_zero _).symm)
  exact c.isLeftRegular_p.pow n hn

end New.Variety.PadicTest

/-! ## The square-zero extension W(R♭)[1/p]/(ker θ)² of R[1/p] -/

section GenericFibreTests

namespace New.Variety

open CategoryTheory Function Ideal WittVector Period Algebra IsLocalization RingHom PadicTest
  Functor CommAlgCat Quot FormallySmooth FormallyUnramified

/-- The field k has characteristic zero and comes with an embedding in Q̄_p, the algebraic
closure of ℚ_p, for the fixed prime p. -/
class EmbeddedInQpBar (p : outParam ℕ) (k : outParam Type) [Field k] extends ThePrime p,
  Algebra k (PadicAlgCl p), CharZero k

section

variable {p : ℕ} [ThePrime p] (c : PadicTest)

namespace PadicTest

/-- The ℂ_p-algebra structure on R[1/p] of a p-adic test with ring R, induced from its structure map
O_C → R by inverting p. It is introduced through a choice, so that its definition does not
unfold. -/
instance algebraGenericRing : ∀ c : PadicTest, Algebra ℂ_[p] c.GenericRing :=
  (@exists_eq _ (map _ ·.structureMap (powers_le_comap_powers p _) |>.toAlgebra)).choose

/-- For a p-adic test c with ring R, the structure map ℂ_p → K = R[1/p]. -/
def genericStructureMap : ℂ_[p] →+* c.GenericRing := algebraMap ℂ_[p] c.GenericRing

/-- On `O_C`, the structure map `ℂ_p → R[1/p]` is the structure map `O_C → R` of the test followed
by `R → R[1/p]`. -/
lemma genericStructureMap_coe (x : OC) :
    c.genericStructureMap x.val = algebraMap ((i : c.Index) → c.Cell i) c.GenericRing
      (c.structureMap x) := by
  -- The algebra structure is defined through a choice, so the proof opens that choice.
  simpa +instances [genericStructureMap, algebraGenericRing] using! map_eq ..

/-- `O_C → ℂ_p → R[1/p]` is a scalar tower: on `O_C`, `genericStructureMap` is the structure map
`O_C → R` followed by `R → R[1/p]` (`genericStructureMap_coe`). -/
instance : IsScalarTower OC ℂ_[p] c.GenericRing :=
  .of_algebraMap_eq fun x ↦ (c.genericStructureMap_coe x).symm

/-- For a p-adic test with ring R, the map W(R^♭)[1/p] → R[1/p] obtained from Fontaine's map θ:
W(R^♭) → R by inverting p. -/
def thetaGeneric : Localization.Away (p : WittVector p c.TiltRing) →+* c.GenericRing :=
  IsLocalization.map c.GenericRing (fontaineTheta c.ProdRing p)
    (powers_le_comap_powers p (fontaineTheta c.ProdRing p))

/-- On `A_inf`, the map `θ : W(R♭)[1/p] → R[1/p]` is Fontaine's `θ : A_inf → O_C` followed by the
structure map. -/
lemma thetaGeneric_algebraMap_ainf (a : Ainf) :
    c.thetaGeneric (algebraMap Ainf (Localization.Away (p : WittVector p c.TiltRing)) a) =
      c.genericStructureMap (theta a) := by
  -- On `A_inf` the algebra map to `W(R♭)` is induced by the tilt of `O_C → R`, by definition.
  change c.thetaGeneric (algebraMap (WittVector p c.TiltRing) _
    (WittVector.map (tiltMap c.structureMap) a)) = _
  rw [thetaGeneric, IsLocalization.map_eq, fontaineTheta_map_tiltMap, genericStructureMap_coe]

/-- `θ` kills the element `μ = [ε] - 1` of `A_inf`. -/
lemma thetaGeneric_mu :
    c.thetaGeneric (algebraMap Ainf (Localization.Away (p : WittVector p c.TiltRing)) mu) = 0 := by
  simp [thetaGeneric_algebraMap_ainf, mu]

/-- For a p-adic test with ring R, the quotient B = W(R^♭)[1/p]/(ker θ)², where
θ: W(R^♭)[1/p] → R[1/p]. -/
abbrev Thickening : Type := Localization.Away (p : WittVector p c.TiltRing) ⧸ ker c.thetaGeneric ^ 2

/-- For a p-adic test with ring R, the ring map W(R^♭)[1/p]/(ker θ)² → R[1/p] induced by θ. -/
def thickeningProj :
    Localization.Away (p : WittVector p c.TiltRing) ⧸ ker c.thetaGeneric ^ 2 →+* c.GenericRing :=
  Ideal.Quotient.lift (ker c.thetaGeneric ^ 2) c.thetaGeneric (pow_le_self (by simp))

/-- `R[1/p]` is the localisation of `R` at the image under `f : S → R` of the powers of `p`, for any
ring `S`. -/
instance isLocalization_genericRing {S : Type*} [CommRing S] (f : S →+* c.ProdRing) :
    IsLocalization (Submonoid.map f (Submonoid.powers (p : S))) c.GenericRing := by
  rw [Submonoid.map_powers, map_natCast]
  infer_instance

/-- The map `W(R♭)[1/p] / (ker θ)² → R[1/p]` induced by `θ` is onto: Fontaine's `θ` is onto, and it
stays onto after inverting `p`. -/
lemma thickeningProj_surjective : Surjective c.thickeningProj :=
  (surjective_lift _).2 (map_surjective_of_surjective
    (M := Submonoid.powers (p : WittVector p c.TiltRing)) (Q := c.GenericRing)
    (S := Localization.Away (p : WittVector p c.TiltRing))
    fontaineTheta_surjective_of_isAbsIntegrallyClosed)

/-- The kernel of `θ : W(R♭)[1/p] → R[1/p]` is generated by the image of `ξ`: Fontaine's `θ` has
kernel `(ξ)`, and inverting `p` keeps this. -/
lemma ker_thetaGeneric_eq_span_xi :
    ker c.thetaGeneric =
      span {algebraMap Ainf (Localization.Away (p : WittVector p c.TiltRing)) xi} := by
  -- The image of `ξ` in `W(R♭)[1/p]` passes through `W(R♭)`, by the definition of the algebra.
  change _ = span {(algebraMap (WittVector p c.TiltRing) _
    (WittVector.map (algebraMap OFlat c.TiltRing) xi))}
  simp [thetaGeneric, ker_map, map_span]

lemma thickeningProj_surjective_and_ker_thetaGeneric :
    Surjective c.thickeningProj ∧
      ker c.thetaGeneric =
        span {algebraMap Ainf (Localization.Away (p : WittVector p c.TiltRing)) xi} :=
  ⟨c.thickeningProj_surjective, c.ker_thetaGeneric_eq_span_xi⟩

lemma ker_thickeningProj_sq : ker c.thickeningProj ^ 2 = ⊥ := by
  simp [thickeningProj, ker_quotient_lift, ← Ideal.map_pow]

/-- The structure map `ℚ̄_p → ℂ_p → R[1/p]` lifts uniquely along `thickeningProj` to a
`ℤ_p`-algebra map into the thickening, since `ℚ̄_p` is formally étale over `ℤ_p`. -/
lemma existsUnique_lift_thickening :
    ∃! ρ : PadicAlgCl p →ₐ[ℤ_[p]] c.Thickening,
      ∀ z : PadicAlgCl p, c.thickeningProj (ρ z) = c.genericStructureMap z := by
  -- `thickeningProj` is onto with square-zero kernel, and `ℤ_p → ℚ_p → ℚ̄_p` is formally étale:
  -- a lift exists by formal smoothness and is unique by formal unramifiedness.
  let : Algebra ℤ_[p] c.GenericRing := restrictScalars ℤ_[p] ℂ_[p] c.GenericRing
  have h_nil : IsNilpotent (ker c.thickeningProj) := ⟨2, c.ker_thickeningProj_sq⟩
  have : FormallyEtale ℤ_[p] ℚ_[p] := .of_isLocalization (nonZeroDivisors ℤ_[p])
  have : FormallyEtale ℚ_[p] (PadicAlgCl p) := .of_isSeparable ℚ_[p] (PadicAlgCl p)
  have : FormallyEtale ℤ_[p] (PadicAlgCl p) := .comp ℤ_[p] ℚ_[p] (PadicAlgCl p)
  -- The structure map `ℚ̄_p → ℂ_p → R[1/p]` as a `ℤ_p`-algebra map.
  let s : PadicAlgCl p →ₐ[ℤ_[p]] c.GenericRing :=
    ⟨c.genericStructureMap.comp (algebraMap (PadicAlgCl p) ℂ_[p]), fun _ ↦ rfl⟩
  -- `thickeningProj` is `ℤ_p`-linear, as there is only one ring map `ℤ_p → OC`.
  have h_linear (a : ℤ_[p]) :
      c.thickeningProj (algebraMap ℤ_[p] c.Thickening a) = algebraMap ℤ_[p] c.GenericRing a := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] Ainf c.Thickening]
    exact (c.thetaGeneric_algebraMap_ainf _).trans
      (congrArg c.genericStructureMap ((OC.toPadicIntAlgHom _).commutes a))
  let π : c.Thickening →ₐ[ℤ_[p]] c.GenericRing := ⟨c.thickeningProj, h_linear⟩
  have h_surj : Surjective π := c.thickeningProj_surjective_and_ker_thetaGeneric.left
  exact existsUnique_of_exists_of_unique
    ⟨liftOfSurjective s π h_surj h_nil, liftOfSurjective_apply s π h_surj h_nil⟩
    fun ρ ρ' hρ hρ' ↦ ext' c.thickeningProj h_nil ρ ρ' fun z ↦ by rw [hρ, hρ']

/-- The unique `ℤ_p`-algebra map from `ℚ̄_p` to the thickening that lifts the structure map
`ℚ̄_p → ℂ_p → R[1/p]` along `thickeningProj`. -/
def uniqueLift : PadicAlgCl p →ₐ[ℤ_[p]] c.Thickening :=
  c.existsUnique_lift_thickening.exists.choose

lemma thickeningProj_uniqueLift (z : PadicAlgCl p) :
    c.thickeningProj (c.uniqueLift z) = c.genericStructureMap z :=
  c.existsUnique_lift_thickening.exists.choose_spec z

/-- Every `ℤ_p`-algebra map that lifts the structure map along `thickeningProj` is
`uniqueLift`. -/
lemma eq_uniqueLift (ρ : PadicAlgCl p →ₐ[ℤ_[p]] c.Thickening)
    (hρ : ∀ z : PadicAlgCl p, c.thickeningProj (ρ z) = c.genericStructureMap z) :
      ρ = c.uniqueLift :=
  c.existsUnique_lift_thickening.unique hρ c.thickeningProj_uniqueLift

variable {c} {d : PadicTest} (f : c ⟶ d)

/-! ### Maps induced by a morphism of tests -/

/-- For a morphism of p-adic tests with rings R, R', the induced ℂ_p-algebra map
R[1/p] → R'[1/p]. -/
def mapGeneric : c.GenericRing →ₐ[ℂ_[p]] d.GenericRing where
  toRingHom := IsLocalization.map d.GenericRing f.1 (powers_le_comap_powers p f.toRingHom)
  commutes' _ := by
    simp +instances [algebraMap_toAlgebra, algebraGenericRing, IsLocalization.map_map]
    congr
    exact f.comp_algebraMap

/-- `mapGeneric f` extends the map `f : R → R'` of the rings of the tests. -/
lemma mapGeneric_algebraMap (x : c.ProdRing) :
    mapGeneric f (algebraMap c.ProdRing c.GenericRing x) =
      algebraMap d.ProdRing d.GenericRing (f.toRingHom x) :=
  lift_eq ..

/-- For a morphism of p-adic tests, the induced A_inf-algebra map between the quotients
W(R^♭)[1/p]/(ker θ)². -/
def mapThickening : c.Thickening →ₐ[Ainf] d.Thickening :=
  quotientMapₐ (ker d.thetaGeneric ^ 2)
    -- the map of Witt vectors induced by `f`, with `p` inverted
    ⟨IsLocalization.map _ (_ : WittVector p c.TiltRing →+* WittVector p d.TiltRing)
        (powers_le_comap_powers p _),
      fun a ↦ (map_eq ..).trans (congrArg _ (((tilt ⋙ wittFunctor).map f).1.commutes' a))⟩
    -- both kernels are generated by the image of `xi`
    (by simp [thickeningProj_surjective_and_ker_thetaGeneric, span_singleton_pow, -AlgHom.coe_mk])

/-- The maps induced by `f` on the thickenings and on the rings `R[1/p]` commute with the
projections `thickeningProj`. -/
lemma thickeningProj_mapThickening :
    ∀ x : c.Thickening,
      d.thickeningProj (mapThickening f x) = mapGeneric f (c.thickeningProj x) := by
  rintro ⟨x⟩
  change d.thetaGeneric _ = mapGeneric f (c.thetaGeneric x)
  simp [thetaGeneric, mapGeneric, IsLocalization.map_map, RingHom.comp, fontaineTheta_map_tiltMap,
    tilt, wittFunctor]

lemma mapThickening_uniqueLift (z : PadicAlgCl p) :
    mapThickening f (c.uniqueLift z) = d.uniqueLift z := by
  -- `mapThickening f` composed with the lift for `c` lifts `d.genericStructureMap`; such a lift is
  -- unique.
  have h_lift (w : PadicAlgCl p) :
      d.thickeningProj (mapThickening f (c.uniqueLift w)) = d.genericStructureMap w := by
    rw [thickeningProj_mapThickening, thickeningProj_uniqueLift]
    exact (mapGeneric f).commutes _
  exact DFunLike.congr_fun
    (d.eq_uniqueLift (((mapThickening f).restrictScalars ℤ_[p]).comp c.uniqueLift) h_lift) z

/-! ### The functors `c ↦ c.GenericRing` and `c ↦ c.Thickening` -/

/-- The functor sending a p-adic test with ring R to R[1/p], as a ℂ_p-algebra. -/
def genericAlg : PadicTest ⥤ CommAlg ℂ_[p] where
  obj c := CommAlgCat.of ℂ_[p] c.GenericRing
  map f := ofHom (mapGeneric f)
  map_id _ := CommAlgCat.hom_ext (AlgHom.ext IsLocalization.map_id)
  map_comp := by aesop (add simp [mapGeneric, IsLocalization.map_map])

/-- The functor from p-adic tests to test rings (`TestRing`: commutative rings with the test
property, which passes from R to R[1/p]) sending a test with ring R to R[1/p]. -/
def genericTest : PadicTest ⥤ TestRing :=
  -- The maps are written out, so that the kernel compares a test with its twists without
  -- unfolding `genericAlg`.
  ObjectProperty.lift _
    { genericAlg ⋙ forget₂ (CommAlg ℂ_[p]) CommRingCat with
      obj := _,
      map f := CommRingCat.ofHom (mapGeneric f).1 }
    fun c ↦ c.isTest.localization

end PadicTest

/-- The coefficient on p-adic tests sending a test with ring R to the additive group of R[1/p]. -/
abbrev genericCoeff : AbFunctor PadicTest := moduleCoeff (asModules genericAlg)

/-! ### Comparison with completed tensor products, and Zariski descent -/

/-- On p-adic tests with ring R there is a natural isomorphism of ℂ_p-modules (bound as `θ` in the
statement) from ℂ_p ⊗_{O_C} (O_C ⊗_{A_inf} W(R^♭))^, the hat denoting p-adic completion, to R[1/p],
sending a ⊗ (1 ⊗ w) to a · (Fontaine's map `fontaineTheta` applied to w). -/
lemma exists_periodAlg_iso_genericAlg :
    ∃ θ : asModules (tilt ⋙ periodAlg OC) ⋙ tensorWith ℂ_[p] ℂ_[p] ≅ asModules genericAlg,
      ∀ (c : PadicTest) (a : ℂ_[p]) (w : (wittFunctor (WittVector p OFlat)).obj (tilt.obj c)),
        θ.hom c (a ⊗ₜ AdicCompletion.of _ _ (1 ⊗ₜ w)) =
          c.genericStructureMap a * algebraMap c.ProdRing c.GenericRing
            (fontaineTheta c.ProdRing p w) := by
  -- Compose three isomorphisms: `thetaIso : O_C ⊗ W(ProdRing♭) ≅ ProdRing` under completion, the
  -- inverse of `ProdRing ≅ ProdRing^`, and `ℂ_p ⊗ ProdRing ≅ ProdRing[1/p]`.
  let toCpl : algFunctor ≅ algFunctor ⋙ algCompletion OC p :=
    isoOfAppBijective (algFunctor.whiskerLeft (algCompletion.of OC p)) fun c ↦
      AdicCompletion.of_bijective_iff.mpr c.isAdicComplete_prodRing
  let θ : tilt ⋙ periodAlg OC ≅ algFunctor :=
    isoWhiskerRight thetaIso (algCompletion OC p) ≪≫ toCpl.symm
  have hθ (c : PadicTest) (w : (wittFunctor (WittVector p OFlat)).obj (tilt.obj c)) :
      θ.hom c (.of _ _ (1 ⊗ₜ w)) = fontaineTheta c.ProdRing p w := by
    rw [← c.thetaIso_hom_one_tmul w]
    exact (congrArg _ (adicMap_algebraMap ..)).trans (toCpl.hom_inv_id_app_apply ..)
  let invert : asModules algFunctor ⋙ tensorWith ℂ_[p] ℂ_[p] ≅ asModules genericAlg :=
    NatIso.ofComponents
      (fun c ↦
        ((isLocalization_iff_isPushout _ ℂ_[p]).1
          (c.isLocalization_genericRing _)).symm.out.equiv.toModuleIso)
      fun f ↦ ModuleCat.hom_ext <| tmul_ext fun a x ↦ by
        -- `erw` rewrites through the composite module maps and the pushout equivalence.
        erw [map_smul (mapGeneric f), mapGeneric_algebraMap]
        rfl
  refine ⟨isoWhiskerRight θ (asModules (𝟭 _) ⋙ tensorWith ℂ_[p] ℂ_[p]) ≪≫ invert, fun c a w ↦ ?_⟩
  -- `invert` sends `a ⊗ x` to `a • x`, and `θ` sends `1 ⊗ w` to `θ(w)`.
  exact (congrArg (a • algebraMap c.ProdRing c.GenericRing ·) (hθ c w)).trans
    (c.algebraGenericRing.smul_def' a _)

end

variable {p : ℕ} {k : Type} [Field k] [EmbeddedInQpBar p k] (c : PadicTest)

/-- `ℂ_p` is a `k`-algebra through `k → ℚ̄_p → ℂ_p`. -/
instance : Algebra k ℂ_[p] := .restrictScalars k (PadicAlgCl p) _

/-- `k` acts on `R[1/p]` through `k → ℂ_p`. -/
instance : CoeffAction k genericCoeff := ⟨CoeffAction.act.comp (algebraMap k ℂ_[p])⟩

/-- For a field k with an embedding in Q̄_p, the functor sending a p-adic test with ring R to
R[1/p], as a k-algebra. -/
def genericOver : PadicTest ⥤ CommAlg k := genericAlg ⋙ restrictAlg k ℂ_[p]

/-- The thickening is a `k`-algebra through `k → ℚ̄_p` followed by `uniqueLift`. -/
instance : Algebra k c.Thickening :=
  (c.uniqueLift.toRingHom.comp (algebraMap k (PadicAlgCl p))).toAlgebra

/-- The functor sending a test `c` to the `k`-algebra `c.Thickening = W(R♭)[1/p] / (ker θ)²`. -/
def thickeningOver : PadicTest ⥤ CommAlg k where
  obj c := .of k c.Thickening
  map f := ofHom
    ⟨mapThickening f, fun a ↦ mapThickening_uniqueLift f (algebraMap k (PadicAlgCl p) a)⟩
  map_id c := by
    ext ⟨x⟩
    exact congrArg (⟦·⟧) (by simpa using! IsLocalization.map_id x)
  map_comp f g := by
    ext ⟨x⟩
    exact congrArg (⟦·⟧) (by simpa using! .symm (IsLocalization.map_map ..))

/-- Let `Θ : C ⥤ PadicTest` and let `F : AbFunctor C`, a functor from `C` to abelian groups, be
additive on idempotent partitions (`New.Variety.HasPartitions`) for the rings `R` of the tests
`Θ(X)`. Then `F` satisfies Zariski descent (`New.Variety.HasZariskiDescent`) for the rings
`R[1/p]`. -/
lemma hasZariskiDescent_genericOver {C : Type 1} [Category C] (Θ : C ⥤ PadicTest) {F : AbFunctor C}
    (h : HasPartitions (Θ ⋙ ringFunctor) F) :
    HasZariskiDescent (Θ ⋙ genericOver ⋙ forget₂ (CommAlg k) CommRingCat) F := by
  -- The two hypotheses of `HasPartitions.hasZariskiDescent` for `R → R[1/p]`: the map is injective,
  -- and elements of `R[1/p]` are associated to elements of `R`, which are comparable for
  -- divisibility after cutting along an idempotent.
  exact h.hasZariskiDescent
    ⟨_, fun _ _ g ↦
      CommRingCat.hom_ext (RingHom.ext fun x ↦ (mapGeneric_algebraMap (Θ.map g) x).symm)⟩
    (fun c ↦ eq_zero_of_algebraMap_genericRing (Θ c))
    fun X ↦ (Θ.obj X).isTest.isComparableRing_of_associated exists_associated_localization

namespace thickeningOver

/-! ### The square-zero extension `0 → c.GenericRing → c.Thickening → c.GenericRing → 0` -/

/-- The projection `thickeningProj` from the thickening onto `R[1/p]`, as a natural map of
`k`-algebras. -/
def proj : thickeningOver (k := k) ⟶ genericOver where
  app c := CommAlg.homOfRingHom c.thickeningProj fun a ↦
    c.thickeningProj_uniqueLift (algebraMap k (PadicAlgCl p) a)
  naturality c d f := by
    ext x
    exact thickeningProj_mapThickening f x

/-- The additive map R[1/p] → W(R^♭)[1/p]/(ker θ)² sending θ(x) to the class of μx, where
μ = [ε] − 1. It is well defined since θ is onto and μ · ker θ ⊆ (ker θ)². -/
def mulMu : genericOver c →+ thickeningOver c :=
  c.thickeningProj.toAddMonoidHom.liftOfSurjective
    c.thickeningProj_surjective_and_ker_thetaGeneric.1
    ⟨AddMonoidHom.mulLeft ⟦algebraMap Ainf _ mu⟧, fun b hb ↦ by
      -- `μ` and `b` both lie in the kernel of `thickeningProj`, whose square is zero.
      exact (sq _).ge.trans_eq c.ker_thickeningProj_sq (mul_mem_mul c.thetaGeneric_mu hb)⟩

/-- `mulMu` sends `θ(b)` to `μ b`. -/
lemma mulMu_thickeningProj (b : c.Thickening) :
    mulMu c (c.thickeningProj b) = (algebraMap Ainf c.Thickening mu * b : c.Thickening) :=
  AddMonoidHom.liftOfRightInverse_comp_apply ..

/-- `proj` kills the image of `mulMu`, since `θ(μ) = 0`. -/
lemma proj_mulMu : ∀ t : genericOver.obj c, proj c (mulMu c t) = 0 := by
  refine c.thickeningProj_surjective_and_ker_thetaGeneric.left.forall.mpr fun b ↦ ?_
  -- `proj c` is `thickeningProj`, and `θ(μ) = 0`.
  change c.thickeningProj (mulMu c (c.thickeningProj b)) = 0
  rw [mulMu_thickeningProj, map_mul,
    show c.thickeningProj (algebraMap Ainf c.Thickening mu) = 0 from c.thetaGeneric_mu, zero_mul]

/-- `mulMu` is linear over the thickening, which acts on `R[1/p]` through `proj`. -/
lemma mulMu_proj_mul (b : thickeningOver.obj c) :
    ∀ t : genericOver.obj c, mulMu c (proj c b * t) = b * mulMu c t := by
  refine c.thickeningProj_surjective_and_ker_thetaGeneric.left.forall.mpr fun b' ↦ ?_
  -- `erw`: `b` lives in `thickeningOver.obj c`, and `proj c b` is `c.thickeningProj b` only up to
  -- unfolding.
  erw [← map_mul, mulMu_thickeningProj, mulMu_thickeningProj, mul_left_comm]
  rfl

/-- `mulMu` commutes with the maps induced by a morphism `f` of tests. -/
lemma map_mulMu (d : PadicTest) (f : c ⟶ d) :
    ∀ t : genericOver.obj c, thickeningOver.map f (mulMu c t) = mulMu d (genericOver.map f t) := by
  refine c.thickeningProj_surjective_and_ker_thetaGeneric.left.forall.mpr fun b ↦ ?_
  change mapThickening f (mulMu c (c.thickeningProj b)) =
    mulMu d (mapGeneric f (c.thickeningProj b))
  rw [← thickeningProj_mapThickening, mulMu_thickeningProj, mulMu_thickeningProj,
    map_mul (mapThickening f), AlgHom.commutes]

/-- `ξ` is not a zero divisor in `W(R♭)[1/p]`. -/
lemma isLeftRegular_xi {p : ℕ} [ThePrime p] (c : PadicTest) :
    IsLeftRegular (algebraMap Ainf (Localization.Away (p : WittVector p c.TiltRing)) xi) := by
  -- As the localisation is flat, it is enough to show that `ξ x = 0` in `W(R♭)` forces `x = 0`.
  refine IsSMulRegular.of_flat (R := WittVector p c.TiltRing) (x := algebraMap Ainf _ xi)
    (.of_right_eq_zero_of_smul fun x hx ↦ by_contra fun x_ne ↦ ?_)
  -- Otherwise `x` is a `j`-fold Verschiebung of some `y` with nonzero zeroth coordinate.
  obtain ⟨j, y, hy, rfl⟩ :
      ∃ (j : ℕ) (y : WittVector p c.TiltRing), y.coeff 0 ≠ 0 ∧ x = verschiebung^[j] y :=
    verschiebung_nonzero x_ne
  -- The `j`-th coordinate of `ξ x` is `y.coeff 0` times the `p ^ j`-th power of the zeroth
  -- coordinate of `ξ`, the image of `pFlat`, which is regular in `c.TiltRing`.
  refine hy (IsLeftRegular.pow (R := c.TiltRing) (p ^ j) c.isPerfectTorsionFree_tilt.right ?_)
  -- The `j`-th coordinate of `ξ x = 0`, by the formula for products of Verschiebungs.
  have h_coeff :
      (algebraMap Ainf (WittVector p c.TiltRing) xi).coeff 0 ^ p ^ j * y.coeff 0 = 0 := by
    simpa [← smul_eq_mul, hx] using
      (iterate_verschiebung_mul_coeff (algebraMap Ainf (WittVector p c.TiltRing) xi) y 0 j).symm
  show tiltMap c.structureMap pFlat ^ p ^ j * y.coeff 0 = tiltMap c.structureMap pFlat ^ p ^ j * 0
  rw [mul_zero]
  -- The zeroth coordinate of `ξ` in `W(R♭)` is the image of `pFlat`.
  have h_xi_coeff : (algebraMap Ainf (WittVector p c.TiltRing) xi).coeff 0 =
      tiltMap c.structureMap pFlat := rfl
  rwa [h_xi_coeff] at h_coeff

/-- For a `p`-adic test `c` with ring `R`, `proj c : W(R♭)[1/p] / (ker θ)² → R[1/p]` is the map
induced by `θ`, and `mulMu c : R[1/p] → W(R♭)[1/p] / (ker θ)²` sends `θ(x)` to the class of `μx`,
where `μ = [ε] − 1`. The sequence `0 → R[1/p] → W(R♭)[1/p] / (ker θ)² → R[1/p] → 0` given by
`mulMu c` and `proj c` is exact: `proj c` is surjective, `mulMu c` is injective, and the image of
`mulMu c` is the kernel of `proj c`. -/
lemma exact_mulMu_proj :
    Surjective (proj c) ∧ Function.Injective (mulMu c) ∧ Exact (mulMu c) (proj c) := by
  -- `ker thetaGeneric = (ξ)` and `μ = ξ τ` with `t = θ(τ)` a unit of `c.GenericRing`; so `mulMu`
  -- is, up to the unit `t`, the isomorphism `c.GenericRing ≅ (ξ) / (ξ²)`.
  obtain ⟨h_proj_surj, h_ker_eq⟩ := c.thickeningProj_surjective_and_ker_thetaGeneric
  obtain ⟨t, ht⟩ : IsUnit (c.genericStructureMap (theta tau)) :=
    (IsUnit.mk0 ((theta tau : OC) : ℂ_[p]) (by simp)).map c.genericStructureMap
  have h_mulMu_eq_iff (y : Localization.Away (p : WittVector p c.TiltRing)) (a : c.GenericRing) :
      mulMu c a = Ideal.Quotient.mk (ker c.thetaGeneric ^ 2) (algebraMap Ainf _ xi * y) ↔
        t * a = c.thetaGeneric y := by
    obtain ⟨b, rfl⟩ := h_proj_surj a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [mulMu_thickeningProj]
    change Ideal.Quotient.mk _ (algebraMap Ainf _ mu * x) = _ ↔ t * c.thetaGeneric x = _
    rw [Ideal.Quotient.eq, ht, ← thetaGeneric_algebraMap_ainf, ← map_mul]
    -- Both sides say `ξ ∣ τ x - y`, as `ker θ = (ξ)`.
    rw [← sub_mem_ker_iff, h_ker_eq, span_singleton_pow]
    -- Cancel the regular element `ξ` from `ξ² ∣ ξ (τ x - y)`.
    have h_cancel : algebraMap Ainf _ xi * algebraMap Ainf _ xi ∣
          algebraMap Ainf _ xi * (algebraMap Ainf _ tau * x - y) ↔
        algebraMap Ainf _ xi ∣ algebraMap Ainf _ tau * x - y :=
      (isLeftRegular_xi c).dvd_cancel_left
    simpa [← xi_mul_tau, mul_assoc, ← mul_sub, mem_span_singleton, sq, -isUnit_map_iff] using
      h_cancel
  have h_inj : Function.Injective (mulMu c) := by
    -- injectivity is the case `y = 0`; `using!` is needed since the class of `0` and the unit `t`
    -- match the ring `genericOver.obj c` only after unfolding.
    simpa [injective_iff_map_eq_zero'] using! h_mulMu_eq_iff 0
  refine ⟨h_proj_surj, h_inj, ?_⟩
  rintro ⟨x⟩
  refine ⟨fun hx ↦ ?_, ?_⟩
  · -- an element `ξ y` of the kernel is the image of `t⁻¹ θ(y)`
    obtain ⟨y, rfl⟩ : algebraMap Ainf (Localization.Away (p : WittVector p c.TiltRing)) xi ∣ x :=
      mem_span_singleton.mp (h_ker_eq.le hx)
    -- The witness `t⁻¹ * θ(y)` is left to unification: written out, its ring `c.GenericRing`
    -- does not match `genericOver.obj c`.
    exact ⟨_, (h_mulMu_eq_iff y _).mpr (t.mul_inv_cancel_left _)⟩
  · rintro ⟨a, ha⟩
    rw [← ha]
    exact proj_mulMu c a

/-- For a p-adic test with ring R, the multiplicative map x ↦ [x] from the tilt R^♭ to
B = W(R^♭)[1/p]/(ker θ)², the image of the Teichmüller lift. -/
def teichmullerLift : tilt c →* thickeningOver c :=
  (algebraMap (WittVector p c.TiltRing) c.Thickening).toMonoidHom.comp
    (@teichmuller p c.TiltRing ..)

end thickeningOver

end New.Variety

end GenericFibreTests

end
