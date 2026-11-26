import Lib.Cohomology.Etale.Basic
import Lib.PadicHodge.PeriodRings.Ainf

/-!
# Divided power ideal, p-adic test rings, tilt, Witt vectors and reduction modulo p

This file sets up basic objects of the p-adic and crystalline comparison, for a prime p.
O_C = `New.OC` is the ring of integers of ℂ_p, O♭ = `New.Period.OFlat` is its tilt, and
ξ = `New.Period.xi` generates ker θ in A_inf = W(O♭). The prime p is implicit in `New.Period.OFlat`
and `New.Period.xi`. The file defines the ideal 𝔡(S) of the x with n! ∣ x^n for all n, and
categories of p-complete p-torsion-free test rings. Finally, it collects the commutative algebra of
flatness, reduction modulo an element and Witt vectors that is used throughout the p-adic
comparison.

## Main definitions and results

* `New.Variety.pdIdeal`: the ideal 𝔡(S) of the x with n! ∣ x^n for all n.
  `New.Variety.pdIdeal_le_comap`: ring maps send 𝔡(B) into 𝔡(k).
* `New.Variety.IsCompleteTorsionFree` and `New.Variety.CrysTest`: p-torsion-free p-complete rings,
  and the category of such S-algebras. `New.Variety.CrysTest.restrictScalars` restricts scalars.
* `New.Variety.baseChangeMap`, `New.Variety.HasFlatBaseChange`: the map M ⊗ H^n(N, Φ) → H^n(N,
  M ⊗ Φ), and the statement that it is bijective for flat M.
* `New.Variety.IsCell`, `New.Variety.PadicTest`: cells, and p-adic tests, which are non-empty
  products S of cells with a map from O_C = `New.OC`.
* `New.Variety.PadicTest.tilt`, `New.Variety.algCompletion`, `New.Variety.wittFunctor`,
  `New.Variety.periodAlg`: tilt, p-adic completion, Witt vectors, and the completion of T ⊗ W(b)
  over A_inf.

Notions from other files:
* `New.Variety.Comparison`: A comparison from F on C to F' on C': a functor φ: C' → C with a natural
  transformation β: F∘φ → F'.

## Relation to the literature

Known; see `Lib.PadicComparison.Crystalline.ComparisonMap`, `Lib.PadicComparison.Completion`,
`Lib.PadicComparison.Descent.AlmostDescent` and `Lib.PadicComparison.HodgeTate.PeriodMap` for
sources.
-/

noncomputable section

namespace New.Variety

/-!
## The divided power ideal and p-complete p-torsion-free test rings

No divided power structure is chosen.
-/

section CrystallineTests

open CategoryTheory ObjectProperty Ideal Nat Finset Adic

variable {p : ℕ} [ThePrime p] (S : Type) [CommRing.{0} S]
  {B k : Type} [CommRing B] [CommRing k] (f : B →+* k)

/-- The ideal 𝔡(S) of the elements x of S such that n! divides x^n for every n. -/
def pdIdeal : Ideal S where
  carrier := {x : S | ∀ n : ℕ, ↑n ! ∣ x ^ n}
  add_mem' {x y : S} hx hy n := by
    rw [add_pow]
    refine dvd_sum fun j hj ↦ ?_
    -- Each term of the binomial expansion is divisible by `n ! = j ! * (n - j)! * n.choose j`.
    have h_fact : (n ! : S) = j ! * (n - j)! * n.choose j := by
      rw [← choose_mul_factorial_mul_factorial (mem_range_succ_iff.mp hj), cast_mul, cast_mul,
        mul_assoc, mul_comm]
    rw [h_fact]
    exact mul_dvd_mul_right (mul_dvd_mul (hx j) (hy (n - j))) _
  zero_mem' n := by cases n <;> simp
  smul_mem' (c : S) {x : S} hx n := by
    simpa [mul_pow] using dvd_mul_of_dvd_right (hx n) (c ^ n)

/-- A ring map `f : B → k` sends the ideal `pdIdeal B` of the `x` with `n! ∣ x ^ n` for all `n`
into `pdIdeal k`. -/
lemma pdIdeal_le_comap : pdIdeal B ≤ comap f (pdIdeal k) :=
  fun x hx n ↦ by simpa using map_dvd f (hx n)

/-- The quotient map S → S/𝔡(S), where 𝔡(S) = `New.Variety.pdIdeal` S is the ideal of the x with n!
dividing x^n for all n. -/
abbrev pdQuotientMk : S →+* S ⧸ pdIdeal S := Ideal.Quotient.mk (pdIdeal S)

/-- For a ring homomorphism f: B → k, the induced homomorphism B/𝔡(B) → k/𝔡(k), where 𝔡 is the ideal
`New.Variety.pdIdeal`. -/
abbrev pdQuotientMap : B ⧸ pdIdeal B →+* k ⧸ pdIdeal k :=
  quotientMap (pdIdeal k) f (pdIdeal_le_comap f)

/-- The ring S is p-torsion-free and p-adically complete. -/
structure IsCompleteTorsionFree [ThePrime p] where
  /-- `S` is `p`-torsion-free: multiplication by `p` is injective. -/
  regular : IsSMulRegular S p
  /-- `S` is `p`-adically complete. -/
  complete : IsAdicComplete (span {(p : S)}) S

/-- The full subcategory of commutative S-algebras that are p-torsion-free and p-adically
complete. -/
abbrev CrysTest : Type 1 := FullSubcategory fun A : CommAlg S ↦ IsCompleteTorsionFree A

/-- For a ring map r: k → B/𝔡(B), the functor A ↦ A/𝔡(A) from p-torsion-free p-complete B-algebras
to k-algebras, with 𝔡 the ideal `New.Variety.pdIdeal`. -/
def pdReduction (r : k →+* B ⧸ pdIdeal B) : CrysTest B ⥤ CommAlg k := by
  -- `A ⧸ pdIdeal A` is a `k`-algebra through `k → B ⧸ pdIdeal B → A ⧸ pdIdeal A`.
  let (A : CrysTest B) := ((pdQuotientMap (algebraMap B A.1)).comp r).toAlgebra
  refine
    { obj A := .of k (A.1.1 ⧸ pdIdeal A.1.1)
      map f :=
        ConcreteCategory.ofHom ⟨pdQuotientMap f.1.1.1, fun a ↦ by
          -- On a representative `b : B` of `r a` this says that `f` is a `B`-algebra map.
          change pdQuotientMap _ (pdQuotientMap _ (r a)) = pdQuotientMap _ (r a)
          obtain ⟨b⟩ := r a
          exact congrArg (pdQuotientMk _) (f.1.1.commutes' b)⟩
      map_id _ := ?_
      map_comp _ _ := ?_ }
  -- Both functor laws hold on representatives.
  all_goals
    ext ⟨⟩
    rfl

/-- Restriction of scalars along S → B, from p-torsion-free p-complete B-algebras to p-torsion-free
p-complete S-algebras. -/
def CrysTest.restrictScalars [Algebra S B] : CrysTest B ⥤ CrysTest S :=
  lift _ (ι _ ⋙ restrictAlg S B) fun A ↦ A.property

/-- If `p` is a non-zero-divisor on `B`, the `p`-adic completion `PrincipalCompletion B p` is
`p`-torsion-free and `p`-adically complete. -/
lemma isCompleteTorsionFree_completion (h_reg : IsSMulRegular B p) :
    IsCompleteTorsionFree (PrincipalCompletion B p) where
  regular := isSMulRegular_completion h_reg
  complete := isAdicComplete

end CrystallineTests

/-!
## The test category and coefficient functors

The test category and the coefficient functors of the p-adic comparison theorems. Cohomology
`New.Variety.H` N F n is an Ext group of functors C → Ab, and `New.Variety.moduleCoeff` makes a
functor to modules into coefficients.
-/

section PadicTests

open CategoryTheory Functor CommAlgCat TensorProduct Ideal AdicCompletion Period WittVector
  ModuleCat H

variable {C C' : Type 1} [Category C] [Category C'] {S : Type} [CommRing S] (p : ℕ) [ThePrime p]
  (T M : Type) [CommRing T] [Algebra S T] [AddCommGroup M] [Module S M] [Module T M]
  [IsScalarTower S T M] (m : M) (φ : C' ⥤ C) (N : AbFunctor C) (Φ : C ⥤ ModuleCat S)

/-! ### Tensor products of coefficients -/

/-- For a functor Φ to commutative S-algebras, the functor of underlying S-modules. -/
abbrev asModules (Φ : C ⥤ CommAlg S) : C ⥤ ModuleCat S :=
  Φ ⋙ forget₂ (CommAlg S) (AlgCat S) ⋙ forget₂ (AlgCat S) (ModuleCat S)

/-- For a module M over the S-algebra T, the functor X ↦ M ⊗_S X from S-modules to T-modules. -/
def tensorWith : ModuleCat.{0} S ⥤ ModuleCat T where
  obj X := ModuleCat.of T (M ⊗[S] X)
  map f := ModuleCat.ofHom (AlgebraTensorModule.lTensor T M f.hom)

instance : (tensorWith (S := S) T M).Additive where
  map_add {X Y : ModuleCat S} {f g : X ⟶ Y} :=
    Hom.ext (map_add (AlgebraTensorModule.lTensor T M) f.hom g.hom)

variable {M} in
/-- For m in M and a functor Φ to S-modules, the natural map of abelian-group-valued coefficient
functors Φ → M ⊗_S Φ sending x to m ⊗ x. -/
def tensorWith.mk : moduleCoeff Φ ⟶ moduleCoeff (Φ ⋙ tensorWith T M) :=
  whiskerRight {app A := AddCommGrpCat.ofHom (TensorProduct.mk S M (Φ A) m).toAddMonoidHom}
    AddCommGrpCat.uliftFunctor

variable {M} in
/-- The map `x ↦ m ⊗ x` is additive in `m`. -/
lemma tensorWith.mk_add (a b : M) :
    tensorWith.mk T (a + b) Φ = tensorWith.mk T a Φ + tensorWith.mk T b Φ := by
  ext
  exact ULift.down_injective (add_tmul ..)

variable {M} in
/-- Scalars from `S` pass through the tensor sign, where `End.asHom (CoeffAction.act s)` is
multiplication by `s` on the coefficient functor `moduleCoeff Φ`: `(s • m) ⊗ x = m ⊗ (s • x)`. -/
lemma tensorWith.mk_smul (s : S) :
    tensorWith.mk T (s • m) Φ = End.asHom (CoeffAction.act s) ≫ tensorWith.mk T m Φ := by
  ext
  exact ULift.down_injective (smul_tmul ..)

/-- The canonical T-linear map M ⊗_S H^n(N, Φ) → H^n(N, M ⊗_S Φ), sending m ⊗ z to the image of
z under x ↦ m ⊗ x. -/
def baseChangeMap (n : ℕ) :
    M ⊗[S] H N (moduleCoeff Φ) n →ₗ[T] H N (moduleCoeff (Φ ⋙ tensorWith T M)) n where
  toAddHom := AddMonoidHom.toAddHom <|
    liftAddHom
      ((pushHom N (moduleCoeff Φ) (moduleCoeff (Φ ⋙ tensorWith T M)) n).comp
        (AddMonoidHom.mk' (tensorWith.mk T · Φ) (tensorWith.mk_add T Φ)))
      fun (s : S) m x ↦ by
        change push N (tensorWith.mk T (s • m) Φ) n x = _
        rw [tensorWith.mk_smul, push_comp]
        rfl
  map_smul' t x := by
    induction x with
    | add x y hx hy => simp_all
    | tmul m x =>
      -- By `push_comp`, as `tensorWith.mk T (t • m) Φ` is `tensorWith.mk T m Φ` followed by `t`.
      exact .symm (push_comp ..).symm

/-- The abelian-group-valued functor N : `New.Variety.AbFunctor` C on C has flat base change: M ⊗_S
H^n(N, Φ) → H^n(N, M ⊗_S Φ) is bijective for all n, all functors Φ to S-modules and all S-flat M. -/
def HasFlatBaseChange : Prop :=
  ∀ (S T M : Type) [CommRing S] [CommRing T] [Algebra S T] [AddCommGroup M] [Module S M]
      [Module T M] [IsScalarTower S T M] [Module.Flat S M] (Φ : C ⥤ ModuleCat S) (n : ℕ),
    Function.Bijective (baseChangeMap T M N Φ n)

variable {Φ}

/-- For a natural map β: Φ → Ψ of functors to S-modules, the induced map of abelian-group-valued
coefficient functors. -/
def coeffMap {Ψ : C ⥤ ModuleCat S} (β : Φ ⟶ Ψ) : moduleCoeff Φ ⟶ moduleCoeff Ψ :=
  whiskerRight (whiskerRight β (forget₂ (ModuleCat S) Ab)) AddCommGrpCat.uliftFunctor

/-- The cohomological comparison datum along a functor φ: C' → C whose coefficient map comes
from a natural transformation Φ∘φ → Φ' of module-valued functors. -/
abbrev Comparison.ofModuleHom {Φ' : C' ⥤ ModuleCat S} (β : φ ⋙ Φ ⟶ Φ') :
    Comparison (moduleCoeff Φ) (moduleCoeff Φ') :=
  of (F := moduleCoeff Φ) φ (coeffMap β)

/-- The cohomological comparison datum along a functor φ: C' → C from an abelian-group-valued
functor N to N∘φ, with identity coefficient map. -/
abbrev Comparison.restrict : Comparison N (φ ⋙ N) := of φ (𝟙 (φ ⋙ N))

/-- Base change along S → T: the functor B ↦ T ⊗_S B from commutative S-algebras to commutative
T-algebras. -/
def algBaseChange : CommAlg S ⥤ CommAlg T where
  obj A := CommAlgCat.of T (T ⊗[S] A)
  map f := CommAlgCat.ofHom (Algebra.TensorProduct.lTensor T f.1)

/-- In a nontrivial ring that is `p`-adically complete, `p` is not a unit. -/
instance not_isUnit_p [Nontrivial S] [IsAdicComplete (span {(p : S)}) S] : Fact ¬IsUnit (p : S) :=
  -- if `p` is a unit, all its powers divide `0 - 1`, so `0 = 1` by separatedness
  ⟨fun h ↦ zero_ne_one (eq_of_forall_pow_dvd_sub (p : S) fun n ↦ (h.pow n).dvd)⟩

variable (S) [Algebra Ainf T]

/-! ### Cells and p-adic tests -/

/-- A cell: a p-adically complete, absolutely integrally closed valuation ring T (a domain) in which
p is not zero. By `New.Variety.not_isUnit_p`, p is then not a unit in T. -/
class IsCell extends IsDomain T, ValuationRing T, IsAdicComplete (span {(p : T)}) T,
  IsAbsIntegrallyClosed T where
  /-- `p` is not zero in `T`. -/
  p_ne_zero : (p : T) ≠ 0

/-- A p-adic test: a non-empty family of cells (`New.Variety.IsCell`) with a ring map from O_C to
their product. -/
structure PadicTest {p : ℕ} [ThePrime p] where
  /-- The index set of the product. -/
  Index : Type
  /-- The factors of the product, as types. -/
  Cell : Index → Type
  /-- There is at least one factor. -/
  [nonempty : Nonempty Index]
  /-- The ring structure of each factor. -/
  [commRing (i : Index) : CommRing (Cell i)]
  /-- Each factor is a cell. -/
  [isCell (i : Index) : IsCell p (Cell i)]
  /-- The structure map from O_C to the product of the factors. -/
  structureMap : OC →+* ∀ i : Index, Cell i

namespace PadicTest

variable {p} (c : PadicTest)

attribute [instance] nonempty commRing isCell

/-- The ring S underlying a p-adic test, namely the product of its family of valuation rings. -/
abbrev ProdRing : Type := ∀ i : c.Index, c.Cell i

instance : Algebra OC c.ProdRing := c.structureMap.toAlgebra

instance : Category PadicTest :=
  {Hom := (·.ProdRing →ₐ[OC] ·.ProdRing), id c := .id .., comp f := (·.comp f)}

instance : Nontrivial c.ProdRing := Pi.nontrivial_at c.nonempty.some

/-- The ring S of a p-adic test is p-adically complete, since each of its factors is. -/
instance isAdicComplete_prodRing : IsAdicComplete (span {(p : c.ProdRing)}) c.ProdRing := by
  -- Congruence modulo `p ^ n` in the product is congruence modulo `p ^ n` in each factor.
  have h_smodEq (x y : c.ProdRing) (n : ℕ) :
      x ≡ y [SMOD (span {(p : c.ProdRing)} ^ n • ⊤ : Ideal c.ProdRing)] ↔
        ∀ i : c.Index, x i ≡ y i [SMOD (span {(p : c.Cell i)} ^ n • ⊤ : Ideal (c.Cell i))] := by
    simp only [smodEq_span_pow_iff_dvd, pi_dvd_iff, Pi.pow_apply, Pi.natCast_apply, Pi.sub_apply]
  refine { haus' := fun x hx ↦ funext fun i ↦ ?_, prec' := fun f hf ↦ ?_ }
  · exact (c.isCell i).haus (x i) fun n ↦ (h_smodEq x 0 n).mp (hx n) i
  · have h_lim (i : c.Index) : ∃ L : c.Cell i, ∀ n : ℕ,
        f n i ≡ L [SMOD (span {(p : c.Cell i)} ^ n • ⊤ : Ideal (c.Cell i))] :=
      (c.isCell i).prec' (fun n ↦ f n i) fun {m n} h_le ↦ (h_smodEq (f m) (f n) m).mp (hf h_le) i
    choose L hL using h_lim
    exact ⟨L, fun n ↦ (h_smodEq (f n) L n).mpr fun i ↦ hL i n⟩

/-- The tilt S^♭ of the ring S of a p-adic test, the inverse limit of S/p along Frobenius. -/
abbrev TiltRing : Type := PreTilt c.ProdRing p

instance : Algebra OFlat c.TiltRing := (tiltMap c.structureMap).toAlgebra

/-- For g in the Galois group `New.Gp` p, which acts on O_C by ring automorphisms, the endofunctor
of p-adic tests that keeps the ring S and precomposes its structure map O_C → S with the action of
g. -/
def twist (g : Gp p) : PadicTest ⥤ PadicTest where
  obj c := ⟨c.Index, c.Cell, c.structureMap.comp (MulSemiringAction.toRingHom (Gp p) OC g)⟩
  map f := ⟨f.toRingHom, fun x ↦ f.commutes' (g • x)⟩

/-- The functor from p-adic tests to commutative O_C-algebras sending a test to its product ring
S with its structure map. -/
def algFunctor : PadicTest ⥤ CommAlg OC where
  obj c := CommAlgCat.of OC c.ProdRing
  map := CommAlgCat.ofHom

/-- The functor from p-adic tests to commutative rings sending a test to its underlying product
ring S. -/
abbrev ringFunctor : PadicTest ⥤ CommRingCat := algFunctor ⋙ forget₂ (CommAlg OC) CommRingCat

/-- The functor from p-adic tests to commutative O^♭-algebras sending a test S to its tilt S^♭. -/
def tilt : PadicTest ⥤ CommAlg OFlat where
  obj c := CommAlgCat.of OFlat c.TiltRing
  map {c c'} f :=
    CommAlgCat.ofHom ⟨tiltMap (RingHomClass.toRingHom (F := c.ProdRing →ₐ[OC] c'.ProdRing) f),
      fun a ↦ by
        have h_comp : f.toRingHom.comp c.structureMap = c'.structureMap := f.comp_algebraMap
        exact (tiltMap_comp c.structureMap _ a).symm.trans
          (congrArg (fun g ↦ tiltMap g a) h_comp)⟩
  map_id _ := CommAlgCat.hom_ext (AlgHom.ext fun a ↦ tiltMap_id a)
  map_comp _ _ := CommAlgCat.hom_ext (AlgHom.ext fun a ↦ tiltMap_comp _ _ a)

end PadicTest

open PadicTest Int

/-! ### Completion, Witt vectors and functors of points -/

/-- The functor sending a commutative S-algebra to its p-adic completion. -/
def algCompletion : CommAlg S ⥤ CommAlg S where
  obj A := CommAlgCat.of S (AdicCompletion (span {(p : A)}) A)
  map {A B} f :=
    CommAlgCat.ofHom ⟨adicMap (I := span {(p : A)}) (J := span {(p : B)}) f.hom.toRingHom
      (by simp), fun s ↦ ext_evalₐ (by simp [evalₐ_adicMap])⟩
  -- The functor laws are checked in each quotient by a power of `p`.
  map_id _ := by
    ext x : 2
    cases x using induction_on
    exact ext_evalₐ (by simp [evalₐ_adicMap])
  map_comp _ _ := by
    ext x : 2
    cases x using induction_on
    exact ext_evalₐ (by simp [evalₐ_adicMap])

variable {p S}

instance : IsCell p OC := ⟨NeZero.out⟩

instance : Algebra Ainf OFlat := constantCoeff.toAlgebra

instance : Algebra Ainf OC := (fontaineTheta ..).toAlgebra

/-- For a ring S with a map to W(k), by default S = W(k), the functor sending a k-algebra b to
its p-typical Witt vectors W(b), as an S-algebra. -/
def wittFunctor {k : Type} [CommRing k] (S : Type := WittVector p k) [CommRing S]
    [Algebra S (WittVector p k)] : CommAlg k ⥤ CommAlg S where
  -- `W(b)` is an `S`-algebra through `S → W(k) → W(b)`.
  obj b := @CommAlgCat.of S _ (WittVector p b) _
    ((WittVector.map (algebraMap k b)).comp (algebraMap S (WittVector p k))).toAlgebra
  map f := by
    use map f.hom
    exact fun s ↦ WittVector.ext fun n ↦ f.hom.commutes' _

/-- For an A_inf-algebra T, the functor sending an O^♭-algebra b to the p-adic completion of T
⊗_{A_inf} W(b). -/
abbrev periodAlg : CommAlg OFlat ⥤ CommAlg T :=
  wittFunctor (k := OFlat) ⋙ algBaseChange T ⋙ algCompletion T p

/-- For R → O_C, the functor sending an R-scheme X to the functor S ↦ X(S) of its points over R
in p-adic tests. -/
def testPoints {R : CommRingCat} [Algebra R OC] :
    Over (AlgebraicGeometry.Spec R) ⥤ PadicTest ⥤ Type 1 :=
  algPoints R R ⋙ restrictAlong (algFunctor ⋙ restrictAlg R OC)

/-- If S is absolutely integrally closed, then for every unit x of S there is a homomorphism χ from
ℚ to Sˣ with χ(1) = x, that is, a compatible system of roots of x. -/
lemma exists_compatible_roots {S : Type} [CommRing S] [h : IsAbsIntegrallyClosed S]
    (x : Additive Sˣ) : ∃ χ : ℚ →+ Additive Sˣ, χ 1 = x := by
  -- Units of `S` have `k`-th roots, so `Sˣ` is a divisible group, that is, an injective `ℤ`-module.
  have h_root {k : ℕ} (hk : k ≠ 0) (y : Additive Sˣ) : ∃ z : Additive Sˣ, k • z = y := by
    have : NeZero k := ⟨hk⟩
    obtain ⟨z, hz⟩ : ∃ z : S, z ^ k = (y.toMul : S) := IsAbsIntegrallyClosed.exists_pow_eq k _
    exact ⟨.ofMul (.ofPow _ z hk hz), Units.ext hz⟩
  let h_div_nat : DivisibleBy (Additive Sˣ) ℕ := divisibleByOfSMulRightSurj _ ℕ h_root
  let h_div_int : DivisibleBy (Additive Sˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  -- Extend `n ↦ n • x` from `ℤ` to `ℚ`.
  obtain ⟨χ, hχ⟩ : ∃ χ : ℚ →+ Additive Sˣ, χ.comp (Int.castAddHom ℚ) = zmultiplesHom _ x :=
    (Module.Baer.of_divisible _).extension_property_addMonoidHom _ Int.cast_injective _
  exact ⟨χ, by simpa using DFunLike.congr_fun hχ 1⟩

end PadicTests

/-!
## Flatness, reduction modulo an element and Witt vectors

* `New.Variety.pFlat`: the nonzero nonunit p♭ = ξ mod p of O♭. `New.Variety.IsPerfectTorsionFree` is
  the class of perfect, p♭-torsion-free O♭-algebras.
-/

section ReductionModP

open PrimeSpectrum CategoryTheory TensorProduct Period Ideal Function Module LinearMap WittVector
  Flat Ainf AlgebraTensorModule LocallyConstant Nat ZMod IsSMulRegular
  AlgebraicGeometry.StructureSheaf

variable (M S : Type _) {S' Λ : Type*} [CommRing M] [CommRing S] [CommRing S'] [Algebra M S]
  [AddCommGroup Λ] {f : S →+* S'} {p : ℕ} [ThePrime p]

/-! ### Locally constant functions on the prime spectrum -/

/-- For an M-algebra S there is a ring map f from the locally constant functions Spec S → M to S
such that, for every prime q, f(x) and x(q) have the same image in the localisation S_q. -/
lemma exists_ringHom_of_locallyConstant :
    ∃ f : LocallyConstant (PrimeSpectrum S) M →+* S,
      ∀ (x : LocallyConstant (PrimeSpectrum S) M) (q : PrimeSpectrum S),
      algebraMap S (Localization.AtPrime q.asIdeal) (f x) =
        algebraMap M (Localization.AtPrime q.asIdeal) (x q) := by
  -- A locally constant `x` gives the section `q ↦ x q` of the structure sheaf, and global sections
  -- come from `S`.
  have h_sec (x : LocallyConstant (PrimeSpectrum S) M) :
      ∃ s : S, ∀ q : PrimeSpectrum S, toPiLocalization S s q = algebraMap M _ (x q) := by
    obtain ⟨s, hs⟩ := toOpenₗ_top_bijective.surjective
      ⟨fun q ↦ algebraMap M (Localizations S q.val) (x q.val), fun q ↦ by
        -- On the open fibre `U` of `x` through `q` the section is the fraction `x q / 1`.
        let U : TopologicalSpace.Opens (PrimeSpectrum S) :=
          ⟨x ⁻¹' {x q.val}, x.isLocallyConstant {x q.val}⟩
        have hq : q.val ∈ U := rfl
        refine ⟨U, hq, homOfLE le_top, algebraMap M S (x q.val), 1, fun q' ↦
          ⟨(ne_top_iff_one _).mp q'.val.isPrime.ne_top, ?_⟩⟩
        have h_fibre : x q'.val = x q.val := q'.property
        rw [← h_fibre]
        rfl⟩
    exact ⟨s, fun q ↦ congrArg (fun σ ↦ σ.val ⟨q, trivial⟩) hs⟩
  choose toFun hf using h_sec
  -- Each ring map axiom is checked after the injective map `toPiLocalization S`, that is, in
  -- every localisation, where it holds by `hf`.
  refine ⟨{ toFun, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  all_goals simp [← (toPiLocalization_injective S).eq_iff, funext_iff, hf]

/-- Let f : S → S' be a ring map such that any two elements of S' become comparable for divisibility
after the partition given by f(e), for an idempotent e of S (`New.Variety.IsComparableRing`). Then
pull-back of locally constant Λ-valued functions from Spec S to Spec S' is onto. -/
lemma comapAddMonoidHom_surjective_of_isComparableRing (h_comparable : IsComparableRing f) :
    Surjective (comapAddMonoidHom (Z := Λ) ⟨PrimeSpectrum.comap f, continuous_comap f⟩) := by
  -- It suffices to hit the function equal to `a` on the locus of an idempotent `y`.
  refine locallyConstant_mem_of_indicator (S := AddMonoidHom.range _) fun a y hy ↦ ?_
  obtain ⟨e, he, h₁, h₂⟩ : ∃ e : S, IsIdempotentElem e ∧
      y ∣ f e * (1 - y) ∧ 1 - y ∣ (1 - f e) * y := h_comparable y (1 - y)
  -- Multiply `h₁` by `1 - y` and `h₂` by `y`: both `f e (1 - y)` and `(1 - f e) y` vanish.
  have h_fe_mul : f e * (1 - y) = 0 := by grind [dvd_def, IsIdempotentElem]
  have h_mul_y : (1 - f e) * y = 0 := by grind [dvd_def, IsIdempotentElem]
  obtain rfl : f e = y := by linear_combination h_fe_mul - h_mul_y
  exact ⟨indicator (LocallyConstant.const _ a) (isClopen_iff.2 ⟨e, he, rfl⟩), rfl⟩

/-- The functor sending a commutative ring S to the ℤ/p-algebra of locally constant functions Spec
S → ℤ/p. -/
def locConstAlg : CommRingCat ⥤ CommAlg (ZMod p) where
  obj A := CommAlgCat.of (ZMod p) (LocallyConstant (PrimeSpectrum A) (ZMod p))
  map f := CommAlgCat.ofHom (comapₐ (ZMod p) ⟨_, continuous_comap f.hom⟩)

instance : Algebra (ZMod p) OFlat := algebra ..

deriving instance Algebra (ZMod p), IsScalarTower (ZMod p) OFlat for @CFlat p _

/-- For every commutative ring A, the algebra of locally constant functions Spec A → ℤ/p
(`New.Variety.locConstAlg`) is perfect. -/
instance perfectRing_locConstAlg (A : CommRingCat) : PerfectRing (locConstAlg A) p := by
  -- Frobenius is the identity, by Fermat's little theorem at each point.
  have h_frob : (fun x : locConstAlg A ↦ x ^ p) = _root_.id :=
    funext fun x ↦ ext fun _ ↦ pow_card _
  exact ⟨by simpa only [h_frob] using bijective_id⟩

/-! ### The element p♭ -/

/-- The element p♭ = ξ mod p of O^♭ = A_inf/p, the zeroth Witt coefficient of ξ. -/
def pFlat : OFlat := constantCoeff xi

/-- The O^♭-algebra b is perfect and p♭-torsion-free, where p♭ = ξ mod p (`New.Variety.pFlat`). -/
abbrev IsPerfectTorsionFree (b : CommAlg OFlat) : Prop := PerfectRing b p ∧ IsSMulRegular b pFlat

/-! ### Reduction modulo an integer, flatness and torsion -/

/-- The map f: A → B is surjective, and f(x) = 0 exactly when x = m·y for some y. -/
def IsReductionMod {R A B : Type*} [SMul R A] [Zero B] (m : R) (f : A → B) : Prop :=
  Surjective f ∧ Exact (m • ·) f

/-- A reduction map modulo `m` (`New.Variety.IsReductionMod`) is onto. -/
lemma IsReductionMod.surjective {R A B : Type*} [SMul R A] [Zero B] {m : R} {g : A → B}
    (h_red : IsReductionMod m g) : Surjective g := h_red.left

/-- For a reduction map `g` modulo `m` (`New.Variety.IsReductionMod`), `g x = 0` exactly when
`x = m • y` for some `y`. -/
lemma IsReductionMod.exact {R A B : Type*} [SMul R A] [Zero B] {m : R} {g : A → B}
    (h_red : IsReductionMod m g) : Exact (m • ·) g := h_red.right

private lemma subsingleton_wittVector {q : ℕ} {R : Type*} [CommRing R] [Subsingleton R] :
    Subsingleton (WittVector q R) :=
  ⟨fun x y ↦ WittVector.ext fun n ↦ Subsingleton.elim (x.coeff n) (y.coeff n)⟩

/-- For a perfect algebra `S` over a domain `M` of characteristic `p`, the zeroth Witt coefficient
`W(S) → S` is reduction modulo `p` (`New.Variety.IsReductionMod`). -/
lemma isReductionMod_constantCoeff [IsDomain M] [CharP M p] [PerfectRing S p] :
    IsReductionMod p (constantCoeff : WittVector p S →+* S) := by
  refine ⟨constantCoeff_surjective p, ?_⟩
  cases subsingleton_or_nontrivial S
  · have : Subsingleton (WittVector p S) := subsingleton_wittVector
    simp [Exact, nontriviality]
  · -- Now `S` has characteristic `p`, and the kernel is the `x` with `x.coeff 0 = 0`.
    have : CharP S p := .of_ringHom_of_ne_zero (algebraMap M S) p NeZero.out
    simp [Exact, mul_comm, ← mem_span_singleton', mem_span_p_iff_coeff_zero_eq_zero]

/-- For a perfect algebra `S` over a domain `M` of characteristic `p`, the Witt vectors `W(S)` have
no `p`-torsion and are `p`-adically complete. -/
lemma isCompleteTorsionFree_wittVector [IsDomain M] [CharP M p] [PerfectRing S p] :
    IsCompleteTorsionFree (WittVector p S) := by
  cases subsingleton_or_nontrivial S
  · have : Subsingleton (WittVector p S) := subsingleton_wittVector
    exact ⟨.of_right_eq_zero_of_smul (by simp [nontriviality]), inferInstance⟩
  · have : CharP S p := .of_ringHom_of_ne_zero (algebraMap M S) p NeZero.out
    refine ⟨.of_right_eq_zero_of_smul ?_, inferInstance⟩
    simpa [mul_comm] using eq_zero_of_p_mul_eq_zero

/-- For a perfect algebra `S` over a domain `M` of characteristic `p`, the kernel of the zeroth
Witt coefficient `W(S) → S` is the ideal generated by `p`. -/
lemma ker_constantCoeff_eq_span_p [IsDomain M] [CharP M p] [PerfectRing S p] :
    RingHom.ker (constantCoeff : WittVector p S →+* S) = span {(p : WittVector p S)} := by
  -- The kernel consists of the multiples of `p`.
  ext x
  simpa [mem_span_singleton', mul_comm] using (isReductionMod_constantCoeff M S).exact x

/-- For a perfect algebra `S` over a domain `M` of characteristic `p`, a Witt vector is a multiple
of `p ^ k` exactly when its first `k` coefficients vanish. -/
lemma coeff_lt_eq_zero_iff_exists_p_pow_smul_eq [IsDomain M] [CharP M p] [PerfectRing S p]
    (k : ℕ) (x : WittVector p S) :
    (∀ i < k, x.coeff i = 0) ↔ ∃ y : WittVector p S, p ^ k • y = x := by
  cases subsingleton_or_nontrivial S
  · have : Subsingleton (WittVector p S) := subsingleton_wittVector
    simp [nontriviality]
  · have : CharP S p := .of_ringHom_of_ne_zero (algebraMap M S) p NeZero.out
    simp [mul_comm, ← mem_span_singleton', mem_span_p_pow_iff_le_coeff_eq_zero]

/-- Four facts on the Witt vectors `W(S)` of a perfect algebra `S` over a domain `M` of
characteristic `p`, bundled: `New.Variety.isReductionMod_constantCoeff`,
`New.Variety.isCompleteTorsionFree_wittVector`, `New.Variety.ker_constantCoeff_eq_span_p` and
`New.Variety.coeff_lt_eq_zero_iff_exists_p_pow_smul_eq`. -/
lemma isReductionMod_constantCoeff_and_isCompleteTorsionFree [IsDomain M] [CharP M p]
    [PerfectRing S p] :
    IsReductionMod p (constantCoeff : WittVector p S →+* S) ∧
    IsCompleteTorsionFree (WittVector p S) ∧
    RingHom.ker (constantCoeff : WittVector p S →+* S) = span {↑p} ∧
    ∀ (k : ℕ) (x : WittVector p S),
      (∀ i < k, x.coeff i = 0) ↔ ∃ y : WittVector p S, p ^ k • y = x :=
  ⟨isReductionMod_constantCoeff M S, isCompleteTorsionFree_wittVector M S,
    ker_constantCoeff_eq_span_p M S, coeff_lt_eq_zero_iff_exists_p_pow_smul_eq M S⟩

variable {S M M' L : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup M']
  [Module S M'] [AddCommGroup L] [Module S L] (f : M →ₗ[S] M') {m : ℕ}

/-- The element `p♭ = ξ mod p` of `O^♭` is nonzero, since `p` does not divide `ξ` in `A_inf`. -/
lemma pFlat_ne_zero : pFlat ≠ 0 := not_p_dvd_xi ∘ Witt.p_dvd_iff.mpr

/-- The element `p♭ = ξ mod p` of `O^♭` is not a unit, since `ξ` is prime in `A_inf` and a Witt
vector is a unit exactly when its zeroth coefficient is. -/
lemma not_isUnit_pFlat : ¬IsUnit pFlat := prime_xi.not_isUnit ∘ isUnit_iff_isUnit_constantCoeff.mpr

/-- Reduction modulo `m` is kept by tensoring on the left: if `f : M → M'` is reduction modulo `m`
(`New.Variety.IsReductionMod`: onto, with kernel `m M`), then so is `L ⊗ f`. -/
lemma IsReductionMod.lTensor (h_red : IsReductionMod m f) : IsReductionMod m (f.lTensor L) := by
  -- Tensoring is right exact, and `L ⊗ (m • –)` is multiplication by `m`.
  have h_exact : Exact ((m : End S M).lTensor L) (f.lTensor L) :=
    lTensor_exact L h_red.exact h_red.surjective
  have h_smul : (m : End S M).lTensor L = m := map_natCast (End.lTensorAlgHom S M L) m
  exact ⟨lTensor_surjective L h_red.surjective, by rwa [h_smul] at h_exact⟩

/-- If `f : M → M'` is reduction modulo `m` (`New.Variety.IsReductionMod`) and `m` kills `L`, then
`f ⊗ L` is bijective. -/
lemma IsReductionMod.bijective_rTensor (h_red : IsReductionMod m f) (h_kills : ∀ y : L, m • y = 0) :
    Bijective (f.rTensor L) := by
  -- The kernel is the image of `(m • –) ⊗ L`, which vanishes as `m` kills `L`.
  have h_exact : Exact ((m : End S M).rTensor L) (f.rTensor L) :=
    rTensor_exact L h_red.exact h_red.surjective
  have h_zero : (m : End S M).rTensor L = 0 := ext' fun x y ↦ by simp [smul_tmul, h_kills]
  exact ⟨(injective_iff_eq_zero_of_exact h_exact).mpr h_zero, rTensor_surjective L h_red.surjective⟩

/-- Two additive maps out of `M ⊗[S] L`, bundled in any type `F` of additive maps, are equal if
they agree on pure tensors. -/
lemma tmul_ext {P F : Type*} [AddCommGroup P] [FunLike F (M ⊗[S] L) P]
    [AddMonoidHomClass F (M ⊗[S] L) P] {f g : F}
    (h_tmul : ∀ (m : M) (x : L), f (m ⊗ₜ x) = g (m ⊗ₜ x)) : f = g := by
  refine DFunLike.ext f g fun y ↦ ?_
  induction y with
  | tmul m x => exact h_tmul m x
  | add y z hy hz => rw [map_add, map_add, hy, hz]

/-- Over a Bézout domain, a torsion-free module is flat. -/
instance [IsDomain S] [IsBezout S] [IsTorsionFree S L] : Flat S L := by
  rwa [flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]

/-- Let `S` be a domain and `π` an element such that every nonzero element of `S` divides some power
of `π`. Then an `S`-module without `π`-torsion is torsion-free. -/
lemma isTorsionFree_of_dvd_pow [IsDomain S] {π : S} (hπ_reg : IsSMulRegular L π)
    (h_dvd : ∀ {t : S}, t ≠ 0 → ∃ n : ℕ, t ∣ π ^ n) : IsTorsionFree S L := by
  -- A nonzero `t` divides some `π ^ n`, which is regular on `L`; so is every factor of it.
  refine ⟨fun t ht ↦ ?_⟩
  obtain ⟨n, s, hs⟩ := h_dvd ht.ne_zero
  have h_reg : IsSMulRegular L (s * t) := by simpa only [hs, mul_comm] using hπ_reg.pow n
  exact h_reg.of_mul

/-- Let O = S/m and M' = M/m (`New.Variety.IsReductionMod`), with M' flat over O. If the S-modules M
and L have no m-torsion, then L ⊗_S M has no m-torsion either. -/
lemma isSMulRegular_tensor_of_flat_mod {O : Type} [CommRing O] [Algebra S O] [Module O M']
    [IsScalarTower S O M'] [Flat O M'] (hO_red : IsReductionMod m (Algebra.linearMap S O))
    (hf_red : IsReductionMod m f) (hM_reg : IsSMulRegular M m) (hL_reg : IsSMulRegular L m) :
    IsSMulRegular (L ⊗[S] M) m := by
  -- Present `L` as a quotient `π` of a free module, with `ι` the inclusion of its kernel. The lemma
  -- `lTensor_injective_of_exact_of_exact_of_rTensor_injective` is the balancing of `Tor₁`:
  -- it is used to get `Tor₁(O, L) = 0`, and then to pass from `Tor₁(L, M') = 0` to the claim.
  obtain ⟨hO_surj, hO_exact⟩ := hO_red
  obtain ⟨hf_surj, hf_exact⟩ := hf_red
  simp only [← cast_smul_eq_nsmul S, IsSMulRegular] at hO_exact hf_exact hM_reg hL_reg ⊢
  let π : (L →₀ S) →ₗ[S] L := Finsupp.linearCombination S _root_.id
  let ι : LinearMap.ker π →ₗ[S] L →₀ S := (LinearMap.ker π).subtype
  have hπ : Surjective π := Finsupp.linearCombination_id_surjective S L
  have h_exact : Exact ι π := exact_subtype_ker_map π
  -- `O = S / m` and `L` has no `m`-torsion.
  have hO_inj : Function.Injective (ι.lTensor O) :=
    lTensor_injective_of_exact_of_exact_of_rTensor_injective (f₁ := .mul S S m) hO_exact hO_surj
      h_exact hπ (IsSMulRegular.lTensor _ hL_reg) (by simp [ι])
  -- `M' ⊗ – = M' ⊗[O] (O ⊗ –)` by `cancelBaseChange`, and `M'` is flat over `O`.
  have hM'_inj : Function.Injective (ι.lTensor M') := by
    have h_comp : Function.Injective
        ((cancelBaseChange S O O M' _).toLinearMap ∘ₗ lTensor O M' (lTensor O O ι)) :=
      (cancelBaseChange S O O M' _).injective.comp
        (lTensor_preserves_injective_linearMap (ι.baseChange O) hO_inj)
    rwa [← lTensor_comp_cancelBaseChange, coe_comp, LinearEquiv.coe_coe,
      EquivLike.injective_comp] at h_comp
  -- `M' = M / m`, `M` has no `m`-torsion, and free modules are flat.
  have h_smul_inj : Function.Injective ((DistribSMul.toLinearMap S M (m : S)).lTensor L) :=
    lTensor_injective_of_exact_of_exact_of_rTensor_injective h_exact hπ hf_exact hf_surj
      ((lTensor_inj_iff_rTensor_inj M' ι).mp hM'_inj)
      (lTensor_preserves_injective_linearMap _ hM_reg)
  rwa [lTensor_smul_action] at h_smul_inj

end ReductionModP

end New.Variety

end
