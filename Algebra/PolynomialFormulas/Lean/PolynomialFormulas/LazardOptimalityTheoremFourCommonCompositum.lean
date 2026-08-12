import PolynomialFormulas.LazardOptimalityTheoremFourF20Tower
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# The actual common-compositum path in Lazard's Theorem 4

This file puts the fixed-field tower for a solvable irreducible rational
quintic and a primitive fifth root of unity in one concrete ambient field:
the splitting field of the product of the quintic and `cyclotomic 5 ℚ`.

There are three field-theoretic points which are kept explicit.

* An exact square-root tower maps along the splitting-field embedding.
* A degree-five Galois extension stays degree five after a base change of
  relative degree at most four.  The proof uses coprime-degree linear
  disjointness; it does not assume this noncollapse.
* An arbitrary primitive fifth root in the common field is reconstructed
  from the two square radicals
  `s = 1 + 2 * (z + z^4)` and `t = 4*z + 1 - s`.

The first unconditional theorem gives a literal presentation by `2 + e`
displayed square adjunctions and one fifth-root adjunction, where `e ≤ 2` is
the exponent of the original rational F20 tower.  The exact-count refinement
then deletes the square steps which collapse after adjoining the fifth root
of unity.  Its resulting `eOmega ≤ e` is Lazard's post-base-change exponent:
the relative Galois group has order `5 * 2^eOmega`, the common compositum has
degree `5 * 2^(2+eOmega)`, and the radical presentation uses exactly
`2 + eOmega` displayed square steps followed by one fifth-root step.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardOptimalityTheoremFourCommonCompositum

open IntermediateField
open LeanProofs.PolynomialFormulas
open LazardOptimality
open LazardOptimalityTheoremFourDegree
open LazardOptimalityTheoremFourF20Tower

set_option autoImplicit false

noncomputable section

/-- Primitivity is unchanged when an ambient element is packaged with a
membership proof in an intermediate field. -/
theorem isPrimitiveRoot_mk_mem
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) {z : E} {n : ℕ}
    (hzK : z ∈ K) (hz : IsPrimitiveRoot z n) :
    IsPrimitiveRoot (⟨z, hzK⟩ : K) n := by
  have hmap : IsPrimitiveRoot (K.val (⟨z, hzK⟩ : K)) n := by
    simpa using hz
  exact hmap.of_map_of_injective K.val.injective

section GenericBaseChange

variable {F Ω Ω' : Type*}
variable [Field F] [Field Ω] [Field Ω'] [Algebra F Ω] [Algebra F Ω']

/-- The image of an intermediate field is contained in the field range of
the ambient embedding. -/
theorem map_le_fieldRange
    (K : IntermediateField F Ω) (f : Ω →ₐ[F] Ω') :
    K.map f ≤ f.fieldRange := by
  rw [AlgHom.fieldRange_eq_map]
  exact IntermediateField.map_mono f le_top

/-- Galois structure transports from `Ω/K` to the image of `Ω` over the
image of `K`.  Both the base and the top field are transported; this is why
the simultaneous-base equivalence theorem, rather than a same-base shortcut,
is used. -/
theorem mapped_top_isGalois
    (K : IntermediateField F Ω) (f : Ω →ₐ[F] Ω')
    [IsGalois K Ω] :
    IsGalois (K.map f)
      (IntermediateField.extendScalars (map_le_fieldRange K f)) := by
  let hKrange : K.map f ≤ f.fieldRange := map_le_fieldRange K f
  letI : Algebra (K.map f) f.fieldRange :=
    (IntermediateField.inclusion hKrange).toRingHom.toAlgebra
  let baseEquiv : K ≃+* K.map f :=
    (IntermediateField.equivMap K f).toRingEquiv
  let topEquiv : Ω ≃+* f.fieldRange := f.equivFieldRange.toRingEquiv
  apply IsGalois.of_equiv_equiv
    (f := baseEquiv) (g := topEquiv)
  ext x
  rfl

/-- The corresponding relative degree is unchanged by the simultaneous
base/top transport. -/
theorem mapped_top_finrank
    (K : IntermediateField F Ω) (f : Ω →ₐ[F] Ω') :
    Module.finrank (K.map f)
        (IntermediateField.extendScalars (map_le_fieldRange K f)) =
      Module.finrank K Ω := by
  let hKrange : K.map f ≤ f.fieldRange := map_le_fieldRange K f
  letI : Algebra (K.map f) f.fieldRange :=
    (IntermediateField.inclusion hKrange).toRingHom.toAlgebra
  let baseEquiv : K ≃+* K.map f :=
    (IntermediateField.equivMap K f).toRingEquiv
  let topEquiv : Ω ≃+* f.fieldRange := f.equivFieldRange.toRingEquiv
  symm
  apply Algebra.finrank_eq_of_equiv_equiv baseEquiv topEquiv
  ext x
  rfl

/-- Adjoining an absolute field `W/F` to a field `K/F` has relative degree
over `K` at most `[W:F]`. -/
theorem finrank_extendScalars_sup_le_right
    [FiniteDimensional F Ω]
    (K W : IntermediateField F Ω) :
    Module.finrank K
        (IntermediateField.extendScalars
          (le_sup_left : K ≤ K ⊔ W)) ≤
      Module.finrank F W := by
  let M : IntermediateField F Ω := K ⊔ W
  let hKM : K ≤ M := le_sup_left
  let E : IntermediateField K Ω := IntermediateField.extendScalars hKM
  have htower := Module.finrank_mul_finrank F K E
  change Module.finrank F K * Module.finrank K E =
    Module.finrank F M at htower
  have hsup : Module.finrank F M ≤
      Module.finrank F K * Module.finrank F W := by
    simpa only [M] using
      (IntermediateField.finrank_sup_le (E1 := K) (E2 := W))
  have hmul : Module.finrank F K * Module.finrank K E ≤
      Module.finrank F K * Module.finrank F W := by
    rw [htower]
    exact hsup
  exact Nat.le_of_mul_le_mul_left hmul Module.finrank_pos

/-- Base change of a finite Galois extension inside a fixed ambient field:
if `K/F` is Galois, then the compositum `K W/W` is Galois.  This packages the
restriction-to-the-compositum transport which is implicit in the usual
paper proof. -/
theorem isGalois_extendScalars_sup_right
    [FiniteDimensional F Ω]
    (K W : IntermediateField F Ω) (hgalois : IsGalois F K) :
    IsGalois W
      (IntermediateField.extendScalars
        (le_sup_right : W ≤ K ⊔ W)) := by
  letI : IsGalois F K := hgalois
  let C : IntermediateField F Ω := K ⊔ W
  let hKC : K ≤ C := le_sup_left
  let hWC : W ≤ C := le_sup_right
  let A : IntermediateField F C := K.restrict hKC
  let B : IntermediateField F C := W.restrict hWC
  have htop : A ⊔ B = ⊤ := by
    rw [← IntermediateField.lift_inj,
      IntermediateField.lift_top, IntermediateField.lift_sup,
      IntermediateField.lift_restrict hKC,
      IntermediateField.lift_restrict hWC]
  letI : IsGalois F A :=
    IsGalois.of_algEquiv (IntermediateField.restrict_algEquiv hKC)
  have hgaloisBC : IsGalois B C :=
    IsGalois.sup_right A B htop
  let hWtop : W ≤ K ⊔ W := le_sup_right
  let E : IntermediateField W Ω :=
    IntermediateField.extendScalars hWtop
  let baseEquiv : B ≃+* W :=
    (IntermediateField.restrict_algEquiv hWC).symm.toRingEquiv
  let topEquiv : C ≃+* E :=
    { toFun := fun x => ⟨x, x.property⟩
      invFun := fun x => ⟨x, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  have hcomp :
      (algebraMap W E).comp baseEquiv.toRingHom =
        topEquiv.toRingHom.comp (algebraMap B C) := by
    ext x
    change ((baseEquiv x : W) : Ω) = ((x : C) : Ω)
    exact congrArg (fun y : B => ((y : C) : Ω))
      ((IntermediateField.restrict_algEquiv hWC).apply_symm_apply x)
  letI : IsGalois B C := hgaloisBC
  simpa only [E, hWtop] using
    (IsGalois.of_equiv_equiv
      (f := baseEquiv) (g := topEquiv) hcomp)

/-- Transport Galois structure and an exact relative degree simultaneously
along compatible equivalences of both the base and top fields.  Keeping this
as one lemma avoids repeating the same pair of transports at every
compositum boundary. -/
theorem isGalois_and_finrank_eq_of_equiv_equiv
    {K L K' L' : Type*}
    [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K' L']
    (baseEquiv : K ≃+* K') (topEquiv : L ≃+* L')
    (hcomp :
      (algebraMap K' L').comp baseEquiv.toRingHom =
        topEquiv.toRingHom.comp (algebraMap K L))
    [IsGalois K L] {n : ℕ} (hdegree : Module.finrank K L = n) :
    IsGalois K' L' ∧ Module.finrank K' L' = n := by
  exact ⟨IsGalois.of_equiv_equiv
      (f := baseEquiv) (g := topEquiv) hcomp,
    (Algebra.finrank_eq_of_equiv_equiv
      baseEquiv topEquiv hcomp).symm.trans hdegree⟩

/-- A degree-five Galois extension cannot collapse after a base change of
relative degree at most four.

Writing the original extension and the base-change field as intermediate
fields over `K`, their degrees are coprime, hence they are linearly disjoint.
Inside their compositum, `IsGalois.sup_right` supplies normality and
separability and `LinearDisjoint.finrank_right_eq_finrank` supplies the exact
relative degree.  The last step transports both base and top back to the
original `F`-intermediate-field presentation. -/
theorem galois_degree_five_sup_of_finrank_le_four
    [FiniteDimensional F Ω]
    {K S M : IntermediateField F Ω}
    (hKS : K ≤ S) (hKM : K ≤ M)
    (hfinite : FiniteDimensional K
      (IntermediateField.extendScalars hKS))
    (hgalois : IsGalois K (IntermediateField.extendScalars hKS))
    (hdegree : Module.finrank K
      (IntermediateField.extendScalars hKS) = 5)
    (hbase : Module.finrank K
      (IntermediateField.extendScalars hKM) ≤ 4) :
    IsGalois M
        (IntermediateField.extendScalars
          (le_sup_right : M ≤ S ⊔ M)) ∧
      Module.finrank M
        (IntermediateField.extendScalars
          (le_sup_right : M ≤ S ⊔ M)) = 5 := by
  let SK : IntermediateField K Ω :=
    IntermediateField.extendScalars hKS
  let MK : IntermediateField K Ω :=
    IntermediateField.extendScalars hKM
  letI : FiniteDimensional K SK := hfinite
  letI : IsGalois K SK := hgalois
  have hSKdegree : Module.finrank K SK = 5 := by
    simpa only [SK] using hdegree
  have hMKle : Module.finrank K MK ≤ 4 := by
    simpa only [MK] using hbase
  have hMKpos : 0 < Module.finrank K MK := Module.finrank_pos
  have hcoprime :
      (Module.finrank K SK).Coprime (Module.finrank K MK) := by
    rw [hSKdegree]
    let m := Module.finrank K MK
    change m ≤ 4 at hMKle
    change 0 < m at hMKpos
    change Nat.Coprime 5 m
    have hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases hm with hm | hm | hm | hm <;> norm_num [hm]
  have hlinear : SK.LinearDisjoint MK :=
    IntermediateField.LinearDisjoint.of_finrank_coprime hcoprime

  let C : IntermediateField K Ω := SK ⊔ MK
  let hSKC : SK ≤ C := le_sup_left
  let hMKC : MK ≤ C := le_sup_right
  let A : IntermediateField K C := SK.restrict hSKC
  let B : IntermediateField K C := MK.restrict hMKC
  have htop : A ⊔ B = ⊤ := by
    rw [← IntermediateField.lift_inj,
      IntermediateField.lift_top, IntermediateField.lift_sup,
      IntermediateField.lift_restrict hSKC,
      IntermediateField.lift_restrict hMKC]
  have hAdegree : Module.finrank K A = 5 := by
    calc
      Module.finrank K A = Module.finrank K SK :=
        (IntermediateField.restrict_algEquiv hSKC).toLinearEquiv.finrank_eq.symm
      _ = 5 := hSKdegree
  have hBdegree : Module.finrank K B = Module.finrank K MK := by
    exact
      (IntermediateField.restrict_algEquiv hMKC).toLinearEquiv.finrank_eq.symm
  have hABcoprime :
      (Module.finrank K A).Coprime (Module.finrank K B) := by
    simpa only [hAdegree, hBdegree, hSKdegree] using hcoprime
  have hABlinear : A.LinearDisjoint B :=
    IntermediateField.LinearDisjoint.of_finrank_coprime hABcoprime
  have hdegreeBC : Module.finrank B C = 5 := by
    calc
      Module.finrank B C = Module.finrank K A :=
        hABlinear.finrank_right_eq_finrank htop
      _ = 5 := hAdegree
  letI : IsGalois K A :=
    IsGalois.of_algEquiv (IntermediateField.restrict_algEquiv hSKC)
  have hgaloisBC : IsGalois B C :=
    IsGalois.sup_right A B htop

  let N : IntermediateField F Ω := S ⊔ M
  let hMN : M ≤ N := le_sup_right
  let E : IntermediateField M Ω :=
    IntermediateField.extendScalars hMN
  have hCrestrict : C.restrictScalars F = N := by
    change (SK ⊔ MK).restrictScalars F = S ⊔ M
    rw [← IntermediateField.restrictScalars_sup]
    rfl
  let baseEquiv : B ≃+* M :=
    (IntermediateField.restrict_algEquiv hMKC).symm.toRingEquiv
  let topEquiv : C ≃+* E :=
    (IntermediateField.equivOfEq hCrestrict).toRingEquiv
  have hcomp :
      (algebraMap M E).comp baseEquiv.toRingHom =
        topEquiv.toRingHom.comp (algebraMap B C) := by
    ext x
    change ((baseEquiv x : M) : Ω) = ((x : C) : Ω)
    exact congrArg (fun y : B => ((y : C) : Ω))
      ((IntermediateField.restrict_algEquiv hMKC).apply_symm_apply x)
  letI : IsGalois B C := hgaloisBC
  exact isGalois_and_finrank_eq_of_equiv_equiv
    baseEquiv topEquiv hcomp hdegreeBC

end GenericBaseChange

section PrimitiveFifthRoot

variable {E : Type*} [Field E] [CharZero E]

/-- Every primitive fifth root itself constructs the classical two-square
cyclotomic tower.  This is the reverse direction from the concrete complex
formula: `z` is the input and the square radicals are recovered from it. -/
theorem exists_two_square_tower_containing_primitive_fifth_root
    {z : E} (hz : IsPrimitiveRoot z 5) :
    ∃ (s t : E) (W : IntermediateField ℚ E),
      s = 1 + 2 * (z + z ^ 4) ∧
      t = 4 * z + 1 - s ∧
      IsSquareRadicalTower ℚ E
        (⊥ : IntermediateField ℚ E) 2 W ∧
      z ∈ W ∧ W = ℚ⟮z⟯ ∧ Module.finrank ℚ W = 4 := by
  let s : E := 1 + 2 * (z + z ^ 4)
  let t : E := 4 * z + 1 - s
  have hzcyclotomic : z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0 := by
    have hmul :
        (z - 1) * (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) = 0 := by
      calc
        (z - 1) * (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) =
            z ^ 5 - 1 := by ring
        _ = 0 := by rw [hz.pow_eq_one]; ring
    exact (mul_eq_zero.mp hmul).resolve_left
      (sub_ne_zero.mpr (hz.ne_one (by norm_num)))
  have hsquare : s ^ 2 = 5 := by
    apply sub_eq_zero.mp
    calc
      s ^ 2 - 5 =
          (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) *
            (-4 + 8 * z - 4 * z ^ 3 + 4 * z ^ 4) := by
        dsimp only [s]
        ring
      _ = 0 := by rw [hzcyclotomic, zero_mul]
  have tsquare : t ^ 2 = -10 - 2 * s := by
    apply sub_eq_zero.mp
    calc
      t ^ 2 - (-10 - 2 * s) =
          (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) *
            (12 - 8 * z - 4 * z ^ 3 + 4 * z ^ 4) := by
        dsimp only [s, t]
        ring
      _ = 0 := by rw [hzcyclotomic, zero_mul]
  let B1 : IntermediateField ℚ E :=
    (⊥ : IntermediateField ℚ E) ⊔ ℚ⟮s⟯
  let W : IntermediateField ℚ E := B1 ⊔ ℚ⟮t⟯
  have hsquareMem : s ^ 2 ∈ (⊥ : IntermediateField ℚ E) := by
    rw [hsquare]
    exact IntermediateField.natCast_mem _ 5
  have tsquareMem : t ^ 2 ∈ B1 := by
    rw [tsquare]
    exact sub_mem (neg_mem (IntermediateField.natCast_mem B1 10))
      (mul_mem (IntermediateField.natCast_mem B1 2)
        ((show ℚ⟮s⟯ ≤ B1 from le_sup_right)
          (IntermediateField.mem_adjoin_simple_self ℚ s)))
  have htower : IsSquareRadicalTower ℚ E
      (⊥ : IntermediateField ℚ E) 2 W := by
    have hzero : IsSquareRadicalTower ℚ E
        (⊥ : IntermediateField ℚ E) 0 ⊥ :=
      IsSquareRadicalTower.zero
    have hone := IsSquareRadicalTower.succ hzero s hsquareMem
    have htwo := IsSquareRadicalTower.succ hone t tsquareMem
    simpa only [B1, W] using htwo
  have hzreconstruct : (-1 + s + t) * (4 : E)⁻¹ = z := by
    dsimp only [t]
    field_simp
    ring
  have hsW : s ∈ W :=
    (show B1 ≤ W from le_sup_left)
      ((show ℚ⟮s⟯ ≤ B1 from le_sup_right)
        (IntermediateField.mem_adjoin_simple_self ℚ s))
  have htW : t ∈ W :=
    (show ℚ⟮t⟯ ≤ W from le_sup_right)
      (IntermediateField.mem_adjoin_simple_self ℚ t)
  have hzW : z ∈ W := by
    rw [← hzreconstruct]
    exact mul_mem (add_mem (add_mem (neg_mem (one_mem W)) hsW) htW)
      (inv_mem (IntermediateField.natCast_mem W 4))
  let Z : IntermediateField ℚ E := ℚ⟮z⟯
  have hzZ : z ∈ Z :=
    IntermediateField.mem_adjoin_simple_self ℚ z
  have hsZ : s ∈ Z := by
    dsimp only [s]
    exact add_mem (one_mem Z)
      (mul_mem (IntermediateField.natCast_mem Z 2)
        (add_mem hzZ (pow_mem hzZ 4)))
  have htZ : t ∈ Z := by
    dsimp only [t]
    exact sub_mem
      (add_mem (mul_mem (IntermediateField.natCast_mem Z 4) hzZ)
        (one_mem Z)) hsZ
  have hB1leZ : B1 ≤ Z := by
    dsimp only [B1]
    exact sup_le bot_le
      (IntermediateField.adjoin_simple_le_iff.mpr hsZ)
  have hWleZ : W ≤ Z := by
    dsimp only [W]
    exact sup_le hB1leZ
      (IntermediateField.adjoin_simple_le_iff.mpr htZ)
  have hZleW : Z ≤ W :=
    IntermediateField.adjoin_simple_le_iff.mpr hzW
  have hW_eq_Z : W = Z := le_antisymm hWleZ hZleW
  have hzIntegral : IsIntegral ℚ z := by
    refine ⟨X ^ 5 - 1, monic_X_pow_sub_C 1 (by norm_num), ?_⟩
    simp [hz.pow_eq_one]
  have hminpolyAmbient : cyclotomic 5 ℚ = minpoly ℚ z :=
    cyclotomic_eq_minpoly_rat hz (by norm_num)
  have hZdegree : Module.finrank ℚ Z = 4 := by
    dsimp only [Z]
    rw [IntermediateField.adjoin.finrank hzIntegral, ← hminpolyAmbient,
      natDegree_cyclotomic, Nat.totient_prime Nat.prime_five]
  have hWdegree : Module.finrank ℚ W = 4 := by
    rw [hW_eq_Z, hZdegree]
  exact ⟨s, t, W, rfl, rfl, htower, hzW, hW_eq_Z, hWdegree⟩

end PrimitiveFifthRoot

/-! ## The concrete rational-quintic endpoint -/

/-- The common ambient field used for the actual theorem-four construction. -/
abbrev QuinticFifthCyclotomicSplittingField (p : ℚ[X]) : Type :=
  (p * cyclotomic 5 ℚ).SplittingField

/-- For every solvable irreducible rational quintic, the actual fixed-field
F20 tower and an actual primitive fifth root are combined in the splitting
field of `p * cyclotomic 5`.  The terminal fifth-root generator is obtained
from Kummer theory only after the degree-five noncollapse has been proved.

The returned `2 + e` presentation preserves the two displayed cyclotomic
square roots and all `e` square roots from the original F20 tower.  It makes
no claim that all of these displayed steps remain nontrivial after base
change.  The cyclotomic endpoint is also identified with `ℚ⟮z⟯` and its
degree four is returned for later refinements. -/
theorem exists_solvable_F20_commonCompositum_presentation
    (p : ℚ[X]) (hp : Irreducible p) (hdegree : p.natDegree = 5)
    (hsolvable : IsSolvable p.Gal) :
    ∃ (e : ℕ) (P : Subgroup Gal(p.SplittingField/ℚ))
        (f : p.SplittingField →ₐ[ℚ]
          QuinticFifthCyclotomicSplittingField p)
        (z : QuinticFifthCyclotomicSplittingField p)
        (W : IntermediateField ℚ
          (QuinticFifthCyclotomicSplittingField p)),
      e ≤ 2 ∧ Nat.card p.Gal = 5 * 2 ^ e ∧
      Nat.card P = 5 ∧ P.Normal ∧
      IsPrimitiveRoot z 5 ∧
      IsSquareRadicalTower ℚ (QuinticFifthCyclotomicSplittingField p)
        (⊥ : IntermediateField ℚ
          (QuinticFifthCyclotomicSplittingField p)) 2 W ∧
      z ∈ W ∧
      W = ℚ⟮z⟯ ∧
      Module.finrank ℚ W = 4 ∧
      IsSquareRadicalTower ℚ (QuinticFifthCyclotomicSplittingField p)
        (⊥ : IntermediateField ℚ
          (QuinticFifthCyclotomicSplittingField p)) e
        ((IntermediateField.fixedField P).map f) ∧
      IsDefinedBySquareRootsAndFifthRoot ℚ
        (QuinticFifthCyclotomicSplittingField p)
        (⊥ : IntermediateField ℚ
          (QuinticFifthCyclotomicSplittingField p))
        (f.fieldRange ⊔
          (((IntermediateField.fixedField P).map f) ⊔ W)) (2 + e) := by
  let E := QuinticFifthCyclotomicSplittingField p
  let productPolynomial : ℚ[X] := p * cyclotomic 5 ℚ
  have hproduct : productPolynomial ≠ 0 :=
    mul_ne_zero hp.ne_zero (cyclotomic_ne_zero 5 ℚ)
  letI : productPolynomial.IsSplittingField ℚ E := by
    exact Polynomial.IsSplittingField.splittingField productPolynomial
  letI : FiniteDimensional ℚ E :=
    Polynomial.IsSplittingField.finiteDimensional E productPolynomial

  have hpSplits : (p.map (algebraMap ℚ E)).Splits := by
    exact (SplittingField.splits productPolynomial).of_dvd
      (map_ne_zero hproduct)
      ((map_dvd_map' _).mpr
        (show p ∣ productPolynomial from
          dvd_mul_right p (cyclotomic 5 ℚ)))
  letI : Fact ((p.map (algebraMap ℚ E)).Splits) := ⟨hpSplits⟩
  let f : p.SplittingField →ₐ[ℚ] E :=
    IsScalarTower.toAlgHom ℚ p.SplittingField E

  obtain ⟨e, P, he, hGalCard, hPcard, hPnormal, hfixedTower,
      hfixedFinite, hfixedGalois, hfixedDegree⟩ :=
    exists_fixedField_indexTwoTower_of_isSolvable
      p hp hdegree hsolvable
  have hmappedFixedTower :
      IsSquareRadicalTower ℚ E (⊥ : IntermediateField ℚ E) e
        ((IntermediateField.fixedField P).map f) := by
    have hsquare :=
      IsIndexTwoGaloisTower.isSquareRadicalTower ℚ p.SplittingField
        hfixedTower
    have hmapped := IsSquareRadicalTower.map ℚ p.SplittingField hsquare f
    simpa only [IntermediateField.map_bot] using hmapped

  have hcyclotomicSplits :
      ((cyclotomic 5 ℚ).map (algebraMap ℚ E)).Splits := by
    exact (SplittingField.splits productPolynomial).of_dvd
      (map_ne_zero hproduct)
      ((map_dvd_map' _).mpr
        (show cyclotomic 5 ℚ ∣ productPolynomial from
          dvd_mul_left (cyclotomic 5 ℚ) p))
  obtain ⟨z, hz⟩ :=
    hcyclotomicSplits.exists_eval_eq_zero (by
      rw [degree_map]
      exact degree_ne_of_natDegree_ne (by
        rw [natDegree_cyclotomic]
        norm_num))
  have hzRoot : (cyclotomic 5 E).IsRoot z := by
    rw [IsRoot.def, ← map_cyclotomic 5 (algebraMap ℚ E)]
    exact hz
  have hzPrimitive : IsPrimitiveRoot z 5 :=
    (isRoot_cyclotomic_iff).mp hzRoot
  obtain ⟨s, t, W, hs, ht, hcyclotomicTower, hzW, hW_eq, hWdegree⟩ :=
    exists_two_square_tower_containing_primitive_fifth_root hzPrimitive

  let K : IntermediateField ℚ E :=
    (IntermediateField.fixedField P).map f
  let S : IntermediateField ℚ E := f.fieldRange
  let M : IntermediateField ℚ E := K ⊔ W
  let hKS : K ≤ S := map_le_fieldRange (IntermediateField.fixedField P) f
  let hKM : K ≤ M := le_sup_left
  have hmappedGalois :
      IsGalois K (IntermediateField.extendScalars hKS) := by
    letI : FiniteDimensional (IntermediateField.fixedField P)
        p.SplittingField := hfixedFinite
    letI : IsGalois (IntermediateField.fixedField P)
        p.SplittingField := hfixedGalois
    exact mapped_top_isGalois (IntermediateField.fixedField P) f
  have hmappedDegree :
      Module.finrank K (IntermediateField.extendScalars hKS) = 5 := by
    simpa only [K, S, hKS, hfixedDegree] using
      (mapped_top_finrank (IntermediateField.fixedField P) f)
  have hMdegree :
      Module.finrank K (IntermediateField.extendScalars hKM) ≤ 4 := by
    rw [← hWdegree]
    exact finrank_extendScalars_sup_le_right K W
  have hbaseChange :=
    galois_degree_five_sup_of_finrank_le_four hKS hKM
      (inferInstance : FiniteDimensional K
        (IntermediateField.extendScalars hKS))
      hmappedGalois hmappedDegree hMdegree
  let hMS : M ≤ S ⊔ M := le_sup_right
  have hgaloisFinal :
      IsGalois M (IntermediateField.extendScalars hMS) := by
    simpa only [hMS] using hbaseChange.1
  have hdegreeFinal :
      Module.finrank M (IntermediateField.extendScalars hMS) = 5 := by
    simpa only [hMS] using hbaseChange.2

  have hfixedOverCyclotomic :
      IsSquareRadicalTower ℚ E W e M := by
    have h := IsSquareRadicalTower.sup_left ℚ E hmappedFixedTower W
    simpa only [E, sup_bot_eq, M, K, sup_comm] using h
  have hcombinedTower :
      IsSquareRadicalTower ℚ E (⊥ : IntermediateField ℚ E)
        (2 + e) M :=
    IsSquareRadicalTower.trans ℚ E hcyclotomicTower hfixedOverCyclotomic
  have hzM : z ∈ M := (show W ≤ M from le_sup_right) hzW
  have hzPrimitiveM : IsPrimitiveRoot (⟨z, hzM⟩ : M) 5 := by
    exact isPrimitiveRoot_mk_mem M hzM hzPrimitive
  have hroots : (primitiveRoots 5 M).Nonempty :=
    ⟨⟨z, hzM⟩,
      (mem_primitiveRoots (by norm_num : 0 < 5)).mpr hzPrimitiveM⟩
  letI : IsGalois M (IntermediateField.extendScalars hMS) :=
    hgaloisFinal
  have hpresentation :
      IsDefinedBySquareRootsAndFifthRoot ℚ E
        (⊥ : IntermediateField ℚ E) (S ⊔ M) (2 + e) :=
    IsDefinedBySquareRootsAndFifthRoot.of_square_tower_and_fifth_kummer
      ℚ E hcombinedTower hMS hdegreeFinal hroots
  refine ⟨e, P, f, z, W, he, hGalCard, hPcard, hPnormal, hzPrimitive,
    hcyclotomicTower, hzW, hW_eq, hWdegree, ?_, ?_⟩
  · simpa only [K] using hmappedFixedTower
  · simpa only [S, M, K] using hpresentation

/-- Exact paper-count refinement of
`exists_solvable_F20_commonCompositum_presentation`.

The exponent `eOriginal` belongs to the rational F20 tower.  After adjoining
the internally constructed primitive fifth root, `compress` deletes precisely
the square steps which have collapsed and returns `eOmega ≤ eOriginal`.
Consequently `[M:W] = 2^eOmega`, the final Kummer layer has degree five,
the full common compositum has absolute degree `5 * 2^(2+eOmega)`, and its
Galois group over the fifth-cyclotomic field has order `5 * 2^eOmega`.

All intermediate fields and all inclusions used by the relative-degree and
Galois statements are returned explicitly, so none of these conclusions is
encoded only by a numerical abbreviation. -/
theorem exists_solvable_F20_commonCompositum_exact_paper_count
    (p : ℚ[X]) (hp : Irreducible p) (hdegree : p.natDegree = 5)
    (hsolvable : IsSolvable p.Gal) :
    ∃ (eOriginal eOmega : ℕ)
        (P : Subgroup Gal(p.SplittingField/ℚ))
        (f : p.SplittingField →ₐ[ℚ]
          QuinticFifthCyclotomicSplittingField p)
        (z : QuinticFifthCyclotomicSplittingField p)
        (W M L : IntermediateField ℚ
          (QuinticFifthCyclotomicSplittingField p))
        (hWM : W ≤ M) (hML : M ≤ L) (hWL : W ≤ L),
      eOriginal ≤ 2 ∧ Nat.card p.Gal = 5 * 2 ^ eOriginal ∧
      eOmega ≤ eOriginal ∧
      Nat.card P = 5 ∧ P.Normal ∧ IsPrimitiveRoot z 5 ∧
      W = ℚ⟮z⟯ ∧
      M = ((IntermediateField.fixedField P).map f) ⊔ W ∧
      L = f.fieldRange ⊔ M ∧
      L = f.fieldRange ⊔ W ∧
      L = f.fieldRange ⊔ ℚ⟮z⟯ ∧
      Module.finrank ℚ W = 4 ∧
      IsSquareRadicalTower ℚ
        (QuinticFifthCyclotomicSplittingField p)
        (⊥ : IntermediateField ℚ
          (QuinticFifthCyclotomicSplittingField p)) 2 W ∧
      z ∈ W ∧
      IsSquareRadicalTower ℚ
        (QuinticFifthCyclotomicSplittingField p) W eOmega M ∧
      Module.finrank W
        (IntermediateField.extendScalars hWM) = 2 ^ eOmega ∧
      IsGalois M (IntermediateField.extendScalars hML) ∧
      Module.finrank M
        (IntermediateField.extendScalars hML) = 5 ∧
      IsDefinedBySquareRootsAndFifthRoot ℚ
        (QuinticFifthCyclotomicSplittingField p)
        (⊥ : IntermediateField ℚ
          (QuinticFifthCyclotomicSplittingField p)) L (2 + eOmega) ∧
      IsRadicalExtension ℚ (QuinticFifthCyclotomicSplittingField p)
        (⊥ : IntermediateField ℚ
          (QuinticFifthCyclotomicSplittingField p)) L ∧
      Module.finrank ℚ L = 5 * 2 ^ (2 + eOmega) ∧
      IsGalois W (IntermediateField.extendScalars hWL) ∧
      Nat.card
        ((IntermediateField.extendScalars hWL) ≃ₐ[W]
          (IntermediateField.extendScalars hWL)) =
        5 * 2 ^ eOmega := by
  obtain ⟨eOriginal, P, f, z, W, heOriginal, hGalCard, hPcard, hPnormal,
      hzPrimitive, hWTower, hzW, hW_eq, hWdegree, hKTower, _⟩ :=
    exists_solvable_F20_commonCompositum_presentation
      p hp hdegree hsolvable
  letI : P.Normal := hPnormal
  let E := QuinticFifthCyclotomicSplittingField p
  let K : IntermediateField ℚ E :=
    (IntermediateField.fixedField P).map f
  let S : IntermediateField ℚ E := f.fieldRange
  let M : IntermediateField ℚ E := K ⊔ W
  let L : IntermediateField ℚ E := S ⊔ M
  let hWM : W ≤ M := le_sup_right
  let hML : M ≤ L := le_sup_right
  let hWL : W ≤ L := hWM.trans hML
  letI : (p * cyclotomic 5 ℚ).IsSplittingField ℚ E :=
    Polynomial.IsSplittingField.splittingField (p * cyclotomic 5 ℚ)
  letI : FiniteDimensional ℚ E :=
    Polynomial.IsSplittingField.finiteDimensional E (p * cyclotomic 5 ℚ)

  have hfixedOverCyclotomic :
      IsSquareRadicalTower ℚ E W eOriginal M := by
    have h := IsSquareRadicalTower.sup_left ℚ E hKTower W
    simpa only [E, sup_bot_eq, M, K, sup_comm] using h
  obtain ⟨eOmega, heOmega, hcompressed, hrelativeM, habsoluteM⟩ :=
    hfixedOverCyclotomic.compress
  have hMdegreeOverW :
      Module.finrank W (IntermediateField.extendScalars hWM) =
        2 ^ eOmega := by
    rw [← IntermediateField.relfinrank_eq_finrank_of_le hWM]
    exact hrelativeM

  letI : p.IsSplittingField ℚ p.SplittingField :=
    Polynomial.IsSplittingField.splittingField p
  letI : FiniteDimensional ℚ p.SplittingField :=
    Polynomial.IsSplittingField.finiteDimensional p.SplittingField p
  haveI : IsGalois ℚ p.SplittingField :=
    IsGalois.of_separable_splitting_field (p := p) hp.separable
  let hKS : K ≤ S := map_le_fieldRange (IntermediateField.fixedField P) f
  let hKM : K ≤ M := le_sup_left
  have hsourceFinalGalois :
      IsGalois (IntermediateField.fixedField P) p.SplittingField :=
    inferInstance
  have hmappedFinalGalois :
      IsGalois K (IntermediateField.extendScalars hKS) := by
    letI : IsGalois (IntermediateField.fixedField P)
        p.SplittingField := hsourceFinalGalois
    exact mapped_top_isGalois (IntermediateField.fixedField P) f
  have hsourceFinalDegree :
      Module.finrank (IntermediateField.fixedField P)
        p.SplittingField = 5 := by
    simpa only [hPcard] using
      (IntermediateField.finrank_fixedField_eq_card P)
  have hmappedFinalDegree :
      Module.finrank K (IntermediateField.extendScalars hKS) = 5 := by
    simpa only [K, S, hKS, hsourceFinalDegree] using
      (mapped_top_finrank (IntermediateField.fixedField P) f)
  have hMdegreeLe :
      Module.finrank K (IntermediateField.extendScalars hKM) ≤ 4 := by
    rw [← hWdegree]
    exact finrank_extendScalars_sup_le_right K W
  have hbaseChange :=
    galois_degree_five_sup_of_finrank_le_four hKS hKM
      (inferInstance : FiniteDimensional K
        (IntermediateField.extendScalars hKS))
      hmappedFinalGalois hmappedFinalDegree hMdegreeLe
  have hfinalGalois :
      IsGalois M (IntermediateField.extendScalars hML) := by
    simpa only [L, hML] using hbaseChange.1
  have hfinalDegree :
      Module.finrank M (IntermediateField.extendScalars hML) = 5 := by
    simpa only [L, hML] using hbaseChange.2

  have hcombinedTower :
      IsSquareRadicalTower ℚ E (⊥ : IntermediateField ℚ E)
        (2 + eOmega) M :=
    IsSquareRadicalTower.trans ℚ E hWTower hcompressed
  have hzM : z ∈ M := hWM hzW
  have hzPrimitiveM : IsPrimitiveRoot (⟨z, hzM⟩ : M) 5 := by
    exact isPrimitiveRoot_mk_mem M hzM hzPrimitive
  have hroots : (primitiveRoots 5 M).Nonempty :=
    ⟨⟨z, hzM⟩,
      (mem_primitiveRoots (by norm_num : 0 < 5)).mpr hzPrimitiveM⟩
  letI : IsGalois M (IntermediateField.extendScalars hML) :=
    hfinalGalois
  have hpresentation :
      IsDefinedBySquareRootsAndFifthRoot ℚ E
        (⊥ : IntermediateField ℚ E) L (2 + eOmega) :=
    IsDefinedBySquareRootsAndFifthRoot.of_square_tower_and_fifth_kummer
      ℚ E hcombinedTower hML hfinalDegree hroots

  have hMabsolute :
      Module.finrank ℚ M = 4 * 2 ^ eOmega := by
    calc
      Module.finrank ℚ M = Module.finrank ℚ W * 2 ^ eOmega :=
        habsoluteM
      _ = 4 * 2 ^ eOmega := by rw [hWdegree]
  have htotalTower :=
    Module.finrank_mul_finrank ℚ M
      (IntermediateField.extendScalars hML)
  change Module.finrank ℚ M *
      Module.finrank M (IntermediateField.extendScalars hML) =
      Module.finrank ℚ L at htotalTower
  have htotalDegree :
      Module.finrank ℚ L = 5 * 2 ^ (2 + eOmega) := by
    calc
      Module.finrank ℚ L =
          (4 * 2 ^ eOmega) * 5 := by
        rw [← htotalTower, hMabsolute, hfinalDegree]
      _ = 5 * 2 ^ (2 + eOmega) := by
        rw [pow_add]
        norm_num
        ring

  have hFieldRangeGalois : IsGalois ℚ f.fieldRange :=
    IsGalois.of_algEquiv f.equivFieldRange
  have hL_eq : L = S ⊔ W := by
    dsimp only [L, M]
    rw [← sup_assoc, sup_eq_left.mpr hKS]
  have hL_eq_fieldRange : L = f.fieldRange ⊔ W := by
    simpa only [S] using hL_eq
  have hL_eq_generated : L = f.fieldRange ⊔ ℚ⟮z⟯ := by
    rw [hL_eq_fieldRange, hW_eq]
  have hfullGalois :
      IsGalois W (IntermediateField.extendScalars hWL) := by
    let hWrange : W ≤ f.fieldRange ⊔ W := le_sup_right
    have hRange :
        IsGalois W (IntermediateField.extendScalars hWrange) :=
      isGalois_extendScalars_sup_right
        (F := ℚ) (Ω := E) f.fieldRange W hFieldRangeGalois
    have hExt :
        IntermediateField.extendScalars hWrange =
          IntermediateField.extendScalars hWL := by
      apply SetLike.ext'
      change ((f.fieldRange ⊔ W : IntermediateField ℚ E) : Set E) =
        (L : Set E)
      exact congrArg (fun T : IntermediateField ℚ E => (T : Set E))
        hL_eq_fieldRange.symm
    letI : IsGalois W (IntermediateField.extendScalars hWrange) := hRange
    exact IsGalois.of_algEquiv (IntermediateField.equivOfEq hExt)
  have hrelativeFinal : M.relfinrank L = 5 := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le hML]
    exact hfinalDegree
  have hrelativeFull : W.relfinrank L = 5 * 2 ^ eOmega := by
    calc
      W.relfinrank L = W.relfinrank M * M.relfinrank L :=
        (IntermediateField.relfinrank_mul_relfinrank hWM hML).symm
      _ = 2 ^ eOmega * 5 := by
        rw [hrelativeM, hrelativeFinal]
      _ = 5 * 2 ^ eOmega := by ring
  have hfullDegree :
      Module.finrank W (IntermediateField.extendScalars hWL) =
        5 * 2 ^ eOmega := by
    rw [← IntermediateField.relfinrank_eq_finrank_of_le hWL]
    exact hrelativeFull
  have hfullCard :
      Nat.card
        ((IntermediateField.extendScalars hWL) ≃ₐ[W]
          (IntermediateField.extendScalars hWL)) =
        5 * 2 ^ eOmega := by
    letI : IsGalois W (IntermediateField.extendScalars hWL) :=
      hfullGalois
    rw [IsGalois.card_aut_eq_finrank, hfullDegree]

  have hradical :
      IsRadicalExtension ℚ E (⊥ : IntermediateField ℚ E) L :=
    hpresentation.isRadicalExtension

  exact ⟨eOriginal, eOmega, P, f, z, W, M, L, hWM, hML, hWL,
    heOriginal, hGalCard, heOmega, hPcard, hPnormal, hzPrimitive, hW_eq, rfl, rfl,
    hL_eq_fieldRange, hL_eq_generated,
    hWdegree, hWTower, hzW, hcompressed, hMdegreeOverW,
    hfinalGalois, hfinalDegree, hpresentation, hradical, htotalDegree,
    hfullGalois, hfullCard⟩

/-! ## Exact paper count after reindexing the base-changed group -/

/-- Generic exact-count form matching Lazard's definition of `e`: the
`e`-step index-two tower starts only after the `d`-step cyclotomic field has
been adjoined.  Unlike a pre-base-change count, no redundant square step is
hidden here.  The concrete rational-quintic theorem above obtains the same
paper exponent by compressing the mapped tower and then proves the matching
relative Galois-group order. -/
theorem paper_exact_count_of_baseChanged_indexTwoTower
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [CharZero Ω]
    {K W M L : IntermediateField F Ω} {d e : ℕ}
    (hcyclotomic : IsIndexTwoGaloisTower F Ω K d W)
    (hbaseChanged : IsIndexTwoGaloisTower F Ω W e M)
    (hML : M ≤ L)
    [FiniteDimensional M (IntermediateField.extendScalars hML)]
    [IsGalois M (IntermediateField.extendScalars hML)]
    (hdegree :
      Module.finrank M (IntermediateField.extendScalars hML) = 5)
    (hroots : (primitiveRoots 5 M).Nonempty) :
    IsDefinedBySquareRootsAndFifthRoot F Ω K L (d + e) :=
  IsDefinedBySquareRootsAndFifthRoot.of_index_two_galois_towers_and_fifth_kummer
      F Ω hcyclotomic hbaseChanged hML hdegree hroots

end

end LeanProofs.PolynomialFormulas.LazardOptimalityTheoremFourCommonCompositum
