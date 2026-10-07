/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem integerMatrixImage_index {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) :
    A.mulVecLin.range.toAddSubgroup.index = A.det.natAbs := by
  let e := LinearEquiv.ofInjective A.mulVecLin (Matrix.mulVec_injective_of_det_ne_zero hA)
  have h := Submodule.natAbs_det_equiv A.mulVecLin.range e
  have he : A.mulVecLin.range.subtype.comp e.toLinearMap = A.mulVecLin := by
    ext x i
    rfl
  change (LinearMap.det (A.mulVecLin.range.subtype.comp e.toLinearMap)).natAbs = _ at h
  rw [he] at h
  rw [← Matrix.toLin'_apply', LinearMap.det_toLin'] at h
  exact h.symm

theorem integerMatrixImage_det_smul {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (y : I → ℤ) : A.det • y ∈ A.mulVecLin.range := by
  refine ⟨A.adjugate *ᵥ y, ?_⟩
  change A *ᵥ (A.adjugate *ᵥ y) = A.det • y
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem integerMatrixImage_multiple_smul {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) {m : ℤ} (hm : A.det ∣ m) (y : I → ℤ) :
    m • y ∈ A.mulVecLin.range := by
  obtain ⟨r, rfl⟩ := hm
  simpa only [smul_smul, mul_comm] using
    A.mulVecLin.range.smul_mem r (integerMatrixImage_det_smul A y)

theorem integerMatrixImage_natAbs_smul {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (y : I → ℤ) : (A.det.natAbs : ℤ) • y ∈ A.mulVecLin.range :=
  integerMatrixImage_multiple_smul A Int.dvd_natAbs_self y

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

def pivotFreeLattice {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) : Submodule ℤ (J → ℤ) :=
  A.mulVecLin.range.comap B.mulVecLin

def pivotFullImage {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) : Submodule ℤ (I → ℤ) :=
  A.mulVecLin.range ⊔ B.mulVecLin.range

def pivotFreeAdmissible {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (v : I → ℤ) (y : J → ℤ) : Prop :=
  v - B *ᵥ y ∈ A.mulVecLin.range

theorem pivotFreeAdmissible_iff {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (v : I → ℤ) (y : J → ℤ) :
    pivotFreeAdmissible A B v y ↔ ∃ x : I → ℤ, A *ᵥ x + B *ᵥ y = v := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (eq_sub_iff_add_eq).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (eq_sub_iff_add_eq).mpr hx⟩

theorem pivotFreeAdmissible_coset {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (v : I → ℤ)
    {y₀ : J → ℤ} (hy₀ : pivotFreeAdmissible A B v y₀) (y : J → ℤ) :
    pivotFreeAdmissible A B v y ↔ y - y₀ ∈ pivotFreeLattice A B := by
  change v - B *ᵥ y ∈ A.mulVecLin.range ↔ B *ᵥ (y - y₀) ∈ A.mulVecLin.range
  rw [Matrix.mulVec_sub]
  constructor
  · intro hy
    convert A.mulVecLin.range.sub_mem hy₀ hy using 1
    abel
  · intro hy
    convert A.mulVecLin.range.sub_mem hy₀ hy using 1
    abel

theorem pivotFullImage_iff {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (v : I → ℤ) :
    v ∈ pivotFullImage A B ↔ ∃ x : I → ℤ, ∃ y : J → ℤ, A *ᵥ x + B *ᵥ y = v := by
  rw [pivotFullImage, Submodule.mem_sup]
  constructor
  · rintro ⟨a, ⟨x, rfl⟩, b, ⟨y, rfl⟩, he⟩
    exact ⟨x, y, he⟩
  · rintro ⟨x, y, he⟩
    exact ⟨A *ᵥ x, ⟨x, rfl⟩, B *ᵥ y, ⟨y, rfl⟩, he⟩

noncomputable def pivotIntegerFiberEquiv {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (v : I → ℤ) :
    {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} ≃
      {y : J → ℤ // pivotFreeAdmissible A B v y} where
  toFun p := ⟨p.val.2, (pivotFreeAdmissible_iff A B v p.val.2).mpr ⟨p.val.1, p.property⟩⟩
  invFun y := ⟨⟨(pivotFreeAdmissible_iff A B v y.val).mp y.property |>.choose, y.val⟩,
    (pivotFreeAdmissible_iff A B v y.val).mp y.property |>.choose_spec⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Matrix.mulVec_injective_of_det_ne_zero hA
      have h := (pivotFreeAdmissible_iff A B v p.val.2).mp
        ((pivotFreeAdmissible_iff A B v p.val.2).mpr ⟨p.val.1, p.property⟩) |>.choose_spec
      exact add_right_cancel (h.trans p.property.symm)
    · rfl
  right_inv _ := rfl

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem pivotFreeLattice_index_mul {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) :
    (pivotFreeLattice A B).toAddSubgroup.index * (pivotFullImage A B).toAddSubgroup.index =
      A.det.natAbs := by
  rw [← integerMatrixImage_index A hA]
  unfold pivotFreeLattice pivotFullImage
  rw [Submodule.sup_toAddSubgroup]
  change (A.mulVecLin.range.toAddSubgroup.comap B.mulVecLin.toAddMonoidHom).index *
    (A.mulVecLin.range.toAddSubgroup ⊔ B.mulVecLin.toAddMonoidHom.range).index = _
  rw [AddSubgroup.index_comap]
  rw [← AddSubgroup.relIndex_sup_left]
  exact AddSubgroup.relIndex_mul_index le_sup_left

def integerScalarLattice (J : Type*) [Fintype J] (m : ℤ) : Submodule ℤ (J → ℤ) :=
  (m • (LinearMap.id : (J → ℤ) →ₗ[ℤ] (J → ℤ))).range

theorem integerScalarLattice_mem {J : Type*} [Fintype J] (m : ℤ) (y : J → ℤ) :
    y ∈ integerScalarLattice J m ↔ ∃ z : J → ℤ, m • z = y := Iff.rfl

theorem integerScalarLattice_index {J : Type*} [Fintype J] [DecidableEq J]
    {m : ℤ} (hm : m ≠ 0) :
    (integerScalarLattice J m).toAddSubgroup.index = m.natAbs ^ Fintype.card J := by
  have hM : (m • (1 : Matrix J J ℤ)).det ≠ 0 := by
    simp only [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hm
  have hi := integerMatrixImage_index (m • (1 : Matrix J J ℤ)) hM
  have he : (m • (1 : Matrix J J ℤ)).mulVecLin = m • LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (m • (1 : Matrix J J ℤ)) *ᵥ x = m • x
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [he, Matrix.det_smul, Matrix.det_one, mul_one, Int.natAbs_pow] at hi
  exact hi

theorem integerScalarLattice_le_pivotFreeLattice {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) {m : ℤ} (hm : A.det ∣ m) :
    integerScalarLattice J m ≤ pivotFreeLattice A B := by
  rintro y ⟨z, rfl⟩
  change B *ᵥ (m • z) ∈ A.mulVecLin.range
  rw [Matrix.mulVec_smul]
  exact integerMatrixImage_multiple_smul A hm (B *ᵥ z)

theorem pivot_residue_index_identity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m) :
    (integerScalarLattice J m).toAddSubgroup.relIndex (pivotFreeLattice A B).toAddSubgroup *
      A.det.natAbs = m.natAbs ^ Fintype.card J * (pivotFullImage A B).toAddSubgroup.index := by
  have hsub : (integerScalarLattice J m).toAddSubgroup ≤ (pivotFreeLattice A B).toAddSubgroup :=
    integerScalarLattice_le_pivotFreeLattice A B hdiv
  have hr := AddSubgroup.relIndex_mul_index hsub
  rw [integerScalarLattice_index hm] at hr
  rw [← pivotFreeLattice_index_mul A hA B, ← mul_assoc, hr]

end Erdos3

end

section

namespace Erdos3

def integerLatticeResidue {J : Type*} [Fintype J]
    (L : Submodule ℤ (J → ℤ)) (m : ℤ) :=
  L.toAddSubgroup ⧸ (integerScalarLattice J m).toAddSubgroup.addSubgroupOf L.toAddSubgroup

@[instance_reducible] noncomputable def integerLatticeResidueFintype {J : Type*}
    [Fintype J] [DecidableEq J]
    (L : Submodule ℤ (J → ℤ)) {m : ℤ} (hm : m ≠ 0) :
    Fintype (integerLatticeResidue L m) := by
  let : (integerScalarLattice J m).toAddSubgroup.FiniteIndex :=
    ⟨by rw [integerScalarLattice_index hm]; exact pow_ne_zero _ (Int.natAbs_ne_zero.mpr hm)⟩
  unfold integerLatticeResidue
  exact Fintype.ofFinite _

theorem integerLatticeResidue_card {J : Type*} [Fintype J]
    (L : Submodule ℤ (J → ℤ)) (m : ℤ) :
    Nat.card (integerLatticeResidue L m) =
      (integerScalarLattice J m).toAddSubgroup.relIndex L.toAddSubgroup := rfl

noncomputable def integerScalarPeriodEquiv {J : Type*} [Fintype J]
    (L : Submodule ℤ (J → ℤ)) {m : ℤ} (hm : m ≠ 0)
    (hL : integerScalarLattice J m ≤ L) :
    (J → ℤ) ≃ (integerScalarLattice J m).toAddSubgroup.addSubgroupOf L.toAddSubgroup where
  toFun z := ⟨⟨m • z, hL ⟨z, rfl⟩⟩, ⟨z, rfl⟩⟩
  invFun z := z.property.choose
  left_inv z := by
    funext j
    apply mul_left_cancel₀ hm
    exact congrFun (Exists.choose_spec (show ∃ w : J → ℤ, m • w = m • z from ⟨z, rfl⟩)) j
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact z.property.choose_spec

theorem integerScalarPeriodEquiv_apply {J : Type*} [Fintype J]
    (L : Submodule ℤ (J → ℤ)) {m : ℤ} (hm : m ≠ 0)
    (hL : integerScalarLattice J m ≤ L) (z : J → ℤ) :
    (((integerScalarPeriodEquiv L hm hL z).val).val) = m • z := rfl

noncomputable def additiveResidueEquiv {G : Type*} [AddCommGroup G]
    (H : AddSubgroup G) : G ≃ (G ⧸ H) × H where
  toFun x := ⟨(x : G ⧸ H), ⟨x - Quotient.out (x : G ⧸ H),
    QuotientAddGroup.eq_iff_sub_mem.mp (Quotient.out_eq' _).symm⟩⟩
  invFun p := p.1.out + p.2.val
  left_inv x := by simp
  right_inv := by
    rintro ⟨r, n⟩
    have h : ((r.out + n.val : G) : G ⧸ H) = r := by
      calc
        _ = (r.out : G ⧸ H) := QuotientAddGroup.eq_iff_sub_mem.mpr (by simp)
        _ = r := Quotient.out_eq' r
    apply Prod.ext
    · exact h
    · apply Subtype.ext
      change r.out + n.val - Quotient.out ((r.out + n.val : G) : G ⧸ H) = n.val
      rw [h]
      simp

noncomputable def integerLatticeResidueEquiv {J : Type*} [Fintype J]
    (L : Submodule ℤ (J → ℤ)) {m : ℤ} (hm : m ≠ 0)
    (hL : integerScalarLattice J m ≤ L) :
    L ≃ integerLatticeResidue L m × (J → ℤ) :=
  (additiveResidueEquiv _).trans
    (Equiv.prodCongr (Equiv.refl _) (integerScalarPeriodEquiv L hm hL).symm)

theorem integerLatticeResidueEquiv_symm_apply {J : Type*} [Fintype J]
    (L : Submodule ℤ (J → ℤ)) {m : ℤ} (hm : m ≠ 0)
    (hL : integerScalarLattice J m ≤ L) (r : integerLatticeResidue L m) (z : J → ℤ) :
    ((integerLatticeResidueEquiv L hm hL).symm (r, z)).val = r.out.val + m • z := by
  rfl

end Erdos3

end

section

namespace Erdos3

def integerResidueMap (I : Type*) (m : ℕ) : (I → ℤ) →ₗ[ℤ] (I → ZMod m) where
  toFun v i := v i
  map_add' v w := by ext i; simp
  map_smul' r v := by ext i; simp

theorem integerResidueMap_apply {I : Type*} (m : ℕ) (v : I → ℤ) (i : I) :
    integerResidueMap I m v i = (v i : ZMod m) := rfl

theorem integerResidueMap_surjective (I : Type*) (m : ℕ) :
    Function.Surjective (integerResidueMap I m) := by
  intro v
  choose z hz using fun i => ZMod.intCast_surjective (v i)
  exact ⟨z, funext hz⟩

theorem integerResidueMap_ker (I : Type*) [Fintype I] (m : ℕ) :
    LinearMap.ker (integerResidueMap I m) = integerScalarLattice I (m : ℤ) := by
  ext v
  rw [LinearMap.mem_ker, integerScalarLattice_mem]
  constructor
  · intro hv
    have hd : ∀ i, (m : ℤ) ∣ v i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd (v i) m).mp (congrFun hv i)
    choose z hz using hd
    exact ⟨z, funext fun i => (hz i).symm⟩
  · rintro ⟨z, rfl⟩
    ext i
    change (((m : ℤ) * z i : ℤ) : ZMod m) = 0
    simp

theorem integerResidueMap_eq_iff {I : Type*} (m : ℕ) (v w : I → ℤ) :
    integerResidueMap I m v = integerResidueMap I m w ↔
      ∀ i, v i % (m : ℤ) = w i % (m : ℤ) := by
  constructor
  · intro h i
    exact (ZMod.intCast_eq_intCast_iff' (v i) (w i) m).mp (congrFun h i)
  · intro h
    exact funext fun i => (ZMod.intCast_eq_intCast_iff' (v i) (w i) m).mpr (h i)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix ENNReal

def pivotAdmissibleLatticeEquiv {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (v : I → ℤ)
    (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀) :
    {y : J → ℤ // pivotFreeAdmissible A B v y} ≃ pivotFreeLattice A B where
  toFun y := ⟨y.val - y₀, (pivotFreeAdmissible_coset A B v hy₀ y.val).mp y.property⟩
  invFun z := ⟨y₀ + z.val, (pivotFreeAdmissible_coset A B v hy₀ _).mpr (by
    simpa only [add_sub_cancel_left] using z.property)⟩
  left_inv y := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp

noncomputable def pivotFiberGridEquiv {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (v : I → ℤ)
    (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m) :
    {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} ≃
      integerLatticeResidue (pivotFreeLattice A B) m × (J → ℤ) :=
  (pivotIntegerFiberEquiv A hA B v).trans ((pivotAdmissibleLatticeEquiv A B v y₀ hy₀).trans
    (integerLatticeResidueEquiv (pivotFreeLattice A B) hm
      (integerScalarLattice_le_pivotFreeLattice A B hdiv)))

theorem pivotFiberGridEquiv_free {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (v : I → ℤ)
    (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m)
    (r : integerLatticeResidue (pivotFreeLattice A B) m) (z : J → ℤ) :
    ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm (r, z)).val.2 =
      y₀ + r.out.val + m • z := by
  change y₀ + ((integerLatticeResidueEquiv (pivotFreeLattice A B) hm
    (integerScalarLattice_le_pivotFreeLattice A B hdiv)).symm (r, z)).val = _
  rw [integerLatticeResidueEquiv_symm_apply, add_assoc]

theorem pivotFiberGrid_card_mul {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m) :
    Nat.card (integerLatticeResidue (pivotFreeLattice A B) m) * A.det.natAbs =
      m.natAbs ^ Fintype.card J * (pivotFullImage A B).toAddSubgroup.index :=
  pivot_residue_index_identity A hA B hm hdiv

theorem pivotFiberGrid_tsum {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (v : I → ℤ)
    (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m)
    (w : (I → ℤ) × (J → ℤ) → ℝ≥0∞) :
    letI := integerLatticeResidueFintype (pivotFreeLattice A B) hm
    (∑' p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v}, w p.val) =
      ∑ r : integerLatticeResidue (pivotFreeLattice A B) m,
        ∑' z : J → ℤ, w ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm (r, z)).val := by
  let := integerLatticeResidueFintype (pivotFreeLattice A B) hm
  rw [← (pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm.tsum_eq (fun p => w p.val),
    ENNReal.tsum_prod', tsum_fintype]

theorem pivotFiberGrid_tsum_real {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (v : I → ℤ)
    (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀)
    {m : ℤ} (hm : m ≠ 0) (hdiv : A.det ∣ m)
    (w : (I → ℤ) × (J → ℤ) → ℝ)
    (hw : Summable (fun p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} => w p.val)) :
    letI := integerLatticeResidueFintype (pivotFreeLattice A B) hm
    (∑' p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v}, w p.val) =
      ∑ r : integerLatticeResidue (pivotFreeLattice A B) m,
        ∑' z : J → ℤ, w ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm (r, z)).val := by
  let := integerLatticeResidueFintype (pivotFreeLattice A B) hm
  have hs : Summable (fun p : integerLatticeResidue (pivotFreeLattice A B) m × (J → ℤ) =>
      w ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm p).val) :=
    hw.comp_injective (pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm.injective
  rw [← (pivotFiberGridEquiv A hA B v y₀ hy₀ hm hdiv).symm.tsum_eq (fun p => w p.val),
    hs.tsum_prod, tsum_fintype]

end Erdos3

end

section

namespace Erdos3

def residueLatticeImage {I : Type*} (L : Submodule ℤ (I → ℤ)) (m : ℕ) :
    Submodule ℤ (I → ZMod m) := L.map (integerResidueMap I m)

theorem residueLatticeImage_comap {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).comap (integerResidueMap I m) = L := by
  apply Submodule.comap_map_eq_self
  rwa [integerResidueMap_ker]

theorem residueLatticeImage_mem_iff {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L)
    (v : I → ℤ) : v ∈ L ↔ integerResidueMap I m v ∈ residueLatticeImage L m := by
  change v ∈ L ↔ v ∈ (residueLatticeImage L m).comap (integerResidueMap I m)
  rw [residueLatticeImage_comap L m hperiod]

theorem residueLatticeImage_determines_lattice {I : Type*} [Fintype I]
    (L K : Submodule ℤ (I → ℤ)) (m : ℕ)
    (hL : integerScalarLattice I (m : ℤ) ≤ L) (hK : integerScalarLattice I (m : ℤ) ≤ K)
    (h : residueLatticeImage L m = residueLatticeImage K m) : L = K := by
  rw [← residueLatticeImage_comap L m hL, ← residueLatticeImage_comap K m hK, h]

theorem residueLatticeImage_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).toAddSubgroup.index = L.toAddSubgroup.index := by
  have hk : (integerResidueMap I m).toAddMonoidHom.ker ≤ L.toAddSubgroup := by
    change (LinearMap.ker (integerResidueMap I m)).toAddSubgroup ≤ L.toAddSubgroup
    rw [integerResidueMap_ker]
    exact hperiod
  have h := L.toAddSubgroup.index_map_eq (integerResidueMap_surjective I m) hk
  change (L.toAddSubgroup.map (integerResidueMap I m).toAddMonoidHom).index = _
  exact h

theorem residueLatticeImage_card_mul_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = m ^ Fintype.card I := by
  classical
  have h := (residueLatticeImage L m).toAddSubgroup.card_mul_index
  rw [residueLatticeImage_index L m hperiod] at h
  change Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = Nat.card (I → ZMod m) at h
  have heq : Nat.card (I → ZMod m) = m ^ Fintype.card I := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  exact h.trans heq

theorem residueLatticeImage_index_eq_div {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    L.toAddSubgroup.index = m ^ Fintype.card I / Nat.card (residueLatticeImage L m) := by
  rw [← residueLatticeImage_card_mul_index L m hperiod,
    Nat.mul_div_cancel_left _ (Nat.card_pos (α := residueLatticeImage L m))]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

def integerResidueMatrix {I J : Type*} (A : Matrix I J ℤ) (m : ℕ) : Matrix I J (ZMod m) :=
  A.map (Int.castRingHom (ZMod m))

theorem integerResidueMap_mulVec {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ) (x : J → ℤ) :
    integerResidueMap I m (A *ᵥ x) = integerResidueMatrix A m *ᵥ integerResidueMap J m x := by
  funext i
  exact (Int.castRingHom (ZMod m)).map_mulVec A x i

theorem integerMatrixResidue_mem {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ) (v : I → ZMod m) :
    v ∈ residueLatticeImage A.mulVecLin.range m ↔
      ∃ x : J → ZMod m, integerResidueMatrix A m *ᵥ x = v := by
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, hy⟩
    exact ⟨integerResidueMap J m x, (integerResidueMap_mulVec A m x).symm.trans hy⟩
  · rintro ⟨x, hx⟩
    obtain ⟨z, hz⟩ := integerResidueMap_surjective J m x
    refine ⟨A *ᵥ z, ⟨z, rfl⟩, ?_⟩
    rw [integerResidueMap_mulVec, hz, hx]

theorem integerMatrixResidue_image_eq {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ) :
    residueLatticeImage A.mulVecLin.range m =
      (integerResidueMatrix A m).mulVecLin.range.restrictScalars ℤ := by
  ext v
  exact integerMatrixResidue_mem A m v

theorem integerMatrixImage_residue_iff {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ)
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range) (v : I → ℤ) :
    v ∈ A.mulVecLin.range ↔
      ∃ x : J → ZMod m, integerResidueMatrix A m *ᵥ x = integerResidueMap I m v := by
  rw [residueLatticeImage_mem_iff A.mulVecLin.range m hperiod, integerMatrixResidue_mem]

theorem integerMatrixImage_eq_of_residueMatrix {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I J ℤ) (m : ℕ)
    (hA : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hB : integerScalarLattice I (m : ℤ) ≤ B.mulVecLin.range)
    (hAB : integerResidueMatrix A m = integerResidueMatrix B m) :
    A.mulVecLin.range = B.mulVecLin.range := by
  apply residueLatticeImage_determines_lattice _ _ m hA hB
  rw [integerMatrixResidue_image_eq, integerMatrixResidue_image_eq, hAB]

theorem integerResidueMatrix_eq_of_mod {I J : Type*} (A B : Matrix I J ℤ) (m : ℕ)
    (hAB : ∀ i j, A i j % (m : ℤ) = B i j % (m : ℤ)) :
    integerResidueMatrix A m = integerResidueMatrix B m := by
  ext i j
  exact (ZMod.intCast_eq_intCast_iff' (A i j) (B i j) m).mpr (hAB i j)

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeImage_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    L.toAddSubgroup.index ≤ m ^ Fintype.card I := by
  have h := residueLatticeImage_card_mul_index L m hperiod
  have hpos := Nat.card_pos (α := residueLatticeImage L m)
  nlinarith

theorem residueLatticeImage_real_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (L.toAddSubgroup.index : ℝ) = (m : ℝ) ^ Fintype.card I /
      (Nat.card (residueLatticeImage L m) : ℝ) := by
  have hpos : (0 : ℝ) < Nat.card (residueLatticeImage L m) := by
    exact_mod_cast Nat.card_pos (α := residueLatticeImage L m)
  apply (eq_div_iff hpos.ne').mpr
  rw [mul_comm]
  exact_mod_cast residueLatticeImage_card_mul_index L m hperiod

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

def reducedIntegerMatrix {I J : Type*} (A : Matrix I J ℤ) (M : ℕ) : Matrix I J ℤ :=
  fun i j => A i j % (M : ℤ)

theorem reducedIntegerMatrix_bounds {I J : Type*} (A : Matrix I J ℤ)
    (M : ℕ) [NeZero M] (i : I) (j : J) :
    0 ≤ reducedIntegerMatrix A M i j ∧ reducedIntegerMatrix A M i j < M := by
  have hM : (0 : ℤ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  exact ⟨Int.emod_nonneg _ hM.ne', Int.emod_lt_of_pos _ hM⟩

theorem integerResidueMatrix_reduced {I J : Type*} (A : Matrix I J ℤ) (M : ℕ) :
    integerResidueMatrix (reducedIntegerMatrix A M) M = integerResidueMatrix A M := by
  apply integerResidueMatrix_eq_of_mod
  intro i j
  exact Int.emod_emod _ _

theorem reducedIntegerMatrix_residue {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (M : ℕ) (x : J → ℤ) :
    integerResidueMap I M (A *ᵥ x) =
      integerResidueMatrix (reducedIntegerMatrix A M) M *ᵥ integerResidueMap J M x := by
  rw [integerResidueMatrix_reduced]
  exact integerResidueMap_mulVec A M x

theorem exists_bounded_integerMap_residue_matrix {I J : Type*} [Fintype J] [DecidableEq J]
    (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (M : ℕ) [NeZero M] :
    ∃ A : Matrix I J ℤ,
      (∀ i j, 0 ≤ A i j ∧ A i j < M) ∧
      ∀ x, integerResidueMap I M (f x) = integerResidueMatrix A M *ᵥ integerResidueMap J M x := by
  refine ⟨reducedIntegerMatrix (LinearMap.toMatrix' f) M, reducedIntegerMatrix_bounds _ M, ?_⟩
  intro x
  rw [← LinearMap.toMatrix'_mulVec f x]
  exact reducedIntegerMatrix_residue _ M x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem integerResidueMatrix_eq_iff_dvd_sub {I J : Type*}
    (C D : Matrix I J ℤ) (m : ℕ) :
    integerResidueMatrix C m = integerResidueMatrix D m ↔
      ∀ i j, (m : ℤ) ∣ C i j - D i j := by
  constructor
  · intro h i j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (C i j - D i j) m).mp
    rw [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun (congrFun h i) j)
  · intro h
    ext i j
    change (C i j : ZMod m) = (D i j : ZMod m)
    apply sub_eq_zero.mp
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (C i j - D i j) m).mpr (h i j)
    simpa only [Int.cast_sub] using hz

theorem integerResidueMatrix_reduce {I J : Type*} (C D : Matrix I J ℤ)
    {m n : ℕ} (hmn : m ∣ n) (h : integerResidueMatrix C n = integerResidueMatrix D n) :
    integerResidueMatrix C m = integerResidueMatrix D m := by
  apply (integerResidueMatrix_eq_iff_dvd_sub C D m).mpr
  have hd : (m : ℤ) ∣ (n : ℤ) := by exact_mod_cast hmn
  exact fun i j => hd.trans ((integerResidueMatrix_eq_iff_dvd_sub C D n).mp h i j)

def residueMatrixShift {I J : Type*} [Fintype J]
    (C D : Matrix I J ℤ) (q : ℕ) (r : J → ℤ) : I → ℤ :=
  fun i => ((C - D) *ᵥ r) i / (q : ℤ)

theorem residueMatrixShift_spec {I J : Type*} [Fintype I] [Fintype J]
    (C D : Matrix I J ℤ) (q m : ℕ) (hq : 0 < q)
    (h : integerResidueMatrix C (q * m) = integerResidueMatrix D (q * m)) (r : J → ℤ) :
    (∀ i, (q : ℤ) * residueMatrixShift C D q r i = ((C - D) *ᵥ r) i) ∧
      residueMatrixShift C D q r ∈ integerScalarLattice I (m : ℤ) := by
  classical
  have hd (i) (j) : (q : ℤ) * (m : ℤ) ∣ C i j - D i j := by
    simpa only [Nat.cast_mul] using (integerResidueMatrix_eq_iff_dvd_sub C D (q * m)).mp h i j
  choose Z hZ using hd
  let t : I → ℤ := fun i => ∑ j, Z i j * r j
  have he (i) : ((C - D) *ᵥ r) i = (q : ℤ) * ((m : ℤ) * t i) := by
    change (∑ j, (C i j - D i j) * r j) = _
    simp_rw [hZ]
    dsimp only [t]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hs (i) : residueMatrixShift C D q r i = (m : ℤ) * t i := by
    unfold residueMatrixShift
    rw [he, Int.mul_ediv_cancel_left _ hq0]
  refine ⟨fun i => by rw [hs, he], ?_⟩
  refine ⟨t, ?_⟩
  funext i
  exact (hs i).symm

theorem residueMatrixShift_bound {I J : Type*} [Fintype I] [Fintype J]
    (C D : Matrix I J ℤ) (q m : ℕ) (hq : 0 < q)
    (h : integerResidueMatrix C (q * m) = integerResidueMatrix D (q * m))
    (r : J → ℤ) (hr : ∀ j, |(r j : ℝ)| ≤ q) (i : I) :
    |(residueMatrixShift C D q r i : ℝ)| ≤ ∑ j, |((C i j - D i j : ℤ) : ℝ)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have he := (residueMatrixShift_spec C D q m hq h r).1 i
  have heR : (q : ℝ) * (residueMatrixShift C D q r i : ℝ) = (((C - D) *ᵥ r) i : ℝ) := by
    exact_mod_cast he
  have hm : (q : ℝ) * |(residueMatrixShift C D q r i : ℝ)| =
      |∑ j, ((C i j - D i j : ℤ) : ℝ) * (r j : ℝ)| := by
    rw [← abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q), ← abs_mul, heR]
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Int.cast_sum, Int.cast_mul]
  apply (mul_le_mul_iff_right₀ hqR).mp
  rw [hm]
  calc
    _ ≤ ∑ j, |((C i j - D i j : ℤ) : ℝ) * (r j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |((C i j - D i j : ℤ) : ℝ)| * (q : ℝ) :=
      Finset.sum_le_sum (fun j _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hr j) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm.trans (mul_comm _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def residueRefinedPeriod {X : Type*} [Fintype X] (m : ℕ) (q : X → ℕ) : ℕ :=
  m * ∏ d, q d

theorem residueRefinedPeriod_pos {X : Type*} [Fintype X]
    {m : ℕ} (hm : 0 < m) (q : X → ℕ) (hq : ∀ d, 0 < q d) :
    0 < residueRefinedPeriod m q :=
  Nat.mul_pos hm (Finset.prod_pos (fun d _ => hq d))

theorem stride_mul_dvd_residueRefinedPeriod {X : Type*} [Fintype X]
    (m : ℕ) (q : X → ℕ) (d : X) : q d * m ∣ residueRefinedPeriod m q := by
  classical
  obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem q (Finset.mem_univ d)
  refine ⟨a, ?_⟩
  unfold residueRefinedPeriod
  rw [ha]
  ring

theorem residueRefinedPeriod_exp_bound {X : Type*} [Fintype X]
    (m : ℕ) (q : X → ℕ) {P R : ℝ}
    (hm : (m : ℝ) ≤ Real.exp P) (hq : ∀ d, (q d : ℝ) ≤ Real.exp R) :
    (residueRefinedPeriod m q : ℝ) ≤ Real.exp (P + Fintype.card X * R) := by
  have hprod : (∏ d, (q d : ℝ)) ≤ Real.exp R ^ Fintype.card X := by
    calc
      _ ≤ ∏ _d : X, Real.exp R :=
        Finset.prod_le_prod₀ (fun direction _ => Nat.cast_nonneg (q direction))
          (fun direction _ => hq direction)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ]
  have h := mul_le_mul hm hprod (Finset.prod_nonneg (fun d _ => Nat.cast_nonneg (q d))) (Real.exp_pos P).le
  simpa only [residueRefinedPeriod, Nat.cast_mul, Nat.cast_prod, Real.exp_add, Real.exp_nat_mul] using h

end Erdos3

end

end OAI
