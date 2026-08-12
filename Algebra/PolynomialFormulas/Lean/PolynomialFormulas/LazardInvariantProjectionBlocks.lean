import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.LinearAlgebra.Projection

/-!
# Degree-triangular projection blocks

The Reynolds operator is degree preserving.  In a homogeneous basis ordered
by degree, its matrix is block triangular.  This file isolates the elementary
two-block step used to split its fixed module.

For an endomorphism of `L × H` of the form

```
      ( e  a )
      ( 0  f ),
```

idempotence says `e² = e`, `f² = f`, and `e a + a f = a`.  Its fixed module is
linearly equivalent to `Fix(e) × Fix(f)`: a pair `(x,y)` is sent to
`(x + a y, y)`, and the inverse sends `(l,h)` to `(l - a h, h)`.  Consequently,
bases of the two diagonal fixed modules combine to a basis of the full fixed
module.  Iterating this statement over the finite degree blocks is the
algebraic core of Lazard's Reynolds argument.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantProjectionBlocks

set_option autoImplicit false

noncomputable section

variable {A L H : Type*} [CommRing A]
variable [AddCommGroup L] [AddCommGroup H]
variable [Module A L] [Module A H]

/-- An upper block-triangular endomorphism of `L × H`. -/
def upperBlock (e : L →ₗ[A] L) (a : H →ₗ[A] L) (f : H →ₗ[A] H) :
    L × H →ₗ[A] L × H :=
  (LinearMap.coprod e a).prod
    (f.comp (LinearMap.snd A L H))

@[simp]
theorem upperBlock_apply (e : L →ₗ[A] L) (a : H →ₗ[A] L)
    (f : H →ₗ[A] H) (x : L × H) :
    upperBlock e a f x = (e x.1 + a x.2, f x.2) :=
  rfl

/-- The lower-left block of an endomorphism of `L × H` vanishes.  For the
degree filtration, this says that the span of the lowest-degree block is
preserved. -/
def IsUpperTriangular (p : L × H →ₗ[A] L × H) : Prop :=
  (LinearMap.snd A L H).comp
      (p.comp (LinearMap.inl A L H)) = 0

/-- The three visible blocks of an upper-triangular endomorphism. -/
def leftDiagonalBlock (p : L × H →ₗ[A] L × H) : L →ₗ[A] L :=
  (LinearMap.fst A L H).comp
    (p.comp (LinearMap.inl A L H))

def upperRightBlock (p : L × H →ₗ[A] L × H) : H →ₗ[A] L :=
  (LinearMap.fst A L H).comp
    (p.comp (LinearMap.inr A L H))

def rightDiagonalBlock (p : L × H →ₗ[A] L × H) : H →ₗ[A] H :=
  (LinearMap.snd A L H).comp
    (p.comp (LinearMap.inr A L H))

/-- Any endomorphism preserving the left summand is its associated upper
block matrix. -/
theorem eq_upperBlock_of_isUpperTriangular
    (p : L × H →ₗ[A] L × H) (hp : IsUpperTriangular p) :
    p = upperBlock (leftDiagonalBlock p) (upperRightBlock p)
      (rightDiagonalBlock p) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  have hx : (p (x, 0)).2 = 0 := by
    have h := DFunLike.congr_fun hp x
    simpa [IsUpperTriangular] using h
  have hsplit : p (x, y) = p (x, 0) + p (0, y) := by
    simpa using (p.map_add (x, 0) (0, y))
  rw [hsplit]
  apply Prod.ext
  · simp [upperBlock, leftDiagonalBlock, upperRightBlock]
  · simp [upperBlock, rightDiagonalBlock, hx]

/-- The compatibility equation appearing in the off-diagonal block of an
idempotent upper block matrix. -/
def Compatible (e : L →ₗ[A] L) (a : H →ₗ[A] L) (f : H →ₗ[A] H) : Prop :=
  e.comp a + a.comp f = a

theorem compatible_apply {e : L →ₗ[A] L} {a : H →ₗ[A] L}
    {f : H →ₗ[A] H} (h : Compatible e a f) (y : H) :
    e (a y) + a (f y) = a y := by
  exact DFunLike.congr_fun h y

/-- Fixed vectors of a compatible upper block are exactly a product of fixed
vectors for the diagonal blocks. -/
def fixedUpperBlockEquiv (e : L →ₗ[A] L) (a : H →ₗ[A] L)
    (f : H →ₗ[A] H) (hcompat : Compatible e a f) :
    (e.fixedSubmodule × f.fixedSubmodule) ≃ₗ[A]
      (upperBlock e a f).fixedSubmodule where
  toFun xy := by
    refine ⟨(xy.1.1 + a xy.2.1, xy.2.1), ?_⟩
    rw [LinearMap.mem_fixedSubmodule_iff]
    apply Prod.ext
    · have hleft : e xy.1.1 = xy.1.1 := by
        rw [← LinearMap.mem_fixedSubmodule_iff]
        exact xy.1.2
      have hright : f xy.2.1 = xy.2.1 := xy.2.2
      have hc := compatible_apply hcompat xy.2.1
      rw [hright] at hc
      have hea : e (a xy.2.1) = 0 := by
        simpa using hc
      simp only [upperBlock_apply, map_add, hleft, hright, hea, add_zero]
    · exact xy.2.2
  invFun z := by
    have hz := z.2
    rw [LinearMap.mem_fixedSubmodule_iff] at hz
    have hleft : e z.1.1 + a z.1.2 = z.1.1 := by
      simpa using congrArg Prod.fst hz
    have hright : f z.1.2 = z.1.2 := by
      simpa using congrArg Prod.snd hz
    have hc : e (a z.1.2) + a z.1.2 = a z.1.2 := by
      simpa [hright] using compatible_apply hcompat z.1.2
    have hea : e (a z.1.2) = 0 := by
      simpa using hc
    have hel : e z.1.1 = z.1.1 - a z.1.2 :=
      (eq_sub_iff_add_eq).2 hleft
    refine
      (⟨z.1.1 - a z.1.2, ?_⟩, ⟨z.1.2, ?_⟩)
    · rw [LinearMap.mem_fixedSubmodule_iff, map_sub, hel, hea, sub_zero]
    · exact hright
  left_inv xy := by
    apply Prod.ext
    · apply Subtype.ext
      simp
    · apply Subtype.ext
      rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · change (x.1.1 + y.1.1) + a (x.2.1 + y.2.1) =
        (x.1.1 + a x.2.1) + (y.1.1 + a y.2.1)
      rw [map_add]
      abel
    · rfl
  map_smul' c x := by
    apply Subtype.ext
    apply Prod.ext
    · change c • x.1.1 + a (c • x.2.1) =
        c • (x.1.1 + a x.2.1)
      rw [map_smul, smul_add]
    · rfl

/-- A basis for each diagonal fixed module combines to a basis for the fixed
module of the compatible upper block. -/
def fixedUpperBlockBasis {ι κ : Type*}
    (e : L →ₗ[A] L) (a : H →ₗ[A] L) (f : H →ₗ[A] H)
    (hcompat : Compatible e a f)
    (be : Module.Basis ι A e.fixedSubmodule)
    (bf : Module.Basis κ A f.fixedSubmodule) :
    Module.Basis (ι ⊕ κ) A (upperBlock e a f).fixedSubmodule :=
  (be.prod bf).map (fixedUpperBlockEquiv e a f hcompat)

@[simp]
theorem fixedUpperBlockBasis_apply_inl {ι κ : Type*}
    (e : L →ₗ[A] L) (a : H →ₗ[A] L) (f : H →ₗ[A] H)
    (hcompat : Compatible e a f)
    (be : Module.Basis ι A e.fixedSubmodule)
    (bf : Module.Basis κ A f.fixedSubmodule) (i : ι) :
    (fixedUpperBlockBasis e a f hcompat be bf (Sum.inl i)).1 =
      ((be i).1, 0) := by
  simp [fixedUpperBlockBasis, fixedUpperBlockEquiv]

@[simp]
theorem fixedUpperBlockBasis_apply_inr {ι κ : Type*}
    (e : L →ₗ[A] L) (a : H →ₗ[A] L) (f : H →ₗ[A] H)
    (hcompat : Compatible e a f)
    (be : Module.Basis ι A e.fixedSubmodule)
    (bf : Module.Basis κ A f.fixedSubmodule) (j : κ) :
    (fixedUpperBlockBasis e a f hcompat be bf (Sum.inr j)).1 =
      (a (bf j).1, (bf j).1) := by
  simp [fixedUpperBlockBasis, fixedUpperBlockEquiv]

/-- The compatible upper block is idempotent when its diagonal blocks are. -/
theorem upperBlock_isIdempotent
    (e : L →ₗ[A] L) (a : H →ₗ[A] L) (f : H →ₗ[A] H)
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hcompat : Compatible e a f) :
    IsIdempotentElem (upperBlock e a f) := by
  apply LinearMap.ext
  intro x
  have he' : e (e x.1) = e x.1 :=
    DFunLike.congr_fun he.eq x.1
  have hf' : f (f x.2) = f x.2 :=
    DFunLike.congr_fun hf.eq x.2
  have hc := compatible_apply hcompat x.2
  apply Prod.ext
  · simp only [Module.End.mul_apply, upperBlock_apply, map_add]
    rw [he', add_assoc, hc]
  · exact hf'

/-- Conversely, idempotence of an upper block map exposes idempotence of both
diagonal blocks and the off-diagonal compatibility equation. -/
theorem upperBlock_idempotent_components
    (e : L →ₗ[A] L) (a : H →ₗ[A] L) (f : H →ₗ[A] H)
    (hp : IsIdempotentElem (upperBlock e a f)) :
    IsIdempotentElem e ∧ IsIdempotentElem f ∧ Compatible e a f := by
  constructor
  · ext x
    have hx := DFunLike.congr_fun hp.eq (x, 0)
    simpa [Module.End.mul_apply] using congrArg Prod.fst hx
  constructor
  · ext y
    have hy := DFunLike.congr_fun hp.eq (0, y)
    simpa [Module.End.mul_apply] using congrArg Prod.snd hy
  · apply LinearMap.ext
    intro y
    have hy := DFunLike.congr_fun hp.eq (0, y)
    simpa [Module.End.mul_apply] using congrArg Prod.fst hy

/-- For an idempotent endomorphism, its range is its fixed submodule. -/
theorem range_eq_fixedSubmodule {M : Type*} [AddCommGroup M] [Module A M]
    (p : M →ₗ[A] M) (hp : IsIdempotentElem p) :
    LinearMap.range p = p.fixedSubmodule := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_fixedSubmodule_iff]
    simpa [Module.End.mul_apply] using DFunLike.congr_fun hp.eq y
  · intro hx
    exact ⟨x, LinearMap.mem_fixedSubmodule_iff.mp hx⟩

/-- The two-block basis transported from fixed vectors to the range of the
idempotent projection. -/
def rangeUpperBlockBasis {ι κ : Type*}
    (e : L →ₗ[A] L) (a : H →ₗ[A] L) (f : H →ₗ[A] H)
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hcompat : Compatible e a f)
    (be : Module.Basis ι A e.fixedSubmodule)
    (bf : Module.Basis κ A f.fixedSubmodule) :
    Module.Basis (ι ⊕ κ) A (LinearMap.range (upperBlock e a f)) :=
  (fixedUpperBlockBasis e a f hcompat be bf).map
    (LinearEquiv.ofEq _ _
      (range_eq_fixedSubmodule (upperBlock e a f)
        (upperBlock_isIdempotent e a f he hf hcompat)).symm)

/-- The reusable filtration step: an idempotent preserving a direct summand
has a free range as soon as the fixed modules of its two diagonal blocks have
bases.  The resulting index is the disjoint union of the two block indices. -/
def rangeBasisOfIsUpperTriangular {ι κ : Type*}
    (p : L × H →ₗ[A] L × H)
    (htri : IsUpperTriangular p) (hidem : IsIdempotentElem p)
    (be : Module.Basis ι A (leftDiagonalBlock p).fixedSubmodule)
    (bf : Module.Basis κ A (rightDiagonalBlock p).fixedSubmodule) :
    Module.Basis (ι ⊕ κ) A (LinearMap.range p) := by
  let e := leftDiagonalBlock p
  let a := upperRightBlock p
  let f := rightDiagonalBlock p
  change Module.Basis ι A e.fixedSubmodule at be
  change Module.Basis κ A f.fixedSubmodule at bf
  have hp : p = upperBlock e a f :=
    eq_upperBlock_of_isUpperTriangular p htri
  rw [hp] at hidem ⊢
  obtain ⟨he, hf, hcompat⟩ :=
    upperBlock_idempotent_components e a f hidem
  exact rangeUpperBlockBasis e a f he hf hcompat be bf

end

end LeanProofs.PolynomialFormulas.LazardInvariantProjectionBlocks
