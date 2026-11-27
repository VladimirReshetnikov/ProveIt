import Lib.Adelic.Adeles.StrongApproximation
import Lib.Cohomology.Etale.Basic
import Lib.General.Measure.HaarModulus
import Lib.Shimura.ComplexTheta.AppellHumbertData

/-!
# Adelic frames over a CM field, torsion classes, period lattices and period maps

This file develops the linear algebra over a CM field `E` used to count points. `New.CMBase E` fixes
a CM type `Φ` and a base infinite place `v₀`, where the signature condition is imposed.
`New.AdelicTorsion E n` is `(𝔸f E / Ô E)ⁿ`, an adelic model of `(E / 𝓞 E)ⁿ`. Here `𝔸f E` is the ring
of finite adeles and `Ô E` the ring of integral finite adeles. `New.Variety.torsionClass` is the
class map. Adelic frames give lattices of rational vectors in `(E ⊗ ℝ)ⁿ`, which are shown to be
discrete and full. A complex matrix gives a complex structure on this space.

## Main definitions and results

* `New.Variety.IsFrameFor β x`: `xᴴ β x` is a scalar matrix `ε • 1` with `ε` a unit of `Ẑ = Ô ℚ`.
* `New.Variety.IsSignedFrame x J`: `x` is a frame of some `β` that is positive definite at every
  infinite place other than `v₀`, with `β J` positive definite at `v₀`.
* `New.Variety.ModuliPoint`: points `(x, J, P)` at infinite level, with the action
  `New.Variety.ModuliPoint.act` and the isomorphisms `New.Variety.ModuliPoint.IsLevelIso` at a level
  `K`.
* `New.Variety.IsPeriodMap`: a map onto a complex vector space that carries the complex structure
  `i J` at `v₀` and `i` at the other infinite places to multiplication by `i`.
* `New.Variety.exists_matrix_torsionClass_eq`: an `𝓞 E`-linear map `Eⁿ → AdelicTorsion E n` is
  `y ↦ torsionClass (h y)` for an adelic matrix `h`, found by compactness of `Ô`.

Notions from other files:
* `𝔸f E`, `Ô E`: the finite adeles of `E` and the integral ones (the product of the completions of
  `𝓞 E`); `finAdeleIncl ℚ E` maps the finite adeles of `ℚ` into those of `E`.
* `New.CMType E`: a CM type, a complex embedding `Φ w` for every infinite place `w` of `E`;
  `FinComplexSpace V`: `V` is a finite-dimensional complex vector space with its topology.

## Relation to the literature

Known; see `Lib.Shimura.Uniformisation.AppellHumbert` and `Lib.Shimura.IntegralModel.TowerExistence`
for sources.
-/

noncomputable section

/-!
## Adelic frames, the similitude group and the signature condition

* `New.Variety.GU`, `New.Variety.GUPlus`: the finite adelic similitudes, and those whose inverse is
  integral.
* `New.Variety.IsSignedFrame.mul`: `New.Variety.IsSignedFrame x J` is kept by
  `(x, J) ↦ (z x g, z J z⁻¹)` for `z ∈ GL_n(E)` and a similitude `g`.
-/

section Frames

open NumberField ConjAct Matrix GeneralLinearGroup ComplexOrder Pointwise

namespace New

/-- A choice of one complex embedding Φ_v for each infinite place v of E, together with a base
place v₀; E has at least two infinite places.
It extends `CMType E`, so E is a CM number field. -/
class CMBase (E : Type*) [Field E] extends CMType E, Nontrivial (InfinitePlace E) where
  /-- The base infinite place of `E`. -/
  v₀ : InfinitePlace E

export CMBase (v₀)

variable (E : Type) [Field E] [NumberField E] (n : Type) [Fintype n] [IsCMField E]

/-- The torsion `𝓞 E`-module `(𝔸f E / Ô E)ⁿ`: `n`-tuples of finite adeles of `E` modulo integral
ones, an adelic model of `(E / 𝓞 E)ⁿ`. -/
def AdelicTorsion : Type :=
  (n → 𝔸f E) ⧸ Submodule.pi Set.univ fun _ : n ↦
      -- `Ô E` as an `𝓞 E`-subalgebra, then as a submodule
      Subalgebra.toSubmodule (R := 𝓞 E) ⟨(Ô E).toSubsemiring, (algebraMap_mem_Ô.2 ·.2)⟩
  deriving AddCommGroup, Module (𝓞 E)

namespace Variety

variable {E n} [DecidableEq n] (β : Matrix n n E) (x : GL n (𝔸f E))

/-! ### Frames and similitudes -/

/-- `x` is a frame for the form `β`: `xᴴ β x = ε • 1` (`ᴴ` is the conjugate transpose for the star
of `𝔸f E`) for a unit `ε` of `Ẑ = Ô ℚ`. -/
def IsFrameFor : Prop :=
  ∃ ε : (Ô ℚ)ˣ, xᴴ * β.map (algebraMap E (𝔸f E)) * x.1 = finAdeleIncl ℚ E ε • 1

/-- The rational number c is positive and x is a frame for the scalar matrix c·1: c·xᴴx = ε·1
for some unit ε of Ẑ. -/
@[simp]
abbrev IsScalarFrame (c : ℚ) : Prop := 0 < c ∧ IsFrameFor ((c : E) • 1) x

/-- Let `x` be a frame for `β`. Then `x g` is a frame for `c β` exactly when `g` is a frame for
the scalar form `c • 1`. -/
lemma IsFrameFor.mul_iff {c : E} {g : GL n (𝔸f E)} (hx : IsFrameFor β x) :
    IsFrameFor (c • β) (x * g) ↔ IsFrameFor (c • 1) g := by
  -- Both sides say that `c • gᴴ g` is a unit scalar, the left one after multiplication by the
  -- unit `ε`.
  obtain ⟨ε, hε⟩ : ∃ ε : (Ô ℚ)ˣ,
      (x.val)ᴴ * β.map (algebraMap E (𝔸f E)) * x.val = finAdeleIncl ℚ E ε • 1 := hx
  refine (Equiv.mulLeft ε⁻¹).exists_congr' fun δ ↦ ?_
  have h_unit : IsUnit (finAdeleIncl ℚ E ε) := (ε.isUnit.map (Ô ℚ).subtype).map _
  -- `-conjTranspose_mul` leaves `(x g)ᴴ … (x g)` to `gram_mul`; without it `simpa` gets stuck.
  simpa [map_smul', gram_mul, -conjTranspose_mul, hε, mul_smul, smul_comm c] using
    h_unit.smul_left_cancel

variable (E n)

/-- The number |n| times the number of infinite places of E; for a CM field E this is
|n|·[E⁺:ℚ], with E⁺ the maximal real subfield. -/
def abelianDim : ℕ := Fintype.card n * Fintype.card (InfinitePlace E)

/-- The unitary similitudes: the `g ∈ GL_n(𝔸f E)` with `c • gᴴ g = ε • 1` for some rational
`c > 0` and unit `ε` of `Ẑ`, that is, the frames of the scalar forms `c • 1`. Every finite
idele of `ℚ` has the form `ε / c`, so this says that `gᴴ g` is a scalar finite idele of `ℚ`. -/
def GU : Subgroup (GL n (𝔸f E)) :=
  Subgroup.ofDiv {g : GL n (𝔸f E) | ∃ c : ℚ, IsScalarFrame g c} ⟨1, 1, rfl, 1, by simp⟩ <| by
    rintro g ⟨c, hc, hg⟩ g' ⟨c', hc', hg'⟩
    -- By `IsFrameFor.mul_iff`, `g g'⁻¹` is a frame of `c'⁻¹ • c • 1` if `g'⁻¹` is one of
    -- `c'⁻¹ • 1`, that is, if `g' g'⁻¹ = 1` is one of `c'⁻¹ • c' • 1 = 1`.
    refine ⟨c'⁻¹ * c, by bound, ?_⟩
    simpa [mul_smul, hg.mul_iff, ← hg'.mul_iff, hc'.ne'] using ⟨1, by simp⟩

/-- The monoid of similitudes `g` whose inverse has integral entries, that is, which enlarge the
standard lattice. It is the intersection of `GU` with the inverse of the monoid of integral
matrices, with the carrier written out. -/
def GUPlus : Submonoid (GL n (𝔸f E)) :=
  Submonoid.copy (M := GL n (𝔸f E))
    ((GU E n).toSubmonoid ⊓ ((Ô E).matrix.toSubmonoid.comap (Units.coeHom (Matrix n n (𝔸f E))))⁻¹)
    {g ∈ GU E n | ∀ i j : n, g⁻¹ i j ∈ Ô E} rfl

end Variety

end New

namespace New.Variety

variable {E : Type} [Field E] [CMBase E] {n : Type} [Fintype n] [DecidableEq n]
  {β : Matrix n n E} (x : GL n (𝔸f E)) (z : GL n E) (J : Matrix n n ℂ)

lemma mem_GUPlus_iff {g : GL n (𝔸f E)} :
    g ∈ GUPlus E n ↔ g ∈ GU E n ∧ ∀ i j : n, (g⁻¹ : GL n (𝔸f E)) i j ∈ Ô E :=
  Iff.rfl

/-- The `𝓞 E`-linear map sending a vector of finite adeles to its class in `(𝔸f E / Ô E)ⁿ`. -/
def torsionClass {E : Type} [Field E] [NumberField E] : (n → 𝔸f E) →ₗ[𝓞 E] AdelicTorsion E n :=
  Submodule.mkQ _

/-- `E` is a subfield of `ℂ` through the embedding `Φ v₀` at the base place. -/
instance : Algebra E ℂ := (Φ v₀).toAlgebra

/-! ### Reflections and the signature condition -/

/-- The diagonal embedding of `GL n E` in `GL n (𝔸f E)`. -/
abbrev toFinGL {E : Type} [Field E] [NumberField E] : GL n E →* GL n (𝔸f E) :=
  GeneralLinearGroup.map (algebraMap E (𝔸f E))

/-- A reflection: `J = u wᵀ - 1` with `w ⬝ᵥ u = 2`, so `J` is `1` on the line of `u` and `-1` on
the kernel of `w`. -/
def IsReflection : Prop := ∃ u w : n → ℂ, w ⬝ᵥ u = 2 ∧ J = vecMulVec u w - 1

/-- `x` is a frame for `β`, the matrix `β.map (Φ w)` is positive definite for every infinite place
`w ≠ v₀`, and `β.map (Φ v₀) * J` is positive definite (the `ite` joins the two cases). -/
abbrev IsSignedFrameFor (β : Matrix n n E) : Prop :=
  IsFrameFor β x ∧ ∀ w : InfinitePlace E, (β.map (Φ w) * if w = v₀ then J else 1).PosDef

/-- `x` is a frame for some form `β` over `E` with the positivity conditions of
`IsSignedFrameFor`. -/
def IsSignedFrame : Prop := ∃ β : Matrix n n E, IsSignedFrameFor x J β

/-- The conjugate `Φ v₀ (z) * J * Φ v₀ (z)⁻¹` of the complex matrix `J` by `z` in `GL n E`, taken
through the embedding `Φ v₀`. -/
def ratConj : Matrix n n ℂ := toConjAct (z.map (Φ v₀)) • J

/-- Every conjugate of a reflection is a reflection. -/
lemma IsReflection.conj {J : Matrix n n ℂ} (z : GL n ℂ) (hJ : IsReflection J) :
    IsReflection (z.val * J * z⁻¹.val) := by
  obtain ⟨u, w, h_dot, rfl⟩ := hJ
  -- The new line is `z u` and the new form is `w z⁻¹`.
  refine ⟨z.val *ᵥ u, w ᵥ* z⁻¹.val, by simpa [dotProduct_mulVec] using h_dot, ?_⟩
  simp [mul_sub, sub_mul, mul_vecMulVec, vecMulVec_mul]

/-- Changing the form `β` to `zᴴ β z`, for `z` in `GL_n(E)`, corresponds to multiplying the frame by
`z` on the left. -/
lemma IsFrameFor.conj_iff : IsFrameFor (zᴴ * β * z.val) x ↔ IsFrameFor β (toFinGL z * x) := by
  -- `↓`: the rule must fire before `simp` pushes `map` through `ᴴ`.
  simp [IsFrameFor, ↓map_conjTranspose_mul_mul, mul_assoc]

/-- The signature condition is kept when `x` is multiplied by a rational matrix `z` on the left
and a similitude `g` on the right, and `J` is conjugated by `z` at the base place:
`ratConj z J = Φ v₀ (z) J Φ v₀ (z)⁻¹`, where `Φ w` is the complex embedding of `E` at the infinite
place `w` given by the CM type and `v₀` is the base place. -/
lemma IsSignedFrame.mul {x : GL n (𝔸f E)} {J : Matrix n n ℂ} (h : IsSignedFrame x J) (z : GL n E)
    {g : GL n (𝔸f E)} (hg_GU : g ∈ GU E n) :
    IsSignedFrame (toFinGL z * x * g) (ratConj z J) := by
  -- If `β` serves for `x` and `g` is a frame of the scalar form `c > 0`, then `c • z⁻¹ᴴ β z⁻¹`
  -- serves for `z x g`.
  obtain ⟨c, hc, hg⟩ := hg_GU
  obtain ⟨β, h_frame, h_pos⟩ := h
  have h_conj : IsFrameFor ((z⁻¹).valᴴ * β * (z⁻¹).val) (toFinGL z * x) :=
    (IsFrameFor.conj_iff (toFinGL z * x) z⁻¹).mpr (by simpa using h_frame)
  refine ⟨(c : E) • ((z⁻¹).valᴴ * β * (z⁻¹).val), h_conj.mul_iff.mpr hg, fun w ↦ ?_⟩
  -- At `w` the new matrix is the old positive definite one, scaled by `c` and transported by `z⁻¹`;
  -- at `v₀` the `z⁻¹` of the form cancels `z` in `z J z⁻¹`.
  have h_eq : ((c : E) • ((z⁻¹).valᴴ * β * (z⁻¹).val)).map (Φ w) * ite (w = v₀) (ratConj z J) 1 =
      star (z⁻¹.map (Φ w)).val * c • (β.map (Φ w) * ite (w = v₀) J 1) * (z⁻¹.map (Φ w)).val := by
    obtain rfl | hw := eq_or_ne w v₀ <;>
      simp [*, ratConj, units_smul_def, mul_assoc, ↓map_smul', ↓map_conjTranspose_mul_mul,
        ↓← val_map_apply, Rat.cast_smul_eq_qsmul, star_eq_conjTranspose]
  rw [h_eq]
  exact (z⁻¹.map (Φ w)).isUnit.posDef_star_left_conjugate_iff.mpr ((h_pos w).smul hc)

end New.Variety

end Frames

/-!
## Torsion classes of adelic vectors

* `New.torsionClass_eq_iff`: two vectors have the same class exactly when their difference is
  integral at every entry.
-/

namespace New

open Matrix Variety QuotientAddGroup

variable {E n : Type} [Field E] [NumberField E] {x y : n → 𝔸f E} {h : Matrix n n (𝔸f E)}

lemma torsionClass_eq_iff : torsionClass x = torsionClass y ↔ ∀ i : n, x i - y i ∈ Ô E :=
  eq_iff_sub_mem.trans (by aesop)

@[simp]
lemma torsionClass_eq_zero : torsionClass x = 0 ↔ ∀ i : n, x i ∈ Ô E :=
  torsionClass_eq_iff.trans (by simp)

/-- Induction on torsion classes: a property of all classes `torsionClass y` holds for every element
of `AdelicTorsion E n`. -/
lemma torsionClass_induction {p : AdelicTorsion E n → Prop} :
    (∀ y : n → 𝔸f E, p (torsionClass y)) → ∀ s : AdelicTorsion E n, p s := Quot.ind

variable [Fintype n]

lemma exists_nsmul_adelicTorsion_eq_zero (s : AdelicTorsion E n) : ∃ m : ℕ, m ≠ 0 ∧ m • s = 0 := by
  -- Take a common denominator of the entries of a representative (`exists_forall_mul_mem_Ô`).
  induction s using torsionClass_induction
  simp [← map_nsmul, exists_forall_mul_mem_Ô _]

/-- `AdelicTorsion E n` is discrete: the preimage of every set under `torsionClass` is open. -/
lemma isOpen_preimage_torsionClass (s : Set (AdelicTorsion E n)) :
    IsOpen (torsionClass (E := E) (n := n) ⁻¹' s) :=
  -- The quotient by the open subgroup Ôⁿ is discrete, so every subset of it is open.
  (discreteTopology (isOpen_set_pi (by simp) fun _ _ ↦ isOpen_Ô)).eq_bot.le s trivial

/-- An integral matrix maps vectors of torsion class zero to vectors of torsion class zero. -/
lemma torsionClass_mulVec_eq_zero (h_mem : ∀ i j : n, h i j ∈ Ô E) (hx : torsionClass x = 0) :
    torsionClass (h *ᵥ x) = 0 := by
  rw [torsionClass_eq_zero] at hx ⊢
  intro i
  simpa [mulVec, dotProduct] using sum_mem fun j _ ↦ mul_mem (h_mem i j) (hx j)

end New

/-!
## Points at infinite level, period lattices and period maps

The dictionary between adelic data and complex tori.
-/

section ModuliPoint

open NumberField Matrix

namespace New.Variety

variable (E n : Type) [Field E] [CMBase E] [Fintype n] [DecidableEq n]

/-! ### The real space and points at infinite level -/

/-- The space `(E ⊗ ℝ)ⁿ`, written as `n`-tuples of elements of the product of copies of `ℂ` over
the infinite places of `E`. -/
abbrev RealVectors : Type := n → InfinitePlace E → ℂ

/-- A complex point at infinite level: a finite adelic matrix `frame` (written `x` in the comments),
a complex matrix `reflection` (written `J` in the comments) that satisfies the signature condition
`New.Variety.IsSignedFrame` at `v₀` together with `x`, and marked vectors `markedPoint i` (written
`P i` in the comments) in `(E ⊗ ℝ)ⁿ`. -/
structure ModuliPoint (ν : ℕ) where
  /-- The finite adelic matrix `x`, which gives the lattice `Eⁿ ∩ x Ôⁿ`. -/
  frame : GL n (𝔸f E)
  /-- The complex matrix `J`, which gives the complex structure at the place `v₀`. -/
  reflection : Matrix n n ℂ
  /-- The marked points, given by representatives in `(E ⊗ ℝ)ⁿ`. -/
  markedPoint : Fin ν → RealVectors E n
  /-- `(x, J)` is a signed frame: `x` is a frame for some matrix `β` over `E` with `Φ_{v₀}(β) J` and
  all `Φ_v(β)`, `v ≠ v₀`, positive definite. -/
  isSignedFrame : IsSignedFrame frame reflection
  /-- `J` is a reflection: `1` on a line and `-1` on a complement. -/
  isReflection : IsReflection reflection

variable {E n} {V : Type} [FinComplexSpace.{0} V] (ℓ : Matrix n n ℂ)
  (Q : RealVectors E n ≃L[ℝ] V) {ν : ℕ} (K : Subgroup (GL n (𝔸f E))) (z : GL n E)
  (a b : ModuliPoint E n ν)

/-! ### Rational vectors, frames and lattices -/

/-- The ring homomorphism `x ↦ (Φ_v(x))_v` from `E` to the product of copies of `ℂ` over the
infinite places `v`, given by the CM type `Φ`. -/
abbrev cmEmbedding {E : Type} [Field E] [CMType E] : E →+* InfinitePlace E → ℂ := RingHom.pi Φ

variable {E : Type} [Field E] [CMType E] (β : Matrix n n E) in
/-- The action of a matrix `β` over `E` on `(E ⊗ ℝ)ⁿ`: `Φ_v(β)` at the infinite place `v`. -/
abbrev realVecAction :
    (n → InfinitePlace E → ℂ) →ₗ[InfinitePlace E → ℂ] n → InfinitePlace E → ℂ :=
  (β.map cmEmbedding).mulVecLin

/-- The additive map `Eⁿ → (∏_v ℂ)ⁿ` applying the CM embedding `x ↦ (Φ_v(x))_v` to each
coordinate. -/
@[simps!]
def toRealVectors {E : Type} [Field E] [CMType E] : (n → E) →+ n → InfinitePlace E → ℂ :=
  (cmEmbedding (E := E)).toAddMonoidHom.compLeft n

section

variable {E : Type} [Field E] [NumberField E] (g : GL n (𝔸f E))

/-- The coordinates of a rational vector in the adelic frame `g`: the `E`-linear map `y ↦ g⁻¹ y`
from `Eⁿ` to `n`-tuples of finite adeles. -/
def frameCoords : (n → E) →ₗ[E] n → 𝔸f E :=
  g⁻¹.1.mulVecLin.restrictScalars E ∘ₗ (Algebra.linearMap E (𝔸f E)).compLeft n

/-- The `𝓞 E`-linear map sending `y` in `Eⁿ` to the class of the adelic vector `g⁻¹ y` in the
torsion module `(𝔸f / Ô)ⁿ`. -/
@[simps! -isSimp apply]
def frameTorsionClass : (n → E) →ₗ[𝓞 E] AdelicTorsion E n :=
  torsionClass ∘ₗ (frameCoords g).restrictScalars (𝓞 E)

end

variable {E : Type} [Field E] [CMType E] (g : GL n (𝔸f E)) (S : AddSubgroup (AdelicTorsion E n))
  (Q : RealVectors E n ≃L[ℝ] V) in
/-- The image in `V`, under the CM embedding followed by `Q`, of the group of `y` in `Eⁿ` such that
the class of `g⁻¹ y` in `(𝔸f / Ô)ⁿ` lies in `S`. -/
def classLattice : Submodule ℤ V :=
  ((S.comap (frameTorsionClass g)).map
    ((Q : RealVectors E n →+ V).comp toRealVectors)).toIntSubmodule

variable {E : Type} [Field E] [CMType E] (g : GL n (𝔸f E)) in
/-- The lattice `Eⁿ ∩ g Ôⁿ`, as an additive subgroup of `(E ⊗ ℝ)ⁿ` through the CM embedding. -/
def frameLattice : AddSubgroup (RealVectors E n) :=
  (classLattice g ⊥ (ContinuousLinearEquiv.refl ℝ (RealVectors E n))).toAddSubgroup

/-- `Q` is a period map for the complex matrix `ℓ`: it carries the real endomorphism of
`(E ⊗ ℝ)ⁿ` given by `i ℓ` at the place `v₀` and by `i` at the other infinite places to
multiplication by `i` on `V`. -/
def IsPeriodMap : Prop :=
  ∀ w : RealVectors E n,
    Q (Complex.I • fun (i : n) (v : InfinitePlace E) ↦
        ((if v = v₀ then ℓ else 1) *ᵥ fun j : n ↦ w j v) i) =
      Complex.I • Q w

/-! ### The action on points and isomorphisms at a level -/

/-- The action on a point `a = (x, J, P)` of an adelic similitude `g` and of integers `α i` of
`E`: the result is `(x g, J, α i • P i)`, where `α i` acts on `(E ⊗ ℝ)ⁿ` through the CM type. -/
def ModuliPoint.act (g : GUPlus E n) (α : Fin ν → 𝓞 E := 1) : ModuliPoint E n ν where
  frame := a.frame * g
  reflection := a.reflection
  markedPoint i := cmEmbedding (α i).val • a.markedPoint i
  isSignedFrame := by
    -- `g` is a similitude, and the rational matrix `1` leaves `x` and `J` unchanged
    obtain ⟨hg_GU, -⟩ := mem_GUPlus_iff.mp g.prop
    simpa [ratConj] using a.isSignedFrame.mul 1 hg_GU
  isReflection := a.isReflection

/-- The matrix `z` in `GL n E` is an isomorphism from `a = (x, J, P)` to `b = (x', J', P')` at
level `K`: `x'⁻¹ z x` lies in `K`, `z J z⁻¹ = J'` through `Φ v₀`, and `z (P i) - P' i` lies in
the lattice of `x'`. -/
@[mk_iff]
structure ModuliPoint.IsLevelIso where
  /-- With `x`, `x'` the adelic matrices of `a` and `b`, the matrix `x'⁻¹ z x` lies in `K`. -/
  mem_level : b.frame⁻¹ * toFinGL z * a.frame ∈ (K : Subgroup (GL n (𝔸f E)))
  /-- `z` conjugates the reflection of `a` to that of `b`: `z J z⁻¹ = J'`, through `Φ v₀`. -/
  reflection_eq : ratConj z a.reflection = b.reflection
  /-- `z` carries each marked point of `a` to that of `b`, modulo the lattice of `x'`. -/
  sub_mem_lattice (i : Fin ν) : realVecAction z (a.markedPoint i) - b.markedPoint i ∈ frameLattice
    b.frame

end New.Variety

end ModuliPoint

/-!
## Lattices of rational vectors with given torsion class

Rational vectors `y ∈ Eⁿ` have a torsion class `New.Variety.frameTorsionClass g y`, the class of
`g⁻¹ y` in `(𝔸_f / Ô)ⁿ`, and an image `New.Variety.toRealVectors y` in `(E ⊗ ℝ)ⁿ` by the CM type.
-/

section PeriodLattice

open NumberField Matrix Function Submodule Set

namespace New.Variety

section

variable {E n : Type} [Field E] [NumberField E] [Fintype n] [DecidableEq n] {g : GL n (𝔸f E)}

/-! ### Torsion classes of rational vectors -/

/-- For the trivial frame `g = 1`, the vectors `y` of `Eⁿ` whose class in `(𝔸f / Ô)ⁿ` vanishes are
those with all coordinates in `𝓞 E` (the submodule `1` of `E` over `𝓞 E`). -/
lemma ker_frameTorsionClass_one : (frameTorsionClass (1 : GL n (𝔸f E))).ker = Submodule.pi ⊤ 1 := by
  -- An element of `E` that is integral at every finite place is integral.
  simp [SetLike.ext_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 E), frameTorsionClass,
    frameCoords]

/-- The coordinates `g⁻¹ y` of the rational vectors `y` are dense in `(𝔸f E)ⁿ`. -/
lemma denseRange_frameCoords : DenseRange (frameCoords g) :=
  -- `frameCoords g` is the coordinatewise map `E → 𝔸f E`, of dense range, followed by `g⁻¹`.
  (MulAction.surjective g⁻¹).denseRange.comp (.piMap fun _ ↦ denseRange_algebraMap_finAdele)
    (by fun_prop)

/-- Every class in `(𝔸f / Ô)ⁿ` is the class of `g⁻¹ y` for a rational vector `y`. -/
lemma frameTorsionClass_surjective : Surjective (frameTorsionClass g) := fun t ↦
  -- each fibre of `torsionClass` is open and nonempty, so it meets the dense range of
  -- `frameCoords g`
  denseRange_frameCoords.exists_mem_open (isOpen_preimage_torsionClass {t}) (Quot.exists_rep t)

end

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {g g' : GL n (𝔸f E)}
  {V : Type} {S : AddSubgroup (AdelicTorsion E n)} {A : Matrix n n E} {y : n → E}
  [FinComplexSpace V] {Q : RealVectors E n ≃L[ℝ] V}

/-! ### The embedding by the CM type and the lattices -/

omit [Fintype n] [DecidableEq n] in
lemma toRealVectors_injective : Injective (toRealVectors (E := E) (n := n)) :=
  (cmEmbedding (E := E)).injective.comp_left

omit [Fintype n] [DecidableEq n] in
@[simp]
lemma toRealVectors_smul (c : 𝓞 E) : toRealVectors (c • y) = cmEmbedding c.val • toRealVectors y :=
  funext fun i ↦ cmEmbedding.map_mul _ (y i)

/-- `x` lies in `classLattice g S Q` if and only if it is `Q` of the CM embedding of a rational
vector `y` whose class lies in `S`. -/
lemma mem_classLattice {x : V} :
    x ∈ classLattice g S Q ↔ ∃ y : n → E, frameTorsionClass g y ∈ S ∧ Q (toRealVectors y) = x :=
  .rfl

omit [DecidableEq n] in
@[simp↓]
lemma realVecAction_toRealVectors : realVecAction A (toRealVectors y) = toRealVectors (A *ᵥ y) :=
  (funext (cmEmbedding.map_mulVec _ _)).symm

/-- If `g'⁻¹ A g` is integral, then `A` maps the lattice `Eⁿ ∩ g Ôⁿ` into `Eⁿ ∩ g' Ôⁿ`. -/
lemma realVecAction_mem_frameLattice {P : RealVectors E n}
    (h_int : ∀ i j : n,
      ((g'⁻¹ : GL n (𝔸f E)) * A.map (algebraMap E (𝔸f E)) * (g : Matrix n n (𝔸f E))) i j ∈ Ô E)
    (hP : P ∈ frameLattice g) :
    realVecAction A P ∈ frameLattice g' := by
  -- `P` is the CM embedding of a rational vector `y` with `g⁻¹ y` integral.
  obtain ⟨y, hy, rfl⟩ : ∃ y : n → E,
      frameTorsionClass g y ∈ (⊥ : AddSubgroup (AdelicTorsion E n)) ∧ toRealVectors y = P := hP
  have hy_zero : torsionClass (frameCoords g y) = 0 := by simpa [frameTorsionClass_apply] using hy
  -- The coordinates of `A *ᵥ y` in the frame `g'` are the integral matrix of `h_int` applied to
  -- the coordinates of `y` in the frame `g`.
  have hAy : frameTorsionClass g' (A *ᵥ y) ∈ (⊥ : AddSubgroup (AdelicTorsion E n)) := by
    simpa [frameTorsionClass, frameCoords, LinearMap.compLeft, comp_def, RingHom.map_mulVec] using
      torsionClass_mulVec_eq_zero h_int hy_zero
  exact ⟨A *ᵥ y, hAy, realVecAction_toRealVectors.symm⟩

omit [DecidableEq n] in
@[simp]
lemma map_cmEmbedding_mulVec_apply (w : n → InfinitePlace E → ℂ) (i : n) (v : InfinitePlace E) :
    (A.map cmEmbedding *ᵥ w) i v = (A.map (Φ v) *ᵥ fun j : n ↦ w j v) i :=
  Finset.sum_apply v Finset.univ fun j : n ↦ A.map cmEmbedding i j * w j

omit [Fintype n] [DecidableEq n] in
/-- The image of `Eⁿ` under the CM embedding is dense in `(E ⊗ ℝ)ⁿ`. -/
lemma denseRange_toRealVectors : DenseRange (toRealVectors (E := E) (n := n)) :=
  .piMap fun _ ↦ denseRange_Φ

/-- The lattice `classLattice g ⊥ Q` of rational vectors `y` with `g⁻¹ y` integral is discrete in
`V`. -/
instance : DiscreteTopology (classLattice g ⊥ Q) := by
  -- A compact set `K` holds finitely many lattice points: they come from rational vectors in the
  -- compact adelic set `Q⁻¹ K × g Ô ^ n`, and the rational vectors form a lattice
  -- (`isCovolOneLattice_ratVectors`).
  refine continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact
    (tendsto_cofinite_cocompact_iff.mpr fun K hK ↦ ?_)
  let f (p : V × (n → 𝔸f E)) (i : n) : (InfinitePlace E → ℂ) × 𝔸f E :=
    (Q.symm p.fst i, ((g : Matrix n n (𝔸f E)) *ᵥ p.snd) i)
  have h_compact : IsCompact (f '' K ×ˢ {x : n → 𝔸f E | ∀ i : n, x i ∈ Ô E}) :=
    (hK.prod (isCompact_pi_infinite fun _ : n ↦ isCompact_Ô)).image_of_continuous _
  refine isCovolOneLattice_ratVectors.finite_preimage h_compact
    |>.image (fun y : n → E ↦ Q (toRealVectors y)) |>.preimage injOn_subtype_val |>.subset ?_
  rintro ⟨_, y, hy, rfl⟩ hy_mem
  -- `y` comes from the pair `(Q y, g⁻¹ y)` of the compact set, since `g⁻¹ y` is integral.
  have h_image : f (Q (toRealVectors y), frameCoords g y) =
      (toAdele (E := E)).toAddMonoidHom.compLeft n y := by
    aesop (add simp frameCoords)
  exact ⟨y, ⟨(Q (toRealVectors y), frameCoords g y), ⟨hy_mem, torsionClass_eq_zero.mp hy⟩, h_image⟩,
    rfl⟩

/-- A discrete `classLattice g S Q` is a full lattice in `V`: it spans `V` over `ℝ`. -/
instance [DiscreteTopology (classLattice g S Q)] : IsZLattice ℝ (classLattice g S Q) := by
  -- The real span is closed, so it is enough to reach the dense set of rational points; each has
  -- a nonzero multiple in the lattice, since its class is torsion. The `w` with `Q w` in the
  -- real span form the preimage of a finite-dimensional subspace, hence a closed set.
  have h_closed : IsClosed ((span ℝ (classLattice g S Q : Set V)).comap
      (Q : RealVectors E n →ₗ[ℝ] V) : Set (RealVectors E n)) :=
    Submodule.closed_of_finiteDimensional _
  refine ⟨eq_top_iff'.mpr (Q.surjective.forall.mpr
    (isClosed_property denseRange_toRealVectors h_closed fun y ↦ ?_))⟩
  obtain ⟨m, hm, hy⟩ := exists_nsmul_adelicTorsion_eq_zero (frameTorsionClass g y)
  -- `m y` is a lattice vector, and `Q (m y) = m Q y`
  have h_class : frameTorsionClass g (m • y) ∈ S := by simp only [map_nsmul, hy, zero_mem]
  have h_image : ((Q : RealVectors E n →+ V).comp toRealVectors) (m • y) =
      (m : ℝ) • Q (toRealVectors y) := by
    simp [map_nsmul, Nat.cast_smul_eq_nsmul, -nsmul_eq_mul]
  exact (smul_mem_iff (span ℝ (classLattice g S Q : Set V)) (Nat.cast_ne_zero.mpr hm)).mp
    (subset_span ⟨m • y, h_class, h_image⟩)

end New.Variety

end PeriodLattice

/-!
## Period maps: dimension, conjugation and complex multiplication

Linear algebra of a period map `Q : (E ⊗ ℝ)ⁿ ≃ V`, a real isomorphism from
`New.Variety.RealVectors E n` onto a complex vector space.

* `New.Variety.IsPeriodMap.ratConj_eq`: a complex linear map induced by `z ∈ GL n E` conjugates the
  two complex structures.
-/

section PeriodMultiplication

open Matrix NumberField Module Fintype

namespace New.Variety

variable (E : Type _) (n : Type) [Field E] [CMBase E] [Fintype n]

/-- The complex vector space `ℂ ^ (n − 1)` (`n` the number of indices), which contains the parameter
domains of the families of periods. -/
abbrev BallBase : Type := Fin (card n - 1) → ℂ

/-- The complex vector space `ℂ × ℂ ^ (n − 1) × ∏_v ℂ ^ n`, the product over the infinite places
`v` of `E` other than `v₀`. -/
abbrev BallFibre : Type _ := (ℂ × BallBase n) × ({v : InfinitePlace E // v ≠ v₀} → n → ℂ)

variable {E n} [DecidableEq n] {V V' : Type} [FinComplexSpace V] [FinComplexSpace V']
  {ℓ : Matrix n n ℂ} {Q : RealVectors E n ≃L[ℝ] V}

lemma smul_eq_re_smul_add_im_smul (a : ℂ) (z : V) : a • z = a.re • z + a.im • Complex.I • z := by
  match_scalars
  simp

omit [DecidableEq n] in
/-- If `(E ⊗ ℝ)ⁿ` is isomorphic over `ℝ` to the complex vector space `V`, the complex dimension of
`V` is `abelianDim E n`, the number of indices times the number of infinite places of `E`. -/
lemma finrank_eq_abelianDim (Q : RealVectors E n ≃L[ℝ] V) : finrank ℂ V = abelianDim E n := by
  -- Compare real dimensions: `2 dim_ℂ V` and `2` for each index and infinite place.
  have h_real : 2 * finrank ℂ V = card n * (card (InfinitePlace E) * 2) := by
    simpa [finrank_real_of_complex, finrank_pi_fintype] using Q.symm.finrank_eq
  rw [abelianDim]
  linarith

/-- `finrank_eq_abelianDim` for a period map `Q`, for dot notation; only the real isomorphism is
used. -/
lemma IsPeriodMap.finrank_eq_abelianDim (_hQ : IsPeriodMap ℓ Q) : finrank ℂ V = abelianDim E n :=
  New.Variety.finrank_eq_abelianDim Q

/-- Let `Q` and `R` be period maps for the matrices `ℓ` and `J` (hypotheses `hQ`, `hR`). If a
complex linear map `F` corresponds under them to a matrix `z ∈ GL n E` (hypothesis `hF`), then
`z ℓ z⁻¹ = J` at `v₀`. -/
lemma IsPeriodMap.ratConj_eq (hQ : IsPeriodMap ℓ Q) {J : Matrix n n ℂ}
    {R : RealVectors E n ≃L[ℝ] V'} (hR : IsPeriodMap J R) {z : GL n E} (F : V →ₗ[ℂ] V')
    (hF : ∀ w : RealVectors E n, F (Q w) = R (realVecAction z w)) :
    ratConj z ℓ = J := by
  -- It suffices to show `z * ℓ = J * z` at `v₀`, tested on a vector `u`.
  refine (z.map _).mul_inv_eq_iff_eq_mul.mpr (ext_iff_mulVec.mpr fun u ↦ ?_)
  -- Apply `R.symm ∘ F` to the period equation of `Q` at the vector that is `u` at every place, and
  -- read off the component at `v₀`. By `hF` the left side is `i z ℓ u`; by `ℂ`-linearity of `F`,
  -- `hF` and `hR` the right side is `i J z u`.
  have h_period := congrArg (fun (y : V) (i : n) ↦ R.symm (F y) i v₀) (hQ fun k : n ↦ u k • 1)
  simpa [hF, ← hR _, funext_iff] using h_period

/-- Multiplication by `c ∈ E ⊗ ℝ` (a complex number `c v` at each infinite place `v`), carried to
`V` by the period map `Q`, as a complex linear map; this is a ring homomorphism in `c`. -/
@[simps! apply_apply]
noncomputable def IsPeriodMap.complexMul (h : IsPeriodMap ℓ Q) :
    (InfinitePlace E → ℂ) →+* V →L[ℂ] V where
  toFun c :=
    { Q.arrowCongr Q (c • 1) with
      map_smul' a := by
        -- The map is real linear. By `h`, `I` corresponds under `Q` to matrices acting place by
        -- place, and these commute with the scalars `c v`.
        simp [Q.surjective.forall, ← h _, ← Q.symm.injective.eq_iff, smul_eq_re_smul_add_im_smul a,
          funext_iff,
          mulVec_apply_eq_sum, Finset.mul_sum, mul_left_comm] }
  map_one' := by simp [DFunLike.ext_iff]
  map_mul' := by simp [mul_smul, DFunLike.ext_iff]
  map_zero' := by simp [DFunLike.ext_iff]
  map_add' := by simp [add_smul, DFunLike.ext_iff]

end New.Variety

end PeriodMultiplication

/-! ## Linear maps to the adelic torsion module -/

section TorsionMatrix

open Set Matrix New NumberField Pointwise

variable {E n : Type} [Field E] [NumberField E] [Fintype n] (φ : (n → E) →ₗ[𝓞 E] AdelicTorsion E n)

/-- An `𝓞 E`-linear map `φ` from `Eⁿ` to the torsion module `(𝔸f / Ô)ⁿ` is given by a matrix
`h` of finite adeles: `φ y` is the class of `h y`. Here `frameCoords 1 y` is `y` as an adelic
vector. -/
lemma New.Variety.exists_matrix_torsionClass_eq [DecidableEq n] :
    ∃ h : Matrix n n (𝔸f E), ∀ y : n → E, torsionClass (h *ᵥ frameCoords 1 y) = φ y := by
  -- Column `j` of the matrix is an adelic vector `a` with
  -- `torsionClass (x • a) = φ (Pi.single j x)` for all `x`. It is found by compactness: these are
  -- closed conditions on a compact set, and any finitely many of them can be met by clearing
  -- denominators.
  have h_lift (j : n) (x : E) : ∃ a : n → 𝔸f E, torsionClass a = φ (Pi.single j x) :=
    Quot.exists_rep _
  choose r hr using h_lift
  -- `x ↦ torsionClass (r j x)` is `𝓞 E`-linear
  have h_smul (j : n) (c : 𝓞 E) (y : E) :
      torsionClass (c • r j y) = torsionClass (r j (c • y)) := by
    rw [map_smul, hr, hr, ← map_smul, ← Pi.single_smul]
  have h_column (j : n) :
      ∃ a : n → 𝔸f E, ∀ x : E, torsionClass (x • a) = torsionClass (r j x) := by
    -- the condition on `a` for one `x`
    let T (x : E) : Set (n → 𝔸f E) := {a | torsionClass (x • a) = torsionClass (r j x)}
    -- The compact set `C` is the coset of `r j 1` modulo the integral vectors.
    let C : Set (n → 𝔸f E) := r j 1 +ᵥ {x : n → 𝔸f E | ∀ i : n, x i ∈ Ô E}
    have h_compact : IsCompact C :=
      (isCompact_pi_infinite fun _ : n ↦ isCompact_Ô (E := E)).vadd (r j 1)
    -- the complement of `T x` is the preimage under `a ↦ x • a` of the other classes, an open set
    have h_closed (x : E) : IsClosed (T x) := isOpen_compl_iff.mp <|
      (isOpen_preimage_torsionClass {torsionClass (r j x)}ᶜ).preimage (by fun_prop)
    have h_finite (u : Finset E) : (C ∩ ⋂ x ∈ u, T x).Nonempty := by
      -- For a common denominator `m` of the finite set `u`, take `m • r j m⁻¹`.
      obtain ⟨m, hm⟩ :=
        IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) u fun x : E ↦ x
      let v : n → 𝔸f E := (m : 𝓞 E) • r j ((m : 𝓞 E) : E)⁻¹
      have h_coset : torsionClass v = torsionClass (r j 1) := by simp [v, h_smul, Algebra.smul_def]
      have h_cond (x : E) (hx : x ∈ u) : torsionClass (x • v) = torsionClass (r j x) := by
        obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = (m : 𝓞 E) • x := hm x hx
        -- `x • m = b` is integral, so the left side is the class of `r j (b • m⁻¹) = r j x`
        rw [smul_comm, ← smul_assoc, ← hb, algebraMap_smul, h_smul]
        simp [hb, Algebra.smul_def, ← division_def]
      exact ⟨v, ⟨v - r j 1, fun i ↦ torsionClass_eq_iff.mp h_coset i, add_sub_cancel (r j 1) v⟩,
        mem_biInter h_cond⟩
    obtain ⟨a, -, ha⟩ := h_compact.inter_iInter_nonempty T h_closed h_finite
    exact ⟨a, mem_iInter.mp ha⟩
  choose a ha using h_column
  refine ⟨aᵀ, fun y ↦ ?_⟩
  -- `aᵀ` applied to `y` is `∑ j, y j • a j`; expand `y` in the standard basis.
  calc torsionClass (aᵀ *ᵥ frameCoords 1 y) = ∑ j : n, torsionClass (y j • a j) := by
        simp [← map_sum, mulVec_eq_sum, frameCoords, transpose_transpose a]
    _ = ∑ j : n, φ (Pi.single j (y j)) := by simp only [ha, hr]
    _ = φ y := by rw [← map_sum φ, Finset.univ_sum_single]

end TorsionMatrix

end
