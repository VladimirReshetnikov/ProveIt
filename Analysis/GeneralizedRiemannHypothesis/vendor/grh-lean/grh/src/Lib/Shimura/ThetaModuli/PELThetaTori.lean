import Lib.Shimura.ThetaModuli.FlatClosure
import Lib.Shimura.ThetaNormality.NormalGeneration
import Lib.Shimura.Uniformisation.AdelicFrames

/-!
# PEL data, the adelic Riemann form and theta coordinates of polarised period maps

Let `E` be a CM field with ring of integers `𝓞 E`. The file sets up the PEL data for the moduli
problem of abelian schemes with an action of `𝓞 E`. It studies polarised period maps
`x : New.ThetaTori.PeriodMap` for such data `D`. With `T = D.dualTorsion` the kernel of the
polarisation, of odd order, and `L = D.lagrangian ≤ T` Lagrangian, the file constructs lattices over
groups of torsion classes and canonical theta coordinates `θ_t` for `t ∈ T`.

## Main definitions and results

* `New.PEL`: the data (rank, polarization type, level, theta structure) and their numerical
  conditions. `New.PEL.levelTorsion` is the torsion of the level.
* `New.PEL.HasClassLaws`: the laws required of the class of the embedding line bundle.
* `New.ThetaTori.PeriodMap`: a period map onto a complex vector space, with a polarisation whose
  Riemann form pulls back to `New.Variety.polarisationForm`.
* `New.Variety.fourierChar_polarisationForm`: if `gᴴ β g = a · 1`, its exponential is a value of
  `New.ψf` in the coordinates of `g`.
* `New.ThetaTori.PeriodMap.latticeOver`: the lattice in `V` over a group `S` of torsion classes.
  `New.ThetaTori.PeriodMap.periodLattice` is the lattice for `S = 0`, and its dual for the Riemann
  form is the lattice over `T` (`New.ThetaTori.PeriodMap.dualLattice_periodLattice`).
* `New.ThetaTori.PeriodMap.thetaCoord`: for `t ∈ T`, the normalised translate `θ_t` by a lift of `t`
  of the theta function `New.ThetaTori.PeriodMap.lagrangianTheta` for the
  lattice over `L`. That theta function is unique up to a scalar.
* `New.ThetaTori.PeriodMap.formSpan_eq_normBall`,
  `New.ThetaTori.PeriodMap.thetaCoord_vector_ne_zero`: at a valuation of good reduction, the forms
  of degree `r^j` in the `θ_t` fill a ball of theta functions. The `θ_t` have no common zero.

Notions from other files:
* `New.ψf`: the standard additive character of the finite adeles: ψ_f(x) = exp(2πi Tr_{E/ℚ}(a)) for
  any a in E with x − a integral.
* `New.Variety.toRealVectors`: the additive map E^n → (∏_v C)^n applying the CM-type embedding
  x ↦ (Φ_v(x))_v to each coordinate.
* `New.RealComplexForm.thetaSpace`: the entire functions f on V with
  f(z + l) = χ(l)·exp(B(l,z) + B(l,l)/2)·f(z) for l in L.
* `New.RealComplexForm.thetaShift`, `New.ThetaTori.normalizedShift`: the twisted translation
  f ↦ exp(−B(a,z) − B(a,a)/2)·f(z + a), and the same divided by the multiplier at a.
* `New.AdelicTorsion`, `New.Variety.frameTorsionClass`: the torsion O_E-module (𝔸_f / Ô)ⁿ of
  n-tuples of finite adeles of E modulo integral ones (an adelic model of (E / O_E)ⁿ), and the
  O_E-linear map sending y in Eⁿ to the class of the adelic vector g⁻¹y in it.

## Relation to the literature

Known; see `Lib.Shimura.IntegralModel.TowerExistence`, `Lib.Shimura.Uniformisation.AppellHumbert`
and `Lib.Shimura.ThetaModuli.UniversalFamily` for sources.
-/

noncomputable section

/-!
## PEL data, good primes and the class laws of a line bundle

* `New.PEL.IsGoodAt`: the ideals of `𝓞 E` at which the data are good.

`star` is complex conjugation, and `New.Pic` is written additively.
-/

namespace New

open NumberField Variety Submodule ThetaNull

variable {E : Type} [Field E] [CMBase E] {m : Type} [Fintype m]

/-- For ξ in E and vectors x, y of finite adeles of E, the finite adele ξ·∑ᵢ ȳᵢxᵢ. -/
def Variety.xiForm {E : Type} [Field E] [NumberField E] [IsCMField E]
    (ξ : E) (x y : m → 𝔸f E) : 𝔸f E := algebraMap E (𝔸f E) ξ * star y ⬝ᵥ x

variable (E)

/-- `r = c̄ c + 3 + ∑ₗ āₗ aₗ` in `𝓞 E` for some `r - 3` integers `aₗ` of `E` that span `𝓞 E` over
`ℤ`: the norm of `c` and the norms of the `aₗ` add up to `r - 3`. -/
def Variety.HasPadding (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (c : 𝓞 E) : Prop :=
  ∃ a : Fin (r - 3) → 𝓞 E,
    span ℤ (Set.range a) = ⊤ ∧ star c * c + 3 + ∑ l : Fin (r - 3), star (a l) * a l = r

/-- PEL data over the CM field `E`. (a) An integer `β` with `star β = 1 - β` and a level `𝔑` (field
`level`) with `𝔑 ≠ 0`. (b) An element `ξ` of `E`, which gives the pairing `ψf (ξ zᴴ y)` on vectors
with `rank` coordinates; the group `T` (field `dualTorsion`) of classes that pair trivially with all
integral vectors has odd order, and the subgroup `lagrangian` is its own annihilator and contains
the `r`-torsion. (c) Natural numbers `r` (field `paddedNorm`) with `r ≥ 3` and `i` (field
`exponentBound`) with a degree bound (`isCutDegree`), a bound by the level (`mem_torsionBy_level`)
and paddings of `1` and `β` to `r`. (d) Conditions on the images of `ξ` and `β` under the embeddings
of the CM type. The number `rank` of coordinates is not zero. -/
structure PEL where
  /-- An integer β of E with β̄ = 1 - β (field `star_beta`). -/
  β : 𝓞 E
  /-- The level 𝔑, an integer of E. -/
  level : 𝓞 E
  /-- The element ξ of E that defines the form tr(ξ yᴴ x). -/
  ξ : E
  /-- The number of coordinates of the vectors. -/
  rank : ℕ
  /-- The natural number r to which the norms are padded. -/
  paddedNorm : ℕ
  /-- The bound i on the exponents j of the degrees r ^ j that have to be read. -/
  exponentBound : ℕ
  /-- The group T of classes that pair trivially with all integral vectors (field
  `mem_dualTorsion`). -/
  dualTorsion : AddSubgroup (AdelicTorsion E (Fin rank))
  /-- A Lagrangian subgroup L of the torsion module. -/
  lagrangian : AddSubgroup (AdelicTorsion E (Fin rank))
  /-- The conjugate of β is 1 - β. -/
  star_beta : star β = 1 - β
  /-- The number r is at least 3. -/
  three_le_paddedNorm : 3 ≤ paddedNorm
  /-- The level is not zero. -/
  level_ne_zero : level ≠ 0
  /-- A monomial ideal in variables indexed by T that leaves at most `thetaRanks T r j` monomials of
  degree r ^ j for all j ≤ i does so for all j. Here `thetaRanks T r j` is the integer square root
  of the number of y with r ^ j • y ∈ T. -/
  isCutDegree : IsCutDegree dualTorsion exponentBound paddedNorm (thetaRanks dualTorsion paddedNorm)
  /-- The level 𝔑 kills every y with r ^ j • y in T for some j ≤ i. -/
  mem_torsionBy_level (j : ℕ) (hj : j ≤ exponentBound) (y : AdelicTorsion E (Fin rank))
    (hy : paddedNorm ^ j • y ∈ dualTorsion) :
    y ∈ torsionBy (𝓞 E) (AdelicTorsion E (Fin rank)) level
  /-- The group T has odd order (in particular it is finite). -/
  odd_card : Odd (Nat.card dualTorsion)
  /-- The class of y lies in T exactly when ψ_f(ξ zᴴ y) = 1 for every integral vector z. -/
  mem_dualTorsion (y : Fin rank → 𝔸f E) :
    torsionClass y ∈ dualTorsion ↔ ∀ z : Fin rank → 𝔸f E,
      torsionClass z = 0 → ψf E (xiForm ξ y z) = 1
  /-- L is its own annihilator: the class of y lies in L exactly when ψ_f(ξ zᴴ y) = 1 for every z
  whose class lies in L. -/
  mem_lagrangian (y : Fin rank → 𝔸f E) :
    torsionClass y ∈ lagrangian ↔
      ∀ z : Fin rank → 𝔸f E, torsionClass z ∈ lagrangian → ψf E (xiForm ξ y z) = 1
  /-- L contains the r-torsion. -/
  torsion_mem_lagrangian (s : AdelicTorsion E (Fin rank)) (hs : paddedNorm • s = 0) : s ∈ lagrangian
  /-- r is 1 + 3 plus the norms ā a of r - 3 integers that span the integers of E over ℤ. -/
  hasPadding_one : HasPadding E paddedNorm 1
  /-- r is β̄ β + 3 plus the norms ā a of r - 3 integers that span the integers of E over ℤ. -/
  hasPadding_beta : HasPadding E paddedNorm β
  /-- The rank is not zero. -/
  nonempty : Nonempty (Fin rank)
  /-- Under each embedding of the CM type, ξ has positive imaginary part. -/
  xi_im_pos (v : InfinitePlace E) : 0 < (Φ v ξ).im
  /-- Under each embedding of the CM type, ξ has real part zero. -/
  xi_re_eq_zero (v : InfinitePlace E) : (Φ v ξ).re = 0
  /-- Away from the base place v₀, the embedding takes β to the image of β̄ at v₀. -/
  emb_beta_eq_of_ne (v : InfinitePlace E) (hv : v ≠ v₀) : Φ v (β : E) = Φ v₀ (star (β : E))
  /-- At the base place, β and β̄ have different images. -/
  emb_star_beta_ne : Φ v₀ (star (β : E)) ≠ Φ v₀ (β : E)

namespace PEL

variable {E} (D : PEL E)

/-- Under each embedding of the CM type, `ξ` lies on the positive imaginary axis. -/
lemma xi_im_pos_and_re_eq_zero (v : InfinitePlace E) : 0 < (Φ v D.ξ).im ∧ (Φ v D.ξ).re = 0 :=
  ⟨D.xi_im_pos v, D.xi_re_eq_zero v⟩

/-- The index type `Fin D.rank` of the coordinates. -/
abbrev Index : Type := Fin D.rank

/-- The `𝓞 E`-submodule of classes in the torsion module killed by the level `𝔑`. -/
def levelTorsion : Submodule (𝓞 E) (AdelicTorsion E D.Index) :=
  torsionBy (𝓞 E) (AdelicTorsion E D.Index) D.level

/-- Every class in `T` is killed by the level `𝔑` (the case `j = 0` of `mem_torsionBy_level`). -/
lemma dualTorsion_le_levelTorsion : D.dualTorsion ≤ D.levelTorsion.toAddSubgroup :=
  fun y hy ↦ D.mem_torsionBy_level 0 (Nat.zero_le D.exponentBound) y (by simpa using hy)

attribute [instance] nonempty

/-- `T` is finite, as its order is odd and so nonzero. -/
instance : Finite D.dualTorsion := Nat.finite_of_card_ne_zero D.odd_card.pos.ne'

/-- The data `D` are good at the ideal `w` of `𝓞 E` when the following hold. Neither `r` nor the
order of `T` lies in `w`. There are a prime number `p` in `w` and an integer `b` congruent to `β`
modulo `w` such that `β - b` and `star β - b` are coprime. The ideal of `𝔑` and `w` times the ideal
of `p` and `star β - b` together generate the unit ideal. Some finite place `v ≠ w` contains both
`p` and `β - b`. -/
def IsGoodAt (w : Ideal (𝓞 E)) : Prop :=
  -- (a) `w` contains neither `r` nor the order of `T`
  (↑D.paddedNorm ∉ w ∧ ↑(Nat.card D.dualTorsion) ∉ w) ∧
  -- (b) `w` contains a prime number `p` and `β - b`, `b` an integer
  ∃ (p : ℕ) (b : ℤ),
    Nat.Prime p ∧ ↑p ∈ w ∧ D.β - (b : ℤ) ∈ w ∧
    -- (c) `β - b` is coprime to its conjugate
    IsCoprime (D.β - b) (star D.β - b) ∧
    -- (d) the level is coprime to the product of `w` and the ideal `(p, star β - b)`
    Ideal.span {D.level} ⊔ w * Ideal.span {↑p, star D.β - b} = ⊤ ∧
    -- (e) a nonzero prime other than `w` also contains `p` and `β - b`
    ∃ v : FinPlace E, v ≠ w ∧ ↑p ∈ v.asIdeal ∧ D.β - b ∈ v.asIdeal

/-- The laws of a class `c` in the Picard group of `A`, for all points `x`, `y` of `A` with values
in a scheme `T` over `S`: (a) the parallelogram law `New.Pic.ParallelogramLaw`; (b)
`⟨β x, y⟩ = ⟨x, (1 - β) y⟩` for the pairing `New.Pic.pairing`, where `1 - β = star β`; (c) the
pull-back of `c` along `y` is `⟨β y, y⟩` plus its pull-back along `0` (`x` plays no part here). The
three laws are read with `HasClassLaws.parallelogramLaw`, `pairing_smul_beta` and `atPoint_eq`. -/
def HasClassLaws {S : AlgebraicGeometry.Scheme} {A : CategoryTheory.Over S} [AddObj (S := S) A]
    [ModuleObj (𝓞 E) A] (c : Pic A.left) : Prop :=
  -- (a) the parallelogram law
  c.ParallelogramLaw ∧
  ∀ ⦃T : CategoryTheory.Over S⦄ (x y : T ⟶ A),
    -- (b) `1 - β`, the conjugate of `β`, is adjoint to `β`
    c.pairing (D.β • x) y = c.pairing x ((1 - D.β) • y) ∧
    -- (c) the pairing determines the class up to its value at `0`
    c.atPoint y = c.pairing (D.β • y) y + c.atPoint 0

namespace HasClassLaws

variable {D : PEL E} {S : AlgebraicGeometry.Scheme} {A : CategoryTheory.Over S} [AddObj (S := S) A]
  [ModuleObj (𝓞 E) A] {c : Pic A.left}

lemma parallelogramLaw (h_laws : D.HasClassLaws c) : c.ParallelogramLaw := h_laws.1

/-- For a class with the laws `New.PEL.HasClassLaws`, `1 - β` is adjoint to `β` for the pairing. -/
lemma pairing_smul_beta (h_laws : D.HasClassLaws c) {T : CategoryTheory.Over S} (x y : T ⟶ A) :
    c.pairing (D.β • x) y = c.pairing x ((1 - D.β) • y) :=
  (h_laws.right x y).left

/-- For a class with the laws `New.PEL.HasClassLaws`, the pull-back along `y` is `⟨β y, y⟩` plus the
pull-back along `0`. -/
lemma atPoint_eq (h_laws : D.HasClassLaws c) {T : CategoryTheory.Over S} (y : T ⟶ A) :
    c.atPoint y = c.pairing (D.β • y) y + c.atPoint 0 :=
  (h_laws.right y y).right

end HasClassLaws

end PEL

end New

/-!
## The Riemann form on rational vectors and its adelic character value

* `New.Variety.polarisationForm`: the form `(y, z) ↦ Σ_v 2 Re(Φ_v(ξ) z_vᴴ Φ_v(β) y_v)`.
-/

section RiemannFormAdelic

open Matrix FourierTransform Finset AddChar

namespace New.Variety

variable {E : Type} [Field E] [CMBase E] (D : PEL E)

/-- For a matrix β over E, the real bilinear form (y, z) ↦ Σ_v 2 Re(Φ_v(ξ)·z_vᴴ Φ_v(β) y_v) on
(E ⊗ ℝ)ⁿ, with ξ from the datum D: a map
`RealVectors E D.Index →ₗ[ℝ] RealVectors E D.Index →ₗ[ℝ] ℝ`. -/
noncomputable def polarisationForm (β : Matrix D.Index D.Index E) := by
  apply LinearMap.mk₂ ℝ fun y z : RealVectors E D.Index ↦
    ∑ v, 2 * (Φ v D.ξ * star (z · v) ⬝ᵥ β.map (Φ v) *ᵥ (y · v)).re
  -- Real bilinearity: expand the matrix products into sums and compare term by term.
  all_goals
    simp [mulVec, dotProduct, mul_sum, -sum_sub_distrib, ← sum_add_distrib]
    grind

/-- A polarised period map for the frame `g` and the matrix `ℓ`: a period map Q = `realEquiv` onto
`V`, a matrix β = `formMatrix` over `E` with gᴴ β g a scalar unit of Ẑ, and a form
B = `automorphyForm` with symmetric real part whose Riemann form is positive and pulls back under Q
to `New.Variety.polarisationForm D formMatrix`. -/
structure _root_.New.ThetaTori.PeriodMap (g : GL D.Index (𝔸f E)) (ℓ : Matrix D.Index D.Index ℂ)
    (V : Type) [FinComplexSpace V] where
  /-- The matrix over E of the form that polarises the torus. -/
  formMatrix : Matrix D.Index D.Index E
  /-- The period map, a real linear isomorphism from (E ⊗ ℝ)ⁿ onto V. -/
  realEquiv : RealVectors E D.Index ≃L[ℝ] V
  /-- The form in the factor of automorphy on the period lattice `classLattice g ⊥ realEquiv`: real
  linear in the first variable, complex linear in the second. -/
  automorphyForm : ThetaTori.LatticeForm (classLattice g ⊥ realEquiv)
  /-- g is a frame for β: gᴴ β g is a scalar unit of Ẑ. -/
  isFrameFor : IsFrameFor formMatrix g
  /-- Q is complex linear for the structure that is i ℓ at v₀ and i at the other places. -/
  isPeriodMap : IsPeriodMap ℓ realEquiv
  /-- The real part of B is symmetric. -/
  re_symm (u v : V) : (automorphyForm u v).re = (automorphyForm v u).re
  /-- Through Q, the Riemann form of B is the trace form tr(ξ zᴴ β y) on (E ⊗ ℝ)ⁿ. -/
  riemannForm_eq (y z : RealVectors E D.Index) :
      automorphyForm.riemannForm (realEquiv y) (realEquiv z) = polarisationForm D formMatrix y z
  /-- The Riemann form of B is positive: its value at (u, i u) is positive for u ≠ 0. -/
  isPosRiemann : IsPosRiemann automorphyForm

variable {D : PEL E} {β : Matrix D.Index D.Index E} {g : GL D.Index (𝔸f E)}

/-- For a unit ν of `New.Ô ℚ` and a finite adele a of E, `New.ψf` is trivial at ν·a exactly when it
is trivial at a. So multiplying by a unit of Ẑ does not change the kernel of `New.ψf`. -/
lemma ψf_unit_mul_eq_one_iff (ν : (Ô ℚ)ˣ) {a : 𝔸f E} :
    ψf E (finAdeleIncl ℚ E ν * a) = 1 ↔ ψf E a = 1 := by
  -- The integers are dense in `Ô ℚ`, and `ψf E (n * a) = ψf E a ^ n` for an integer `n`. So the
  -- kernel of `ψf E` is stable under `Ô ℚ`; apply this to `ν` and to `ν⁻¹`.
  have h_mul_eq_one (c : Ô ℚ) {b : 𝔸f E} (hb : ψf E b = 1) :
      ψf E (finAdeleIncl ℚ E c * b) = 1 := by
    refine denseRange_algebraMap_Ô.eq (f := fun x : Ô ℚ ↦ ψf E (finAdeleIncl ℚ E x * b)) (g := 1) ?_
      (x := c)
    -- On the integers: `ψf E (n • b) = ψf E b ^ n = 1`.
    have h_int : ∀ n : ℤ, ψf E (n • b) = 1 := fun n ↦ by rw [map_zsmul_eq_zpow, hb, _root_.one_zpow]
    simp [← zsmul_eq_mul, reindex_equiv Rat.ringOfIntegersEquiv.symm, h_int]
  have h_cancel : finAdeleIncl ℚ E (ν⁻¹ : (Ô ℚ)ˣ) * (finAdeleIncl ℚ E ν * a) = a := by
    simp [← mul_assoc, ← map_mul, ← Subring.coe_mul]
  refine ⟨fun h_unit ↦ ?_, h_mul_eq_one ν⟩
  rw [← h_cancel]
  exact h_mul_eq_one (ν⁻¹ : (Ô ℚ)ˣ) h_unit

/-- On rational vectors y, z in Eⁿ, `New.Variety.polarisationForm D β` is the trace from E to ℚ of
ξ·zᴴβy. Here ξ comes from the datum D. -/
@[simp]
lemma polarisationForm_toRealVectors (y z : D.Index → E) :
    polarisationForm D β (toRealVectors y) (toRealVectors z) =
      Algebra.trace ℚ E (D.ξ * star z ⬝ᵥ β *ᵥ y) := by
  simp [polarisationForm, trace_eq_sum_Φ, mulVec, dotProduct]

private lemma frameCoords_eq_mulVec (y : D.Index → E) :
    frameCoords g y = (g⁻¹).val *ᵥ (algebraMap E (𝔸f E) ∘ y) :=
  rfl

/-- If `gᴴ β g = a • 1` for a finite adele `a` of `E`, then for rational vectors `y, z` in `Eⁿ` the
value of `𝐞` at `polarisationForm D β y z`, that is exp(2πi Tr_{E/ℚ}(ξ zᴴ β y)), is
ψ_f(a ξ (g⁻¹z)ᴴ (g⁻¹y)). Here ξ comes from the datum `D`. -/
lemma fourierChar_polarisationForm {a : 𝔸f E}
    (h_gram : g.valᴴ * β.map (algebraMap E (𝔸f E)) * g.val = a • 1) (y z : D.Index → E) :
    𝐞 (polarisationForm D β (toRealVectors y) (toRealVectors z)) =
      ψf E (a * xiForm D.ξ (frameCoords g y) (frameCoords g z)) := by
  -- Both sides are values of `ψf E`; compare their arguments in the finite adeles.
  rw [polarisationForm_toRealVectors, ← ψf_coe]
  congr 1
  -- By `h_gram`, the adelic matrix of `β` is `a • (g⁻¹ᴴ * g⁻¹)`.
  have h_beta : β.map (algebraMap E (𝔸f E)) = a • ((g⁻¹).valᴴ * (g⁻¹).val) := by
    rw [← gram_inv_of_gram_eq h_gram]
    simp
  calc algebraMap E (𝔸f E) (D.ξ * star z ⬝ᵥ β *ᵥ y)
      = algebraMap E (𝔸f E) D.ξ * star (algebraMap E (𝔸f E) ∘ z) ⬝ᵥ
          β.map (algebraMap E (𝔸f E)) *ᵥ (algebraMap E (𝔸f E) ∘ y) := by
        simp [dotProduct, RingHom.map_mulVec]
    _ = a * (algebraMap E (𝔸f E) D.ξ * star (algebraMap E (𝔸f E) ∘ z) ⬝ᵥ
          ((g⁻¹).valᴴ * (g⁻¹).val) *ᵥ (algebraMap E (𝔸f E) ∘ y)) := by
        simp [h_beta, smul_mulVec, mul_left_comm a]
    _ = a * xiForm D.ξ (frameCoords g y) (frameCoords g z) := by
        rw [xiForm, frameCoords_eq_mulVec, frameCoords_eq_mulVec, star_mulVec_dotProduct,
          mulVec_mulVec]

end New.Variety

end RiemannFormAdelic

/-!
## Lattices of polarised period maps and the theta coordinates θ_t

* `New.ThetaTori.ThetaTorus`: period maps on which `𝓞 E` acts by the standard diagonal maps.

The multiplier `New.ThetaTori.PeriodMap.multiplier` is `χ(u) = exp (π i e(β₁ u, u))`, with `e` the
Riemann form of `x.automorphyForm` and `β₁ = D.rescaledBeta`, for which `β₁ + β̄₁ = 1`. The phase
`x.automorphyForm.riemannPhase u w` is exp(2πi·e(u, w)).
-/

namespace New

open AddSubgroup Submodule Variety Complex Function NumberField AddChar Set thetaSpace
  IsAppellHumbert PEL

variable {E n : Type} [Field E] [CMBase E] [Fintype n] [DecidableEq n] (D : PEL E)

/-! ### Lifts of torsion classes, the action of `𝓞 E` and theta tori -/

/-- The integer β₁ = |T|β − ⌊|T|/2⌋ of E. -/
def PEL.rescaledBeta : 𝓞 E := Nat.card D.dualTorsion • D.β - ↑(Nat.card D.dualTorsion / 2)

/-- The Lagrangian subgroup `L` lies in `T`. -/
lemma PEL.lagrangian_le_dualTorsion : D.lagrangian ≤ D.dualTorsion := by
  -- A class of `L` pairs trivially with every class of `L`, among them the class `0` of the
  -- integral vectors; so it lies in `T`.
  refine torsionClass_induction fun (y : D.Index → 𝔸f E) (hy : torsionClass y ∈ D.lagrangian) ↦ ?_
  exact (D.mem_dualTorsion y).mpr fun z hz ↦ (D.mem_lagrangian y).mp hy z (by simp [hz])

/-- The `D.paddedNorm`-torsion subgroup of the torsion module indexed by `D.Index`: the classes `s`
with `D.paddedNorm • s = 0`. -/
def PEL.rTorsion : AddSubgroup (AdelicTorsion E D.Index) :=
  AddSubgroup.comap (nsmulAddMonoidHom D.paddedNorm) ⊥

namespace ThetaTori

variable {D : PEL E} {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ} {y z : D.Index → E}
  {V : Type} [FinComplexSpace V] (x : PeriodMap D g ℓ V) (s t : D.dualTorsion) {u : V}
  {S S' : AddSubgroup (AdelicTorsion E D.Index)}

/-- A chosen vector `y` of `Eⁿ` with `frameTorsionClass g y = s`, normalised so that the class `0`
is represented by `0`. -/
def ratLift (g : GL n (𝔸f E)) (s : AdelicTorsion E n) : n → E :=
  surjInv (frameTorsionClass_surjective (g := g)) s -
    surjInv (frameTorsionClass_surjective (g := g)) 0

@[simp]
lemma frameTorsionClass_ratLift (s : AdelicTorsion E D.Index) :
    frameTorsionClass g (ratLift g s) = s := by
  simp [ratLift, surjInv_eq]

/-- The ring homomorphism from O_E to the complex endomorphisms of V given by multiplication,
transported through the period map. -/
def PeriodMap.intAction : 𝓞 E →+* V →L[ℂ] V :=
  x.isPeriodMap.complexMul.comp (cmEmbedding.comp (algebraMap (𝓞 E) E))

variable (D g ℓ V) in
/-- A theta torus is a polarised period map in which ℓ is a reflection and multiplication by c̄ is
adjoint to multiplication by c for B. Also, some isomorphism V ≅ `New.Variety.BallFibre` makes each
a ∈ O_E act by Φ_{v₀}(a) on the line, by its conjugate on the complement, and by Φ_w(a) at each
place w ≠ v₀. -/
structure ThetaTorus extends PeriodMap D g ℓ V where
  /-- The matrix `ℓ` is a reflection. -/
  reflection : IsReflection ℓ
  /-- The adjoint for `automorphyForm` of multiplication by `c ∈ 𝓞 E` is multiplication by
  `star c`. -/
  adjoint (c : 𝓞 E) (y z : V) :
      automorphyForm (toPeriodMap.intAction c y) z = automorphyForm y
        (toPeriodMap.intAction (star c) z)
  /-- In suitable coordinates `a ∈ 𝓞 E` acts diagonally: at `v₀` by `Φ v₀ a` on the line and by its
  conjugate on the complement, and by `Φ w a` at each place `w ≠ v₀`. -/
  exists_std_equiv : ∃ e : V ≃ₗ[ℂ] BallFibre E D.Index, ∀ a : 𝓞 E,
    e.1 ∘ₗ toPeriodMap.intAction a ∘ₗ e.symm.1 =
      .prodMap (.prodMap (Φ v₀ a.val • 1) (star (Φ v₀ a.val) • 1)) (.piMap (Φ ·.1 a • 1))

namespace PeriodMap

/-- For a subgroup S of the torsion module, the image in V under the period map of the vectors
of E^n whose class with respect to g lies in S. -/
abbrev latticeOver (S : AddSubgroup (AdelicTorsion E D.Index)) : Submodule ℤ V :=
  classLattice g S x.realEquiv

/-! ### Lattices over groups of torsion classes and their duals -/

/-- The period lattice in V: the image under the period map of the vectors y in E^n with g⁻¹y
integral. -/
abbrev periodLattice : Submodule ℤ V := x.latticeOver ⊥

/-- The function on V sending u to exp(πi·e(β₁u, u)), where e is the Riemann form of B and β₁ =
|T|β − ⌊|T|/2⌋. -/
abbrev multiplier : V → ℂ := canonicalMultiplier x.automorphyForm (x.intAction D.rescaledBeta)

/-- For y in E^n, the point of V obtained by applying the period map of x to the image of y in the
real vectors (E ⊗ ℝ)^n. -/
abbrev periodPoint (y : D.Index → E) : V := x.realEquiv (toRealVectors y)

/-- For a torsion class s, the vector of V that is the image under the period map of the chosen
representative of s in E^n. -/
def torsionLift (s : AdelicTorsion E D.Index) : V := x.periodPoint (ratLift g s)

attribute [instance] isPosRiemann

@[simp]
lemma torsionLift_zero : x.torsionLift 0 = 0 := by simp [ratLift, torsionLift]

/-- The image `x.periodPoint y` of a rational vector lies in the lattice over `S` exactly when
its class `frameTorsionClass g y` lies in `S`. -/
@[simp]
lemma mem_latticeOver : x.periodPoint y ∈ x.latticeOver S ↔ frameTorsionClass g y ∈ S :=
  mem_map_iff_mem (f := (x.realEquiv : RealVectors E D.Index →+ V).comp toRealVectors)
    (by simp [toRealVectors_injective])

/-- The lattice over a group of torsion classes grows with the group. -/
lemma latticeOver_mono (h_le : S ≤ S') : x.latticeOver S ≤ x.latticeOver S' :=
  AddSubgroup.toIntSubmodule.monotone (AddSubgroup.map_mono (AddSubgroup.comap_mono h_le))

/-- For a subgroup `S` of the torsion module `(𝔸f E / Ô E)ⁿ`, `x.latticeOver S` is the image in `V`,
under the period map, of the vectors of `Eⁿ` whose class with respect to `g` lies in `S`. If `S'` is
the annihilator of `S` for the adelic pairing `(y, w) ↦ ψ_f(ξ wᴴ y)`, then the vectors of
`x.latticeOver ⊤` lying in the dual of `x.latticeOver S` for the Riemann form of `x.automorphyForm`
are exactly those of `x.latticeOver S'`. -/
lemma dualLattice_inf_latticeOver_top
    (h_ann : ∀ y : D.Index → 𝔸f E,
      torsionClass y ∈ S' ↔ ∀ w : D.Index → 𝔸f E, torsionClass w ∈ S → ψf E (xiForm D.ξ y w) = 1) :
    x.automorphyForm.dualLattice (L := x.latticeOver S) ⊓ x.latticeOver ⊤ = x.latticeOver S' := by
  ext u
  -- Annihilating the vectors over `S` is a closed condition, so rational vectors (dense) suffice.
  have h_dense (y : D.Index → 𝔸f E)
      (hy : ∀ a : D.Index → E,
        torsionClass (frameCoords g a) ∈ S → ψf E (xiForm D.ξ y (frameCoords g a)) = 1) :
      ∀ w : D.Index → 𝔸f E, torsionClass w ∈ S → ψf E (xiForm D.ξ y w) = 1 :=
    isClosed_property denseRange_frameCoords (isClosed_imp (isOpen_preimage_torsionClass S.carrier)
      (isClosed_eq (by fun_prop [xiForm]) continuous_one)) hy
  -- On rational vectors, the Riemann form is integral exactly when the adelic pairing is trivial.
  have h_riem (a b : D.Index → E) :
      Real.fourierChar (x.automorphyForm.riemannForm (x.periodPoint a) (x.periodPoint b)) = 1 ↔
        ψf E (xiForm D.ξ (frameCoords g a) (frameCoords g b)) = 1 := by
    rw [x.riemannForm_eq, fourierChar_polarisationForm x.isFrameFor.choose_spec,
      ψf_unit_mul_eq_one_iff]
  -- Both sides consist of images `x.periodPoint a` of rational vectors `a`; compare the conditions.
  constructor
  · rintro ⟨hu_dual, hu_top⟩
    obtain ⟨a, -, rfl⟩ := mem_classLattice.mp hu_top
    have h_pair : ∀ b : D.Index → E, torsionClass (frameCoords g b) ∈ S →
        ψf E (xiForm D.ξ (frameCoords g a) (frameCoords g b)) = 1 := by
      intro b hb
      obtain ⟨n, hn⟩ : ∃ n : ℤ, x.automorphyForm.riemannForm (x.periodPoint a) (x.periodPoint b) =
        n :=
        hu_dual (x.periodPoint b) (x.mem_latticeOver.mpr (by rwa [frameTorsionClass_apply]))
      exact (h_riem a b).mp (fourierChar_eq_one_iff.mpr ⟨n, hn⟩)
    rw [x.mem_latticeOver, frameTorsionClass_apply]
    exact (h_ann _).mpr (h_dense _ h_pair)
  · intro hu
    obtain ⟨a, ha, rfl⟩ := mem_classLattice.mp hu
    have ha_ann : ∀ w : D.Index → 𝔸f E,
        torsionClass w ∈ S → ψf E (xiForm D.ξ (frameCoords g a) w) = 1 :=
      (h_ann (frameCoords g a)).mp (by rwa [← frameTorsionClass_apply])
    refine ⟨fun l hl ↦ ?_, x.mem_latticeOver.mpr (AddSubgroup.mem_top _)⟩
    obtain ⟨b, hb, rfl⟩ := mem_classLattice.mp hl
    rw [frameTorsionClass_apply] at hb
    exact fourierChar_eq_one_iff.mp ((h_riem a b).mpr (ha_ann _ hb))

/-- Multiplication by an integer of `E` maps the period lattice into itself. -/
lemma intAction_mem_periodLattice (c : 𝓞 E) :
    ∀ l ∈ x.periodLattice, x.intAction c l ∈ x.periodLattice := by
  intro l hl
  obtain ⟨y, hy, rfl⟩ := mem_classLattice.mp hl
  -- `x.intAction c` sends the image of `y` to the image of `c • y`, and `c • y` is again integral.
  have h_image : x.intAction c (x.realEquiv (toRealVectors y)) = x.periodPoint (c • y) := by
    simp [intAction, ← toRealVectors_smul]
  have h_class : frameTorsionClass g (c • y) ∈ (⊥ : AddSubgroup (AdelicTorsion E D.Index)) := by
    rw [AddSubgroup.mem_bot] at hy ⊢
    rw [map_smul, hy, smul_zero]
  rw [h_image]
  exact x.mem_latticeOver.mpr h_class

/-- For `m ≠ 0`, `m • u` lies in the lattice over `S` exactly when `u` lies in the lattice over the
classes that multiplication by `m` sends into `S`. -/
lemma nsmul_mem_latticeOver {m : ℕ} (hm : m ≠ 0) :
    m • u ∈ x.latticeOver S ↔ u ∈ x.latticeOver (S.comap (nsmulAddMonoidHom m)) := by
  -- Every rational vector is `m` times a rational vector, and `m` cancels.
  have hm_cast : (m : E) ≠ 0 := by exact_mod_cast hm
  refine (MulAction.surjective₀ hm_cast).exists.trans ?_
  simp only [mem_classLattice]
  refine exists_congr fun y ↦ and_congr ?_ ?_
  · rw [Nat.cast_smul_eq_nsmul E]
    simp only [SetLike.mem_coe, AddSubgroup.mem_comap, map_nsmul, nsmulAddMonoidHom_apply,
      AddMonoidHom.coe_ofClass]
  · rw [Nat.cast_smul_eq_nsmul E]
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_ofClass, map_nsmul]
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ m u]
    exact smul_right_inj (Nat.cast_ne_zero.mpr hm)

/-- The lattice over `S`, as an additive subgroup, is the image under `x.realEquiv ∘ toRealVectors`
of the rational vectors whose class lies in `S`. -/
private lemma toAddSubgroup_latticeOver :
    (x.latticeOver S).toAddSubgroup =
      (S.comap (frameTorsionClass g : (D.Index → E) →+ AdelicTorsion E D.Index)).map
        ((x.realEquiv : RealVectors E D.Index →+ V).comp toRealVectors) :=
  rfl

/-- The index of the lattice over `S` in the lattice over `S'` is the index of `S` in `S'`. -/
lemma relIndex_latticeOver :
    (x.latticeOver S).toAddSubgroup.relIndex (x.latticeOver S').toAddSubgroup = S.relIndex S' := by
  rw [x.toAddSubgroup_latticeOver, x.toAddSubgroup_latticeOver, relIndex_map_map_of_injective,
    relIndex_comap, map_comap_eq_self_of_surjective]
  · simp [frameTorsionClass_surjective]
  · simp [toRealVectors_injective]

/-- `|T|` times a vector of the lattice over `T` lies in the period lattice. -/
lemma card_nsmul_mem_periodLattice (h : u ∈ x.latticeOver D.dualTorsion) :
    Nat.card D.dualTorsion • u ∈ x.periodLattice := by
  -- The index of `x.periodLattice` in `x.latticeOver D.dualTorsion` is the order of `T`.
  rw [← D.dualTorsion.relIndex_bot_left, ← x.relIndex_latticeOver]
  exact nsmul_relIndex_mem _ h

/-- If `S ≤ D.dualTorsion`, multiplication by `β₁ = |T|β − ⌊|T|/2⌋` (`New.PEL.rescaledBeta`) maps
the lattice over `S` into itself. -/
lemma intAction_rescaledBeta_mem_latticeOver (h_le : S ≤ D.dualTorsion) (hu : u ∈ x.latticeOver S) :
    x.intAction D.rescaledBeta u ∈ x.latticeOver S := by
  -- `rescaledBeta u = β (#T • u) - ⌊#T / 2⌋ • u`, and `#T • u` lies in `x.periodLattice`.
  have h_β : x.intAction D.β (Nat.card D.dualTorsion • u) ∈ x.periodLattice :=
    x.intAction_mem_periodLattice D.β _
      (x.card_nsmul_mem_periodLattice (x.latticeOver_mono h_le hu))
  have h_eq : x.intAction D.rescaledBeta u =
      x.intAction D.β (Nat.card D.dualTorsion • u) - (Nat.card D.dualTorsion / 2) • u := by
        simp [rescaledBeta]
  rw [h_eq]
  exact _root_.sub_mem (x.latticeOver_mono bot_le h_β) (nsmul_mem hu _)

/-- e(β₁u, w) + e(u, β₁w) = e(u, w) for the Riemann form e of B, where β₁ is `D.rescaledBeta`. -/
lemma riemannForm_intAction_rescaledBeta (u w : V) :
    x.automorphyForm.riemannForm (x.intAction D.rescaledBeta u) w =
      x.automorphyForm.riemannForm u w - x.automorphyForm.riemannForm u
        (x.intAction D.rescaledBeta w) := by
  -- With `#T = 2 τ + 1` we have `rescaledBeta = (2 τ + 1) β - τ`, and `star β = 1 - β`.
  have h_star : star D.rescaledBeta = 1 - D.rescaledBeta := by
    obtain ⟨τ, hτ⟩ : ∃ τ : ℕ, Nat.card D.dualTorsion = 2 * τ + 1 := D.odd_card
    have h_half : Nat.card D.dualTorsion / 2 = τ := by omega
    rw [rescaledBeta, h_half, hτ, star_sub, star_nsmul, D.star_beta, star_natCast, nsmul_eq_mul]
    push_cast
    ring
  -- For the Riemann form, the adjoint of `rescaledBeta` is `star rescaledBeta`. The flags
  -- `-smul_eq_mul` and `-mul_re` stop `simp` from expanding the form into coordinates.
  -- Stated for all vectors, so that `reindex_equiv x.realEquiv` can move it to the real vectors.
  have h_adj : ∀ u w : V, x.automorphyForm.riemannForm (x.intAction D.rescaledBeta u) w =
      x.automorphyForm.riemannForm u (x.intAction (star D.rescaledBeta) w) := by
    simp [reindex_equiv x.realEquiv, intAction, riemannForm_eq, polarisationForm,
      ← map_star_complex,
      ← Pi.smul_def, -smul_eq_mul, ← coe_star_ringOfIntegers, -mul_re, Matrix.mulVec_smul]
  rw [h_adj u w, h_star, map_sub, map_one, _root_.sub_apply, one_apply_eq_self, map_sub]

/-- The multiplier χ is a semicharacter of every subgroup of the lattice over `D.lagrangian`. -/
lemma isAppellHumbert_of_le {L : Submodule ℤ V} (hL : L ≤ x.latticeOver D.lagrangian) :
    IsAppellHumbert (L := L) x.automorphyForm x.multiplier := by
  refine ThetaTori.isAppellHumbert_canonicalMultiplier x.riemannForm_intAction_rescaledBeta
    x.re_symm fun u hu w hw ↦ ?_
  -- `x.latticeOver D.lagrangian` is stable under `rescaledBeta` and lies in its own dual lattice.
  have h_dual : x.intAction D.rescaledBeta u ∈
      x.automorphyForm.dualLattice (L := x.latticeOver D.lagrangian) ⊓ x.latticeOver ⊤ := by
    rw [x.dualLattice_inf_latticeOver_top D.mem_lagrangian]
    exact x.intAction_rescaledBeta_mem_latticeOver D.lagrangian_le_dualTorsion (hL hu)
  exact (Submodule.mem_inf.mp h_dual).left w (hL hw)

/-- The multiplier χ is a semicharacter of the period lattice for B. -/
instance isAppellHumbert_periodLattice : IsAppellHumbert x.automorphyForm x.multiplier :=
  x.isAppellHumbert_of_le (x.latticeOver_mono bot_le)

/-- The multiplier χ is a semicharacter of the lattice over `D.lagrangian` for B. -/
instance isAppellHumbert_latticeOver_lagrangian :
    IsAppellHumbert (L := x.latticeOver D.lagrangian) x.automorphyForm x.multiplier :=
  x.isAppellHumbert_of_le le_rfl

/-- Every vector of the dual of the lattice over `S`, for the Riemann form of `x.automorphyForm`, is
rational: it lies in the lattice over `⊤`. -/
lemma dualLattice_le_latticeOver_top :
    x.automorphyForm.dualLattice (L := x.latticeOver S) ≤ x.latticeOver ⊤ := by
  -- Some `N ≠ 0` multiplies the dual of `x.periodLattice` into `x.periodLattice`, so dual vectors
  -- are rational.
  obtain ⟨N, hN, h_mul⟩ := x.isAppellHumbert_periodLattice.exists_nsmul_mem_of_mem_dualLattice
  intro u hu
  have h_dual : u ∈ x.automorphyForm.dualLattice (L := x.periodLattice) :=
    fun l hl ↦ hu l (x.latticeOver_mono bot_le hl)
  exact x.latticeOver_mono le_top ((x.nsmul_mem_latticeOver hN).1 (h_mul u h_dual))

/-- The dual of the period lattice for the Riemann form of `x.automorphyForm` is the lattice over
`T = D.dualTorsion`. -/
lemma dualLattice_periodLattice : x.automorphyForm.dualLattice = x.latticeOver D.dualTorsion := by
  -- Dual vectors are rational, and `T` is the annihilator of the zero subgroup.
  rw [← inf_of_le_left x.dualLattice_le_latticeOver_top,
    x.dualLattice_inf_latticeOver_top D.mem_dualTorsion]

/-- The lattice over `D.lagrangian` is discrete. -/
instance discreteTopology_latticeOver_lagrangian : DiscreteTopology (x.latticeOver D.lagrangian) :=
  -- `x.latticeOver D.lagrangian` lies in `x.latticeOver D.dualTorsion`, the dual lattice of
  -- `x.periodLattice`.
  isFullRankLattice_dualLattice.toDiscreteTopology.of_subset
    ((x.latticeOver_mono D.lagrangian_le_dualTorsion).trans x.dualLattice_periodLattice.ge)

/-- The images in `V` of two rational vectors `y` and `z` differ by a vector of the period lattice
exactly when `y` and `z` have the same torsion class. -/
lemma sub_mem_periodLattice_iff :
    x.periodPoint y - x.periodPoint z ∈ x.periodLattice ↔
      frameTorsionClass g y = frameTorsionClass g z := by
  simp [← map_sub, ← sub_eq_zero]

lemma torsionLift_mem_latticeOver : x.torsionLift s ∈ x.latticeOver D.dualTorsion := by
  simp [torsionLift]

/-! ### The bicharacter on `T` and the theta coordinates -/

/-- Let `u` and `x.periodPoint y` lie in `x.latticeOver D.dualTorsion`, the image in V under the
period map of the vectors of Eⁿ whose class `frameTorsionClass g` in `(𝔸f / Ô)ⁿ` lies in T, and let
`frameTorsionClass g z = frameTorsionClass g y`. Then e(β₁u, y) and e(z, ⌊|T|/2⌋u) differ by an
integer, so their phases `x.automorphyForm.riemannPhase` agree. Here e is the Riemann form of B,
β₁ = |T|β − ⌊|T|/2⌋ acts on V through `x.intAction`, and y and z stand for their points
`x.periodPoint` in V. -/
lemma riemannPhase_rescaledBeta_eq (hu : u ∈ x.latticeOver D.dualTorsion)
    (hy : x.periodPoint y ∈ x.latticeOver D.dualTorsion)
    (hzy : frameTorsionClass g z = frameTorsionClass g y) :
    x.automorphyForm.riemannPhase (x.intAction D.rescaledBeta u) (x.periodPoint y) =
      x.automorphyForm.riemannPhase (x.periodPoint z) ((Nat.card D.dualTorsion / 2) • u) := by
  -- Write `rescaledBeta = #T • β - ⌊#T / 2⌋`. The term in `#T • β` is integral, as `#T • u` lies in
  -- `x.periodLattice`; in the other term `y` may be replaced by `z`, as the two differ by a vector
  -- of `x.periodLattice`.
  obtain ⟨m₁, hm₁⟩ :
      ∃ m : ℤ, x.automorphyForm.riemannForm (x.periodPoint y)
        (x.intAction D.β (Nat.card D.dualTorsion • u)) = m :=
    x.dualLattice_periodLattice.ge hy _
      (x.intAction_mem_periodLattice D.β _ (x.card_nsmul_mem_periodLattice hu))
  obtain ⟨m₂, hm₂⟩ : ∃ m : ℤ, x.automorphyForm.riemannForm u (x.periodPoint z - x.periodPoint y) =
    m :=
    x.dualLattice_periodLattice.ge hu _ (x.sub_mem_periodLattice_iff.mpr hzy)
  set k : ℕ := Nat.card D.dualTorsion / 2 with hk
  have h_rescaled : x.intAction D.rescaledBeta u =
      x.intAction D.β (Nat.card D.dualTorsion • u) - k • u := by simp [rescaledBeta, hk]
  -- The two Riemann forms differ by the integer `-m₁ + k m₂`, where `k = ⌊#T / 2⌋`.
  have h_diff : x.automorphyForm.riemannForm (x.intAction D.rescaledBeta u) (x.periodPoint y) =
      x.automorphyForm.riemannForm (x.periodPoint z) (k • u) + ((-m₁ + k * m₂ : ℤ) : ℝ) := by
    have h_beta_eq :
        x.automorphyForm.riemannForm (x.intAction D.β (Nat.card D.dualTorsion • u))
          (x.periodPoint y) = -m₁ := by
      rw [riemannForm_swap, hm₁]
    rw [map_sub] at hm₂
    rw [h_rescaled, map_sub, LinearMap.sub_apply, h_beta_eq, map_nsmul, LinearMap.smul_apply,
      map_nsmul, riemannForm_swap u (x.periodPoint z), nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    linear_combination (k : ℝ) * hm₂
  have h_int_phase : Real.fourierChar (((-m₁ + k * m₂ : ℤ) : ℝ)) = 1 :=
    fourierChar_eq_one_iff.mpr ⟨_, rfl⟩
  simp only [RealComplexForm.riemannPhase, h_diff, map_add_eq_mul, h_int_phase, mul_one]

/-- For u in the lattice over T, the additive character t ↦ exp(2πi·e(β₁u, a_t)) of T, with e
the Riemann form of B and a_t the chosen lift of t. -/
def bicharacter (h : u ∈ x.latticeOver D.dualTorsion) : AddChar D.dualTorsion ℂ where
  toFun s := x.automorphyForm.riemannPhase (x.intAction D.rescaledBeta u) (x.torsionLift s)
  map_zero_eq_one' := by simp
  -- By `riemannPhase_rescaledBeta_eq` the value depends only on the class of the representative,
  -- and `ratLift g s + ratLift g t` represents `s + t`.
  map_add_eq_mul' s t := by
    simp [riemannPhase_rescaledBeta_eq (z := ratLift g s + ratLift g t),
      riemannPhase_rescaledBeta_eq _ h _ rfl, add_mem, h, RealComplexForm.riemannPhase, torsionLift,
      periodPoint, map_add_eq_mul]

/-- Let `c_s` be the character `x.bicharacter` of `T` attached to the chosen lift of `s`. Then
`c_s(-t) = c_t(s)`. -/
lemma bicharacter_neg_eq_swap :
    x.bicharacter (x.torsionLift_mem_latticeOver s) (-t) = x.bicharacter
      (x.torsionLift_mem_latticeOver t) s := by
  simp [bicharacter, x.riemannPhase_rescaledBeta_eq _ _ rfl,
    riemannForm_swap (x.periodPoint (ratLift g t)), RealComplexForm.riemannPhase, torsionLift,
    map_neg_eq_inv]

/-- If the character `x.bicharacter` of `T` attached to the chosen lift `x.torsionLift s` of `s` has
square `1` on the Lagrangian subgroup `D.lagrangian` (as a subgroup of `T`), then `s` lies in
`D.lagrangian`. -/
lemma mem_lagrangian_of_bicharacter_sq
    (h_sq : ∀ l : D.lagrangian.addSubgroupOf D.dualTorsion,
      x.bicharacter (x.torsionLift_mem_latticeOver s) l ^ 2 = 1) :
    ↑s ∈ D.lagrangian := by
  -- Since `D.lagrangian` is its own annihilator, it suffices that `riemannForm (x.torsionLift s) l`
  -- is integral on `x.latticeOver D.lagrangian`.
  suffices h_dual : x.torsionLift s ∈ x.automorphyForm.dualLattice (L := x.latticeOver D.lagrangian)
    by
    have h_top : x.torsionLift s ∈ x.latticeOver ⊤ := by simp [torsionLift]
    have h_mem : x.torsionLift s ∈ x.latticeOver D.lagrangian :=
      (x.dualLattice_inf_latticeOver_top D.mem_lagrangian).le ⟨h_dual, h_top⟩
    simpa [torsionLift] using h_mem
  intro l ⟨y, hyL, hyl⟩
  have hyT : frameTorsionClass g y ∈ D.dualTorsion := D.lagrangian_le_dualTorsion hyL
  -- With `#T = 2 τ + 1`, both `(2 τ + 1) * riemannForm l (x.torsionLift s)` and, by the hypothesis
  -- and `riemannPhase_rescaledBeta_eq`, `2 τ * riemannForm l (x.torsionLift s)` are integers;
  -- subtract.
  obtain ⟨τ, hτ⟩ : ∃ τ : ℕ, Nat.card D.dualTorsion = 2 * τ + 1 := D.odd_card
  obtain ⟨m, hm⟩ : ∃ m : ℤ, x.automorphyForm.riemannForm l
    (Nat.card D.dualTorsion • x.torsionLift s) = m :=
    x.dualLattice_periodLattice.ge ⟨y, hyT, hyl⟩ _
      (x.card_nsmul_mem_periodLattice (x.torsionLift_mem_latticeOver s))
  -- The hypothesis at the class of `y`, moved to `l` by `riemannPhase_rescaledBeta_eq`.
  have h_phase : x.bicharacter (x.torsionLift_mem_latticeOver s) ⟨frameTorsionClass g y, hyT⟩ =
      x.automorphyForm.riemannPhase l (τ • x.torsionLift s) := by
    rw [show τ = Nat.card D.dualTorsion / 2 by omega, ← hyl]
    exact x.riemannPhase_rescaledBeta_eq (x.torsionLift_mem_latticeOver s)
      (x.torsionLift_mem_latticeOver _)
      (frameTorsionClass_ratLift _).symm
  have h_sq_phase : x.automorphyForm.riemannPhase l (τ • x.torsionLift s) ^ 2 = 1 := by
    rw [← h_phase]
    exact h_sq ⟨⟨frameTorsionClass g y, hyT⟩, hyL⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, 2 * τ * x.automorphyForm.riemannForm l (x.torsionLift s) = n := by
    refine fourierChar_eq_one_iff.mp (Circle.coe_eq_one.mp ?_)
    calc (Real.fourierChar (2 * τ * x.automorphyForm.riemannForm l (x.torsionLift s)) : ℂ)
        = x.automorphyForm.riemannPhase l (τ • x.torsionLift s) ^ 2 := by
          simp [RealComplexForm.riemannPhase, ← Complex.exp_nat_mul, mul_assoc, mul_left_comm]
      _ = 1 := h_sq_phase
  -- `(2 τ + 1) r = m` and `2 τ r = n` for `r = riemannForm l (x.torsionLift s)`; subtract.
  have h_odd : (2 * τ + 1) * x.automorphyForm.riemannForm l (x.torsionLift s) = m := by
    simpa [hτ] using hm
  refine ⟨n - m, ?_⟩
  rw [riemannForm_swap]
  push_cast
  linarith

/-- The theta functions for the lattice over the Lagrangian subgroup form a line: there is a
nonzero one of which all are complex multiples. -/
lemma exists_generator_thetaSpace :
    ∃ θ : x.automorphyForm.thetaSpace (L := x.latticeOver D.lagrangian) x.multiplier,
      θ ≠ 0 ∧ ∀ f : x.automorphyForm.thetaSpace (L := x.latticeOver D.lagrangian) x.multiplier,
        ∃ c : ℂ, c • θ = f := by
  -- The lattice is its own dual, and the square of the dimension is its index in the dual.
  have h_self_dual :
      x.automorphyForm.dualLattice (L := x.latticeOver D.lagrangian) = x.latticeOver D.lagrangian :=
    (inf_of_le_left x.dualLattice_le_latticeOver_top).symm.trans
      (x.dualLattice_inf_latticeOver_top D.mem_lagrangian)
  have h_finrank :
      Module.finrank ℂ (x.automorphyForm.thetaSpace (L := x.latticeOver D.lagrangian) x.multiplier)
        = 1 := by
    simpa [h_self_dual] using x.isAppellHumbert_latticeOver_lagrangian.finrank_thetaSpace_sq
  exact finrank_eq_one_iff'.1 h_finrank

/-- A chosen generator of the line of theta functions for the lattice over the Lagrangian
subgroup. -/
def lagrangianTheta : V → ℂ :=
  x.exists_generator_thetaSpace.choose

lemma lagrangianTheta_mem_thetaSpace_lagrangian :
    x.lagrangianTheta ∈ x.automorphyForm.thetaSpace (L := x.latticeOver D.lagrangian)
      x.multiplier :=
  x.exists_generator_thetaSpace.choose.prop

lemma lagrangianTheta_ne_zero : x.lagrangianTheta ≠ 0 := by
  obtain ⟨h_ne, -⟩ := x.exists_generator_thetaSpace.choose_spec
  exact fun h_zero ↦ h_ne (Subtype.ext h_zero)

/-- Every theta function for the lattice over the Lagrangian subgroup is a complex multiple of
`x.lagrangianTheta`. -/
lemma exists_smul_lagrangianTheta_eq {f : V → ℂ}
    (hf : f ∈ x.automorphyForm.thetaSpace (L := x.latticeOver D.lagrangian) x.multiplier) :
    ∃ c : ℂ, c • x.lagrangianTheta = f := by
  obtain ⟨-, h_span⟩ := x.exists_generator_thetaSpace.choose_spec
  obtain ⟨c, hc⟩ := h_span ⟨f, hf⟩
  exact ⟨c, congrArg Subtype.val hc⟩

/-- The theta coordinate at `t`: the normalised translate of `x.lagrangianTheta` by the chosen
lift of `t`. -/
def thetaCoord : V → ℂ :=
  normalizedShift x.automorphyForm (x.intAction D.rescaledBeta) (x.torsionLift t) x.lagrangianTheta

/-- The theta coordinate `θ_t` is a theta function of type `(B, χ)` for the period lattice. -/
@[simp] lemma thetaCoord_mem_thetaSpace :
    x.thetaCoord t ∈ x.automorphyForm.thetaSpace x.multiplier := by
  -- `x.lagrangianTheta` is a theta function for the larger lattice `x.latticeOver D.lagrangian`,
  -- and `x.torsionLift t` lies in the dual of `x.periodLattice`.
  obtain ⟨h_diff, h_eq⟩ := x.lagrangianTheta_mem_thetaSpace_lagrangian
  have h_gen : x.lagrangianTheta ∈ x.automorphyForm.thetaSpace x.multiplier :=
    ⟨h_diff, fun l hl ↦ h_eq l (x.latticeOver_mono bot_le hl)⟩
  have h_dual : x.torsionLift t ∈ x.automorphyForm.dualLattice := by
    simp [dualLattice_periodLattice, torsionLift]
  exact smul_mem _ _ (thetaShift_mem_of_mem_dualLattice h_dual h_gen)

/-- `θ_t` is a theta function for the lattice over `L`, with the multiplier twisted by
l ↦ exp(2πi·e(l, a_t)), where e is the Riemann form of B and a_t = `x.torsionLift t` is the chosen
lift of t. -/
lemma thetaCoord_mem_thetaSpace_lagrangian :
    x.thetaCoord t ∈ x.automorphyForm.thetaSpace (L := x.latticeOver D.lagrangian)
      fun l : V ↦ x.multiplier l * x.automorphyForm.riemannPhase l (x.torsionLift t) :=
  smul_mem _ _ (thetaShift_mem x.lagrangianTheta_mem_thetaSpace_lagrangian (x.torsionLift t))

lemma thetaCoord_ne_zero : x.thetaCoord t ≠ 0 := by
  -- Translating back by `-x.torsionLift t` gives a nonzero multiple of `x.lagrangianTheta`.
  refine ne_of_apply_ne (x.automorphyForm.thetaShift (-x.torsionLift t)) ?_
  simp [thetaCoord, normalizedShift, x.isAppellHumbert_periodLattice.thetaShift_thetaShift,
    x.lagrangianTheta_ne_zero, canonicalMultiplier]

/-- For `s` in the Lagrangian subgroup, `θ_s = θ_0`. -/
lemma thetaCoord_eq_of_mem_lagrangian (h_mem : ↑s ∈ D.lagrangian) :
    x.thetaCoord s = x.thetaCoord 0 := by
  -- `x.lagrangianTheta` is fixed by the normalised translations along its lattice.
  have h_fixed : ∀ l ∈ x.latticeOver D.lagrangian,
      normalizedShift x.automorphyForm (x.intAction D.rescaledBeta) l x.lagrangianTheta =
        x.lagrangianTheta :=
    (mem_thetaSpace_iff_normalizedShift.mp x.lagrangianTheta_mem_thetaSpace_lagrangian).right
  simp [thetaCoord, h_fixed, h_mem, torsionLift]

end PeriodMap

end ThetaTori

namespace ThetaTori

variable {E : Type} [Field E] [CMBase E] {D : PEL E} {g : GL D.Index (𝔸f E)}
  {ℓ : Matrix D.Index D.Index ℂ} {y z : D.Index → E} {V : Type} [FinComplexSpace V]
  (x : PeriodMap D g ℓ V) {s t : D.dualTorsion} {u : V} {S : AddSubgroup (AdelicTorsion E D.Index)}
  {S' : AddSubgroup (AdelicTorsion E D.Index)}

namespace PeriodMap

/-- The theta coordinate at `t` may be computed with any rational vector `y` that represents
`t`. -/
lemma thetaCoord_eq_normalizedShift (y : D.Index → E) (hy : frameTorsionClass g y = t) :
    x.thetaCoord t =
      normalizedShift x.automorphyForm (x.intAction D.rescaledBeta) (x.periodPoint y)
        x.lagrangianTheta := by
  -- `x.thetaCoord t` is invariant under the normalised translation by the lattice vector `l`. By
  -- the Heisenberg law `normalizedShift_normalizedShift`, whose cocycle is trivial here, composing
  -- it with the translation by `x.torsionLift t` gives the translation by `x.periodPoint y`.
  set l : V := x.periodPoint y - x.torsionLift t with hl_def
  have hl : l ∈ x.periodLattice := x.sub_mem_periodLattice_iff.mpr (by simp [hy])
  obtain ⟨m, hm⟩ :
      ∃ m : ℤ, x.automorphyForm.riemannForm (x.torsionLift t) (x.intAction D.rescaledBeta l) = m :=
    x.dualLattice_periodLattice.ge (x.torsionLift_mem_latticeOver t) _
      (x.intAction_rescaledBeta_mem_latticeOver bot_le hl)
  have h_cocycle : x.automorphyForm.riemannPhase (x.intAction D.rescaledBeta l) (x.torsionLift t) =
    1 :=
    Circle.coe_eq_one.mpr (fourierChar_eq_one_iff.mpr
      ⟨-m, by rw [riemannForm_swap, hm, Int.cast_neg]⟩)
  calc x.thetaCoord t
      = normalizedShift x.automorphyForm (x.intAction D.rescaledBeta) l (x.thetaCoord t) :=
      ((mem_thetaSpace_iff_normalizedShift.mp (x.thetaCoord_mem_thetaSpace t)).right l hl).symm
    _ = x.automorphyForm.riemannPhase (x.intAction D.rescaledBeta l) (x.torsionLift t) •
          normalizedShift x.automorphyForm (x.intAction D.rescaledBeta) (l + x.torsionLift t)
            x.lagrangianTheta :=
      x.isAppellHumbert_periodLattice.normalizedShift_normalizedShift
        x.riemannForm_intAction_rescaledBeta
    _ = normalizedShift x.automorphyForm (x.intAction D.rescaledBeta) (x.periodPoint y)
      x.lagrangianTheta := by
      rw [h_cocycle, one_smul, hl_def, sub_add_cancel]

/-- If the rational vector `y` represents `s ∈ T`, its image in `V` lies in the lattice over `T`. -/
lemma periodPoint_mem_latticeOver_of_frameTorsionClass_eq (hy : frameTorsionClass g y = s) :
    x.periodPoint y ∈ x.latticeOver D.dualTorsion := by
  simp [hy]

/-- The theta law. If the rational vector `y` represents `s ∈ T` and `u` is its image in `V`, the
twisted translation `New.RealComplexForm.thetaShift` by `u` sends `θ_t` to `χ(u) c_u(t) θ_{s+t}`,
where χ is `x.multiplier` and `c_u` is the character `New.ThetaTori.PeriodMap.bicharacter` attached
to `u`: c_u(t) = exp(2πi·e(β₁u, a_t)), with e the Riemann form of B and a_t the chosen lift of t. -/
lemma thetaShift_thetaCoord (hy : frameTorsionClass g y = s) (t : D.dualTorsion) :
    x.automorphyForm.thetaShift (x.periodPoint y) (x.thetaCoord t) =
      (x.multiplier (x.periodPoint y) *
          x.bicharacter (x.periodPoint_mem_latticeOver_of_frameTorsionClass_eq hy) t) •
        x.thetaCoord (s + t) := by
  -- The twisted translation `thetaShift` by `u = x.periodPoint y` is `χ(u)` times the normalised
  -- one. By the Heisenberg law, the normalised translation by `u` of `θ_t` is `c_u(t)` times the
  -- normalised translation of `x.lagrangianTheta` by `u + a_t`, the image of `y + ratLift g t`,
  -- which represents `s + t`.
  have h_shift_eq : x.automorphyForm.thetaShift (x.periodPoint y) (x.thetaCoord t) =
      x.multiplier (x.periodPoint y) •
        normalizedShift x.automorphyForm (x.intAction D.rescaledBeta) (x.periodPoint y)
          (x.thetaCoord t) := by
    simp [normalizedShift, canonicalMultiplier, smul_smul]
  have h_law :
      normalizedShift x.automorphyForm (x.intAction D.rescaledBeta) (x.periodPoint y)
        (x.thetaCoord t) =
        x.automorphyForm.riemannPhase (x.intAction D.rescaledBeta (x.periodPoint y))
          (x.torsionLift t) •
          normalizedShift x.automorphyForm (x.intAction D.rescaledBeta)
            (x.periodPoint y + x.torsionLift t)
            x.lagrangianTheta :=
    x.isAppellHumbert_periodLattice.normalizedShift_normalizedShift
      x.riemannForm_intAction_rescaledBeta
  have h_phase : x.automorphyForm.riemannPhase (x.intAction D.rescaledBeta (x.periodPoint y))
    (x.torsionLift t) =
      x.bicharacter (x.periodPoint_mem_latticeOver_of_frameTorsionClass_eq hy) t := rfl
  have h_sum : x.periodPoint y + x.torsionLift t = x.periodPoint (y + ratLift g t) := by
    simp [torsionLift, periodPoint]
  rw [h_shift_eq, h_law, h_phase, h_sum,
    ← x.thetaCoord_eq_normalizedShift (t := s + t) (y + ratLift g t) (by simp [hy]), mul_smul]

/-- For a unit `m = ±1` of ℤ, there is a constant `ε`, independent of `z` and `t`, with
`θ_t(m z) = ε · θ_{m t}(z)` for all `z ∈ V` and `t ∈ T`. So up to a single scalar, `-1` permutes the
theta coordinates by `t ↦ -t`. -/
lemma exists_thetaCoord_sign_smul (m : ℤˣ) :
    ∃ ε : ℂ, ∀ (z : V) (t : D.dualTorsion),
      x.thetaCoord t (m.val • z) = ε * x.thetaCoord (m.val • t) z := by
  rcases Int.units_eq_one_or m with rfl | rfl
  · exact ⟨1, by simp⟩
  · -- `z ↦ x.lagrangianTheta (-z)` is again a theta function for `x.latticeOver D.lagrangian`, so a
    -- multiple of `x.lagrangianTheta`.
    obtain ⟨h_diff, h_eq⟩ := x.lagrangianTheta_mem_thetaSpace_lagrangian
    have h_neg : (fun z : V ↦ x.lagrangianTheta (-z)) ∈
        x.automorphyForm.thetaSpace (L := x.latticeOver D.lagrangian) x.multiplier := by
      refine ⟨h_diff.comp differentiable_fun_id.neg, fun l hl z ↦ ?_⟩
      -- The functional equation at `-l` and `-z`; the multiplier is even in `l`, and the exponent
      -- is unchanged when `l` and `z` are both negated.
      have h_at : x.lagrangianTheta (-z + -l) =
          x.multiplier (-l) * cexp (x.automorphyForm (-l) (-z) + x.automorphyForm (-l) (-l) / 2) *
            x.lagrangianTheta (-z) :=
        h_eq (-l) (neg_mem hl) (-z)
      simp only [neg_add, h_at]
      simp [canonicalMultiplier]
    obtain ⟨ε, hε⟩ := x.exists_smul_lagrangianTheta_eq h_neg
    refine ⟨ε, fun z t ↦ ?_⟩
    -- Compute `x.thetaCoord (-t)` with the representative `-ratLift g t` of `-t`.
    have h_coord_neg : x.thetaCoord (-t) = normalizedShift x.automorphyForm
      (x.intAction D.rescaledBeta)
        (-x.torsionLift t) x.lagrangianTheta := by
      simpa [torsionLift, periodPoint] using
        x.thetaCoord_eq_normalizedShift (t := -t) (-ratLift g t) (by simp)
    have h_reflect : x.lagrangianTheta (-z + x.torsionLift t) =
        ε * x.lagrangianTheta (z + -x.torsionLift t) := by
      simpa [add_comm] using (congrFun hε (z + -x.torsionLift t)).symm
    rw [Units.val_neg, Units.val_one, neg_one_smul, neg_one_smul, h_coord_neg]
    -- With `a = x.torsionLift t`, both sides unfold to `χ(a)⁻¹ exp(-B(a, a) / 2 - B(a, -z))` times
    -- `θ(-z + a)` (the right side by `h_reflect`, `χ(-a) = χ(a)` and `B(-a, z) = B(a, -z)`).
    simp only [thetaCoord, normalizedShift, LinearMap.smul_apply, Pi.smul_apply, thetaShift_apply,
      smul_eq_mul, h_reflect]
    simp [canonicalMultiplier, field]

attribute [irreducible] thetaCoord bicharacter

/-- Let `v` be a valuation on `ℂ`, let `u` lie in the lattice over `T` and let `t ∈ T`. The product
`χ(u) · c_u(t)` of the multiplier and of the character `x.bicharacter` attached to `u` has
valuation `1`: both factors are roots of unity. -/
lemma valuation_multiplier_mul_bicharacter_eq_one (v : Valuation ℂ NNReal)
    (hu : u ∈ x.latticeOver D.dualTorsion) :
    v (x.multiplier u * x.bicharacter hu t) = 1 := by
  -- Both factors are roots of unity by `exp_riemannForm_pow_eq_one`, as `#T` multiplies the lattice
  -- over `T` into `x.periodLattice`.
  have h_beta_card : Nat.card D.dualTorsion • x.intAction D.rescaledBeta u ∈ x.periodLattice :=
    x.card_nsmul_mem_periodLattice (x.intAction_rescaledBeta_mem_latticeOver le_rfl hu)
  -- `v (exp (π i e(β₁ u, w))) = 1` whenever `#T • w` lies in the period lattice.
  have h_val_exp : ∀ w : V, Nat.card D.dualTorsion • w ∈ x.periodLattice →
      v (cexp (Real.pi * I * x.automorphyForm.riemannForm (x.intAction D.rescaledBeta u) w)) = 1 :=
    fun w hw ↦ valuation_eq_one_of_pow_eq_one (by simp [Nat.card_pos.ne'])
      (x.isAppellHumbert_periodLattice.exp_riemannForm_pow_eq_one h_beta_card hw)
  have h_mult : v (x.multiplier u) = 1 := by
    simpa [canonicalMultiplier] using h_val_exp u (x.card_nsmul_mem_periodLattice hu)
  -- The character value is the square of `exp (π i e(β₁ u, a_t))`, `a_t` the lift of `t`.
  have h_char_eq : x.bicharacter hu t =
      cexp (Real.pi * I *
        x.automorphyForm.riemannForm (x.intAction D.rescaledBeta u) (x.torsionLift t)) ^ 2 := by
    simp [bicharacter, RealComplexForm.riemannPhase, two_mul, add_mul, exp_add, sq]
  rw [map_mul, h_mult, h_char_eq, map_pow,
    h_val_exp _ (x.card_nsmul_mem_periodLattice (x.torsionLift_mem_latticeOver t)), one_pow,
      mul_one]

/-- At the trivial valuation `1` on ℂ, the form `x.automorphyForm` of the polarised period map `x`
and its multiplier `x.multiplier` satisfy `HasGoodReduction` of level `D.paddedNorm`. This means the
conditions of `IsAmpleType` hold, some natural `N` with `v(N) = 1` maps the dual lattice into the
lattice, the level `D.paddedNorm > 1` has `v(D.paddedNorm) = 1`, and the sup norm is
multiplicative. -/
lemma hasGoodReduction_one :
    HasGoodReduction x.automorphyForm x.multiplier (1 : Valuation ℂ NNReal) D.paddedNorm := by
  -- The multiplier takes the values `±1` on `x.periodLattice`; the exponent is the `2 * n * m` of
  -- `exp_riemannForm_pow_eq_one` with `n = m = 1`.
  have h_sign : ∀ l ∈ x.periodLattice, x.multiplier l ^ (2 * 1 * 1) = 1 := by
    intro l hl
    exact x.isAppellHumbert_periodLattice.exp_riemannForm_pow_eq_one (n := 1) (m := 1)
      (by simp [intAction_mem_periodLattice, hl]) (by simpa using hl)
  have h_dual : ∃ N : ℕ, (1 : Valuation ℂ NNReal) (N : ℂ) = 1 ∧
      ∀ a ∈ x.automorphyForm.dualLattice, N • a ∈ x.periodLattice := by
    simp [x.isAppellHumbert_periodLattice.exists_nsmul_mem_of_mem_dualLattice]
  have h_ample : IsAmpleType x.automorphyForm x.multiplier :=
    { finite_order := ⟨2 * 1 * 1, by simp, h_sign⟩ }
  have h_val_r : (1 : Valuation ℂ NNReal) (D.paddedNorm : ℂ) = 1 := by
    simp [D.three_le_paddedNorm.trans_lt', ne_of_gt]
  have h_one_lt : 1 < D.paddedNorm := by linarith [D.three_le_paddedNorm]
  refine ⟨h_ample, h_dual, h_val_r, h_one_lt, ?_⟩
  -- For the trivial valuation a size takes the values 0 and 1, so the sup norm of a theta function
  -- is 1 unless the function is zero; a product of nonzero entire functions is nonzero.
  -- `@` names the theta functions, which are implicit arguments of `LatticeForm.sizes`.
  rintro B C _ _ @⟨_, f, -, hf, -⟩ @⟨_, f', -, hf', -⟩
  -- A nonzero entire function has theta norm `1`: a norm other than `1` means every size is `0`,
  -- so the function vanishes on the torsion points, hence everywhere.
  have h_norm_one : ∀ (B : LatticeForm x.periodLattice) (f : V → ℂ), Differentiable ℂ f →
      f ≠ 0 → B.thetaNorm 1 f = 1 := by
    intro B f hf hf_ne
    by_contra h_nm
    have h_not_greatest : ¬IsGreatest (range (B.sizeAt 1 f)) 1 := mt IsGreatest.csSup_eq h_nm
    have h_torsion_zero : ∀ y : torsionPoints x.periodLattice, f y = 0 := by
      -- `-map_mul` keeps the valuation of each product in one piece.
      simpa [IsGreatest, LatticeForm.sizeAt, upperBounds, -map_mul,
        Valuation.one_apply_le_one, thetaShift_apply] using h_not_greatest
    exact hf_ne (eq_zero_of_torsionPoints hf h_torsion_zero)
  -- The three sup norms are `0` or `1`.
  rw [← sizeAt_mul]
  show (B + C).thetaNorm 1 (f * f') = B.thetaNorm 1 f * C.thetaNorm 1 f'
  by_cases hf_zero : f = 0
  · simp [hf_zero, thetaNorm_zero]
  by_cases hf'_zero : f' = 0
  · simp [hf'_zero, thetaNorm_zero]
  have h_prod_ne : f * f' ≠ 0 := fun h_prod ↦
    hf'_zero (eq_zero_of_differentiable_of_mul_eq_zero hf hf' h_prod hf_zero)
  rw [h_norm_one (B + C) (f * f') (hf.mul hf') h_prod_ne, h_norm_one B f hf hf_zero,
    h_norm_one C f' hf' hf'_zero, mul_one]

/-- For a valuation `v` on `ℂ`, every theta coordinate `θ_i` has the theta norm of `θ_0`. The theta
norm of f is the supremum, over torsion points a, of the size v(exp(-B(a, a)/2)·f(a)). -/
lemma thetaNorm_thetaCoord (v : Valuation ℂ NNReal) (i : D.dualTorsion) :
    x.automorphyForm.thetaNorm v (x.thetaCoord i) = x.automorphyForm.thetaNorm v
      (x.thetaCoord 0) := by
  -- `x.thetaCoord i` is the translate of `x.thetaCoord 0` by `x.torsionLift i` up to a factor of
  -- valuation `1`.
  calc
    _ = x.automorphyForm.thetaNorm v (x.automorphyForm.thetaShift (x.torsionLift i)
      (x.thetaCoord 0)) := by
      rw [torsionLift, x.thetaShift_thetaCoord (frameTorsionClass_ratLift _) 0,
        thetaNorm_smul, x.valuation_multiplier_mul_bicharacter_eq_one, one_mul, add_zero]
    _ = _ := x.hasGoodReduction_one.thetaNorm_thetaShift
        (x.dualLattice_periodLattice.ge (x.torsionLift_mem_latticeOver i))

/-- Normal generation: let `v` be a valuation of good reduction for `x.automorphyForm`,
`x.multiplier` and the level `r = D.paddedNorm`, and let `θ_t = x.thetaCoord t` be the theta
coordinates. Then, for any `c ∈ T`, the forms of degree `r^j` in the `θ_t` with coefficients in the
valuation ring are exactly the theta functions of type `(r^j B, χ^(r^j))` in the ball of
`θ_c^(r^j)`. This ball consists of those theta functions `f` whose size
`v(exp(-r^j B(a, a) / 2) · f(a))` at every torsion point `a` (a vector of finite order modulo the
period lattice) is at most the supremum of the sizes of `θ_c^(r^j)`. -/
lemma formSpan_eq_normBall (v : Valuation ℂ NNReal)
    (hG : HasGoodReduction x.automorphyForm x.multiplier v D.paddedNorm)
    (c : D.dualTorsion) (j : ℕ) :
    formSpan v.valuationSubring x.thetaCoord (D.paddedNorm ^ j) =
    (hG.pow j).normBall (x.thetaCoord c ^ D.paddedNorm ^ j) := by
  -- The span of the `x.thetaCoord t` holds the translates of `x.thetaCoord c` by the dual lattice,
  -- by `thetaShift_thetaCoord`.
  have h_shift :
      ∀ u ∈ x.automorphyForm.dualLattice,
        x.automorphyForm.thetaShift u (x.thetaCoord c) ∈ span v.valuationSubring
          (range x.thetaCoord) := by
    rw [x.dualLattice_periodLattice]
    intro u hu
    obtain ⟨y, hy, rfl⟩ := mem_classLattice.mp hu
    rw [x.thetaShift_thetaCoord (s := ⟨frameTorsionClass g y, hy⟩) rfl c]
    exact smul_mem _ (⟨_, (x.valuation_multiplier_mul_bicharacter_eq_one v _).le⟩ : v.integer)
      (subset_span ⟨_, rfl⟩)
  -- So it holds the ball of `x.thetaCoord c`; conversely all `x.thetaCoord t` have the same norm.
  have h_range : range x.thetaCoord ⊆ hG.normBall (x.thetaCoord c) := by
    simp [hG.mem_normBall, thetaNorm_thetaCoord, range_subset_iff]
  have h_lattice (u : V) (hu : D.paddedNorm • u ∈ x.periodLattice) :
    u ∈ x.latticeOver D.lagrangian :=
    x.latticeOver_mono D.torsion_mem_lagrangian ((x.nsmul_mem_latticeOver hG.one_lt.ne_bot).mp hu)
  have h_span : span v.valuationSubring (range x.thetaCoord) = hG.normBall (x.thetaCoord c) :=
    span_eq_of_le _ h_range fun f hf ↦
      hG.mem_of_mem_normBall (x.thetaCoord_mem_thetaSpace c) le_rfl hG.isAppellHumbert
        (x.thetaCoord_mem_thetaSpace c) hf.left h_shift hf
  -- Normal generation, since `x.thetaCoord c` is a theta function for
  -- `x.latticeOver D.lagrangian ⊇ r⁻¹ x.periodLattice`.
  rw [formSpan, h_span]
  exact hG.normBall_pow_pow (x.thetaCoord_mem_thetaSpace c)
    (x.isAppellHumbert_latticeOver_lagrangian.mul_riemannPhase _)
      (x.thetaCoord_mem_thetaSpace_lagrangian c)
    h_lattice j

/-- The theta functions θ_t, t in T, have no common zero: for every z in V the vector (θ_t(z))_t
is non-zero. -/
lemma thetaCoord_vector_ne_zero (z : V) : (x.thetaCoord · z) ≠ 0 := by
  -- Some theta function of degree `D.paddedNorm` does not vanish at `z`. By `formSpan_eq_normBall`
  -- for the trivial valuation it is a multiple of a form of degree `D.paddedNorm` in the
  -- `x.thetaCoord t`, so these cannot all vanish at `z`.
  intro h_zero
  obtain ⟨f, hf, hfz⟩ : ∃ f ∈ thetaSpace (x.multiplier ^ D.paddedNorm)
    (D.paddedNorm • x.automorphyForm), f z ≠ 0 :=
    x.isAppellHumbert_periodLattice.exists_mem_thetaSpace_nsmul_apply_ne_zero z D.paddedNorm
      x.hasGoodReduction_one.one_lt
  -- This is the case `j = 1` of `formSpan_eq_normBall`, whose powers are `D.paddedNorm ^ j`; so
  -- `hf` is restated with the exponent `D.paddedNorm ^ 1`.
  have h_pow_mem :
      x.thetaCoord 0 ^ D.paddedNorm ^ 1 ∈ thetaSpace (x.multiplier ^ D.paddedNorm ^ 1)
        (D.paddedNorm ^ 1 • x.automorphyForm) :=
    pow (x.thetaCoord_mem_thetaSpace 0) (D.paddedNorm ^ 1)
  have h_pow_ne : x.thetaCoord 0 ^ D.paddedNorm ^ 1 ≠ 0 := by simp [thetaCoord_ne_zero]
  obtain ⟨c, f₀, h_ball, rfl, -⟩ := (x.hasGoodReduction_one.pow 1).exists_eq_smul_normBall
    h_pow_mem h_pow_ne (g := f) (by simpa using hf)
  rw [← x.formSpan_eq_normBall 1 x.hasGoodReduction_one] at h_ball
  -- Evaluation at `z` sends `f₀` into a positive power of the zero module.
  set ev := mapHom (Pi.evalAlgHom (1 : Valuation ℂ NNReal).valuationSubring (fun _ : V ↦ ℂ) z)
  set M := span (1 : Valuation ℂ NNReal).valuationSubring (range x.thetaCoord)
  have h_eval : f₀ z ∈ ev M ^ D.paddedNorm ^ 1 := by
    rw [← map_pow]
    exact ⟨f₀, h_ball, rfl⟩
  have h_eval_zero : ev M = ⊥ := by simp [ev, M, map_span, ← range_comp', h_zero]
  rw [h_eval_zero, pow_one, bot_pow x.hasGoodReduction_one.one_lt.ne_bot, Submodule.mem_bot]
    at h_eval
  have h_smul_zero : (c • f₀) z = 0 := by simp [h_eval]
  exact hfz h_smul_zero

end PeriodMap

end ThetaTori

end New

end
