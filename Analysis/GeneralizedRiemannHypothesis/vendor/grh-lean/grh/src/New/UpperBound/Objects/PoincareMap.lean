import New.UpperBound.Seesaw.EdgePairEvaluation

/-!
# The Poincaré map

The Poincaré map `𝒫 = D.poincareAt g t : 𝒜(X₀) → 𝒜(Y₀)` sends a source form `φ` to the form that
represents the Bessel period of `φ` in the Petersson inner product.

Notions from other files:
* `V.Form e`: the automorphic forms of archimedean type `e` on the adelic unitary group
  `G E s = GInf E s × Gf E n` of `V`; `V.quotMeasure` integrates over the quotient by the rational
  points, and `HasLevel z J` says that `z` is right invariant under `J ⊆ Gf E n`.
* `D.SourceForm` is the space `𝒜(X₀)` of algebraic forms on the definite unitary group of `X₀`,
  with values in a Weyl module and of level `D.levelX 0`. `D.principalForms (D.spaceY 0)` is the
  space `𝒜(Y₀)` of forms on the group `G₀` of `Y₀` whose archimedean type is the discrete series of
  doubled parameter `D.paramW` and whose level is `J_M = D.chosenLevel`, the group of integral
  finite adelic points that reduce to `1` at every prime divisor of `D.piM`.
* `Y.besselGroup` is the adelic Bessel subgroup `R(𝔸)` of a grading `Y`, and `Y.besselMeasure`
  integrates over `[R] = R(F) \ R(𝔸)`. For `Y = D.gradingY 0` the group is written `R₀`.
* `Y.sourceFn t φ` is the function `𝒲_φ (u h) = ψ_U (u) · t (ρ (h_∞⁻¹) φ (h_f))` on `R(𝔸)`. Here
  `u` is unipotent, `h` lies in the unitary group of `X`, `ψ_U` is the generic character,
  `ρ = conjWeylRep` is the action on the values of `φ`, and `t` is a linear form on these values.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work.
-/

open MeasureTheory ComplexConjugate
noncomputable section
namespace New

section Riesz
variable {M F : Type*} [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- On an inner product space `F` of finite dimension, every conjugate linear form is `y ↦ ⟨y, z⟩`
for a unique vector `z` (Riesz). -/
lemma bijective_flip_innerₛₗ : Function.Bijective (innerₛₗ ℂ (E := F)).flip := by
  have : CompleteSpace F := FiniteDimensional.complete ℂ F
  refine ⟨fun z z' h_eq ↦ ext_inner_left ℂ (LinearMap.congr_fun h_eq), fun l ↦ ?_⟩
  -- Apply the Riesz theorem to the linear form `conj ∘ l`.
  let z : F := (InnerProductSpace.toDual ℂ F).symm
    ((starRingEnd ℂ).toSemilinearMap ∘ₛₗ l).toContinuousLinearMap
  have hz (y : F) : inner ℂ z y = conj (l y) := InnerProductSpace.toDual_symm_apply
  refine ⟨z, LinearMap.ext fun y ↦ ?_⟩
  rw [LinearMap.flip_apply, innerₛₗ_apply_apply, ← inner_conj_symm, hz, Complex.conj_conj]

/-- The linear map that sends `x` to the vector representing the conjugate linear form `B x`. -/
def rieszMap (B : M →ₗ[ℂ] F →ₗ⋆[ℂ] ℂ) : M →ₗ[ℂ] F :=
  (LinearEquiv.ofBijective (innerₛₗ ℂ).flip bijective_flip_innerₛₗ).symm.toLinearMap ∘ₗ B

/-- The inner product of `y` with `rieszMap B x` is `B x y`. -/
lemma inner_rieszMap (B : M →ₗ[ℂ] F →ₗ⋆[ℂ] ℂ) (x : M) (y : F) :
    inner ℂ y (rieszMap B x) = B x y := by
  have h_flip : (innerₛₗ ℂ).flip (rieszMap B x) = B x :=
    (LinearEquiv.ofBijective (innerₛₗ ℂ).flip bijective_flip_innerₛₗ).apply_symm_apply (B x)
  rw [← h_flip, LinearMap.flip_apply, innerₛₗ_apply_apply]

end Riesz

namespace Space
variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  {V : Space E n s} {e : GInf E s → ℂ}

lemma Form.add_apply (y z : V.Form e) (x : G E s) : (y + z) x = y x + z x := rfl

lemma Form.smul_apply (c : ℂ) (y : V.Form e) (x : G E s) : (c • y) x = c * y x := rfl

/-- The sum of the right translates of a form `z` under the chosen representatives of
`K / (J ∩ K)`, for subgroups `J` and `K` of the finite adelic group. -/
def Form.levelTrace (J K : Subgroup (Gf E n)) [Fintype (K ⧸ J.subgroupOf K)] (z : V.Form e) :
    V.Form e :=
  ∑ q : K ⧸ J.subgroupOf K, V.formRep e q.out z

/-- The value of `z.levelTrace J K` at `x` is the sum, over the cosets `q` in `K ⧸ J.subgroupOf K`,
of `z (x * (1, q.out))`. This is the value of `z` at `x` translated on the right by the chosen
representative of `q`. -/
lemma Form.levelTrace_apply (J K : Subgroup (Gf E n)) [Fintype (K ⧸ J.subgroupOf K)]
    (z : V.Form e) (x : G E s) :
    z.levelTrace J K x = ∑ q : K ⧸ J.subgroupOf K, z (x * (1, (q.out : Gf E n))) := by
  exact (congrFun (Submodule.coe_sum ..) x).trans (Finset.sum_apply ..)

/-- If a form `z` is right invariant under `J`, then the sum of its translates under
representatives of `K / (J ∩ K)` is right invariant under `K`. -/
lemma Form.hasLevel_levelTrace {J : Subgroup (Gf E n)} (K : Subgroup (Gf E n))
    [Fintype (K ⧸ J.subgroupOf K)] {z : V.Form e} (hz : HasLevel z J) :
    HasLevel (z.levelTrace J K) K := by
  intro k hk x
  rw [levelTrace_apply, levelTrace_apply]
  -- Left multiplication by `k` permutes the cosets.
  refine Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ fun q ↦ ?_
  obtain ⟨⟨j, hj_mem⟩, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf K) (⟨k, hk⟩ * q.out)
  have h_out : (((⟨k, hk⟩ : K) • q).out : Gf E n) = k * q.out * j := by
    rw [← MulAction.Quotient.mk_smul_out, smul_eq_mul, hj, Subgroup.coe_mul, Subgroup.coe_mul]
  rw [MulAction.toPerm_apply, h_out, ← hz j hj_mem (x * (1, k) * (1, (q.out : Gf E n)))]
  simp only [mul_assoc, Prod.mk_mul_mk, mul_one]

/-- Let `y` be a form of level `K` and `z` any form. The integral against `y` of the sum of the
translates of `z` under representatives of `K / (J ∩ K)` is `[K : J ∩ K]` times the integral of
`z · y`, both over the quotient of `G` by its rational points. -/
lemma Form.integral_levelTrace_mul {J : Subgroup (Gf E n)} (K : Subgroup (Gf E n))
    [Fintype (K ⧸ J.subgroupOf K)] {e' : GInf E s → ℂ} (z : V.Form e) {y : V.Form e'}
    (hy : HasLevel y K) :
    ∫ x : G E s, z.levelTrace J K x * y x ∂V.quotMeasure =
      J.relIndex K * ∫ x : G E s, z x * y x ∂V.quotMeasure := by
  have h_aut : V.IsAutomorphic fun x ↦ z x * y x :=
    z.2.toIsAutomorphic.map₂ y.2.toIsAutomorphic (fun a b ↦ a * b) (by fun_prop)
  -- The integral is invariant under right translation, which fixes `y`.
  have h_term (k : K) : ∫ x, z (x * (1, (k : Gf E n))) * y x ∂V.quotMeasure =
      ∫ x, z x * y x ∂V.quotMeasure := by
    rw [← (integral_comp_mul_right (1, (k : Gf E n)) h_aut.rat_mul h_aut.continuous).1]
    simp only [hy k k.2]
  have h_int (k : K) : Integrable (fun x ↦ z (x * (1, (k : Gf E n))) * y x) V.quotMeasure :=
    (z.2.comp_mul_right k).memLp.integrable_mul y.2.memLp
  simp only [levelTrace_apply, Finset.sum_mul]
  rw [integral_finsetSum _ fun q _ ↦ h_int q.out]
  simp [h_term, Subgroup.relIndex, Subgroup.index]

end Space

namespace Grading
variable {E ι X : Type} [Field E] [CMType E] [WeilData E] [Fintype ι] [DecidableEq ι] [Fintype X]
  [DecidableEq X] {s : ℕ} {ε : ι → ℤˣ} {N : E} {V : Space E ι ε} {Y : Grading V N X s}

/-- Let `W` be an equivariant function on `R(𝔸)`: it is continuous and left invariant under `R(F)`,
and `W (u r) = ψ_U (u) W (r)` for `u` in the subgroup `U^{≥2}(𝔸)` of elements for which `u - 1`
raises the grading by at least `2`. Let `y` be an automorphic function on the unitary group `G E ε`
of `V`, and let `x` be a point of `G E ε`. Then `r ↦ W r * y (r * x)` is integrable over
`[R] = R(F) \ R(𝔸)`, because it is continuous on a compact quotient. -/
lemma IsEquivariant.integrable_mul {W : Y.besselGroup → ℂ} (hW : Y.IsEquivariant W)
    {y : G E ε → ℂ} (hy : V.IsAutomorphic y) (x : G E ε) :
    Integrable (fun r : Y.besselGroup ↦ W r * y (r.1 * x)) Y.besselMeasure := by
  refine integrable_of_isCocompact Y.isCocompact_ratBessel
    (hW.continuous.mul (hy.continuous.comp (by fun_prop))) fun γ hγ r ↦ ?_
  have h_rat : γ.1 ∈ V.Γ := (Subgroup.mem_subgroupOf.1 hγ).1
  rw [hW.rat_mul γ h_rat, Subgroup.coe_mul, mul_assoc, hy.rat_mul γ h_rat]

end Grading

namespace Data
variable {P : Parameters} (D : Data P) (g : GInf D.E (D.signsY 0))
  (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ)

/-- For a source form `φ` on `X₀`, the function `𝒲_φ = sourceFn t φ` on the Bessel group `R₀(𝔸)`
of `D.gradingY 0` is continuous, left invariant under the rational points, and transforms by the
generic character under the unipotent part. -/
lemma isEquivariant_sourceFn (φ : D.SourceForm) :
    (D.gradingY 0).IsEquivariant ((D.gradingY 0).sourceFn t φ.1) :=
  (D.gradingY 0).isEquivariant_sourceFn (odd_two_mul_add_one D.ϱ) t φ.1

/-- The Bessel period `∫_{[R₀]} 𝒲_φ (r) conj (y (r g)) dr`, linear in the source form `φ` and
conjugate linear in the form `y` on `Y₀`. Here `g` is an archimedean point of `G₀`, and `𝒲_φ` is
formed with the linear form `t`. -/
def besselPeriod : D.SourceForm →ₗ[ℂ] D.principalForms (D.spaceY 0) →ₗ⋆[ℂ] ℂ :=
  have h_int (φ : D.SourceForm) (y : D.principalForms (D.spaceY 0)) : Integrable
      (fun r : (D.gradingY 0).besselGroup ↦
        (D.gradingY 0).sourceFn t φ.1 r * conj (y.1 (r.1 * (g, 1))))
      (D.gradingY 0).besselMeasure :=
    (D.isEquivariant_sourceFn t φ).integrable_mul y.1.2.toIsAutomorphic.conj (g, 1)
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun (φ : D.SourceForm) (y : D.principalForms (D.spaceY 0)) ↦
      ∫ r : (D.gradingY 0).besselGroup, (D.gradingY 0).sourceFn t φ.1 r * conj (y.1 (r.1 * (g, 1)))
        ∂(D.gradingY 0).besselMeasure)
    (fun φ ψ y ↦ by
      simp [Grading.sourceFn_add, add_mul, integral_add (h_int φ y) (h_int ψ y)])
    (fun c φ y ↦ by simp [Grading.sourceFn_smul, mul_assoc, integral_const_mul])
    (fun φ y y' ↦ by
      simp [Space.Form.add_apply, mul_add, integral_add (h_int φ y) (h_int φ y')])
    (fun c φ y ↦ by
      simp [Space.Form.smul_apply, mul_left_comm _ (conj c), integral_const_mul])

/-- Let `g` be an archimedean point of the unitary group `G₀` of `Y₀`, let `φ` be a source form and
`t` a linear form on the Weyl module of its values. Let `y` be a form on `G₀` of discrete series
type `D.paramW` and principal level `D.chosenLevel`. Then `D.besselPeriod g t φ y = ∫_{[R₀]} 𝒲_φ (r)
conj (y (r g)) dr`. -/
lemma besselPeriod_apply (φ : D.SourceForm) (y : D.principalForms (D.spaceY 0)) :
    D.besselPeriod g t φ y =
      ∫ r : (D.gradingY 0).besselGroup,
        (D.gradingY 0).sourceFn t φ.1 r * conj (y.1 (r.1 * (g, 1)))
        ∂(D.gradingY 0).besselMeasure :=
  rfl

/-- The Poincaré map `𝒫 : 𝒜(X₀) → 𝒜(Y₀)` for an archimedean point `g` of `G₀` and a linear form
`t`: the form `𝒫 φ` represents the Bessel period of `φ`. The measure on `[R₀]` is `besselMeasure`;
another Haar measure on `R₀(𝔸)` would multiply `𝒫` by a positive constant, which can be absorbed
in `t` by `poincareAt_smul`. -/
def poincareAt (g : GInf D.E (D.signsY 0)) (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) :
    D.SourceForm →ₗ[ℂ] D.principalForms (D.spaceY 0) :=
  rieszMap (D.besselPeriod g t)

/-- The defining property of the Poincaré map `𝒫 = D.poincareAt g t`. Let `g` be an archimedean
point of the unitary group `G₀` of `Y₀`, let `φ` be a source form and `t` a linear form on the Weyl
module `ρ = conjWeylRep` of its values. Let `y` be a form on `G₀` of level `D.chosenLevel` whose
archimedean type is the discrete series of doubled parameter `D.paramW`. Then the Petersson product
`⟨y, 𝒫 φ⟩` is the Bessel period `∫_{[R₀]} 𝒲_φ (r) conj (y (r g)) dr`. -/
theorem inner_poincareAt (φ : D.SourceForm) (y : D.principalForms (D.spaceY 0)) :
    inner ℂ y (D.poincareAt g t φ) =
      ∫ r : (D.gradingY 0).besselGroup,
        (D.gradingY 0).sourceFn t φ.1 r * conj (y.1 (r.1 * (g, 1)))
        ∂(D.gradingY 0).besselMeasure := by
  rw [poincareAt, inner_rieszMap, besselPeriod_apply]

/-- Scaling the linear form `t` scales the Poincaré map `𝒫 = D.poincareAt g t` by the same factor,
so that a change of the Haar measure can be absorbed in `t`. -/
theorem poincareAt_smul (c : ℂ) : D.poincareAt g (c • t) = c • D.poincareAt g t := by
  refine LinearMap.ext fun φ ↦ ext_inner_left ℂ fun y ↦ ?_
  rw [LinearMap.smul_apply, inner_smul_right, inner_poincareAt, inner_poincareAt,
    ← integral_const_mul]
  simp only [Grading.sourceFn_smul_left, mul_assoc]

/-- Let `z` be a form on `G₀`, right invariant under `J`, whose archimedean type is conjugate to
that of the values of `𝒫 = D.poincareAt g t`. Then `[J_M : J ∩ J_M] ∫_{[G₀]} z · 𝒫 φ` is the sum
over representatives `γ` of `J_M / (J ∩ J_M)` of `∫_{[R₀]} 𝒲_φ (r) z (r g γ) dr`. -/
theorem integral_mul_poincareAt (g : GInf D.E (D.signsY 0))
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
    {J : Subgroup (Gf D.E (D.Y 0))}
    [Fintype (D.chosenLevel ⧸ J.subgroupOf D.chosenLevel)]
    (z : (D.spaceY 0).Form (star (typeKernel (D.paramY 0) (D.signsY 0))))
    (hz_level : HasLevel z J) :
    J.relIndex D.chosenLevel *
        ∫ x : New.G D.E (D.signsY 0), z x * (D.poincareAt g t φ).1 x ∂(D.spaceY 0).quotMeasure =
      ∑ q : D.chosenLevel ⧸ J.subgroupOf D.chosenLevel,
        ∫ r : (D.gradingY 0).besselGroup,
          (D.gradingY 0).sourceFn t φ.1 r * z (r.1 * (g, q.out.1))
          ∂(D.gradingY 0).besselMeasure := by
  -- The conjugate `y` of the sum of the translates of `z` lies in `𝒜(Y₀)`.
  have h_trace : HasLevel (z.levelTrace J D.chosenLevel) D.chosenLevel :=
    Space.Form.hasLevel_levelTrace D.chosenLevel hz_level
  let y : D.principalForms (D.spaceY 0) :=
    ⟨conjForm (star_star _).symm (z.levelTrace J D.chosenLevel),
      Space.mem_levelSpace_formRep_iff.2 fun k hk x ↦ congrArg star (h_trace k hk x)⟩
  have hy (x : New.G D.E (D.signsY 0)) : conj (y.1 x) = z.levelTrace J D.chosenLevel x :=
    Complex.conj_conj _
  have h_level : HasLevel (D.poincareAt g t φ).1 D.chosenLevel :=
    Space.mem_levelSpace_formRep_iff.1 (D.poincareAt g t φ).2
  calc J.relIndex D.chosenLevel * ∫ x, z x * (D.poincareAt g t φ).1 x ∂(D.spaceY 0).quotMeasure
    _ = ∫ x, z.levelTrace J D.chosenLevel x * (D.poincareAt g t φ).1 x ∂(D.spaceY 0).quotMeasure :=
        (z.integral_levelTrace_mul D.chosenLevel h_level).symm
    _ = ∫ x, conj (y.1 x) * (D.poincareAt g t φ).1 x ∂(D.spaceY 0).quotMeasure := by
        simp only [hy]
    -- The inner product on `𝒜(Y₀)` is `⟨y, y'⟩ = ∫ conj y · y'` by definition.
    _ = inner ℂ y (D.poincareAt g t φ) := rfl
    _ = ∫ r, ∑ q : D.chosenLevel ⧸ J.subgroupOf D.chosenLevel,
          (D.gradingY 0).sourceFn t φ.1 r * z (r.1 * (g, q.out.1))
          ∂(D.gradingY 0).besselMeasure := by
        simp only [inner_poincareAt, hy, Space.Form.levelTrace_apply, Finset.mul_sum, mul_assoc,
          Prod.mk_mul_mk, mul_one, one_mul]
    _ = ∑ q : D.chosenLevel ⧸ J.subgroupOf D.chosenLevel,
          ∫ r, (D.gradingY 0).sourceFn t φ.1 r * z (r.1 * (g, q.out.1))
            ∂(D.gradingY 0).besselMeasure :=
        integral_finsetSum _ fun q _ ↦
          (D.isEquivariant_sourceFn t φ).integrable_mul z.2.toIsAutomorphic (g, q.out.1)

end Data

end New

end
