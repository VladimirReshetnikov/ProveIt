import Lib.DiscreteSeries.Bruhat.ComplexPlace
import New.UpperBound.Divisibility.ChainValuation
import New.UpperBound.Objects.PoincareMap
import New.UpperBound.Seesaw.Cut
import New.UpperBound.Seesaw.GoodDatum

/-!
# The seesaw identity and the top of the chain

On the definite space `Y_m`, the integral of a matrix coefficient of a form on `X_m` against a form
on `Y_m` is a multiple of the inner product with the restricted form. To prove the seesaw identity,
we pair `Θ_ξ 𝒫 φ` with a form on `Y_m` and move the Bessel period up the lower chain, one lift at a
time. Each outer integral is a real integral times a weighted sum over the classes `Ω_j`. What
remains is the upper chain for the tensor `φ_ξ`, a multiple of which is the glued tensor of a chain
datum.

Notions from other files:
* `D.spaceY j`, `D.FormY j`: the space `Y_j` of the lower chain and the forms on its unitary group.
* `liftY ϑ j`, `lowerChainUpTo ϑ j`: the theta lift from `Y_j` to `Y_(j+1)` with twist `ϑ`,
  normalised by the index of its level, and the composite of the first `j` lifts.
* `D.poincareAt g t`: the Poincaré map `𝒫` from forms on `X_0` to forms on `Y_0`.
* `Grading`, `unfoldStage`: a grading of a space, with its Bessel group `R`, and the function `𝒲`
  that is left after some steps of unfolding.
* `cutPoints ϑ j`, `cutSum`: the classes `Ω_j` of the finite variables and the weighted sum over
  them.

In the notation of the comments the subscript `ξ` of `Θ_ξ`, `J_ξ` and `φ_ξ` stands for the twist
`ϑ`: `Θ_ξ = lowerChainUpTo ϑ`, `J_ξ(Y_j) = levelY ϑ j`. A `ξ` by itself is the tuple of real parts
of the outer variables. The lattice stabiliser `stdLevel` is written `J°`, and the index
`stdLevelIndex J` is `[J° : J]`. A tame character `ϑ` is an automorphic character of `U(1)` of
weight `0` with a finite set `ϑ.Q` of places (its modulus) outside which its tame part is trivial;
it is a twist if the tame part is nontrivial at every place of `ϑ.Q`. The chosen places, those
dividing `D.piM`, are fixed by the data `D` and do not depend on `ϑ`.

## Relation to the literature

For ramified source forms φ and every twist, the restricted definite chain of lifts of φ, with data
of controlled support and denominators, is a non-zero constant, free of φ and the twist, times the
indefinite chain of lifts of the Poincaré series of φ. The transfer of a Bessel or Fourier–Jacobi
period under one theta lift is known, locally and globally. Related work: B. Wang, Global theta
lifting and periods associated to nilpotent orbits, 2025; Gomez–Zhu, Local theta lifting of
generalized Whittaker models, 2014; Gan–Ichino, The Gross–Prasad conjecture and local theta
correspondence, 2016.

Each period in the seesaw unfolding is a constant times a finite sum over cosets of a small level,
weighted by reciprocals of stabiliser indices that divide powers of the norm of the twist's
conductor. So the coefficients of the definite chain get no new denominators away from the
conductor. Related work: Gross, Algebraic modular forms, 1999; Hsieh–Namikawa, Bessel periods and
non-vanishing of Yoshida lifts modulo a prime, 2015; X. Zhang, Non-vanishing mod p of theta lifts
for (O(2n+1), Mp(4n)), 2022.
-/

noncomputable section

/-! ## Restriction to the definite space `Y_m` at the top of the chain -/

section TopStage

open New Seesaw Space Fintype Matrix Grading MeasureTheory

namespace New.Data
variable {P : Parameters} {D : Data P} {M : ℕ}

/-- The restriction from the forms `D.FormX M` on `X_m` to the forms `D.FormY M` of the lower chain
on `Y_m`: it is `D.restrictToY`, read in automorphic forms. The index `m` is written as any number
`M` equal to it. -/
noncomputable def restrictToFormY (hM : D.m = M) : D.FormX M →ₗ[ℂ] D.FormY M := by
  subst hM
  exact (toAlgForm _ D.isHCParam_paramY).symm.toLinearMap ∘ₗ D.restrictToY

/-- If the image `lowerChainUpTo ϑ M f` of a form `f` on `Y_0` under the composite of the lifts with
twist `ϑ` is the restriction `restrictToFormY hM ψ` to `Y_m` of a form `ψ` on `X_m`, where `M = m`,
then `lowerChain ϑ f = restrictToYOfEq hM ψ`. Here `lowerChain` and `restrictToYOfEq` are the same
two maps with values in algebraic forms in place of automorphic forms. -/
lemma lowerChain_eq_of_lowerChainUpTo_eq (hM : D.m = M) {ϑ : D.TameChar}
    {f : D.principalForms (D.spaceY 0)}
    {ψ : D.FormX M} (h_lift : lowerChainUpTo ϑ M f = restrictToFormY hM ψ) :
    lowerChain ϑ f = restrictToYOfEq hM ψ := by
  subst hM
  exact (toAlgForm _ D.isHCParam_paramY).eq_symm_apply.1 h_lift

/-- Let `M = m`, the number of lifts. For every linear form `t` on the values of forms on `X_m`
there is a constant `C` as follows. Let `x` be a form on `Y_m`, `ψ` one on `X_m` and `F` a function
on `G_m = U(Y_m)`, whose signs at infinity are `D.signsY M`. The last grading `D.lastGrading hM`
identifies `Y_m` with the standard definite space on `D.InitIndex M`, the `n_m - 1` basis indices of
`X_m` other than the last, and `inclX` is the resulting map of unitary groups. Suppose that at the
image of `k` under `inclX` the value of `F` is the coefficient `t (ψ (diag (k, 1)))`. Then the
integral of `F` times the conjugate of `x` over `[G_m]` is `C` times `⟨x, res ψ⟩`, where `res` is
`restrictToFormY`. -/
lemma exists_integral_eq_mul_inner_restrictToFormY (hM : D.m = M)
    (t : (WeylIndex (D.X M) D.columnCount → ℂ) →ₗ[ℂ] ℂ) :
    ∃ C : ℂ, ∀ (x : D.FormY M) {ψ : D.FormX M} {F : New.G D.E (D.signsY M) → ℂ}
      (_hF : ∀ k : New.G D.E (1 : D.InitIndex M → ℤˣ), F ((D.lastGrading hM).inclX k) =
        algFormCoeff 1 t ψ (.blockEmb (e := .refl (D.InitIndex M ⊕ Unit)) Sum.elim_one_one.symm
          (k, 1))),
      ∫ g : New.G D.E (D.signsY M), (F * star x.val) g ∂(D.lastGrading hM).ratBessel.quotMeasure =
        C * inner ℂ x (restrictToFormY hM ψ) := by
  subst hM
  have hs : D.signsY D.m = 1 := D.isStd_spaceY_last.signs_eq_one
  have hw : IsHCParam D.columnsY (D.lastEntry D.m) (D.paramY D.m) := D.isHCParam_paramY
  -- The integral over `[G_m]` of an automorphic function made from the highest vector against the
  -- matrix coefficient `h ↦ t (ψ (diag (h, 1)))` is `C` times a mean over the finite points.
  obtain ⟨C, hC⟩ := integral_algFormCoeff_blockEmb (D.spaceY D.m) (by simp [hs])
    D.isBranchingMap_branching.spans t
    (highestVector D.columnsY (D.paramY D.m))
  let c : ℂ := ∏ τ, New.Φ τ (star ↑D.piN) ^ D.branchExponent τ
  refine ⟨C * card (WeylIndex (D.Y D.m) D.columnsY) * c, fun x ψ F hF ↦ ?_⟩
  -- `x̄` is the pairing of its algebraic form `xAlg` with the translates of the highest vector.
  let xAlg : AlgForm (D.Y D.m) D.columnsY (D.lastEntry D.m) := toAlgForm _ hw x
  have h_conj (a : GInf D.E (D.signsY D.m)) (g : Gf D.E (D.Y D.m)) : star (x.1 (a, g)) =
      gramForm (xAlg.1 g) (conjWeylRep D.columnsY (D.lastEntry D.m) a
        (highestVector D.columnsY (D.paramY D.m))) := by
    rw [← star_ofAlgForm hs, ofAlgForm_toAlgForm]
  -- `avg` is the common mean over the finite points of both sides.
  let avg : ℂ := classIntegral stdRatPoints (stdLevel D.E (D.Y D.m)) fun h ↦
    gramForm (xAlg.1 h) (D.branching.map (↑) *ᵥ ψ.1 (D.borderU h))
  -- `Y_m` is standard and its last grading has no isotropic vectors split off: so `hF` describes
  -- `F` at every point, after relabelling along `D.lastIndexEquiv`, and the Bessel subgroup is the
  -- whole group.
  have hF' (g : New.G D.E (D.signsY D.m)) : F g = algFormCoeff 1 t ψ (New.G.blockEmb (s₂ := 1)
      (e := D.lastIndexEquiv.sumCongr (.refl Unit)) (by simp [hs]) (g, 1)) := by
    convert hF (.reindex D.lastIndexEquiv (by rw [hs]; rfl) g)
    · -- `inclX` of the relabelled point is `g`: they have the same matrix in rational coordinates.
      apply (D.spaceY _).isEmbedding_ratCoordMatrix.2
      -- '↓' rewrites `ratCoordMatrix` of `inclX` before its arguments are unfolded.
      simp [← ext_iff, lastGrading, ↓ratCoordMatrix_inclX, ratCoordMatrix_eq, IsStd.point_eq_one]
    · exact New.G.ext_adeleMatrix (by simp [← ext_iff, New.G.blockEmb])
  have hΓ : (lastGrading rfl).ratBessel = (D.spaceY D.m).Γ :=
    inf_eq_left.2 fun g _ ↦ by simp [mem_besselGroup_iff, lastGrading]
  have h_left : ∫ g, F g * star (x.1 g) ∂(D.spaceY D.m).quotMeasure = C * avg := by
    simp_rw [mul_comm (F _), hF']
    refine (hC ψ (star x.1) 1 (fun g ↦ gramForm (xAlg.1 g)) (stdLevel D.E (D.Y D.m))
      x.2.conj.toIsAutomorphic h_conj).trans ?_
    -- The index of `stdLevel` in itself is `1`, and `D.borderU h` is the point `diag (h, 1)`.
    have h_index : stdLevelIndex (stdLevel D.E (D.Y D.m)) = 1 := by simp
    rw [h_index, Nat.cast_one, div_one]
    rfl
  -- The inner product is the mean divided by the dimension, and `D.restrictToY` is the branching
  -- map divided by `c`.
  have h_right : inner ℂ x (restrictToFormY rfl ψ) =
      (card (WeylIndex (D.Y D.m) D.columnsY) : ℂ)⁻¹ * (c⁻¹ * avg) := by
    refine (integral_mul_eq_classIntegral hw (stdLevel D.E (D.Y D.m)) x.2.conj.toIsAutomorphic _
      h_conj).trans ?_
    simp [restrictToY, c, avg]
  rw [hΓ, h_right]
  simp only [Pi.mul_apply, Pi.star_apply, h_left]
  have hc : c ≠ 0 := by simp [c, Finset.prod_ne_zero_iff, zpow_ne_zero]
  have h_card : (card (WeylIndex (D.Y D.m) D.columnsY) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 card_ne_zero
  field_simp

end New.Data

end TopStage

section SeesawTheorem

open MeasureTheory Function Finset MulAction
namespace New.Data
open Seesaw Space TensorChain

section Unfolding

variable {P : Parameters} {D : Data P}

/-! ### Iterated unfolding -/

/-- Forms on `Y_j` of the conjugate type; they are paired with the forms of the lower chain. -/
abbrev ConjFormY (D : Data P) (j : ℕ) : Type :=
  (D.spaceY j).Form (star (typeKernel (D.paramY j) (D.signsY j)))

/-- The transposed lift, or descent, from `Y_{j+1}` to `Y_j`, times the index `[J° : J_ξ(Y_j)]`
that normalises the lift `liftY ϑ j`. -/
def transposedLiftY (ϑ : D.TameChar) (j : ℕ) : D.ConjFormY (j + 1) →ₗ[ℂ] D.ConjFormY j :=
  (stdLevelIndex (levelY ϑ j) : ℂ) • formLift (thetaKernelY ϑ j).swap
    (star (typeKernel (D.paramY (j + 1)) (D.signsY (j + 1))))
    (star (typeKernel (D.paramY j) (D.signsY j))) (datumY ϑ j)

/-- The descent as a theta integral. Let `ϑ` be a tame character, let `j < m`, and let `z` be a
conjugate form on `Y_(j+1)`. The descent of `z` at `g` is the index of the level `levelY ϑ j` in the
lattice stabiliser `stdLevel` of `Y_j`, times the integral over `h ∈ [G_(j+1)]` of `z h` times
`θ (ω (g, h) (datumY ϑ j))`. Here `datumY ϑ j` is the Schwartz function on `Hom(Y_j, Y_(j+1))` that
defines the lift, `θ` is the theta functional, `G_j = U(Y_j)`, and `ω` is the Weil representation of
`G_j × G_(j+1)` whose character on a space of rank `n` is `rankTwist` of `D.chainChar ϑ (j + 1)`:
this character of `U(1)`, formed from `ϑ ^ (j + 1)`, times `υ ^ ⌊n / 2⌋`, with `υ` the fixed
character `upsilonU1`. -/
lemma transposedLiftY_apply (ϑ : D.TameChar) {j : ℕ} (hj : j < D.m) (z : D.ConjFormY (j + 1))
    (g : New.G D.E (D.signsY j)) :
    transposedLiftY ϑ j z g = stdLevelIndex (levelY ϑ j) *
      ∫ h : New.G D.E (D.signsY (j + 1)),
        θ ((D.spaceY j).hom (D.spaceY (j + 1)))
          (twistedPairWeil (rankTwist (D.chainChar ϑ (j + 1))) (g, h) (datumY ϑ j)) * z h
        ∂(D.spaceY (j + 1)).quotMeasure := by
  -- The datum is an arrow for the swapped kernel, so the transposed lift is a theta integral.
  have h_lift := congrFun ((isArrow_swap_thetaKernelY_datumY ϑ hj).coe_formLift z) g
  exact congrArg (fun c : ℂ ↦ (stdLevelIndex (levelY ϑ j) : ℂ) * c) h_lift

/-- Lift and descent are transposes of each other. Let `ϑ` be a tame character, which twists both
maps, let `j < m`, and let `f` be a form on `Y_j` and `z` a conjugate form on `Y_(j+1)`. Then the
integral over `[G_(j+1)]` of `z` times the lift `liftY ϑ j f` is the integral over `[G_j]` of the
descent `transposedLiftY ϑ j z` times `f`. Here `G_j` is the unitary group of `Y_j`. -/
lemma integral_mul_liftY (ϑ : D.TameChar) {j : ℕ} (hj : j < D.m) (z : D.ConjFormY (j + 1))
    (f : D.FormY j) :
    ∫ h : New.G D.E (D.signsY (j + 1)), z h * liftY ϑ j f h ∂(D.spaceY (j + 1)).quotMeasure =
      ∫ g : New.G D.E (D.signsY j), transposedLiftY ϑ j z g * f g ∂(D.spaceY j).quotMeasure := by
  obtain ⟨h_up, h_down⟩ := isArrow_datumY ϑ hj
  calc
    _ = stdLevelIndex (levelY ϑ j) * ∫ h, z h * formLift (thetaKernelY ϑ j) _ _ (datumY ϑ j) f h
        ∂(D.spaceY (j + 1)).quotMeasure := by
      rw [← integral_const_mul]
      congr with h
      have h_lift : liftY ϑ j f h = stdLevelIndex (levelY ϑ j) *
          formLift (thetaKernelY ϑ j) _ _ (datumY ϑ j) f h := rfl
      rw [h_lift, mul_left_comm]
    _ = stdLevelIndex (levelY ϑ j) *
        ∫ g, f g * formLift (thetaKernelY ϑ j).swap _ _ (datumY ϑ j) z g
          ∂(D.spaceY j).quotMeasure := by
      rw [h_up.integral_mul_formLift_swap h_down]
    _ = _ := by
      rw [← integral_const_mul]
      congr with g
      have h_descent : transposedLiftY ϑ j z g = stdLevelIndex (levelY ϑ j) *
          formLift (thetaKernelY ϑ j).swap _ _ (datumY ϑ j) z g := rfl
      rw [h_descent, mul_comm (f g), mul_assoc]

/-- Let `ϑ` be a tame character and `u` an element of its level `levelY ϑ j`: an integral finite
adelic point of `G_j = U(Y_j)` that reduces to `1` at the chosen places and at the places of the
modulus `ϑ.Q`. Let `datumY ϑ j` be the Schwartz function on `Hom(Y_j, Y_(j+1))` that defines the
lift from `Y_j` to `Y_(j+1)`. In the Weil representation of `G_j × G_(j+1)` for this lift, with
characters given by `rankTwist` of `D.chainChar ϑ (j + 1)`, the pair of the point `(1, u)` of `G_j`,
with archimedean part `1` and finite part `u`, and the identity of `G_(j+1)` fixes this datum. -/
lemma twistedPairWeil_datumY_of_mem_levelY (ϑ : D.TameChar) {j : ℕ} {u : Gf D.E (D.Y j)}
    (hu : u ∈ levelY ϑ j) :
    twistedPairWeil (rankTwist (D.chainChar ϑ (j + 1))) ((1, u), 1) (datumY ϑ j) =
      datumY ϑ j := by
  -- The finite part `pointDatumY` of the datum is fixed by `(u, 1)`; the other part is archimedean.
  have h_fin : twistedPairWeil (rankTwist (D.chainChar ϑ (j + 1))) ((1, u), 1)
      (pointDatumY ϑ j).val = (pointDatumY ϑ j).val := by
    -- Both `u` and `1` reduce to `1` at the level places, so the tame characters contribute `1`.
    refine (thetaKernelY_omega_pointDatumY_eq_smul ϑ j (k' := 1) (mem_levelOf.1 hu).2 (map_one _)
      fun _ ↦ (Matrix.mul_one _).symm).trans ?_
    simp
  calc
    _ = ((D.spaceY j).hom (D.spaceY (j + 1))).integrated (Fock.polyVector _ (D.harmonicY j))
        (twistedPairWeil (rankTwist (D.chainChar ϑ (j + 1))) ((1, u), 1) (pointDatumY ϑ j).val) :=
      pairWeil_integrated_fin (k := u) (k' := 1) ..
    _ = datumY ϑ j := by rw [h_fin]

/-- Let `ϑ` be a tame character, `j < m` and `z` a conjugate form on `Y_(j+1)`. The descent
`transposedLiftY ϑ j z` is fixed by right translation by the level `levelY ϑ j` (`HasLevel`),
because the datum of the lift is. -/
lemma hasLevel_transposedLiftY (ϑ : D.TameChar) {j : ℕ} (hj : j < D.m) (z : D.ConjFormY (j + 1)) :
    HasLevel (transposedLiftY ϑ j z) (levelY ϑ j) := by
  intro u hu g
  rw [transposedLiftY_apply ϑ hj, transposedLiftY_apply ϑ hj]
  congr with h
  conv_rhs => rw [← twistedPairWeil_datumY_of_mem_levelY ϑ hu, ← mul_apply_eq_comp,
    ← map_mul, Prod.mk_mul_mk, mul_one]

/-- For `j < m` every conjugate form on `Y_(j+1)` is rapidly decreasing. -/
lemma isRapid_conjFormY {j : ℕ} (hj : j < D.m) (z : D.ConjFormY (j + 1)) :
    (D.spaceY (j + 1)).IsRapid z := by
  -- The rapid decrease does not depend on a twist, so it is read off from the arrow of the trivial
  -- twist, whose forms are rapidly decreasing on the source.
  obtain ⟨⟨-, h_rapid⟩, -⟩ := isArrow_swap_thetaKernelY_datumY (D := D) .one hj z
  exact h_rapid

/-- The integral `Ξ_{k+1}` of the product `𝒲_{k+1} z` over `R_{k+1}(F) \ G_{k+1}(𝔸)`, where
`𝒲_{k+1} = unfoldStage ϑ t φ ξ y k hk Y` is the function on `G_{k+1}` left by the first `k + 1`
steps of unfolding for the source form `φ`, the linear form `t` and the outer variables
`g_i = (ξ i, y i)`, and `R_{k+1}(F) = Y.ratBessel` consists of the rational points of the Bessel
group of `Y`. -/
def unfoldedPeriod (ϑ : D.TameChar)
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
    (ξ : ∀ i : ℕ, GInf D.E (D.signsY i)) (y : ∀ i : ℕ, Gf D.E (D.Y i))
    (k : ℕ) (hk : k ≤ 2 * D.ϱ + 1) {X : Type} {s : ℕ} [Fintype X] [DecidableEq X]
    (Y : Grading (D.spaceY (k + 1)) D.N X s) (z : D.ConjFormY (k + 1)) : ℂ :=
  ∫ h : New.G D.E (D.signsY (k + 1)),
    (unfoldStage ϑ t φ ξ y k hk Y * z.val) h ∂Y.ratBessel.quotMeasure

/-- The integral `Ξ_{k+1}` converges absolutely. Let `k ≤ 2 ϱ + 1`, let `ϑ` be a tame character,
`φ` a form on `X_0`, `t` a linear form on its values and `(ξ i, y i)` the archimedean and finite
parts of points `g_i` of `U(Y_i)`, at which the earlier stages are evaluated. These define the
function `unfoldStage` on `G_{k+1} = U(Y_{k+1})` that is left after `k + 1` steps of unfolding. For
a grading `Y` of `Y_{k+1}`, whose Bessel group has rational points `R_{k+1}(F) = Y.ratBessel`, and a
conjugate form `z` on `Y_{k+1}`, its product with `z` is integrable over
`R_{k+1}(F) \ G_{k+1}(𝔸)`. -/
lemma integrable_unfoldStage_mul (ϑ : D.TameChar)
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
    (ξ : ∀ i : ℕ, GInf D.E (D.signsY i)) (y : ∀ i : ℕ, Gf D.E (D.Y i))
    {k : ℕ} (hk : k ≤ 2 * D.ϱ + 1) {X : Type} [Fintype X]
    [DecidableEq X] (Y : Grading (D.spaceY (k + 1)) D.N X (2 * D.ϱ + 1 - (k + 1)))
    (z : D.ConjFormY (k + 1)) :
    Integrable (unfoldStage ϑ t φ ξ y k hk Y * z.val) Y.ratBessel.quotMeasure := by
  exact (integral_unfoldStageOn ϑ t φ ξ y k hk Y z.2.toIsAutomorphic
    (isRapid_conjFormY (lt_m_of_le hk) z)).1

/-- The recursion of the iterated unfolding, for the tame character `ϑ`, the source form `φ` on
`X_0`, the linear form `t` on its values and the outer variables `g_i = (ξ i, y i)`, points of
`U(Y_i)` split into archimedean and finite part. Let `k ≤ 2 ϱ + 1`, where `m = 2 ϱ + 2` is the
number of lifts, let `Y` be a grading of `Y_{k+1}`, and let `z` be a conjugate form on `Y_{k+1}`.
The function `unfoldStageOn` on the Bessel group `R_k` of the standard grading `D.gradingY k` is the
Bessel function of `φ` for `k = 0`, and for `k > 0` the function left by `k` steps of unfolding,
translated by `g_k`. Integrate it at `r ∈ [R_k]` times the descent of `z` at `r g_k`. The result is
the index of `levelY ϑ k` in the lattice stabiliser times `Ξ_{k+1}` (`unfoldedPeriod`): the integral
of `z` times the function left by `k + 1` steps over the quotient of `U(Y_{k+1})` by the rational
Bessel group of `Y`. -/
lemma integral_unfoldStageOn_mul_transposedLiftY (ϑ : D.TameChar)
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
    (ξ : ∀ i : ℕ, GInf D.E (D.signsY i)) (y : ∀ i : ℕ, Gf D.E (D.Y i))
    {k : ℕ} (hk : k ≤ 2 * D.ϱ + 1) {X : Type} [Fintype X] [DecidableEq X]
    (Y : Grading (D.spaceY (k + 1)) D.N X (2 * D.ϱ + 1 - (k + 1))) (z : D.ConjFormY (k + 1)) :
    ∫ r : (gradingY k hk).besselGroup,
      unfoldStageOn ϑ t φ ξ y k hk r * transposedLiftY ϑ k z (r.val * (ξ k, y k))
        ∂(D.gradingY k hk).besselMeasure =
      stdLevelIndex (levelY ϑ k) * unfoldedPeriod ϑ t φ ξ y k hk Y z := by
  obtain ⟨-, h_step⟩ := integral_unfoldStageOn ϑ t φ ξ y k hk Y z.2.toIsAutomorphic
    (isRapid_conjFormY (lt_m_of_le hk) z)
  -- `h_step` evaluates `Ξ_{k+1}` as the period of `𝒲_k` against the theta integral of `z`.
  rw [unfoldedPeriod, ← h_step, ← integral_const_mul]
  congr with r
  rw [transposedLiftY_apply ϑ (lt_m_of_le hk), mul_left_comm]

/-- Let `ϑ` be a tame character and `J = levelY ϑ 0` its level on `Y_0`, a subgroup of
`J_M = D.chosenLevel`. Let `f` be a function on the finite adelic unitary group of `Y_0` that is
fixed by right translation by `J`. Then the sum of `f` over representatives of `J_M / J` is its sum
over representatives of `Ω_0 = cutPoints ϑ 0`, the classes modulo `J` of the elements of `J_M`. -/
lemma sum_quotient_chosenLevel_eq_sum_cutPoints (ϑ : D.TameChar)
    [Fintype (D.chosenLevel ⧸ (levelY ϑ 0).subgroupOf D.chosenLevel)] {f : Gf D.E (D.Y 0) → ℂ}
    (hf : ∀ x : Gf D.E (D.Y 0), ∀ u ∈ levelY ϑ 0, f (x * u) = f x) :
    ∑ q : D.chosenLevel ⧸ (levelY ϑ 0).subgroupOf D.chosenLevel, f q.out =
      ∑ c ∈ cutPoints ϑ 0 (2 * D.ϱ + 1).zero_le, f c.out := by
  let J : Subgroup (Gf D.E (D.Y 0)) := levelY ϑ 0
  have h_out (x : Gf D.E (D.Y 0)) : f (x : Gf D.E (D.Y 0) ⧸ J).out = f x := by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul J x
    rw [hu, hf x u u.2]
  -- A class of `J_M` modulo `J` goes to the class modulo `J` of its representative.
  refine sum_bij (fun q _ ↦ ↑(q.out : Gf D.E (D.Y 0)))
    (fun q _ ↦ (mk_mem_cutPoints_zero ϑ).2 q.out.2) (fun q _ q' _ h_eq ↦ ?_) (fun c hc ↦ ?_)
    fun q _ ↦ (h_out q.out).symm
  · rw [← q.out_eq', ← q'.out_eq']
    exact QuotientGroup.eq.2 (QuotientGroup.eq.1 h_eq :)
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    let x' : D.chosenLevel := ⟨x, (mk_mem_cutPoints_zero ϑ).1 hc⟩
    have h_mem : (x' : D.chosenLevel ⧸ J.subgroupOf D.chosenLevel).out⁻¹ * x' ∈
        J.subgroupOf D.chosenLevel := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    exact ⟨x', mem_univ _, QuotientGroup.eq.2 h_mem⟩

/-- Let `ϑ` be a tame character, `t` a linear form on the values of forms on `X_0`, `g` an
archimedean point of `U(Y_0)` and `𝒫 φ = D.poincareAt g t φ` the Poincaré series of `φ` on `Y_0`.
Let `Y` be a grading of `Y_1` with a string of `2 ϱ` vectors. The integral of a conjugate form `z`
on `Y_1` times the first lift `liftY ϑ 0 (𝒫 φ)` is `[J° : J_M]` times the sum of the periods `Ξ_1`
over the classes `c` in `Ω_0 = cutPoints ϑ 0`. Here `J°` is the lattice stabiliser `stdLevel`,
`J_M = D.chosenLevel` is its subgroup of elements that reduce to `1` at the chosen places, and `Ω_0`
consists of the classes modulo `levelY ϑ 0` of the elements of `J_M`. The period `Ξ_1`
(`unfoldedPeriod`) is the integral, over the quotient of `U(Y_1)` by the rational Bessel group of
`Y`, of `z` times the function left by one step of unfolding of `φ` at the outer variable
`(g, c.out)` of index `0`; the others are `1`. -/
lemma integral_mul_liftY_poincareAt (ϑ : D.TameChar)
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ)
    (φ : D.SourceForm) (g : GInf D.E (D.signsY 0)) {X : Type} [Fintype X] [DecidableEq X]
    (Y : Grading (D.spaceY 1) D.N X (2 * D.ϱ)) (z : D.ConjFormY 1) :
    ∫ h : New.G D.E (D.signsY 1),
      z h * liftY ϑ 0 (D.poincareAt g t φ).val h ∂(D.spaceY 1).quotMeasure =
      stdLevelIndex (D.chosenLevel (n := D.Y 0)) * ∑ c ∈ cutPoints ϑ 0 (2 * D.ϱ + 1).zero_le,
        unfoldedPeriod ϑ t φ (update 1 0 g) (update 1 0 c.out) 0 (2 * D.ϱ + 1).zero_le Y z := by
  have h_zero : 0 ≤ 2 * D.ϱ + 1 := (2 * D.ϱ + 1).zero_le
  have hm : 0 < D.m := lt_m_of_le h_zero
  let J : Subgroup (Gf D.E (D.Y 0)) := levelY ϑ 0
  have h_index : J.relIndex D.chosenLevel * stdLevelIndex (D.chosenLevel (n := D.Y 0)) =
      stdLevelIndex J :=
    Subgroup.relIndex_mul_relIndex J _ _ (levelY_le_chosenLevel ϑ 0) levelOf_le_stdLevel
  have h_ne : stdLevelIndex J ≠ 0 := isCompact_stdLevel.relIndex_ne_zero IsLevel.isOpen
  have h_rel_ne : J.relIndex D.chosenLevel ≠ 0 := left_ne_zero_of_mul (h_index.trans_ne h_ne)
  have : Fintype (D.chosenLevel ⧸ J.subgroupOf D.chosenLevel) :=
    Subgroup.fintypeOfIndexNeZero h_rel_ne
  -- The period over `[R_0]` at `(g, x)` depends only on the class of `x` modulo `J`.
  let period (x : Gf D.E (D.Y 0)) : ℂ :=
    ∫ r : (D.gradingY 0).besselGroup,
      (D.gradingY 0).sourceFn t φ.1 r * transposedLiftY ϑ 0 z (r.1 * (g, x))
        ∂(D.gradingY 0).besselMeasure
  have period_mul (x u : Gf D.E (D.Y 0)) (hu : u ∈ J) : period (x * u) = period x := by
    have h_mul : ((g, x * u) : New.G D.E (D.signsY 0)) = (g, x) * (1, u) := by simp
    simp only [period, h_mul, ← mul_assoc, hasLevel_transposedLiftY ϑ hm z u hu]
  have period_eq (x : Gf D.E (D.Y 0)) : period x =
      stdLevelIndex J * unfoldedPeriod ϑ t φ (update 1 0 g) (update 1 0 x) 0 h_zero Y z :=
    integral_unfoldStageOn_mul_transposedLiftY ϑ t φ (update 1 0 g) (update 1 0 x) h_zero Y z
  -- Multiply by `[J_M : J]`, move the lift to `z` and apply the unfolding of the Poincaré map.
  apply mul_left_cancel₀ (Nat.cast_ne_zero.2 h_rel_ne)
  calc
    _ = J.relIndex D.chosenLevel * ∫ x : New.G D.E (D.signsY 0),
        transposedLiftY ϑ 0 z x * (D.poincareAt g t φ).val x ∂(D.spaceY 0).quotMeasure :=
      congrArg _ (integral_mul_liftY ϑ hm z _)
    _ = ∑ q : D.chosenLevel ⧸ J.subgroupOf D.chosenLevel, period q.out :=
      D.integral_mul_poincareAt g t φ (transposedLiftY ϑ 0 z) (hasLevel_transposedLiftY ϑ hm z)
    _ = ∑ c ∈ cutPoints ϑ 0 h_zero, period c.out :=
      sum_quotient_chosenLevel_eq_sum_cutPoints ϑ period_mul
    _ = _ := by
      rw [← mul_assoc, ← Nat.cast_mul, h_index, mul_sum]
      exact sum_congr rfl fun c _ ↦ period_eq c.out

/-- The outer integrals of the seesaw, one at a time. Let `t` be a linear form on the values of
forms on `X_0`, `g` an archimedean point of `U(Y_0)`, `k ≤ 2 ϱ + 1`, `Y` a grading of `Y_{k+1}`
with a string of `s = 2 ϱ + 1 - (k + 1)` vectors, and `a` a function of tuples `ξ` of archimedean
points of the groups `U(Y_i)`. There is a number `c` as follows, for every tame character `ϑ`,
ramified source form `φ` on `X_0`, conjugate form `z` on `Y_{k+1}` and function `S` of the classes
modulo `levelY ϑ i` of tuples `y` of finite points. Suppose that `unfoldedPeriod` at step `k`, the
integral of `z` times the function on `U(Y_{k+1})` left by `k + 1` steps of unfolding of `φ` at
`(ξ, y)`, is `a ξ` times `S` at the classes of `y` whenever `y 0 ∈ D.chosenLevel` and `y m = 1`,
where `m = 2 ϱ + 2`. Then the pairing of `z` with the image of the Poincaré series
`D.poincareAt g t φ` under the first `k + 1` lifts is `c` times `cutSum`: the sum of `S` over
`Ω_0 × ⋯ × Ω_k`, where `Ω_j = cutPoints ϑ j`, each term divided by the multiplicities
`cutMultiplicity` of its classes. -/
lemma exists_integral_mul_lowerChainUpTo_eq_cutSum
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ)
    (g : GInf D.E (D.signsY 0)) (k : ℕ) (hk : k ≤ 2 * D.ϱ + 1) {X : Type} [Fintype X]
    [DecidableEq X] {s : ℕ} (Y : Grading (D.spaceY (k + 1)) D.N X s)
    (hs : s = 2 * D.ϱ + 1 - (k + 1)) (a : (∀ i : ℕ, GInf D.E (D.signsY i)) → ℂ) :
    ∃ c : ℂ, ∀ (ϑ : D.TameChar) (φ : D.ramifiedSourceForms) (z : D.ConjFormY (k + 1))
      (S : (∀ i : ℕ, Gf D.E (D.Y i) ⧸ levelY ϑ i) → ℂ)
      (_h_period : ∀ (ξ : ∀ i : ℕ, GInf D.E (D.signsY i)) (y : ∀ i : ℕ, Gf D.E (D.Y i)),
        y 0 ∈ D.chosenLevel → y (2 * D.ϱ + 2) = 1 →
          unfoldedPeriod ϑ t φ ξ y k hk Y z = a ξ * S fun i : ℕ ↦ y i),
      ∫ h : New.G D.E (D.signsY (k + 1)),
        z h * lowerChainUpTo ϑ (k + 1) (D.poincareAt g t φ) h ∂(D.spaceY (k + 1)).quotMeasure =
        c * cutSum ϑ (k + 1) (Nat.succ_le_succ hk) S := by
  -- Induction on `k`, for all `a` and `S`: the step passes from `S` to its sum over `Ω_{k+1}`.
  subst hs
  have mk_update {ϑ : D.TameChar} (y : ∀ i, Gf D.E (D.Y i)) (j : ℕ) (x : Gf D.E (D.Y j)) :
      (fun i ↦ (update y j x i : Gf D.E (D.Y i) ⧸ levelY ϑ i)) = update (fun i ↦ ↑(y i)) j ↑x :=
    funext (apply_update (fun i ↦ QuotientGroup.mk (s := levelY ϑ i)) y j x)
  induction k generalizing X a with
  | zero =>
    refine ⟨stdLevelIndex (D.chosenLevel (n := D.Y 0)) * a (update 1 0 g),
      fun ϑ φ z S h_period ↦ ?_⟩
    -- On `Ω_0` the multiplicities are `1`, and `h_period` evaluates each period `Ξ_1`.
    have h_term (c : Gf D.E (D.Y 0) ⧸ levelY ϑ 0) (hc : c ∈ cutPoints ϑ 0 hk) :
        unfoldedPeriod ϑ t φ (update 1 0 g) (update 1 0 c.out) 0 hk Y z =
          a (update 1 0 g) * (cutMultiplicity ϑ 0 hk c : ℂ)⁻¹ •
            S (update (fun i : ℕ ↦ ↑(1 : Gf D.E (D.Y i))) 0 c) := by
      rw [h_period _ _ ((mk_mem_cutPoints_zero ϑ).1 (by rwa [update_self, QuotientGroup.out_eq']))
        rfl, mk_update, QuotientGroup.out_eq']
      simp [cutMultiplicity]
    refine (integral_mul_liftY_poincareAt ϑ t φ g Y z).trans ?_
    rw [mul_assoc, cutSum, cutSum, cutSumAt, mul_sum _ _ (a _)]
    exact congrArg _ (sum_congr rfl h_term)
  | succ k ih =>
    let Y₀ : Grading (D.spaceY (k + 1)) D.N (D.X (k + 1)) (2 * D.ϱ + 1 - (k + 1)) :=
      D.gradingY (k + 1) hk
    -- `a' ξ` is what the real part of the outer variable of index `k + 1` contributes.
    choose a' integral_eq using fun ξ : ∀ i : ℕ, GInf D.E (D.signsY i) ↦
      Y₀.exists_integral_eq_sum_over_cut (stdLevel D.E (D.Y (k + 1))) fun x ↦ a (update ξ (k + 1) x)
    obtain ⟨c, hc⟩ := ih (by omega) a' Y₀
    refine ⟨c, fun ϑ φ z S h_period ↦ ?_⟩
    let z' : D.ConjFormY (k + 1) := transposedLiftY ϑ (k + 1) z
    have hz' : (D.spaceY (k + 1)).IsAutomorphic z' := z'.2.toIsAutomorphic
    -- Descend `z`. It remains to show that the period of `z'` at step `k` is `a' ξ` times the
    -- weighted sum of `S` over `cutPoints ϑ (k + 1) _`.
    refine (integral_mul_liftY ϑ (lt_m_of_le hk) z _).trans
      (hc ϑ φ z' _ fun ξ y hy_zero hy_top ↦ ?_)
    let f : New.G D.E (D.signsY (k + 1)) → ℂ := unfoldStage ϑ t φ ξ y k (by omega) Y₀ * z'.1
    have h_cut : IsStageCut ϑ (k + 1) hk (cutPoints ϑ (k + 1) hk) := isStageCut_cutPoints ϑ k hk
    have h_fix : Y₀.ratBessel.FixesLeft f := fun γ hγ x ↦ by
      simp only [f, Pi.mul_apply, fixesLeft_ratBessel_unfoldStage ϑ t φ ξ y k _ Y₀ γ hγ,
        hz'.rat_mul γ hγ.1]
    have h_cover_ne_zero (x : New.G D.E (D.signsY (k + 1))) (hx : f x ≠ 0) :
        coverMultiplicity Y₀.besselFin (stdLevel D.E (D.Y (k + 1))) (cutPoints ϑ (k + 1) hk) x.2 ≠
          0 :=
      h_cut.ne_zero_of_hasBoundedOrbit x.2 <| .of_forall fun r ↦
        hasLatticeBounds_of_unfoldStage_ne_zero ϑ t φ ξ y φ.property hy_zero k hk x.1 x.2
          (left_ne_zero_of_mul hx)
    -- The recursion, with `x` as the outer variable of index `k + 1`.
    have h_step (x : New.G D.E (D.signsY (k + 1))) :
        ∫ r : Y₀.besselGroup, f (r * x) ∂Y₀.besselMeasure =
          stdLevelIndex (levelY ϑ (k + 1)) *
            (a (update ξ (k + 1) x.1) * S (update (fun i : ℕ ↦ ↑(y i)) (k + 1) ↑x.2)) := by
      have h_next := h_period (update ξ (k + 1) x.1) (update y (k + 1) x.2)
        (by rwa [update_of_ne (by omega)]) (by rwa [update_of_ne (by omega)])
      rw [← mk_update, ← h_next, ← integral_unfoldStageOn_mul_transposedLiftY]
      congr with r
      rw [unfoldStageOn_succ, unfoldStage_update (hkl := k.lt_succ_self), update_self, update_self]
      rfl
    exact integral_eq ξ (fun q ↦ S (update (fun i : ℕ ↦ ↑(y i)) (k + 1) q))
      ((continuous_unfoldStage ..).mul hz'.continuous) h_fix
      (integrable_unfoldStage_mul ϑ t φ ξ y _ Y₀ z') h_cut.mem_iff_smul_mem h_cover_ne_zero
      fun x _ ↦ h_step x

/-! ### The tensor `φ_ξ` and the seesaw identity -/

/-- The tensor product of the evaluated data (`evaluatedDatum`) of all double lifts, translated by
representatives of the classes `c j` of the outer variables of the lower chain. -/
def evaluatedTensor (ϑ : D.TameChar) (c : ∀ i : ℕ, Gf D.E (D.Y i) ⧸ levelY ϑ i) :
    D.ChainTensor :=
  pure (evaluatedDatum ϑ fun i ↦ (c i).out) (D.ϱ + 1)

/-- At the classes of a tuple `y` of points of `G_f`, `evaluatedTensor ϑ` is the pure tensor
`pure (evaluatedDatum ϑ y) (D.ϱ + 1)`, built from the first `D.ϱ + 1` evaluated data. -/
lemma evaluatedTensor_mk (ϑ : D.TameChar) (y : ∀ i : ℕ, Gf D.E (D.Y i)) :
    (evaluatedTensor ϑ fun i : ℕ ↦ y i) = pure (evaluatedDatum ϑ y) (D.ϱ + 1) := by
  rw [evaluatedTensor, evaluatedDatum_out]

/-- The tensor `φ_ξ` of finite data for the upper chain: the weighted sum `cutSum` over the cuts of
the lower chain of the evaluated translates `evaluatedTensor` of its data. -/
def seesawDatum (ϑ : D.TameChar) : D.ChainTensor :=
  cutSum ϑ (2 * D.ϱ + 2) le_rfl (evaluatedTensor ϑ)

/-- The tensor `φ_ξ = seesawDatum ϑ` of finite data for the chain of lifts `X_0 → ⋯ → X_m`, where
`ϑ` is a tame character and `m = 2 ϱ + 2`, is jointly invariant for `ϑ` (`IsInvariant`): it is fixed
by every tuple `b` with `b j` in the level `D.levelX j` of `X_j` and `b m = 1`. -/
lemma isInvariant_seesawDatum (ϑ : D.TameChar) : (seesawDatum ϑ).IsInvariant ϑ := by
  -- Translating the cut variables by the images of the tuple `b` does not change the weighted sum,
  -- and evaluation turns this translation into the joint action of `b`.
  intro b hb_top
  let bY (i : ℕ) : Gf D.E (D.Y i) :=
    if hi : i < 2 * D.ϱ + 2 then (D.gradingY i).inclXFin (b i) else 1
  rw [seesawDatum, map_cutSum, ← cutSum_comp_smul ϑ _ le_rfl (h := bY) (evaluatedTensor ϑ)
    (fun i hi ↦ ⟨b i, (b i).2, dite_eq_left hi⟩) fun i hi ↦ dite_eq_right hi.not_gt]
  congr with c
  simp only [evaluatedTensor, ← Quotient.mk_smul_out, evaluatedDatum_out,
    twoKernelAction, TensorChain.map_pure]
  refine (pure_congr fun i hi ↦ ?_).symm
  have h_lower (k : ℕ) (hk : k < 2 * D.ϱ + 2) : bY k = (D.gradingY k).inclXFin (b k) :=
    dite_eq_left hk
  have h_top : bY (2 * D.ϱ + 2) = (D.lastGrading D.m_eq_two_mul_varrho_add_two).inclXFin 1 := by
    simp [bY]
  simp only [evaluatedDatum, translatedPointDatumY, smul_eq_mul, ← Prod.mk_mul_mk, map_mul,
    Module.End.mul_apply]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
  · -- An earlier double lift is evaluated by a middle pair, which commutes with its three groups.
    simp (disch := lia) only [doubleLiftEvalY, dite_eq_left, h_lower]
    exact DoubleLiftData.finEval_arrowProduct_equivariant _ _ _ rfl _ _
  · -- The last double lift is evaluated by the last pair; there both `bY` and `b` end in `1`.
    simp (disch := lia) only [doubleLiftEvalY, dite_eq_left, dite_eq_right, h_lower, h_top, hb_top]
    exact DoubleLiftData.finEval_arrowProduct_equivariant _ _ _ (map_one _) _ _

/-- Fix an archimedean point `g` of `U(Y_0)` and a linear form `t`, and let `m = 2 ϱ + 2`. There is
a number `c₀` such that, for every tame character `ϑ` and every ramified source form `φ` on `X_0`,
the `m` lifts along `Y_0, …, Y_m` take the Poincaré series `D.poincareAt g t φ` to `c₀` times the
restriction to `Y_m` of the image of `φ` under the chain of lifts `X_0 → ⋯ → X_m` with twist `ϑ` and
tensor of finite data `seesawDatum ϑ`. -/
lemma exists_lowerChainUpTo_poincareAt_eq (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ)
    (g : GInf D.E (D.signsY 0)) :
    ∃ c₀ : ℂ, ∀ (ϑ : D.TameChar) (φ : D.ramifiedSourceForms),
      lowerChainUpTo ϑ (2 * D.ϱ + 2) (D.poincareAt g t φ) =
        c₀ • restrictToFormY D.m_eq_two_mul_varrho_add_two (chainOfTensor ϑ φ (seesawDatum ϑ)) := by
  have hm : D.m = 2 * D.ϱ + 2 := D.m_eq_two_mul_varrho_add_two
  choose c integral_top using exists_integral_eq_mul_inner_restrictToFormY hm
  -- The top function is the coefficient at `l ξ` of the chain of `ϱ + 1` double lifts, on the block
  -- embedding of `exists_integral_eq_mul_inner_restrictToFormY`.
  have h_top_coeff (ξ : ∀ i : ℕ, GInf D.E (D.signsY i)) :
      ∃ l : (WeylIndex (D.X (2 * D.ϱ + 2)) D.columnCount → ℂ) →ₗ[ℂ] ℂ,
        ∀ (ϑ : D.TameChar) (φ : D.SourceForm) (y : ∀ i : ℕ, Gf D.E (D.Y i)), y (2 * D.ϱ + 2) = 1 →
          ∀ k : New.G D.E (1 : D.InitIndex (2 * D.ϱ + 2) → ℤˣ),
            unfoldStage ϑ t φ ξ y _ le_rfl (D.lastGrading hm) ((D.lastGrading hm).inclX k) =
              algFormCoeff 1 l (doubleLiftChain (D.liftKernel ϑ) (evaluatedDatum ϑ y) (D.ϱ + 1) φ)
                (.blockEmb (e := .refl (D.InitIndex (2 * D.ϱ + 2) ⊕ Unit)) Sum.elim_one_one.symm
                  (k, 1)) := by
    -- The evaluation `doubleLiftEvalY` of the double lift `i = ϱ` is by definition that of the last
    -- pair.
    obtain ⟨l, hl⟩ := exists_unfoldStage_eq_algFormCoeff t ξ D.ϱ (by omega) _
      (hR := (dite_eq_right (lt_irrefl D.ϱ)).trans (dite_eq_left rfl)) (x := 1)
    refine ⟨l, fun ϑ φ y hy k ↦ ?_⟩
    have h_eq := hl ϑ φ y k
    rw [hy, Prod.mk_one_one, mul_one] at h_eq
    exact h_eq
  choose l h_stage using h_top_coeff
  obtain ⟨c₀, h_sum⟩ :=
    exists_integral_mul_lowerChainUpTo_eq_cutSum t g _ le_rfl (D.lastGrading hm) (by omega) (c ∘ l)
  -- Pair both sides with a form `x` on `Y_m`.
  refine ⟨c₀, fun ϑ φ ↦ ext_inner_left ℂ fun x ↦ ?_⟩
  let L : D.ChainTensor →ₗ[ℂ] ℂ := innerₛₗ ℂ x ∘ₗ restrictToFormY hm ∘ₗ chainOfTensor ϑ φ
  have h_top (ξ : ∀ i, GInf D.E (D.signsY i)) (y : ∀ i, Gf D.E (D.Y i)) (hy : y (2 * D.ϱ + 2) = 1) :
      unfoldedPeriod ϑ t φ ξ y _ le_rfl (D.lastGrading hm) ⟨_, x.2.conj⟩ =
        c (l ξ) * L (pure (evaluatedDatum ϑ y) (D.ϱ + 1)) :=
    (integral_top _ x (h_stage ξ ϑ φ y hy)).trans (by simp [L, doubleLiftChain])
  calc
    _ = c₀ * cutSum ϑ _ le_rfl fun q ↦ L (evaluatedTensor ϑ q) :=
      h_sum ϑ φ ⟨_, x.2.conj⟩ _ fun ξ y _ hy ↦ by
        rw [evaluatedTensor_mk, h_top ξ y hy, comp_apply]
    _ = c₀ * L (seesawDatum ϑ) := by rw [seesawDatum, map_cutSum]
    _ = _ := by simp [L, inner_smul_right]

/-- The tensor `φ_ξ = seesawDatum ϑ` of data for the upper chain is a combination of translated
vacuum data, with bounds. There is one number `C` as follows for every tame character `ϑ`. Let `ϑ.Q`
be its modulus, a finite set of finite places, and `q = ϑ.normQ` the product of their norms. Let
`m = 2 ϱ + 2` be the number of lifts and `B = D.residueMatrixCount = D.M ^ (D.f * D.n D.m ^ 2)`,
with `D.M` the principal level and `D.n D.m` the rank of `X_m`. An element `x` of `Translations` is
a tuple of finite adelic matrices, one for each lift, and `D.gluedVacuum x` is the tensor of the
integral vacuum data translated by `x`. Then `φ_ξ` is a finite sum `∑ r x • C • D.gluedVacuum x`,
with coefficients `r x`, over `x` in `admissibleTranslations q`. Each `B ^ (2 m) * r x` is integral
at the primes not dividing `q`. If `ϑ.Q = ∅`, then `∑ ‖σ (r x)‖ ≤ B ^ (2 ϱ + 2)` for every
automorphism `σ` of `ℂ`. -/
lemma exists_isAdmissibleCombination_seesawDatum (D : Data P) :
    ∃ C : ℂ, ∀ ϑ : D.TameChar,
      IsAdmissibleCombination (fun x : Translations (P := P) (D := D) ↦ C • D.gluedVacuum x)
        (admissibleTranslations ϑ.normQ)
        ϑ.normQ (D.residueMatrixCount ^ (2 * D.m)) (ϑ.Q = ∅) (D.residueMatrixCount ^ (2 * D.ϱ + 2))
        (seesawDatum ϑ) := by
  obtain ⟨C, h_comb⟩ := D.exists_isAdmissibleCombination_gluedVacuum
  refine ⟨C, fun ϑ ↦ ?_⟩
  -- The values of `evaluatedTensor` at integral points are such combinations with size `1`, and
  -- `seesawDatum ϑ` is an admissible combination of these values.
  have h_value (y : ∀ i : ℕ, localLevel (D.Y i) {w : FinPlace D.E | ↑ϑ.normQ ∉ w.asIdeal}) :
      IsAdmissibleCombination (fun x : Translations (P := P) (D := D) ↦ C • D.gluedVacuum x)
        (admissibleTranslations ϑ.normQ) ϑ.normQ (D.residueMatrixCount ^ (2 * D.m)) (ϑ.Q = ∅) 1
        (evaluatedTensor ϑ fun i : ℕ ↦ ⟦(y i).val⟧) := by
    simpa [evaluatedTensor_mk] using h_comb ϑ _ fun i ↦ (y i).2
  exact (isAdmissibleCombination_cutSum ϑ _ le_rfl _).bind _ 1 (fun y _ ↦ h_value y) (one_mul _).dvd
    (by simp)

end Unfolding

/-- **Seesaw identity**. Let `D` be admissible data, with field `E = D.E`, number of lifts
`m = D.m`, and hermitian spaces `X_j` (upper chain) and `Y_j` over `E`. Let `t` be a linear form on
the values of forms on `X_0` and `g` an archimedean point of `U(Y_0)`. Then there is a number
`c ≠ 0` such that every twist `ϑ` has a chain datum `Ψ` with
`lowerChain ϑ (𝒫 φ) = c • compositeLift ϑ Ψ φ` for all ramified source forms `φ` on `X_0`, where
`𝒫 = D.poincareAt g t` is the Poincaré map from forms on `X_0` to forms on `Y_0`. The datum
`Ψ` is a finitely supported function on `D.Translations`, the tuples of finite adelic matrices, one
for each lift of the upper chain; its glued tensor is the sum of `Ψ x` times the vacuum data
translated by `x`, and `compositeLift ϑ Ψ` is the upper chain from `X_0` to `X_m` with this tensor
as data, restricted to `Y_m`. That `Ψ` is a chain datum (`IsChainDatum`) means that its support is
admissible and supported at the level, its values are integral away from the modulus of `ϑ` and
bounded if this is empty, and its glued tensor is invariant under the levels of the `X_j`. -/
theorem seesaw_identity {P : Parameters} {D : Data P}
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (g : GInf D.E (D.signsY 0)) :
    ∃ c : ℂˣ, ∀ ϑ : D.Twist, ∃ Ψ : D.Translations →₀ ℂ, IsChainDatum ϑ Ψ ∧
      ∀ φ : D.ramifiedSourceForms,
        lowerChain ϑ (D.poincareAt g t φ) = (c : ℂ) • compositeLift ϑ Ψ φ := by
  obtain ⟨c₀, h_chain⟩ := exists_lowerChainUpTo_poincareAt_eq t g
  obtain ⟨C, h_admissibleComb⟩ := D.exists_isAdmissibleCombination_seesawDatum
  -- `u` is the inverse of `c₀ C / d`, with `d` the denominator of the combination. If this number
  -- is `0`, then `u = 1` and `u • c₀ • seesawDatum ϑ = 0`. In both cases `u • c₀ • seesawDatum ϑ`
  -- comes from a chain datum.
  let u : ℂˣ := normUnit (c₀ * C / (D.residueMatrixCount ^ (2 * D.m) : ℕ))
  refine ⟨u⁻¹, fun ϑ ↦ ?_⟩
  have h_rescaled : IsAdmissibleCombination D.gluedVacuum (admissibleTranslations ϑ.normQ)
      ϑ.normQ 1 (ϑ.Q = ∅) ((D.residueMatrixCount ^ (2 * D.m) : ℕ) * D.residueMatrixCount ^
        (2 * D.ϱ + 2))
      ((u : ℂ) • c₀ • seesawDatum ϑ) :=
    (h_admissibleComb ϑ).normUnit_smul c₀ NeZero.out
  -- Each translation may be replaced by a supported one with the same glued vacuum.
  obtain ⟨Ψ, h_adm, h_glued : (u : ℂ) • c₀ • seesawDatum ϑ = gluedTensor Ψ⟩ :=
    h_rescaled.of_eq_isOfFinOrder_smul
      (A' := admissibleTranslations ϑ.normQ ∩ supportedTranslations (D.M * ϑ.normQ))
      (v' := D.gluedVacuum) fun x hx ↦ by
        obtain ⟨x', hx', h_eq⟩ := D.exists_supported_translateDatum_eq hx
        exact ⟨1, .one, x', hx', by simp only [one_smul, gluedVacuum, h_eq]⟩
  have h_size : (↑(D.residueMatrixCount ^ (2 * D.m)) * D.residueMatrixCount ^ (2 * D.ϱ + 2) : ℝ) =
      D.M ^ (3 * D.f * D.m * D.n D.m ^ 2) := by
    rw [← D.m_eq_two_mul_varrho_add_two]
    -- `D.residueMatrixCount = D.M ^ (D.f * D.n D.m ^ 2)` by definition.
    push_cast
    ring
  rw [h_size] at h_adm
  refine ⟨Ψ, ⟨h_adm, fun b hb ↦ ?_⟩, fun φ ↦ ?_⟩
  · simp only [← h_glued, _root_.map_smul, isInvariant_seesawDatum _ b hb]
  have h_scaled : lowerChain ϑ ((u : ℂ) • D.poincareAt g t φ) = compositeLift ϑ Ψ φ :=
    lowerChain_eq_of_lowerChainUpTo_eq D.m_eq_two_mul_varrho_add_two <| by
      simp only [_root_.map_smul, h_chain, ← h_glued]
  rw [← h_scaled, _root_.map_smul, smul_smul, Units.inv_mul, one_smul]

end New.Data

end SeesawTheorem

end
