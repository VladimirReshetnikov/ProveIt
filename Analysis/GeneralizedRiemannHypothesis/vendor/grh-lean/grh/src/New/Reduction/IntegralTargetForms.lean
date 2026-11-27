import New.Determinant.Chain.NormOfChain
import New.Reduction.Lattices.TwistedLattice

/-!
# The target forms as a twisted lattice

The target forms `D.targetForms` have no evident integral structure, so a target form is called
integral if its lifts are. The maps `Θ_ϑ`, with the inner products, conjugates and integrality of
algebraic forms, make the target a twisted lattice (`New.Data.targetLattice`). Its twists are the
`m`-fold twists `ϑ`, and `ϑ` is allowed at `l` if the norm of its modulus is prime to `l`. The file
identifies the integral vectors, the conjugate norms and the volumes of this lattice.

Notions from other files:
* `New.TwistedLattice`: maps `Θ_ϑ` from a space to inner product spaces with integral structures.
* `New.Data.targetForms`: the target forms, the good forms on the space `Y_0`.
* `New.Data.TameChar`: an automorphic character `ϑ` of `U(1)` of weight `0` whose tame part is
  supported on a finite set `Q` of places, its modulus.
* `New.Data.MFoldTwist`: a twist `ϑ` whose tame part `ψ` has `ψ_w^n ≠ 1` for `w ∈ Q`, `1 ≤ n ≤ m`.
* `New.Data.Θ`: the chain of `m` lifts with twist `ϑ`, from the target forms to forms on `Y_m`.
* `New.Data.lastResidueLevel`: the group of reductions that cuts out the level of the forms on
  `Y_m`.
* `New.LevelPlaces.LevelForm.integralForms`: the forms integral at an embedding `ℂ → ℂ_l`.
-/

noncomputable section

namespace New.Data

open LevelPlaces.LevelForm

variable {P : Parameters} {D : Data P}

/-- Let `ϑ` be a tame character. Its level places, listed by `placeAt`, are the chosen places and
the places of `Q`. The left side is the group of elements of the finite adelic unitary group of
`Y_m` that are integral at every finite place and whose reductions lie in `lastResidueLevel ϑ`, that
is, are `1` at the chosen places and block upper triangular at the places of `Q`. It lies in
`D.chosenLevel`, the integral elements that reduce to `1` at every chosen place. -/
lemma levelOf_lastResidueLevel_le_chosenLevel (ϑ : D.TameChar) :
    levelOf (D.levelPlaces ϑ).placeAt (lastResidueLevel ϑ) ≤ D.chosenLevel := by
  refine Subgroup.map_mono fun k hk ↦ ?_
  rw [Subgroup.mem_comap, Subgroup.mem_bot]
  funext w
  exact eq_one_of_mem_lastResidueLevel ϑ hk w

/-- Let `ϑ` be a tame character, and `K` the level cut out by `lastResidueLevel ϑ`: the integral
elements that reduce to `1` at the chosen places and to a block upper triangular matrix at the
places of `Q`. Then `K` is sufficiently small: for every `g`, the stabiliser
`classAut Γ K g = Γ ∩ gKg⁻¹` of the coset `gK` in the group `Γ = stdRatPoints` of rational points is
trivial. -/
lemma classAut_lastResidueLevel_eq_bot (ϑ : D.TameChar) (g : Gf D.E (D.Y D.m)) :
    classAut stdRatPoints (levelOf (D.levelPlaces ϑ).placeAt (lastResidueLevel ϑ)) g = ⊥ := by
  have h_card : Fintype.card (D.Y D.m) ≤ 2 * D.n D.m := by linarith [D.card_Y_le le_rfl]
  exact D.classAut_eq_bot_of_le_chosenLevel (levelOf_lastResidueLevel_le_chosenLevel ϑ) h_card g

variable (D) in
/-- The target forms `D.targetForms` as a twisted lattice. Its twists are the `m`-fold twists `ϑ`:
twists whose tame part `ψ` has `ψ_w^n ≠ 1` for `1 ≤ n ≤ m` and `w` in its modulus, a finite set `Q`
of places. The map at `ϑ` is the chain of lifts `Θ_ϑ` to the forms on `Y_m` with the level and
character of `ϑ` and the weight given by the column counts `D.columnsY` and the last entries
`D.lastEntry D.m`. The lattice at `ι` consists of the forms integral at `ι`, and `ϑ` is allowed at
`l` if the norm `ϑ.normQ` of its modulus is prime to `l`. The coordinates of a form for the
trivial twist are those of its values at representatives of the classes, in the standard basis of
the Weyl module. -/
def targetLattice : TwistedLattice D.targetForms D.MFoldTwist where
  Space (ϑ : D.MFoldTwist) := (D.levelPlaces ϑ.toTameChar).LevelForm (lastResidueLevel ϑ.toTameChar)
    (lastLevelChar ϑ.toTameChar) D.columnsY (D.lastEntry D.m)
  lift := D.Θ
  IsAllowed (l : ℕ) (ϑ : D.MFoldTwist) := l.Coprime ϑ.normQ
  lattice (_ : D.MFoldTwist) (ι : PrimePadicIso) := integralForms ι.place
  norm_inner_le_one {ϑ} ι _ φ hφ φ' hφ' := by
    -- The place of `ῑ` is that of `ι` composed with complex conjugation.
    have hφ_conj : φ ∈ integralForms ⟨ι.place.ιₚ.comp (starRingEnd ℂ)⟩ := hφ
    have h_card (g : Gf D.E (D.Y D.m)) : Nat.card (classAut stdRatPoints
        (levelOf (D.levelPlaces ϑ.toTameChar).placeAt (lastResidueLevel ϑ.toTameChar)) g) ∣ 1 := by
      rw [classAut_lastResidueLevel_eq_bot, Subgroup.card_bot]
    have h_bound : ‖ι.place.ιₚ ((1 : ℕ) • inner ℂ φ φ')‖ ≤ 1 :=
      norm_nsmul_inner_le_one φ φ' ι.place h_card hφ_conj hφ'
    rwa [one_nsmul, ι.norm_place] at h_bound
  Coord := ValueIndex (lastResidueLevel (1 : D.MFoldTwist).toTameChar) D.columnsY
  coord := valueCoord
  gramMatrix := valueMetric (lastResidueLevel (1 : D.MFoldTwist).toTameChar) D.columnsY
  posDef_gramMatrix := posDef_valueMetric
  inner_eq := inner_eq_valueCoord (classAut_lastResidueLevel_eq_bot _)

/-- Let `y` be a target form: an automorphic form on the unitary group of the space `Y_0`, of
principal level at the chosen places, in the image of the idempotent `D.e₀`. Let `ι : ℂ ≃ ℚ̄_l`,
where `l = ι.prime`, and let `ι.place` be the embedding `ℂ → ℂ_l` that it gives. Then `y` is an
integral vector of the twisted lattice at `ι` if and only if `Θ_ϑ y` is integral at `ι.place` for
every `ϑ` with `ϑ.normQ` prime to `l`. -/
lemma mem_integralVectors_targetLattice {ι : PrimePadicIso} {y : D.targetForms} :
    y ∈ D.targetLattice.integralVectors ι ↔
      ∀ ϑ : D.MFoldTwist, Nat.Coprime ι.prime ϑ.normQ → D.Θ ϑ y ∈ integralForms ι.place :=
  TwistedLattice.mem_integralVectors

/-- Let `y` be a target form, `σ ∈ Aut ℂ`, and `φ = Θ₁ y` the lift of `y` to an algebraic form on
`Y_m` for the trivial twist, of level `K`. The coordinates of `y` in the twisted lattice are those
of the values `φ(g_c)` in the standard basis of the Weyl module, where `g_c` runs over
representatives of the classes `c ∈ Γ\G_f/K`. The left side is the sum over `c` of the squared norms
of the vectors `σ(φ(g_c))` for the Gram matrix of the Weyl module. The right side `‖φ‖²_σ` is the
same sum with the term at `c` divided by `#(Γ ∩ g_c K g_c⁻¹)`. They agree since these stabilisers
are trivial. -/
lemma normSqAt_targetLattice (y : D.targetForms) (σ : ℂ ≃+* ℂ) :
    D.targetLattice.normSqAt y σ = (D.Θ 1 y).normSqAt σ :=
  (normSqAt_eq_re_valueCoord (classAut_lastResidueLevel_eq_bot _) σ (D.Θ 1 y)).symm

/-- The volume of the twisted lattice of target forms at `ϑ` is
`chainDeterminant(ϑ) = det (Θ_ϑ* Θ_ϑ)`. -/
lemma volume_targetLattice (ϑ : D.MFoldTwist) : D.targetLattice.volume ϑ = D.chainDeterminant ϑ :=
  rfl

/-- For every `m`-fold twist `ϑ`, the map `D.targetLattice.lift ϑ` is injective on the target forms
`D.targetForms`. -/
lemma injective_lift_targetLattice (ϑ : D.MFoldTwist) :
    Function.Injective (D.targetLattice.lift ϑ) := by
  change Function.Injective (D.lowerChainAtLevel ϑ ∘ D.targetForms.subtype)
  exact (D.lowerChainAtLevel_injective ϑ).comp D.targetForms.injective_subtype

end New.Data

end
