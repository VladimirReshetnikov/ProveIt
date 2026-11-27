import Lib.General.Groups.IndexOfProduct
import Lib.SiegelWeil.RallisInner.SharpData
import New.OneLift.HeckeValues.CharacterLift
import New.Spanning.Multiplicities.HeckeEigensystems

/-!
# The lift Θ_W, its adjoint and its norm

For a descent pair (`New.DescentPair`, a descent datum) with spaces W and V, the lift Θ_W is the
theta lift from forms on W to algebraic forms on V. The descent `New.DescentPair.normalizedDescent`
maps forms on V to functions on the adelic group of W; it is defined as a class sum and shown here
to be the adjoint of Θ_W. Both commute with the finite group of the chosen places. The finite datum
of the lift is the block datum modulo `π_M Q` times the vacuum, and the block datum is sharp for the
level `J_M`. For the pair `New.Data.descentPair D ϑ j`, which is `(W_j, V_j)` with a tame character
ξ = `ϑ`, the lift Θ_{j,ξ} = `New.Data.singleLift` goes from the forms of level `J_M` on W_j to the
definite space V_j.

## Main definitions and results

* `New.DescentPair.thetaLift`: the lift Θ_W from forms on W to forms on V. It is the lift
  `New.formLift` by the datum `New.DescentPair.fockDatum` of the highest vector, read as an
  algebraic form.
* `New.Data.singleLift`: the lift Θ_{j,ξ} on `New.Data.principalForms` on W_j. It is Θ_W for the
  pair `New.Data.descentPair` when 1 ≤ j ≤ m and 0 otherwise.
* `New.DescentPair.inner_thetaLift`: `New.DescentPair.normalizedDescent` is adjoint to
  `New.DescentPair.thetaLift`, for the Petersson product on `W` and the class sum product on `V`.
* `New.Data.coe_adjoint_singleLift`, `New.Data.normalizedDescent_eq_zero_iff`: the adjoint of
  Θ_{j,ξ} is the descent θ, so θ kills exactly the forms orthogonal to the lifts.
* `New.Data.singleLift_injective`, `New.Data.exists_hasSum_rallisTerm_inner_singleLift`: Θ_{j,ξ} is
  injective, and its Gram form is a constant `A` times the factor `New.DescentPair.gramFactor` of
  the pair times the sum of the terms `New.Data.rallisTerm`.
* `New.Data.exists_hasSum_inner_singleLift`: the same Gram form as a constant `c` times
  `New.DescentPair.twistFactor` times the sum of the terms `cosetTerm`.

Notions from other files:
* `New.Data.descentPair`: the pair of W_j, of rank r, and the definite space V_j, of rank r + t,
  with the character χ_j ξ = `New.Data.liftChar` of weight −κ_j and the places
  `New.Data.levelPlaces`.
* `New.Data.principalForms`: the forms of parameter λ^Y (twice it is `New.Data.paramW`) and level
  `J_M`, which is principal at the chosen places and maximal elsewhere.

## Relation to the literature

For every tame twist, the theta lift from U(W_j) to a definite unitary group of much larger rank is
injective, and its Gram form is a non-zero twist-free constant times an explicit count at the level
and the twist's conductor times a sum of Hecke operators. The Rallis inner product in the convergent
range, with small-support data giving injectivity at a level, is known in the literature. Related
work: J.-S. Li, Non-vanishing theorems for the cohomology of certain arithmetic quotients, 1992;
Cossutta–Marshall, Theta lifting and cohomology growth in p-adic towers, arXiv 1106.2765, 2011;
Rallis, Injectivity properties of liftings associated to Weil representations, 1984; Rallis,
L-functions and the oscillator representation, 1987.
-/

noncomputable section

namespace New

/-!
## The theta lift of a descent pair as an equivariant map of forms

* `New.DescentPair.normalizedDescent_mul_eq_normalizedDescent_formAction`: the descent θ turns the
  action `New.DescentPair.formAction` into right translation by the stabiliser of the standard
  lattice.
* `New.DescentPair.thetaLift`, `New.Data.singleLift`: the lifts, with their equivariance.
-/

section ThetaLift

open Set MulChar Space stdLevel DescentPair

variable {E r n : Type} [Field E] [CMType E] [WeilData E] [Fintype r] [DecidableEq r] [Fintype n]
  [DecidableEq n] (O : DescentPair E r n)

/-- The pair `(k, k')` scales the datum. Let `k` lie in the stabiliser of the standard lattice in
the finite adelic group of `W`, let `s` be its reduction at the chosen places of the pair, and let
`k'` be the lift to the finite adelic group of `V` of the family `diag(s_w, 1)`. The representation
`O.pairThetaKernel.ω` is the Weil representation of `U(W) × U(V)` on the Schwartz space of
`Hom(W, V)`, and `O.fockDatum ξ` is the vector of that space made of the Fock polynomial of `ξ` at
the real places and the block datum at the finite places. Here `ξ` is any vector of the
representation of weight `O.columnCount`, in coordinates indexed by `WeylIndex n O.columnCount`.
Then `(k, k')` multiplies `O.fockDatum ξ` by `χ(s)⁻¹`, where `χ(s) = ∏_w ψ_w(det s_w)` and
`ψ = O.tamePart` is the tame part of the character of the pair. -/
lemma DescentPair.omega_fockDatum_eq_inv_prod_smul (k : stdLevel E r) {s : O.ChosenGL r}
    (hk : reduceFamily O.chosenPlace k = s) (ξ : WeylIndex n O.columnCount → ℂ) :
    O.pairThetaKernel.ω
        ((1, k.val), 1, (liftResidue (firstBlockHom O.toLevelPlaces O.incl s) : stdLevel E n).val)
        (O.fockDatum ξ) =
      (∏ i : O.ChosenIndex, O.tamePart (O.chosenPlace i) (s i).val.det)⁻¹ • O.fockDatum ξ := by
  let k' : stdLevel E n := liftResidue (firstBlockHom O.toLevelPlaces O.incl s)
  have h_fin : pairWeil O.W (stdSpace E n) O.charW O.charV ((1, k.val), 1, k'.val) O.blockDatum.val
    =
      (∏ i : O.ChosenIndex, O.tamePart (O.chosenPlace i) (s i).val.det)⁻¹ • O.blockDatum.val := by
    simpa only [hk, map_one, mul_one] using
      O.omega_blockDatum_eq_smul k k' 1 (by simp [k', hk, reduceFamily_liftResidue])
  -- Finite points act only on the finite part `O.blockDatum` of the datum.
  change pairWeil O.W (stdSpace E n) O.charW O.charV ((1, k.val), 1, k'.val) (O.fockDatum ξ) = _
  rw [pairWeil_integrated_fin, h_fin, map_smul]

omit [WeilData E] in
/-- An element `s` of the finite group of the chosen places acts on a form on `V` as
`∏_w ψ_w(det s_w)` times translation by the lift of the family `diag(s_w, 1)`, whose block `s_w`
sits on the rows `O.incl`, the embedding of the indices of `W` into those of `V`. Translation is the
representation `algFormRep` on algebraic forms of weight `O.columnCount`, twisted by the power
`O.detExp` of the determinant. -/
lemma DescentPair.coe_formAction (s : O.ChosenGL r) (Ξ : O.FormV) :
    (O.formAction s Ξ).val =
      (∏ i : O.ChosenIndex, O.tamePart (O.chosenPlace i) (s i).val.det) • algFormRep O.columnCount
        O.detExp
        (liftResidue (firstBlockHom O.toLevelPlaces O.incl s) : stdLevel E n).val Ξ.val :=
  rfl

/-- Equivariance of the descent θ = `O.normalizedDescent`, which maps forms on V to functions on the
adelic group of W. Let k lie in the stabiliser of the standard lattice in the finite adelic group of
W, and let s be its reduction at the chosen places of the pair. Then (θΞ)(gk) = θ(ρ(s)Ξ)(g) for
ρ = `O.formAction`, every form Ξ on V and every adelic point g. -/
lemma DescentPair.normalizedDescent_mul_eq_normalizedDescent_formAction (k : stdLevel E r)
    {s : O.ChosenGL r} (hk : reduceFamily O.chosenPlace k = s) (Ξ : O.FormV) (g : G E O.signs) :
    O.normalizedDescent Ξ (g * (1, k.val)) = O.normalizedDescent (O.formAction s Ξ) g := by
  -- Both sides are multiples of conjugates of transposed lifts. Move `k` into the datum together
  -- with a lift `k'` of `diag(s, 1)`: the pair `(k, k')` scales the datum by `c⁻¹`, while
  -- `O.formAction s` is `c` times translation by `k'`, where `c = ∏ ψ_w(det s_w)`.
  let k' : stdLevel E n := liftResidue (firstBlockHom O.toLevelPlaces O.incl s)
  let c : ℂ := ∏ i : O.ChosenIndex, O.tamePart (O.chosenPlace i) (s i).val.det
  have h_datum : O.pairThetaKernel.swap.ω ((1, k'.val), 1, k.val)
      (O.fockDatum (highestVector O.columnCount O.paramV)) =
        c⁻¹ • O.fockDatum (highestVector O.columnCount O.paramV) :=
    O.omega_fockDatum_eq_inv_prod_smul k hk _
  have h_form : (O.formAction s Ξ).val = c • algFormRep O.columnCount O.detExp k'.val Ξ.val :=
    O.coe_formAction s Ξ
  have h_conj : starRingEnd ℂ c = c⁻¹ := by
    simp [c, ← Finset.prod_inv_distrib, ← inv_apply_eq_inv', ← star_apply']
  simp only [normalizedDescent_eq_smul_star_lift_swap, Pi.smul_apply, Pi.star_apply]
  -- The transposed lift is equivariant under the pair `(k', k)`.
  rw [h_form, O.pairThetaKernel.swap.lift_equivariant
    (isAutomorphic_algFormCoeff Ξ.val).conj _ (1, k'.val), h_datum]
  -- The scalar `c⁻¹` from the datum matches the conjugate of `c` from the conjugated form.
  simp [lift, ← algFormCoeff_algFormRep, h_conj, mul_assoc, mul_left_comm c⁻¹]

/-- If the parameter `l` on `W` fits the pair, the datum of the highest vector is an arrow from `W`
to `V`: the theta lift by it takes forms of parameter `l` to forms of parameter `O.paramV`. -/
lemma DescentPair.FitsParams.isArrow_fockDatum [Nonempty r] {O : DescentPair E r n}
    {l : NumberField.InfinitePlace E → r → ℤ} (hfit : O.FitsParams l) :
    IsArrow O.pairThetaKernel (typeKernel l O.signs) (typeKernel O.paramV 1)
      (O.fockDatum (highestVector O.columnCount O.paramV)) :=
  (hfit.isEdge.isArrow O.charW O.charV O.blockDatum.property).left

/-- If the parameter `l` on `W` fits the pair, the datum of the highest vector is an arrow from `V`
to `W` between the conjugate types, for the transposed theta kernel. -/
lemma DescentPair.FitsParams.isArrow_swap_fockDatum [Nonempty r] {O : DescentPair E r n}
    {l : NumberField.InfinitePlace E → r → ℤ} (hfit : O.FitsParams l) :
    IsArrow O.pairThetaKernel.swap (star (typeKernel O.paramV 1)) (star (typeKernel l O.signs))
      (O.fockDatum (highestVector O.columnCount O.paramV)) :=
  (hfit.isEdge.isArrow O.charW O.charV O.blockDatum.property).right

/-- The lift `Θ_W` from forms on `W`, of any level and of a parameter `l` that fits the pair, to
algebraic forms on `V`: the theta lift by the datum `O.fockDatum` of the highest vector, read as an
algebraic form. That `l` fits the pair (`New.DescentPair.FitsParams`) means that it corresponds to
the parameter `O.paramV` on `V` and to the numbering and column multiplicities of the pair;
`O.signs` are the signs of `W` and `typeKernel l O.signs` is the type of parameter `l` there. -/
noncomputable def DescentPair.thetaLift [Nonempty r] {l : NumberField.InfinitePlace E → r → ℤ}
    (hfit : O.FitsParams l) : O.W.Form (typeKernel l O.signs) →ₗ[ℂ] O.FormV :=
  (((stdSpace E n).toAlgForm O.isHCParam_paramV).toLinearMap ∘ₗ formLift O.pairThetaKernel
    (typeKernel l O.signs) (typeKernel O.paramV 1)
    (O.fockDatum (highestVector O.columnCount O.paramV))).codRestrict _ fun y ↦ by
    -- The level on `V` acts on the datum through the character of `O.FormV`.
    refine mem_levelSpace.2 fun k ↦ ?_
    have h_datum := O.omega_fockDatum_star 1 k (highestVector O.columnCount O.paramV)
    simp only [map_one, Module.End.one_apply, star_highestVector] at h_datum
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← toAlgForm_formRep,
      hfit.isArrow_fockDatum.formRep_formLift_of_eq_smul h_datum, map_one, Module.End.one_apply,
      map_smul]

/-- The function on the adelic group of `V` attached to the algebraic form `Θ_W y` is the theta lift
of `y` by the datum of the highest vector. -/
lemma DescentPair.ofAlgForm_thetaLift [Nonempty r] {l : NumberField.InfinitePlace E → r → ℤ}
    (hfit : O.FitsParams l) (y : O.W.Form (typeKernel l O.signs)) :
    ofAlgForm O.paramV 1 (O.thetaLift hfit y).val =
      formLift O.pairThetaKernel (typeKernel l O.signs) (typeKernel O.paramV 1)
        (O.fockDatum (highestVector O.columnCount O.paramV)) y :=
  ofAlgForm_toAlgForm O.isHCParam_paramV _

/-- The algebraic form underlying `Θ_W y` is the image under `New.Space.toAlgForm` of the theta
lift of `y` by the datum of the highest vector. -/
lemma DescentPair.coe_thetaLift [Nonempty r] {l : NumberField.InfinitePlace E → r → ℤ}
    (hfit : O.FitsParams l) (y : O.W.Form (typeKernel l O.signs)) :
    (O.thetaLift hfit y).val = (stdSpace E n).toAlgForm O.isHCParam_paramV
      (formLift O.pairThetaKernel (typeKernel l O.signs) (typeKernel O.paramV 1)
        (O.fockDatum (highestVector O.columnCount O.paramV)) y) :=
  rfl

/-- Let `y` be a form on `W` of a parameter `l` that fits the pair (`O.FitsParams l`). Let `k` lie
in the stabiliser of the standard lattice in the finite adelic group of `W`, with reduction `s` at
the chosen places. Then the lift `Θ_W` of the translate of `y` by `k` is `O.formAction s` applied to
`Θ_W y`. -/
lemma DescentPair.thetaLift_formRep [Nonempty r] {l : NumberField.InfinitePlace E → r → ℤ}
    (hfit : O.FitsParams l) (k : stdLevel E r) {s : O.ChosenGL r}
    (hk : reduceFamily O.chosenPlace k = s) (y : O.W.Form (typeKernel l O.signs)) :
    O.thetaLift hfit (O.W.formRep (typeKernel l O.signs) k y) =
      O.formAction s (O.thetaLift hfit y) := by
  -- With `k'` a lift of `diag(s, 1)` and `c = ∏ ψ_w(det s_w)`, the pair `(k, k')` scales the datum
  -- by `c⁻¹`, and `O.formAction s` is `c` times translation by `k'`.
  let k' : stdLevel E n := liftResidue (firstBlockHom O.toLevelPlaces O.incl s)
  let c : ℂ := ∏ i : O.ChosenIndex, O.tamePart (O.chosenPlace i) (s i).val.det
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦
    apply_ne_zero_iff.2 (s i).det_ne_zero.isUnit
  have h_datum : O.pairThetaKernel.ω ((1, k.val), 1, k'.val)
      (O.fockDatum (highestVector O.columnCount O.paramV)) = c⁻¹ • O.fockDatum
        (highestVector O.columnCount O.paramV) :=
    O.omega_fockDatum_eq_inv_prod_smul k hk _
  apply Subtype.ext
  rw [coe_formAction, coe_thetaLift, coe_thetaLift, ← toAlgForm_formRep,
    hfit.isArrow_fockDatum.formRep_formLift_of_eq_smul h_datum, map_smul, smul_inv_smul₀ hc]

/-- Let `w` be a split place such that neither `w` nor `w̄` is a chosen place or a place of the
twist, and let `y` be a form on `W` of a parameter `l` that fits the pair (`O.FitsParams l`). If `y`
is spherical at `w` and the Hecke polynomial at `X` acts on it by `p(X)`, then its lift `Θ_W y` is
spherical at `w` and the Hecke polynomial at `X` acts on it by
`∏_{i<t}(1 − q^i α X) · p(q^t α β⁻¹ X)`. Here `q` is the norm of `w`, `t` is the rank of `V` minus
the rank of `W`, and `α`, `β` are the values `New.AutChar.frobValue` at `w` of the characters
`O.charW` of `W` and `O.charV` of `V`, respectively. -/
lemma DescentPair.hasHeckePolynomial_thetaLift [Nonempty r]
    {l : NumberField.InfinitePlace E → r → ℤ}
    (hfit : O.FitsParams l) {w : FinPlace E} (hw : star w ≠ w)
    (hw_off : w ∉ O.places.conjClosure) {p : ℂ → ℂ} {y : O.W.Form (typeKernel l O.signs)}
    (hy : HasHeckePolynomial (O.W.formRep (typeKernel l O.signs)) hw p y) :
    HasHeckePolynomial (rightRegular ℂ (Gf E n) (WeylIndex n O.columnCount → ℂ)) hw
      (fun X : ℂ ↦
        SiegelWeil.qPochhammer w.q O.rankDiff (O.charW.frobValue r w * X) *
          p (w.q ^ O.rankDiff * O.charW.frobValue r w / O.charV.frobValue n w * X))
      ((O.thetaLift hfit y : O.FormV) : Gf E n → WeylIndex n O.columnCount → ℂ) := by
  -- At `w` both characters are unramified and the datum is the vacuum, so
  -- `SiegelWeil.hasHeckePolynomial_formLift` transfers the Hecke polynomial.
  obtain ⟨h_self_off, h_star_off⟩ : w ∉ O.places ∧ star w ∉ O.places := by
    simpa [conjClosure, not_or] using hw_off
  have hW_unram : CharUnramifiedAt O.charW.baseChange.finPart w :=
    AutChar.HasWeight.charUnramifiedAt rfl rfl
  have hV_unram : CharUnramifiedAt O.charV.baseChange.finPart w :=
    AutChar.HasWeight.charUnramifiedAt (O.tame_eq_one w h_self_off)
      (O.tame_eq_one (star w) h_star_off)
  have h_disjoint : Disjoint (O.levelModulus 2).places.conjClosure {w} := by
    simpa [Rows.places_levelModulus] using hw_off
  have h_vac : (O.W.hom (stdSpace E n)).projOn {w}
    (O.fockDatum (highestVector O.columnCount O.paramV)) =
      O.fockDatum (highestVector O.columnCount O.paramV) := by
    simp [blockDatum, projOn_schrodingerOp_vacElem _ h_disjoint]
  exact (hasHeckePolynomial_toAlgForm_iff _ O.isHCParam_paramV).mpr
    (SiegelWeil.hasHeckePolynomial_formLift (Nat.add_sub_cancel' O.rank_lt.le).symm hW_unram
      hV_unram hw h_vac
      hfit.isArrow_fockDatum hy)

variable {P : Parameters} (D : Data P) (ϑ : D.TameChar)

/-- The lift `Θ_{j,ξ}`, for the tame character `ξ = ϑ`, from the forms of level `J_M` on `W_j` to
the forms on `V_j`. It is the restriction of the lift `Θ_W` of the pair `D.descentPair ϑ j`, and `0`
for `j` outside `1, …, m`. -/
noncomputable def Data.singleLift (j : ℕ) :
    D.principalForms (D.spaceW j) →ₗ[ℂ] (D.descentPair ϑ j).FormV :=
  if hj : j ∈ D.LiftIndex then
    ((D.descentPair ϑ j).thetaLift (D.fitsParams_descentPair ϑ ⟨j, hj⟩)).domRestrict
      (D.principalForms (D.spaceW j))
  else 0

/-- For `1 ≤ j ≤ m`, the lift `D.singleLift ϑ j` is the theta lift of the pair
`D.descentPair ϑ j`. -/
lemma Data.singleLift_apply (j : D.LiftIndex) (y : D.principalForms (D.spaceW j)) :
    D.singleLift ϑ j y = (D.descentPair ϑ j).thetaLift (D.fitsParams_descentPair ϑ j) y.val :=
  LinearMap.congr_fun (dite_eq_left j.property) y

end ThetaLift

/-!
## Formulas for lift and descent, and the block datum

`M` is the family `chosenPlace` of chosen places and `Q` the family `twistPlace` of the places of
the twist.

* `New.DescentPair.blockFn`: the block datum as a function modulo `π_M Q`.
* `New.DescentPair.blockDatum_eq_vacuumDatum`: `New.DescentPair.blockDatum` is the vacuum datum of
  `New.DescentPair.blockFn`.
* `New.DescentPair.isSharpFn_blockFn`, `New.DescentPair.gramFactor_div_card`: the block datum is
  sharp, and the index of the level on `V` times its mass `New.DescentPair.blockMass` is `c_Q` times
  a factor of the chosen places.
-/

section AdjointOfClassSum

open Matrix Finset Fintype SiegelWeil Rows Space DescentPair LevelPlaces Fin Function Sum AutChar

attribute [local instance low] Fintype.ofFinite

variable {E r n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
  (O : DescentPair E r n)

/-- The descent `O.normalizedDescent` is adjoint to the lift `Θ_W = O.thetaLift hfit`: for a form
`y` on `W` whose parameter fits the pair `O` and a form `Ξ` on `V`, the inner product of `Θ_W y` and
`Ξ` on `V` equals the Petersson product of `y` and `O.normalizedDescent Ξ` on `W`. -/
lemma DescentPair.inner_thetaLift [WeilData E]
    [Nonempty r] {l : NumberField.InfinitePlace E → r → ℤ}
    (hfit : O.FitsParams l) (y : O.W.Form (typeKernel l O.signs)) (Ξ : O.FormV) :
    inner ℂ (O.thetaLift hfit y) Ξ = O.W.petersson y (O.normalizedDescent Ξ) := by
  -- Pass to the Petersson product on `V` (a factor `c` = index · dimension appears), then move the
  -- lift to the other side, where it becomes the conjugate `adjointLift` of the transposed lift.
  let Φ : 𝒮 (O.W.hom (stdSpace E n)) := O.fockDatum (highestVector O.columnCount O.paramV)
  let x : (stdSpace E n).Form (typeKernel O.paramV 1) :=
    ⟨ofAlgForm O.paramV 1 Ξ.val, isForm_ofAlgForm O.isHCParam_paramV Ξ.val⟩
  let c : ℂ := stdLevelIndex O.levelGroup * card (WeylIndex n O.columnCount)
  have h_star : typeKernel l O.signs = star (star (typeKernel l O.signs)) := (star_star _).symm
  let adjointLift : O.W.Form (typeKernel l O.signs) := conjForm h_star
    (formLift O.pairThetaKernel.swap (star (typeKernel O.paramV 1)) (star (typeKernel l O.signs)) Φ
      (conjForm rfl x))
  have h_adjointLift : adjointLift.val = star (lift O.pairThetaKernel.swap Φ (star x.val)) :=
    congrArg star (hfit.isArrow_swap_fockDatum.coe_formLift _)
  have h_descent : c • adjointLift.val = O.normalizedDescent Ξ := by
    rw [h_adjointLift, O.normalizedDescent_eq_smul_star_lift_swap, mul_comm]
  calc inner ℂ (O.thetaLift hfit y) Ξ
      = c * (stdSpace E n).petersson (ofAlgForm O.paramV 1 (O.thetaLift hfit y).val) x :=
        LevelForm.inner_eq_petersson (stdSpace E n) O.isHCParam_paramV _ Ξ
    _ = c * inner ℂ
          (formLift O.pairThetaKernel (typeKernel l O.signs) (typeKernel O.paramV 1) Φ y) x := by
        rw [ofAlgForm_thetaLift, inner_eq_petersson]
    _ = c * inner ℂ y adjointLift := by
        rw [hfit.isArrow_fockDatum.inner_formLift_adjoint hfit.isArrow_swap_fockDatum rfl h_star]
    _ = O.W.petersson y (O.normalizedDescent Ξ) := by
        rw [← inner_smul_right, inner_eq_petersson, ← h_descent]
        rfl

/-- If the parameter `l` on `W` fits the pair (`New.DescentPair.FitsParams`), the descent
`O.normalizedDescent Ξ` of a form `Ξ` on `V` is a form of parameter `l` on `W`. -/
lemma DescentPair.isForm_normalizedDescent [WeilData E]
    [Nonempty r] {l : NumberField.InfinitePlace E → r → ℤ} (hfit : O.FitsParams l) (Ξ : O.FormV) :
      O.W.IsForm (typeKernel l O.signs) (O.normalizedDescent Ξ) := by
  -- `O.normalizedDescent Ξ` is a multiple of the descent from `V` to `W` of the form of `Ξ`.
  let x : (stdSpace E n).Form (typeKernel O.paramV 1) :=
    ⟨ofAlgForm O.paramV 1 Ξ.val, isForm_ofAlgForm O.isHCParam_paramV Ξ.val⟩
  have h_descent : O.W.IsForm (typeKernel l O.signs) (star
      (lift O.pairThetaKernel.swap (O.fockDatum (highestVector O.columnCount O.paramV))
        (star x.val))) :=
    hfit.isEdge.isForm_star_lift_swap O.charW O.charV O.blockDatum.property x
  simpa [normalizedDescent_eq_smul_star_lift_swap] using
    h_descent.smul_add_smul O.W _ h_descent _ 0

/-- For a form `y` on `W` whose parameter fits the pair, the function `g ↦ y(g) θ_W(g, ·)` with
values in the forms on `V` is integrable on `[U(W)]`. Here `θ_W(g, ·) = O.vectorKernelForm g`. -/
lemma DescentPair.integrable_smul_vectorKernelForm [WeilData E] [Nonempty r]
    {l : NumberField.InfinitePlace E → r → ℤ} (hfit : O.FitsParams l)
    (y : O.W.Form (typeKernel l O.signs)) :
    MeasureTheory.Integrable (fun g : G E O.signs ↦ y g • O.vectorKernelForm g)
      O.W.quotMeasure := by
  -- A coordinate in an orthonormal basis is `y` times the conjugate of a form, and forms are
  -- square integrable.
  let b := stdOrthonormalBasis ℂ O.FormV
  have h_coord (i : Fin _) : MeasureTheory.Integrable
      (fun g : G E O.signs ↦ (y g * starRingEnd ℂ (O.normalizedDescent (b i) g)) • b i)
        O.W.quotMeasure :=
    (y.property.memLp.integrable_mul (O.isForm_normalizedDescent hfit (b i)).memLp.star).smul_const
      (b i)
  refine (MeasureTheory.integrable_finsetSum univ fun i _ ↦ h_coord i).congr
    (.of_forall fun g ↦ ?_)
  simp only [normalizedDescent_eq_inner_vectorKernelForm, inner_conj_symm, ← inner_smul_right,
    b.sum_repr']

/-- For the descent pair `O` and a point `g` of `U(W)(𝔸)`, `O.vectorKernelForm g` = `θ_W(g, ·)` is
an algebraic form on the definite space `V = stdSpace E n`, and `ofAlgForm O.paramV 1` turns it
into a function on `U(V)(𝔸)` (all signs `1`). This function is the theta kernel
`h ↦ θ(ω(g, h) φ_W)` of the pair, with the characters `O.charW` of `W` and `O.charV` of `V`, where
`φ_W` is the datum `O.fockDatum` of the highest weight vector of weight `O.columnCount`. -/
lemma DescentPair.ofAlgForm_vectorKernelForm [WeilData E] (g : G E O.signs) (h : G E (1 : n → ℤˣ)) :
    ofAlgForm O.paramV 1 (O.vectorKernelForm g).val h =
      pairTheta O.W (stdSpace E n) O.charW O.charV
        (O.fockDatum (highestVector O.columnCount O.paramV)) (g, h) := by
  -- The real part `x` of `h` moves the highest vector `ζ`, which is real, on both sides.
  obtain ⟨x, k⟩ := h
  let ζ : WeylIndex n O.columnCount → ℂ := highestVector O.columnCount O.paramV
  have h_move : pairWeil O.W (stdSpace E n) O.charW O.charV (1, x, 1) (O.fockDatum ζ) =
      O.fockDatum (star (conjWeylRep O.columnCount O.detExp x ζ)) := by
    simpa only [ζ, star_highestVector, map_one, one_smul, OneMemClass.coe_one] using
      O.omega_fockDatum_star x 1 ζ
  calc ofAlgForm O.paramV 1 (O.vectorKernelForm g).val (x, k)
      = gramForm ζ (conjWeylRep O.columnCount O.detExp x⁻¹ (O.vectorKernel g k)) := rfl
    _ = gramForm (conjWeylRep O.columnCount O.detExp x ζ) (O.vectorKernel g k) := by
        rw [← gramForm_conjWeylRep x, Representation.self_inv_apply]
    _ = pairTheta O.W (stdSpace E n) O.charW O.charV (O.fockDatum ζ) ((g, 1, k) * (1, x, 1)) := by
        rw [gramForm_vectorKernel, pairTheta_mul, h_move]
    _ = _ := by simp [ζ]

/-- Let the parameter `l` on `W` fit the descent pair `O`, and let `y` be a form on `W` of the type
`typeKernel l O.signs` of parameter `l` at the real places. Then the theta lift
`Θ_W y = O.thetaLift hfit y` is `∫ y(g) θ_W(g, ·) dg` over `[U(W)]`. Here
`θ_W(g, ·) = O.vectorKernelForm g`, the measure is that of the Petersson product, and the integral
has values in the forms on `V`. -/
lemma DescentPair.thetaLift_eq_integral [WeilData E]
    [Nonempty r] {l : NumberField.InfinitePlace E → r → ℤ}
    (hfit : O.FitsParams l) (y : O.W.Form (typeKernel l O.signs)) :
    O.thetaLift hfit y = ∫ g : G E O.signs, y g • O.vectorKernelForm g ∂O.W.quotMeasure := by
  -- Both sides have the same image under the injective map `ofAlgForm`.
  refine Subtype.ext (((stdSpace E n).toAlgForm O.isHCParam_paramV).symm.injective
    (Subtype.ext (funext fun h ↦ ?_)))
  let ev : O.FormV →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    (LinearMap.proj h ∘ₗ ofAlgForm O.paramV 1 ∘ₗ Submodule.subtype _)
  have h_kernel (g : G E O.signs) : ev (O.vectorKernelForm g) =
      pairTheta O.W (stdSpace E n) O.charW O.charV
        (O.fockDatum (highestVector O.columnCount O.paramV)) (g, h) :=
    O.ofAlgForm_vectorKernelForm g h
  change ofAlgForm O.paramV 1 (O.thetaLift hfit y).val h = ev _
  -- Evaluation of the image at `h` is continuous and linear, so it commutes with the integral.
  rw [ofAlgForm_thetaLift, hfit.isArrow_fockDatum.coe_formLift,
    ← ev.integral_comp_comm (O.integrable_smul_vectorKernelForm hfit y)]
  simp only [map_smul, h_kernel, smul_eq_mul, lift, pairTheta, mul_comm (y.val _)]

/-! ### The block datum and the constant in the Gram form -/

/-- Over a finite commutative ring `R`, the number of `n × r` matrices whose square block on the
rows `ι` is invertible is `card (GL r R) · (card R) ^ ((card n − card r) · card r)`: the block is an
element of `GL r R`, and the other rows are free. -/
lemma card_isUnit_submatrix {R : Type} [CommRing R] [Finite R] (ι : r ↪ n) :
    Nat.card {x : Matrix n r R // IsUnit (x.submatrix ι id)} =
      Nat.card (GL r R) * Nat.card R ^ ((card n - card r) * card r) := by
  let rows : r ⊕ {a : n // a ∉ Set.range ι} ≃ n :=
    (ι.toEquivRange.sumCongr (.refl _)).trans (Equiv.sumCompl fun a : n ↦ a ∈ Set.range ι)
  let blocks : Matrix n r R ≃ Matrix r r R × ({a : n // a ∉ Set.range ι} → r → R) :=
    (rows.symm.arrowCongr (.refl (r → R))).trans (Equiv.sumArrowEquivProdArrow r _ (r → R))
  have card_rows : Nat.card {a : n // a ∉ Set.range ι} = card n - card r := by
    have h_sum := Nat.card_congr rows
    rw [Nat.card_sum, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := n)] at h_sum
    lia
  calc Nat.card {x : Matrix n r R // IsUnit (x.submatrix ι id)}
      = Nat.card ({x' : Matrix r r R // IsUnit x'} × ({a : n // a ∉ Set.range ι} → r → R)) :=
        Nat.card_congr ((blocks.subtypeEquiv fun _ ↦ Iff.rfl).trans
          Equiv.prodSubtypeFstEquivSubtypeProd)
    _ = Nat.card {x' : Matrix r r R // IsUnit x'} * Nat.card R ^ ((card n - card r) * card r) := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, card_rows, ← pow_mul, mul_comm (Nat.card r),
          Nat.card_eq_fintype_card (α := r)]
    _ = _ := congrArg (· * _)
        (Nat.card_congr Submonoid.unitsTypeEquivIsUnitSubmonoid.toEquiv).symm

/-- The block datum as a function of `n × r` matrices `x` modulo `π_M Q = O.levelModulus 1`: with
`x_w` the reduction of `x` at `w` (`levelResidueAt`), it is `0` unless at every chosen place `x_w`
is the inclusion matrix of `O.incl`, the embedding of the indices of `W` into those of `V`, and then
it is `∏ ψ_w (det x'_w)` over the places `w` of the twist, with `x'_w` the block on the rows
`O.incl` (`New.DescentPair.residueBlockDatum`). -/
def DescentPair.blockFn (x : Matrix n r (O.levelModulus 1).ResidueRing) : ℂ :=
  O.residueBlockDatum fun i : O.ChosenIndex ⊕ O.TwistIndex ↦ x.map (levelResidueAt i)

/-- The finite datum `O.blockDatum` of the theta kernel, defined modulo `π_M² Q`, is also the datum
given by the function `O.blockFn` modulo `π_M Q = O.levelModulus 1` and the vacuum elsewhere. -/
lemma DescentPair.blockDatum_eq_vacuumDatum [WeilData E] :
    O.blockDatum = vacuumDatum O.W (stdSpace E n) (O.levelModulus 1) O.blockFn := by
  -- The two moduli have the same places, and both functions factor through the reductions there.
  refine Subtype.ext ?_
  unfold blockDatum vacuumDatum blockFn
  simp only [liftFn_eq_residueDatum places_levelModulus O.residueBlockDatum, places_levelModulus]

/-- For a complex multiplicative character `χ` of a finite field and a square matrix `X` over that
field, the squared modulus of `χ(det X)` is `1` if `X` is invertible and `0` otherwise. -/
lemma star_mulChar_det_mul_self {F : Type} [Field F] [Finite F] (χ : MulChar F ℂ)
    (X : Matrix r r F) [Decidable (IsUnit X)] :
    star (χ X.det) * χ X.det = if IsUnit X then 1 else 0 := by
  rw [MulChar.star_apply', ← MulChar.mul_apply, inv_mul_cancel]
  split_ifs with hX
  · exact MulChar.one_apply ((isUnit_iff_isUnit_det X).1 hX)
  · exact MulChar.map_nonunit _ (mt (isUnit_iff_isUnit_det X).2 hX)

omit [DecidableEq n] in
/-- Chinese remainder theorem for matrices: a matrix modulo `π_M Q = O.levelModulus 1` is the same
as the family of its reductions at the chosen places and the places of `Q`. -/
lemma DescentPair.bijective_map_levelResidueAt :
    Bijective fun (x : Matrix n r (O.levelModulus 1).ResidueRing)
      (i : O.ChosenIndex ⊕ O.TwistIndex) ↦
      (x.map (levelResidueAt i) : Matrix n r (ResField (O.placeAt i))) := by
  have h_card : Nat.card (∀ i : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (ResField (O.placeAt i))) ≤
      Nat.card (Matrix n r (O.levelModulus 1).ResidueRing) := by
    simp only [Matrix, Nat.card_pi, card_ResField, Finset.prod_const, card_univ]
    simp [O.card_levelModulus_residueRing, prod_pow]
  exact Injective.bijective_of_nat_card_le (fun x y h ↦ (Modulus.matrix_eq_iff_map_modulusResidue_eq
    O.apart.injective O.ideal_levelModulus_one).2 (congrFun h)) h_card

/-- The squared norm of the block datum `O.blockFn`: the sum of `|O.blockFn x|²` over the `n × r`
matrices `x` modulo the product `π_M Q = O.levelModulus 1` of the chosen places `M` and the places
`Q` of the twist, two finite families of places that come with the pair. The function is `0` unless
`x` is the inclusion matrix of `O.incl` at every chosen place, and is then a product over `w ∈ Q` of
characters of the determinant of the block on the rows `O.incl`. So it counts one matrix at each
chosen place; at `w ∈ Q`, of norm `q_w`, it counts the matrices whose block on those rows is
invertible, the other `O.rankDiff` rows being free. The sum is thus the order of
`O.TwistGL r = ∏_w GL_r(k_w)` times `(∏_w q_w) ^ (O.rankDiff * r)`. -/
lemma DescentPair.blockFn_normSq : star O.blockFn ⬝ᵥ O.blockFn =
    Nat.card (O.TwistGL r) * (∏ i : O.TwistIndex, (O.twistPlace i).q) ^ (O.rankDiff * card r) := by
  classical
  let e : Matrix n r (O.levelModulus 1).ResidueRing ≃ ∀ i, Matrix n r (ResField (O.placeAt i)) :=
    Equiv.ofBijective _ O.bijective_map_levelResidueAt
  -- The squared modulus of `O.blockFn` is a product of local indicators.
  let ind : ∀ i : O.ChosenIndex ⊕ O.TwistIndex, Matrix n r (ResField (O.placeAt i)) → ℂ
    | .inl _ => fun X ↦ if X = inclMatrix _ O.incl then 1 else 0
    | .inr _ => fun X ↦ if IsUnit (X.submatrix O.incl id) then 1 else 0
  have h_sq (x : Matrix n r (O.levelModulus 1).ResidueRing) :
      star (O.blockFn x) * O.blockFn x = ∏ i, ind i (e x i) := by
    rw [blockFn, residueBlockDatum, prod_sum_type]
    split_ifs with h_chosen
    · have h_one : ∏ i, ind (.inl i) (e x (.inl i)) = 1 :=
        Finset.prod_eq_one fun i _ ↦ ite_eq_left (h_chosen i)
      rw [h_one, one_mul, star_prod, ← prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ ↦ star_mulChar_det_mul_self _ _
    · obtain ⟨i, hi⟩ : ∃ i : O.ChosenIndex, e x (.inl i) ≠ inclMatrix _ O.incl :=
        not_forall.1 h_chosen
      have h_zero : ∏ i, ind (.inl i) (e x (.inl i)) = 0 :=
        prod_eq_zero (mem_univ i) (ite_eq_right hi)
      rw [mul_zero, h_zero, zero_mul]
  have h_chosen (i : O.ChosenIndex) : ∑ X, ind (.inl i) X = 1 := Fintype.sum_ite_eq' _ fun _ ↦ 1
  have h_twist (i : O.TwistIndex) : ∑ X, ind (.inr i) X =
      Nat.card (GL r (ResField (O.twistPlace i))) * (O.twistPlace i).q ^ (O.rankDiff * card r) := by
    rw [← card_ResField, ← Nat.cast_pow, ← Nat.cast_mul, DescentPair.rankDiff,
      ← card_isUnit_submatrix O.incl, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact sum_boole _ _
  calc star O.blockFn ⬝ᵥ O.blockFn
      = ∑ x : Matrix n r (O.levelModulus 1).ResidueRing, ∏ i, ind i (e x i) :=
        Finset.sum_congr rfl fun x _ ↦ h_sq x
    _ = ∑ X : ∀ i, Matrix n r (ResField (O.placeAt i)), ∏ i, ind i (X i) :=
        e.sum_comp fun X ↦ ∏ i, ind i (X i)
    _ = ∏ i, ∑ X, ind i X := (Fintype.prod_sum ind).symm
    _ = ∏ i : O.TwistIndex, (Nat.card (GL r (ResField (O.twistPlace i))) *
          (O.twistPlace i).q ^ (O.rankDiff * card r) : ℂ) := by
        simp only [prod_sum_type, h_chosen, h_twist, prod_const_one, one_mul]
    _ = Nat.card (O.TwistGL r) * (∏ i, (O.twistPlace i).q) ^ (O.rankDiff * card r) := by
        simp only [prod_mul_distrib, prod_pow, TwistGL, Nat.card_pi, Nat.cast_prod]
        rfl

/-- Let `x` be an `n × r` matrix modulo the product `π_M Q = O.levelModulus 1` of the chosen places
`M` and the places `Q` of the twist, and suppose that the block datum `O.blockFn` does not vanish at
`x`: at each chosen place `x` is the inclusion matrix of `O.incl : r ↪ n`, and at each place of the
twist its block on those rows is invertible. Then this block is the reduction modulo `π_M Q`
(`reductionGL`) of an integral point `k` of the finite adelic group of `W` that lies in the level
`J_M = levelOf O.chosenPlace ⊥` of the integral points that reduce to `1` at every chosen place. -/
lemma DescentPair.exists_reductionGL_eq_submatrix_of_blockFn_ne_zero
    {x : Matrix n r (O.levelModulus 1).ResidueRing} (hx : O.blockFn x ≠ 0) :
    ∃ k : stdLevel E r, k.val ∈ levelOf O.chosenPlace ⊥ ∧
      ((O.levelModulus 1).reductionGL k).val = x.submatrix O.incl id := by
  -- The block is `1` at the chosen places and invertible at the places of `Q`; lift this family.
  classical
  let block (i : O.ChosenIndex ⊕ O.TwistIndex) : Matrix r r (ResField (O.placeAt i)) :=
    (x.map (levelResidueAt i)).submatrix O.incl id
  rw [blockFn, residueBlockDatum, ite_ne_right_iff, prod_ne_zero_iff] at hx
  obtain ⟨hx_chosen, hx_twist⟩ := hx
  have h_chosen (i : O.ChosenIndex) : block (.inl i) = 1 :=
    calc block (.inl i) = (inclMatrix _ O.incl).submatrix O.incl id :=
          congrArg (submatrix · O.incl id) (hx_chosen i)
      _ = 1 := by rw [← inclMatrix_transpose_mul, inclMatrix_transpose_mul_self]
  have h_unit : ∀ i : O.ChosenIndex ⊕ O.TwistIndex, IsUnit (block i)
    | .inl i => by simp only [h_chosen, isUnit_one]
    | .inr i =>
      (isUnit_iff_isUnit_det _).2 (MulChar.apply_ne_zero_iff.1 (hx_twist i (mem_univ i)))
  obtain ⟨k, hk⟩ : ∃ k : stdLevel E r, stdLevel.reduceFamily O.placeAt k = fun i ↦
    (h_unit i).unit :=
    (exists_reduceFamily_eq _).imp fun _ ↦ And.right
  have h_reduce (i : O.ChosenIndex ⊕ O.TwistIndex) :
      (stdLevel.reduceAt (O.placeAt i) k).val = block i := congrArg Units.val (congrFun hk i)
  have h_one : stdLevel.reduceFamily O.chosenPlace k = 1 :=
    funext fun i ↦ Units.ext ((h_reduce (.inl i)).trans (h_chosen i))
  refine ⟨k, mem_levelOf.2 ⟨k.property, h_one⟩, (Modulus.matrix_eq_iff_map_modulusResidue_eq
    O.apart.injective O.ideal_levelModulus_one).2 fun i ↦ ?_⟩
  rw [reductionGL_map_modulusResidue, ← submatrix_map]
  exact h_reduce i

/-- Let `π_M Q = O.levelModulus 1` be the product of the chosen places and the places of the twist.
The block datum `O.blockFn`, which on matrices modulo `π_M Q` is the indicator of the inclusion
matrix at the chosen places times characters of the determinant of the block on the rows `O.incl` at
the places of the twist, is sharp for the level `J_M = levelOf O.chosenPlace ⊥`, principal at the
chosen places and maximal elsewhere. -/
lemma DescentPair.isSharpFn_blockFn [WeilData E] :
    IsSharpFn O.W (stdSpace E n) O.charV (O.levelModulus 1)
    (levelOf O.chosenPlace ⊥) O.blockFn where
  principal_le := by
    rintro _ ⟨k, hk, rfl⟩
    have h_all : stdLevel.reduceFamily O.placeAt k = 1 := O.ker_reductionGL_eq.le hk
    exact mem_levelOf.2 ⟨k.property, funext fun i ↦ congrFun h_all (.inl i)⟩
  le_stdLevel := levelOf_le_stdLevel
  ne_zero h := by
    have h_normSq : star O.blockFn ⬝ᵥ O.blockFn ≠ 0 := by simp [O.blockFn_normSq, prod_eq_zero_iff]
    simp [h] at h_normSq
  fixes k hk := by
    -- This is the transformation law of the datum for the pair `(k, 1)`.
    obtain ⟨hk_int, hk_one⟩ : ∃ hk_int : k ∈ stdLevel E r,
        stdLevel.reduceFamily O.chosenPlace ⟨k, hk_int⟩ = 1 := mem_levelOf.1 hk
    have h_law : O.pairThetaKernel.ω ((1, k), 1, 1) O.blockDatum.val = O.blockDatum.val := by
      simpa [hk_one] using O.omega_blockDatum_eq_smul ⟨k, hk_int⟩ 1 1 (by simp [hk_one])
    simpa [← blockDatum_eq_vacuumDatum, pairWeil_apply, Prod.mk_one_one] using h_law
  exists_mul_eq := ⟨(inclMatrix (O.levelModulus 1).ResidueRing O.incl)ᵀ, fun x hx ↦ by
    simpa only [inclMatrix_transpose_mul] using
      O.exists_reductionGL_eq_submatrix_of_blockFn_ne_zero hx⟩

/-- The mass `c_Ψ` of the block datum: the sum of `|O.blockFn x|²` over the `n × r` matrices `x`
modulo `π_M Q` (`New.DescentPair.blockFn_normSq`), divided by the number of these matrices and by
the index `∏_{w ∈ M} |GL_r(k_w)|` of the level `J_M`. -/
def DescentPair.blockMass : ℂ :=
  Nat.card (O.TwistGL r) * (∏ i : O.TwistIndex, (O.twistPlace i).q) ^ (O.rankDiff * card r) /
    card (n × r → (O.levelModulus 1).ResidueRing) / Nat.card (O.ChosenGL r)

/-- Suppose that the signs of `W` agree or that `π_M Q ≠ (1)`. Then the finite datum `O.blockDatum`
is sharp (`New.SiegelWeil.IsSharp`) for the level `J_M = levelOf O.chosenPlace ⊥`, off the places of
`π_M Q` and their conjugates, and its mass is `c_Ψ = O.blockMass`. -/
lemma DescentPair.isSharp_blockDatum [WeilData E]
    (hW : (∀ i j : r, O.signs i = O.signs j) ∨ Nonempty (O.levelModulus 1).places) :
    IsSharp O.charV (O.levelModulus 1).places.conjClosure O.blockDatum.val (levelOf O.chosenPlace ⊥)
      O.blockMass := by
  have h_index : stdLevelIndex (levelOf (n := r) O.chosenPlace ⊥) = Nat.card (O.ChosenGL r) :=
    relIndex_levelOf.trans Subgroup.index_bot
  simpa only [blockMass, ← O.blockFn_normSq, ← h_index, blockDatum_eq_vacuumDatum] using
    O.isSharpFn_blockFn.isSharp hW

/-- The index of the level on `V`, times the sum of `|O.blockFn x|²` over the matrices `x` modulo
`π_M Q` (`New.DescentPair.blockFn_normSq`), over the index of the level `J_M` on `W`. Divided by the
number of these matrices, it is the index of the level on `V` times the mass `c_Ψ` of the block
datum (`New.DescentPair.stdLevelIndex_mul_blockMass`), and this is `c_Q` times a factor of the
chosen places (`New.DescentPair.gramFactor_div_card`). -/
def DescentPair.gramFactor : ℂ :=
  stdLevelIndex O.levelGroup * Nat.card (O.TwistGL r) *
    (∏ w : O.TwistIndex, (O.twistPlace w).q : ℕ) ^ (O.rankDiff * card r) / Nat.card (O.ChosenGL r)

lemma DescentPair.stdLevelIndex_mul_blockMass : stdLevelIndex O.levelGroup * O.blockMass =
    O.gramFactor / card (n × r → (O.levelModulus 1).ResidueRing) := by
  rw [blockMass, gramFactor]
  ring

/-- The constant `c_Q = (Nm Q) ^ (r t) ∏_{w ∈ Q} ∏_{i = t + 1}^{t + r} (1 - q_w ^ (-i))`. Here `r`
is the rank of `W`, `t = O.rankDiff`, so that `V` has rank `r + t`, `q_w` is the norm of `w`, and
`Nm Q` is the product of the `q_w` over `w ∈ Q`. -/
def DescentPair.twistFactor : ℂ :=
  (∏ w : O.TwistIndex, ((O.twistPlace w).q : ℂ)) ^ (card r * O.rankDiff) *
    ∏ w : O.TwistIndex, ∏ i ∈ Icc (O.rankDiff + 1) (O.rankDiff + card r),
      (1 - ((O.twistPlace w).q : ℂ)⁻¹ ^ i)

/-- The contribution of the chosen places to the norm of one lift: the product over the chosen
places `w` of `∏_{i = t + 1}^{t + r} (1 - q_w ^ (-i))` divided by the order of `GL_r(k_w)`, with
`r` the rank of `W` and `t = O.rankDiff`. -/
def DescentPair.chosenFactor : ℂ :=
  ∏ w : O.ChosenIndex,
    (∏ i ∈ Icc (O.rankDiff + 1) (O.rankDiff + card r), (1 - ((O.chosenPlace w).q : ℂ)⁻¹ ^ i)) /
      Nat.card (GL r (ResField (O.chosenPlace w)))

omit [DecidableEq n] in
/-- The factor of the chosen places is not zero, since `q_w ^ i ≠ 1` for `i ≥ 1`. -/
lemma DescentPair.chosenFactor_ne_zero : O.chosenFactor ≠ 0 := by
  refine prod_ne_zero_iff.2 fun w _ ↦
    div_ne_zero (prod_ne_zero_iff.2 fun i hi ↦ ?_) (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  rw [sub_ne_zero, inv_pow, ne_comm, Ne, inv_eq_one]
  exact_mod_cast (one_lt_pow₀ (O.chosenPlace w).one_lt_q (by grind : i ≠ 0)).ne'

/-- The index of the level on `V`, times the order of `∏_{w ∈ Q} GL_r(k_w)`, is the product over all
places `w` of `M` and `Q` of the index in `GL_n(k_w)` of the group that fixes the basis vectors
indexed by `O.incl`. -/
lemma DescentPair.stdLevelIndex_levelGroup_mul_card :
    stdLevelIndex O.levelGroup * Nat.card (O.TwistGL r) =
      ∏ i : O.ChosenIndex ⊕ O.TwistIndex, (MulAction.stabilizer (GL n (ResField (O.placeAt i)))
        (inclMatrix (ResField (O.placeAt i)) O.incl).col).index := by
  -- The component of the level is this group at a place of `M` and a parabolic at a place of `Q`.
  rw [stdLevelIndex, relIndex_levelOf, descentResidueLevel, Seesaw.index_pi_univ, Nat.card_pi,
    prod_sum_type,
    prod_sum_type, mul_assoc, ← prod_mul_distrib]
  exact congrArg _ (Finset.prod_congr rfl fun w _ ↦ index_rangeParabolic_mul_card_GL O.incl)

/-- The constant `O.gramFactor` of the Gram form of the lift for the descent pair `O`, divided by
the number of `n × r` matrices modulo `π_M Q = O.levelModulus 1`, the product of the chosen places
`M` and the places `Q` of the twist, is `O.chosenFactor * O.twistFactor`. With
`t = O.rankDiff = n - r` and `f(q) = ∏_{i = t + 1}^{t + r} (1 - q ^ (-i))`, the first is
`∏_{w ∈ M} f(q_w) / |GL_r(k_w)|` and the second is `c_Q = (Nm Q) ^ (r t) ∏_{w ∈ Q} f(q_w)`, where
`q_w` is the norm of `w` and `k_w` its residue field. -/
lemma DescentPair.gramFactor_div_card :
    O.gramFactor / card (n × r → (O.levelModulus 1).ResidueRing) = O.chosenFactor *
      O.twistFactor := by
  -- At `w ∈ Q` the index of the parabolic times the order of `GL_r(k_w)` is the index of the group
  -- that fixes `r` basis vectors. This is the number of `n × r` matrices of rank `r` over `k_w`,
  -- and `fullRankProportion w` is their proportion among all `n × r` matrices.
  let fullRankProportion (w : FinPlace E) : ℂ :=
    ∏ i ∈ Icc (O.rankDiff + 1) (O.rankDiff + card r), (1 - (w.q : ℂ)⁻¹ ^ i)
  have h_count (w : FinPlace E) :
      ((MulAction.stabilizer (GL n (ResField w)) (inclMatrix (ResField w) O.incl).col).index : ℂ) =
        w.q ^ (card n * card r) * fullRankProportion w := by
    simp only [cast_index_stabilizer_inclMatrix, card_ResField, fullRankProportion, rankDiff,
      Nat.sub_add_cancel O.rank_lt.le]
  have h_card : card (n × r → (O.levelModulus 1).ResidueRing) =
      ∏ i : O.ChosenIndex ⊕ O.TwistIndex, (O.placeAt i).q ^ (card n * card r) := by
    simp [O.card_levelModulus_residueRing, prod_pow, prod_sum_type, placeAt]
  have h_card_ne :
      (∏ i : O.ChosenIndex ⊕ O.TwistIndex, ((O.placeAt i).q : ℂ) ^ (card n * card r)) ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ (Nat.cast_ne_zero.2 (O.placeAt i).one_lt_q.ne_bot)
  calc O.gramFactor / card (n × r → (O.levelModulus 1).ResidueRing)
      = (∏ i : O.ChosenIndex ⊕ O.TwistIndex, fullRankProportion (O.placeAt i)) *
          (∏ w : O.TwistIndex, (O.twistPlace w).q : ℕ) ^ (O.rankDiff * card r) /
          Nat.card (O.ChosenGL r) := by
        rw [gramFactor, ← Nat.cast_mul, stdLevelIndex_levelGroup_mul_card, h_card]
        push_cast [h_count, prod_mul_distrib]
        field_simp [h_card_ne]
    _ = O.chosenFactor * O.twistFactor := by
        rw [chosenFactor, twistFactor, prod_sum_type, prod_div_distrib, Nat.card_pi,
          mul_comm O.rankDiff]
        push_cast [fullRankProportion, placeAt, elim_inl, elim_inr]
        ring

end AdjointOfClassSum

/-!
## The lift from W_j, adjoint to the descent

`Θ_{j,ξ}` with `ξ = ϑ`, or `Θ_j` for short, is the lift `D.singleLift ϑ j`, and
`J_M = levelOf D.chosenPlace ⊥` is the level of the forms `D.principalForms`.
-/

section AdjointLift

open Matrix Finset Fintype SiegelWeil Rows Space DescentPair LevelPlaces Fin Function Sum AutChar

attribute [local instance low] Fintype.ofFinite

namespace Data

variable {P : Parameters} (D : Data P)

section FixedTwist

variable (ϑ : D.TameChar)

/-- The term of a coset `γ` in Rallis' formula for two forms `y'`, `y` of principal level on a space
`V` of rank `r`, such as `W_j`. It is `mc(γ)⟨y', R(γ)y⟩` (`New.SiegelWeil.cosetTerm`), with the
vacuum coefficient `mc` (the matrix coefficient of the vacuum vector of the Weil representation) for
the rank `r + t = card (D.Y 1)` of `V_j` and the second character `(D.descentPair ϑ j).charV` of the
pair, divided by the number of `(r + t) × r` matrices modulo `π_M Q = D.twistModulus ϑ 1`. Here
`γ` is a coset of finite points modulo those that are integral away from the places of `π_M Q` and
their conjugates. -/
abbrev rallisTerm {s : D.RowIndex → ℤˣ} (j : ℕ) (V : Space D.E D.RowIndex s)
    (y' y : D.principalForms V)
    (γ : Gf D.E D.RowIndex ⧸ localLevel D.RowIndex (D.twistModulus ϑ 1).places.conjClosureᶜ) : ℂ :=
  cosetTerm (card (D.Y 1)) (D.descentPair ϑ j).charV (D.twistModulus ϑ 1).places.conjClosureᶜ y'.val
    y.val γ /
    card (D.Y 1 × D.RowIndex → (D.twistModulus ϑ 1).ResidueRing)

/-- The series `∑_γ mc(γ) γ` of Rallis' formula for the `j`-th lift with the tame character `ϑ`, on
functions on the adelic points of a unitary group of rank `r` with signs `s`. It is
`New.SiegelWeil.rallisSeries` for the rank `r + t = card (D.Y 1)` of `V_j`, the character
`(D.descentPair ϑ j).charV`, and the places off `π_M Q = D.twistModulus ϑ 1` and its conjugate. -/
abbrev liftSeries {s : D.RowIndex → ℤˣ} (j : ℕ) : (New.G D.E s → ℂ) → New.G D.E s → ℂ :=
  rallisSeries (card (D.Y 1)) (D.descentPair ϑ j).charV (D.twistModulus ϑ 1).places.conjClosureᶜ

/-- The rank `r + t` of `V_j` exceeds twice the rank `r` of `W_j`. -/
lemma two_mul_card_rowIndex_lt : 2 * card D.RowIndex < card (D.RowIndex ⊕ Fin D.t) := by
  grind [card_rowIndex, card_rowIndex_sum_fin]

/-- The series `D.liftSeries ϑ j` of a form of level `J_M` on a space `V` of rank `r` is a form of
level `J_M` on `V`. -/
lemma exists_principalForms_eq_liftSeries {s : D.RowIndex → ℤˣ} (j : ℕ)
    {V : Space D.E D.RowIndex s} (y : D.principalForms V) :
    ∃ z : D.principalForms V, ⇑z.val = D.liftSeries ϑ j ⇑y.val := by
  -- The block datum is sharp for `J_M`. So off `π_M Q` the character is unramified, and `J_M`
  -- contains the integral points.
  have h_sharp := (D.descentPair ϑ j).isSharp_blockDatum (.inr nonempty_modulus_places)
  obtain ⟨z, hz_level, hz⟩ := exists_form_eq_rallisSeries D.two_mul_card_rowIndex_lt
    h_sharp.isUnramifiedOn h_sharp.inf_supportedOn_le
      (levelOf_le_stdLevel.trans stdLevel_le_localLevel)
    (mem_levelSpace_formRep_iff.1 y.property)
  exact ⟨⟨z, mem_levelSpace_formRep_iff.2 hz_level⟩, hz⟩

/-- Fix a tame character `ϑ`, a lift index `j` and a space `V` of rank `r` with signs `s`. The forms
`D.principalForms V` are those on `V` of the fixed parameter of `D` and of the level `J_M`,
principal at the chosen places and maximal elsewhere. Let `x`, `y`, `z` be such forms, with `z` the
series `D.liftSeries ϑ j y = ∑_γ mc(γ) γ y`. Here `γ` runs over the finite points of `U(V)` modulo
those integral away from `D.twistModulus ϑ 1` (the product of the chosen places and the places of
`ϑ`) and its conjugate, taken at representatives supported away from these places, and
`mc(γ) = vacuumCoeff (r + t) charV γ = (charV(det γ) · finMultiplier(γ) ^ (r + t))⁻¹`, for the rank
`r + t = card (D.Y 1)` of `V_j` and the character `charV` on that side of the `j`-th pair. Then
`⟨x, z⟩` is the sum of the terms `mc(γ) ⟨x, γ y⟩` (`New.SiegelWeil.cosetTerm`). -/
lemma hasSum_cosetTerm_of_eq_liftSeries {s : D.RowIndex → ℤˣ} {j : ℕ}
    {V : Space D.E D.RowIndex s} (x : D.principalForms V) {y z : D.principalForms V}
    (hz : ⇑z.val = D.liftSeries ϑ j ⇑y.val) :
    HasSum (cosetTerm (card (D.Y 1)) (D.descentPair ϑ j).charV
      (D.twistModulus ϑ 1).places.conjClosureᶜ x.val y.val)
      (inner ℂ x z) := by
  have h_inner : inner ℂ x z = V.petersson x.val (D.liftSeries ϑ j y.val) :=
    congrArg (V.petersson x.val) hz
  -- The Petersson product with the series may be taken term by term.
  have h_series := hasSum_petersson_rallisSeries (S := V) D.two_mul_card_rowIndex_lt
    (D.descentPair ϑ j).charV (D.twistModulus ϑ 1).places.conjClosureᶜ
      y.val.property.isBoundedMeasurable
    (x.val.property.memLp.integrable one_le_two) 1
  simp only [mul_one] at h_series
  rwa [h_inner]

/-- For every `j`, every tame character `ϑ` and every space `W` of rank `r` with signs `s` there is
a linear endomorphism `R` of the forms of level `J_M` on `W` that sends every form `y` to the series
`D.liftSeries ϑ j y = ∑_γ mc(γ) γ y` of the formula for the inner product of two theta lifts
(Rallis' formula). The sum is over the finite points of `U(W)` modulo those integral away from the
chosen places, the places of `ϑ` and their conjugates; `γ` acts by right translation, and
`mc(γ) = (charV(det γ) · finMultiplier(γ) ^ (r + t))⁻¹`, for the rank `r + t` of `V_j` and the
character `charV` on that side of the `j`-th pair. -/
lemma exists_end_eq_liftSeries {s : D.RowIndex → ℤˣ} (j : ℕ) (W : Space D.E D.RowIndex s) :
    ∃ R : Module.End ℂ (D.principalForms W),
      ∀ y : D.principalForms W, ⇑(R y).val = D.liftSeries ϑ j ⇑y.val := by
  choose seriesForm h_seriesForm using D.exists_principalForms_eq_liftSeries ϑ j (V := W)
  -- The form `seriesForm y` is determined by its inner products, which are sums of terms linear
  -- in `y`.
  have h_sum (x y : D.principalForms W) : HasSum
      (cosetTerm (card (D.Y 1)) (D.descentPair ϑ j).charV (D.twistModulus ϑ 1).places.conjClosureᶜ
        x.val y.val)
      (inner ℂ x (seriesForm y)) :=
    D.hasSum_cosetTerm_of_eq_liftSeries ϑ x (h_seriesForm y)
  have h_add (y y' : D.principalForms W) : seriesForm (y + y') = seriesForm y + seriesForm y' :=
    ext_inner_left ℂ fun x ↦ by
      rw [inner_add_right]
      refine (h_sum x (y + y')).unique (((h_sum x y).add (h_sum x y')).congr_fun fun γ ↦ ?_)
      rw [Submodule.coe_add, cosetTerm, cosetTerm, cosetTerm, map_add, inner_add_right, mul_add]
  have h_smul (a : ℂ) (y : D.principalForms W) : seriesForm (a • y) = a • seriesForm y :=
    ext_inner_left ℂ fun x ↦ by
      rw [inner_smul_right]
      refine (h_sum x (a • y)).unique (((h_sum x y).mul_left a).congr_fun fun γ ↦ ?_)
      rw [Submodule.coe_smul, cosetTerm, cosetTerm, map_smul, inner_smul_right, mul_left_comm]
  exact ⟨{ toFun := seriesForm, map_add' := h_add, map_smul' := h_smul }, h_seriesForm⟩

/-- The operator `Ral_{j,ξ}` on the forms of level `J_M` on a space `V` of rank `r`: it sends a form
to its series `D.liftSeries ϑ j` (`New.Data.coe_rallisOperator_apply`). -/
def rallisOperator {s : D.RowIndex → ℤˣ} (j : ℕ) (V : Space D.E D.RowIndex s) :
    Module.End ℂ (D.principalForms V) :=
  (D.exists_end_eq_liftSeries ϑ j V).choose

lemma coe_rallisOperator_apply {s : D.RowIndex → ℤˣ} (j : ℕ) (V : Space D.E D.RowIndex s)
    (y : D.principalForms V) :
    ⇑(D.rallisOperator ϑ j V y).val = D.liftSeries ϑ j ⇑y.val :=
  (D.exists_end_eq_liftSeries ϑ j V).choose_spec y

/-- The matrix coefficient `⟨x, R y⟩` of `R = D.rallisOperator ϑ j V` is the sum of the terms
`mc(γ) ⟨x, γ y⟩` (`New.SiegelWeil.cosetTerm`). -/
lemma hasSum_inner_rallisOperator {s : D.RowIndex → ℤˣ} (j : ℕ) (V : Space D.E D.RowIndex s)
    (x y : D.principalForms V) :
    HasSum (cosetTerm (card (D.Y 1)) (D.descentPair ϑ j).charV
      (D.twistModulus ϑ 1).places.conjClosureᶜ x.val y.val)
      (inner ℂ x (D.rallisOperator ϑ j V y)) :=
  D.hasSum_cosetTerm_of_eq_liftSeries ϑ x (D.coe_rallisOperator_apply ϑ j V y)

/-- Adjointness for 1 ≤ j ≤ m: the class sum inner product of the lift `D.singleLift ϑ j y` with a
form Ξ on V_j equals the Petersson product on W_j of y with the descent θΞ, the class sum
`(D.descentPair ϑ j).normalizedDescent Ξ` for the pair (W_j, V_j). -/
theorem inner_singleLift {j : D.LiftIndex} (y : D.principalForms (D.spaceW j))
    (Ξ : (D.descentPair ϑ j).FormV) :
    inner ℂ (D.singleLift ϑ j y) Ξ = (D.spaceW j).petersson y.val
      ((D.descentPair ϑ j).normalizedDescent Ξ) := by
  rw [D.singleLift_apply]
  exact (D.descentPair ϑ j).inner_thetaLift (D.fitsParams_descentPair ϑ j) y.val Ξ

/-- The adjoint of the theta lift `D.singleLift ϑ j` sends a form `Ξ` on `V_j` to the form on `W_j`
whose function on the adelic group `U(W_j)(𝔸)` is `θ Ξ`: at `g` it is the sum, over the classes `h`
of `U(V_j)` at the level of `Ξ`, of the conjugate theta kernel at `(g, h)` applied to `Ξ(h)`, each
class divided by the order of its automorphism group. -/
theorem coe_adjoint_singleLift {j : D.LiftIndex} (Ξ : (D.descentPair ϑ j).FormV) :
    (((D.singleLift ϑ j).adjoint Ξ).val : New.G D.E (D.signsW j) → ℂ) =
      (D.descentPair ϑ j).normalizedDescent Ξ := by
  let O : DescentPair D.E D.RowIndex (D.RowIndex ⊕ Fin D.t) := D.descentPair ϑ j
  -- The form `θ Ξ` has level `J_M`: integral points with trivial reduction fix it.
  have h_level : HasLevel (O.normalizedDescent Ξ) (levelOf D.chosenPlace ⊥) := by
    rintro _ ⟨k, hk : stdLevel.reduceFamily O.chosenPlace k = 1, rfl⟩ g
    change O.normalizedDescent Ξ (g * (1, k.val)) = O.normalizedDescent Ξ g
    simpa using O.normalizedDescent_mul_eq_normalizedDescent_formAction k hk Ξ g
  let descentForm : D.principalForms (D.spaceW j) :=
    ⟨⟨O.normalizedDescent Ξ, O.isForm_normalizedDescent (D.fitsParams_descentPair ϑ j) Ξ⟩,
      mem_levelSpace_formRep_iff.2 h_level⟩
  have h_eq : (D.singleLift ϑ j).adjoint Ξ = descentForm := ext_inner_left ℂ fun y ↦ by
    rw [LinearMap.adjoint_inner_right, inner_singleLift, Submodule.coe_inner, inner_eq_petersson]
  rw [h_eq]

/-- The descent is the inner product with the kernel: for a form `φ` on `V_j` and `g` in
`U(W_j)(𝔸)`, the value at `g` of the adjoint of the lift applied to `φ` is the inner product of the
form `New.DescentPair.vectorKernelForm` at `g` with `φ`. -/
theorem adjoint_singleLift_apply {j : D.LiftIndex} (φ : (D.descentPair ϑ j).FormV)
    (g : New.G D.E (D.signsW j)) :
    ((D.singleLift ϑ j).adjoint φ).val g = inner ℂ ((D.descentPair ϑ j).vectorKernelForm g) φ := by
  rw [coe_adjoint_singleLift]
  exact (D.descentPair ϑ j).normalizedDescent_eq_inner_vectorKernelForm φ g

/-- The lift is integration against the kernel: the lift of a form `y` of level `J_M` on `W_j` is
the integral over `g` in `[U(W_j)]` of `y(g)` times the form `New.DescentPair.vectorKernelForm` at
`g`. -/
theorem singleLift_eq_integral {j : D.LiftIndex} (y : D.principalForms (D.spaceW j)) :
    D.singleLift ϑ j y = ∫ g : New.G D.E (D.signsW j),
      y.val g • (D.descentPair ϑ j).vectorKernelForm g ∂(D.spaceW j).quotMeasure :=
  (D.singleLift_apply ϑ j y).trans
    ((D.descentPair ϑ j).thetaLift_eq_integral (D.fitsParams_descentPair ϑ j) y.val)

/-- For `1 ≤ j ≤ m`, a form `Ξ` on `V_j` has descent `θ Ξ = 0` exactly when it is orthogonal to the
lifts of all forms of level `J_M` on `W_j`. -/
theorem normalizedDescent_eq_zero_iff {j : D.LiftIndex} (Ξ : (D.descentPair ϑ j).FormV) :
    (D.descentPair ϑ j).normalizedDescent Ξ = 0 ↔
      ∀ y : D.principalForms (D.spaceW j), inner ℂ (D.singleLift ϑ j y) Ξ = 0 := by
  have h_descent : (D.descentPair ϑ j).normalizedDescent Ξ = 0 ↔ (D.singleLift ϑ j).adjoint Ξ =
    0 := by
    rw [← D.coe_adjoint_singleLift]
    exact ⟨fun h ↦ Subtype.ext (Subtype.ext h), fun h ↦ by rw [h]; rfl⟩
  simp only [h_descent, ← LinearMap.adjoint_inner_right]
  exact ⟨fun h y ↦ by simp [h], fun h ↦ ext_inner_left ℂ (by simpa using h)⟩

/-- The function `ofAlgForm` on the adelic group of `V_j`, applied to the algebraic form
`D.singleLift ϑ j y`, is the theta lift `formLift` of `y`. -/
lemma ofAlgForm_singleLift {j : D.LiftIndex} (y : D.principalForms (D.spaceW j)) :
    ofAlgForm (D.descentPair ϑ j).paramV 1 (D.singleLift ϑ j y).val =
      formLift (D.descentPair ϑ j).pairThetaKernel (typeKernel D.paramW (D.signsW j))
        (typeKernel (D.descentPair ϑ j).paramV 1)
        ((D.descentPair ϑ j).fockDatum (highestVector (D.descentPair ϑ j).columnCount
          (D.descentPair ϑ j).paramV))
        y.val := by
  rw [D.singleLift_apply]
  exact (D.descentPair ϑ j).ofAlgForm_thetaLift (D.fitsParams_descentPair ϑ j) y.val

end FixedTwist

/-- Let `ϑ` be a tame character, that is a weight `0` character of `U(1)(𝔸)` that is at most tamely
ramified, at a finite set of places, and let `j` lie in `D.LiftIndex`, the integers `1, …, m` for
the number `m = D.m` of lifts of the data. Then the theta lift `D.singleLift ϑ j` by the `j`-th pair
twisted by `ϑ` is injective. -/
theorem singleLift_injective (ϑ : D.TameChar) {j : D.LiftIndex} :
    Injective (D.singleLift ϑ j) := by
  -- The block datum is sharp for `J_M`, so Rallis' formula gives the injectivity of the lift `L`.
  let O : DescentPair D.E D.RowIndex (D.RowIndex ⊕ Fin D.t) := D.descentPair ϑ j
  let L : O.W.Form (typeKernel D.paramW O.signs) →ₗ[ℂ]
      (stdSpace D.E (D.RowIndex ⊕ Fin D.t)).Form (typeKernel O.paramV 1) :=
    formLift O.pairThetaKernel (typeKernel D.paramW O.signs) (typeKernel O.paramV 1)
      (O.fockDatum (highestVector O.columnCount O.paramV))
  obtain ⟨C, -, h_rallis⟩ := rallis_inner_product_cosetTerm (S := D.spaceW j)
    (T := stdSpace D.E (D.RowIndex ⊕ Fin D.t)) (D.fitsParams_descentPair ϑ j).isEdge
    D.two_mul_card_rowIndex_lt
  refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_
  have h_inj : L y.val = 0 → y.val = 0 :=
    (h_rallis O.charW O.charV (O.isSharp_blockDatum (.inr nonempty_modulus_places)) y.val
      (mem_levelSpace_formRep_iff.1 y.property)).left
  have h_up : ofAlgForm O.paramV 1 (D.singleLift ϑ j y).val = L y.val := D.ofAlgForm_singleLift ϑ y
  have h_zero : L y.val = 0 := Subtype.ext (by rw [← h_up, hy]; exact map_zero _)
  exact Subtype.ext (h_inj h_zero)

/-- For `1 ≤ j ≤ m` there is a constant `A ≠ 0` such that for every tame character `ϑ` the Gram form
`⟨Θ_j x, Θ_j y⟩` of the theta lift `Θ_j = D.singleLift ϑ j` on the forms of level `J_M` on `W_j` is
`A` times `gramFactor` times the sum over `γ` of `mc(γ)⟨x, γ y⟩ / #matrices`. Here
`π_M Q = D.twistModulus ϑ 1` is the product of the chosen places and the places of `ϑ`. The index
`γ` runs over the finite points (`Gf`) of `U(W_j)` modulo the subgroup `localLevel` of those that
are integral away from the places of `π_M Q` and their conjugates. The coefficient is
`mc(γ) = (charV(det γ) · finMultiplier(γ) ^ (r + t))⁻¹`, with `r + t` the rank of `V_j` and
`#matrices` the number of `(r + t) × r` matrices modulo `π_M Q`. -/
theorem exists_hasSum_rallisTerm_inner_singleLift (j : D.LiftIndex) :
    ∃ A : ℂ, A ≠ 0 ∧ ∀ (ϑ : D.TameChar) (x y : D.principalForms (D.spaceW j)),
      HasSum (fun γ : Gf D.E D.RowIndex ⧸ localLevel D.RowIndex
        (D.twistModulus ϑ 1).places.conjClosureᶜ ↦
          A * (D.descentPair ϑ j).gramFactor * D.rallisTerm ϑ j (D.spaceW j) x y γ)
        (inner ℂ (D.singleLift ϑ j x) (D.singleLift ϑ j y)) := by
  -- The block datum is sharp for `J_M`, so Rallis' formula gives the Gram form of the lift `L`.
  -- The constant `C` depends only on the real data, which do not involve `ϑ`, as `ϑ` has weight
  -- `0`; they are written for the trivial character.
  obtain ⟨C, hC, h_rallis⟩ := rallis_inner_product_cosetTerm (S := D.spaceW j)
    (T := stdSpace D.E (D.RowIndex ⊕ Fin D.t)) (D.fitsParams_descentPair .one j).isEdge
    D.two_mul_card_rowIndex_lt
  let dim : ℂ := card (WeylIndex (D.Y 1) (D.descentPair .one j).columnCount)
  refine ⟨C * dim, mul_ne_zero hC NeZero.out, fun ϑ x y ↦ ?_⟩
  let O : DescentPair D.E D.RowIndex (D.RowIndex ⊕ Fin D.t) := D.descentPair ϑ j
  let V : Space D.E (D.RowIndex ⊕ Fin D.t) 1 := stdSpace D.E (D.RowIndex ⊕ Fin D.t)
  let L : O.W.Form (typeKernel D.paramW O.signs) →ₗ[ℂ] V.Form (typeKernel O.paramV 1) :=
    formLift O.pairThetaKernel (typeKernel D.paramW O.signs) (typeKernel O.paramV 1)
      (O.fockDatum (highestVector O.columnCount O.paramV))
  let term : Gf D.E D.RowIndex ⧸ localLevel D.RowIndex (D.twistModulus ϑ 1).places.conjClosureᶜ →
    ℂ :=
    cosetTerm (card (D.Y 1)) O.charV (D.twistModulus ϑ 1).places.conjClosureᶜ x.val y.val
  have h_gram : HasSum (fun γ ↦ C * O.blockMass * term γ) (V.petersson (L x.val) (L y.val)) :=
    (h_rallis O.charW O.charV (O.isSharp_blockDatum (.inr nonempty_modulus_places)) y.val
      (mem_levelSpace_formRep_iff.1 y.property)).right x.val
  -- The class sum product is index · dimension · `⟨L x, L y⟩`.
  have h_inner : inner ℂ (D.singleLift ϑ j x) (D.singleLift ϑ j y) =
      stdLevelIndex O.levelGroup * dim * V.petersson (L x.val) (L y.val) := by
    rw [LevelForm.inner_eq_petersson V O.isHCParam_paramV (D.singleLift ϑ j x),
      D.ofAlgForm_singleLift ϑ x, D.ofAlgForm_singleLift ϑ y]
    rfl
  have h_mass : stdLevelIndex O.levelGroup * O.blockMass =
      O.gramFactor / card (D.Y 1 × D.RowIndex → (D.twistModulus ϑ 1).ResidueRing) :=
        O.stdLevelIndex_mul_blockMass
  rw [h_inner]
  refine (h_gram.mul_left _).congr_fun fun γ ↦ ?_
  calc C * dim * O.gramFactor * D.rallisTerm ϑ j (D.spaceW j) x y γ
      = C * dim * (O.gramFactor / card (D.Y 1 × D.RowIndex → (D.twistModulus ϑ 1).ResidueRing)) *
        term γ := by
        rw [rallisTerm]; ring
    _ = stdLevelIndex O.levelGroup * dim * (C * O.blockMass * term γ) := by rw [← h_mass]; ring

/-- The Gram form of one lift, term by term: for `1 ≤ j ≤ m`, on the forms of level `J_M` on the
rank `r` space `W_j` of the data `D`, `⟨Θ_j x, Θ_j y⟩ = ∑_γ c_j c_Q mc(γ) ⟨x, γ y⟩`, with
`Θ_j = D.singleLift ϑ j` the theta lift to the definite space `V_j` of rank `r + t`. The constant
`c_j ≠ 0` does not depend on the tame character `ϑ`. With `Q` the places of `ϑ`, `c_Q` is
`New.DescentPair.twistFactor`. The sum runs over the finite points of `U(W_j)` modulo those that are
integral away from the places of `π_M Q = D.twistModulus ϑ 1` and their conjugates. As in
`New.SiegelWeil.cosetTerm`, a coset is represented by a point `γ` supported away from these places,
which acts by right translation. Its coefficient `mc(γ) = (charV(det γ) · finMultiplier(γ) ^
(r + t))⁻¹` (`New.SiegelWeil.vacuumCoeff`) is that by which `γ` changes the matrix coefficient of
the unramified vector of the Weil representation, for the character
`charV = (D.descentPair ϑ j).charV` on the side of `V_j`. -/
theorem exists_hasSum_inner_singleLift (j : D.LiftIndex) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (ϑ : D.TameChar) (x y : D.principalForms (D.spaceW j)),
      HasSum (fun γ : Gf D.E D.RowIndex ⧸ localLevel D.RowIndex
        (D.twistModulus ϑ 1).places.conjClosureᶜ ↦
          c * (D.descentPair ϑ j).twistFactor *
            cosetTerm (card (D.Y 1)) (D.descentPair ϑ j).charV
              (D.twistModulus ϑ 1).places.conjClosureᶜ x.val y.val γ)
        (inner ℂ (D.singleLift ϑ j x) (D.singleLift ϑ j y)) := by
  obtain ⟨A, hA, h_gram⟩ := D.exists_hasSum_rallisTerm_inner_singleLift j
  refine ⟨A * (D.descentPair .one j).chosenFactor, mul_ne_zero hA (chosenFactor_ne_zero _),
    fun ϑ x y ↦ (h_gram ϑ x y).congr_fun fun γ ↦ ?_⟩
  -- The chosen places and the ranks do not depend on `ϑ`.
  have h_factor : (D.descentPair ϑ j).gramFactor / card
    (D.Y 1 × D.RowIndex → (D.twistModulus ϑ 1).ResidueRing) =
      (D.descentPair .one j).chosenFactor * (D.descentPair ϑ j).twistFactor :=
    (D.descentPair ϑ j).gramFactor_div_card
  rw [mul_assoc A, ← h_factor, rallisTerm]
  ring

/-- **Norm of one lift.** For `1 ≤ j ≤ m` there is a constant `c_j ≠ 0` such that for every tame
character `ϑ` the lift `Θ_j = D.singleLift ϑ j` satisfies `Θ_j^* Θ_j = c_j c_Q R` on the forms of
level `J_M` on `W_j`. Here `c_Q` is `New.DescentPair.twistFactor` and `R` is the series of Rallis'
formula (`New.Data.rallisOperator`). -/
theorem exists_adjoint_singleLift_comp_eq (j : D.LiftIndex) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ ϑ : D.TameChar,
      (D.singleLift ϑ j).adjoint ∘ₗ D.singleLift ϑ j =
        (c * (D.descentPair ϑ j).twistFactor) • D.rallisOperator ϑ j (D.spaceW j) := by
  obtain ⟨c, hc, h_gram⟩ := D.exists_hasSum_inner_singleLift j
  refine ⟨c, hc, fun ϑ ↦ LinearMap.ext fun y ↦ ext_inner_left ℂ fun x ↦ ?_⟩
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, LinearMap.smul_apply, inner_smul_right]
  exact (h_gram ϑ x y).unique ((D.hasSum_inner_rallisOperator ϑ j (D.spaceW j) x y).mul_left _)

/-- Let `ϑ` be a tame character, let `1 ≤ j ≤ m`, and let `y` be a form of level `J_M` on `W_j` in
`D.eigenPart (D.spaceW j) p`: each `D.heckeOperator (w, i)`, which is `T_{w,i}` at a split place `w`
not above `M` and `0` elsewhere, acts on `y` by `p (w, i)`. Then at each split `w` with `w`, `w̄`
off the chosen places and those of the twist, the lift `D.singleLift ϑ j y` is spherical. Its Hecke
polynomial is the q-Pochhammer polynomial of rank `t` times the rank `r` polynomial of the
eigenvalues `p (w, ·)`, both at rescaled variables. -/
theorem hasLiftHeckePolynomial_singleLift (ϑ : D.TameChar) {j : D.LiftIndex}
    {p : FinPlace D.E × ℕ → ℂ} {y : D.principalForms (D.spaceW j)}
    (hy : y ∈ D.eigenPart (D.spaceW j) p) :
    (D.descentPair ϑ j).HasLiftHeckePolynomial (D.singleLift ϑ j y) fun (w : FinPlace D.E) (i : ℕ) ↦
      p (w, i) := by
  intro w hw hw_off
  -- The chosen places are among the places of the pair.
  have h_off : w ∉ (Set.range D.chosenPlace).conjClosure := by simp_all [descentPair, levelPlaces]
  rw [D.singleLift_apply]
  exact (D.descentPair ϑ j).hasHeckePolynomial_thetaLift (D.fitsParams_descentPair ϑ j) hw hw_off
    (D.hasHeckePolynomial_of_mem_eigenPart _ hy ⟨hw, h_off⟩)

/-- Let `ϑ` be a tame character, let `1 ≤ j ≤ m`, and let `w` be a split place such that `w` and
`w̄` are neither chosen places nor places of the twist. The Hecke polynomial operator
`H_w(X) = ∑_i (−X)^i q^{i(i−1)/2} T_{w,i}` on the forms on `V_j`, at the value `X = (α q^{t−1})⁻¹`,
kills the lift `D.singleLift ϑ j y` of every form `y` of level `J_M` on `W_j`. Here `q` is the norm
of `w` and `α` is the Frobenius value at `w` of the character `(D.descentPair ϑ j).charW`, the
character of the pair on the side of `W_j`. -/
theorem heckePolyOnForms_liftHeckeRoot_singleLift_eq_zero (ϑ : D.TameChar) {j : D.LiftIndex}
    {w : FinPlace D.E} (hw : star w ≠ w) (hw_off : w ∉ (D.descentPair ϑ j).places.conjClosure)
    (y : D.principalForms (D.spaceW j)) :
    (D.descentPair ϑ j).heckePolyOnForms hw hw_off ((D.descentPair ϑ j).liftHeckeRoot w)
      (D.singleLift ϑ j y) = 0 := by
  -- The forms with an eigensystem span, and the lift of such a form is killed.
  let heckeCompLift : D.principalForms (D.spaceW j) →ₗ[ℂ] (D.descentPair ϑ j).FormV :=
    (D.descentPair ϑ j).heckePolyOnForms hw hw_off ((D.descentPair ϑ j).liftHeckeRoot w) ∘ₗ
      D.singleLift ϑ j
  have h_eigen (p : FinPlace D.E × ℕ → ℂ) :
      D.eigenPart (D.spaceW j) p ≤ LinearMap.ker heckeCompLift :=
    fun x hx ↦ heckePolyOnForms_liftHeckeRoot_eq_zero hw hw_off
      (D.hasLiftHeckePolynomial_singleLift ϑ hx)
  exact (D.iSup_eigenPart_eq_top (D.spaceW j)).ge.trans (iSup_le h_eigen) Submodule.mem_top

/-- The lift `D.singleLift ϑ j` commutes with the finite group `D.chosenGL = ∏ GL_r(k_w)` of the
chosen places, which acts on the forms on `W_j` by `New.Data.principalRep` and on the forms on `V_j`
by `New.DescentPair.formAction`. -/
theorem singleLift_principalRep (ϑ : D.TameChar) {j : D.LiftIndex} (s : D.chosenGL)
    (y : D.principalForms (D.spaceW j)) :
    D.singleLift ϑ j (D.principalRep (D.spaceW j) s y) =
      (D.descentPair ϑ j).formAction s (D.singleLift ϑ j y) := by
  rw [D.singleLift_apply, D.singleLift_apply]
  exact (D.descentPair ϑ j).thetaLift_formRep (D.fitsParams_descentPair ϑ j) _
    (reduceFamily_liftResidue (w := D.chosenPlace) s) y.val

end Data

end AdjointLift

end New

end
