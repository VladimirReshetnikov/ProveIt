import Lib.Weil.Periods.Unfolding
import New.UpperBound.Objects.CharactersAtLevel
import New.UpperBound.Objects.RowChain
import New.UpperBound.Seesaw.Frequency
import New.UpperBound.Seesaw.GluedLevel
import New.UpperBound.Seesaw.LevelIdeles
import New.UpperBound.Seesaw.Sandwich

/-!
# Unfolding the chain of lifts: double lifts and the functions of the unfolding

A double theta integral over two definite unitary groups is a coefficient of the composite of two
lifts. Two unfolding steps give the double lift of the finite evaluation. Starting from `𝒲_φ`, each
unfolding step then gives an equivariant function on the next group `R_j`. Their supports are
bounded when the source form is ramified.

## Main definitions and results

* `New.Seesaw.DoubleLiftData.exists_integral_constTermAtStringMap_mul_eq`: take the product of two
  constant terms. Integrate it over the Bessel subgroup `New.Grading.besselGroup` of `Y'`, and over
  that of `Y` against an equivariant function `W`. The result is an integral over the unitary group
  of `X`. Its integrand is `W` times a constant times a theta integral over the unitary group of
  `X'`. The theta integral is of the datum translated by `New.Seesaw.stackedStringMap` and cut down
  along `New.Seesaw.DoubleLiftData.splitting`.
* `New.Data.unfoldStage`: the function `𝒲_{k+1}` that the first `k + 1` unfolding steps leave;
  `New.Data.exists_unfoldStage_eq_algFormCoeff` evaluates it after each double lift.
* `New.Data.hasLatticeBounds_of_unfoldStage_ne_zero`: the support lemma, in terms of graded
  lattices.

Notions from other files:
* `New.Grading`: A presentation of a hermitian space as a definite part `X` (grade 0) plus a string
  of `s` graded basis vectors; `Y.inclX` embeds the unitary group of `X`.
* `New.Seesaw.DoubleLiftData`: For gradings `Y, Y', Y''` of `V, V', V''`, it identifies the
  grade-zero part of V⁻ ⊕ V'' with X⁻ ⊕ X'' plus hyperbolic planes.
* `New.Space.Splitting.zeroTerm`: For a splitting with frames `i`, `k`, the map that sends a datum f
  to y ↦ the mean of f(i y + k b) over adelic vectors b modulo rational ones.
* `New.Seesaw.flipSum`: For hermitian spaces V and V'', the orthogonal sum V⁻ ⊕ V'' of V with its
  form negated and V''.
* `New.Seesaw.stackedStringMap`: The adelic map (T*, T') from V' to V⁻ ⊕ V'', where
  `T = Y.stringMap Y'` and `T' = Y'.stringMap Y''`.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work. See
`Lib.Weil.CompactLift.DefiniteThetaLift` for sources.
-/

/-!
## Two unfolding steps and the double lift of the finite evaluation

Notation as in `New.UpperBound.Seesaw.EdgePairEvaluation`. `D : New.Seesaw.DoubleLiftData X'' q Y Y'
Y''` describes three graded spaces `V, V', V''` with definite parts. `New.Seesaw.arrowProduct` joins
data on `Hom (V, V')` and `Hom (V', V'')`, and `New.Seesaw.tripleWeil` is the joint Weil action.
`New.stdSpace E X` is the standard definite space on `X`, and `(stdSpace E X).quotMeasure`
integrates over its unitary group modulo rational points. `New.Grading.constTermAtStringMap` is the
constant term at the map `Y.stringMap Y'` along maps of positive degree. `New.algFormCoeff 1 t φ` is
the coefficient of an algebraic form `φ` at a linear form `t`.
-/

namespace New.Seesaw

open Matrix MeasureTheory Space Subtype Fintype Exchange Splitting Grading LinearMap MvPolynomial
  Subgroup Fock CoordChange Finset

variable {E ι ι' ι'' X X' X'' X₀ q : Type} [Field E] [CMType E] [WeilData E] [Fintype ι]
  [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype ι''] [DecidableEq ι''] [Fintype X]
  [DecidableEq X] [Fintype X'] [DecidableEq X'] [Fintype X''] [DecidableEq X''] [Fintype X₀]
  [DecidableEq X₀] [Fintype q] [DecidableEq q] {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ} {N : E}
  {s s' s'' : ℕ} {V : Space E ι ε} {V' : Space E ι' ε'} {V'' : Space E ι'' ε''}
  {Y : Grading V N X s} {Y' : Grading V' N X' s'} {Y'' : Grading V'' N X₀ s''}

/-- A coefficient of an algebraic form times the theta function of a triple Weil translate is
integrable over the compact quotients of the two definite unitary groups. -/
lemma integrable_algFormCoeff_mul_theta_tripleWeil {κ : NumberField.InfinitePlace E → ℕ → ℕ}
    {e : NumberField.InfinitePlace E → ℤ} (a b : AutChar E)
    (t : (WeylIndex X κ → ℂ) →ₗ[ℂ] ℂ) (φ : ↥(AlgForm X κ e)) (g : G E (1 : X'' → ℤˣ))
    (f : 𝒮 ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X'')))) :
    Integrable (fun x : G E (1 : X → ℤˣ) × G E (1 : X' → ℤˣ) ↦ algFormCoeff 1 t φ x.1 *
        θ ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X'')))
          (tripleWeil a b (x.1, x.2, g) f))
      ((stdSpace E X).quotMeasure.prod (stdSpace E X').quotMeasure) := by
  obtain ⟨h_cont, h_rat, -⟩ := (stdSpace E X).isAutomorphic_algFormCoeff (L := t) φ
  refine integrable_of_isCocompact (isCocompact_prod (stdSpace E X).isCocompact_Gamma
    (stdSpace E X').isCocompact_Gamma) ?_ ?_
  · -- the coefficient is continuous and the Weil action is continuous in the group points
    simp [tripleWeil, pairChar, mul_assoc, -circleChar_inv_apply]
    fun_prop
  · -- both factors are invariant under rational points
    rintro ⟨γ, δ⟩ ⟨hγ, hδ⟩ ⟨x, r⟩
    simp only [Prod.mk_mul_mk, h_rat γ hγ x, theta_tripleWeil_rat_mul a b f γ hγ δ hδ x r g]

/-- Write `P ⊗ Φ` for `integrated` applied to the Fock vector `polyVector P` and the finite datum
`Φ`. Combining with `arrowProduct` the data `P ⊗ Φ` on `Hom(X, X')` and `Q ⊗ Φ'` on `Hom(X', X'')`,
for polynomials `P` and `Q`, gives the datum `P Q ⊗ arrowTensor (Φ ⊗ Φ')` on `Hom(X', X⁻ ⊕ X'')`.
The variables of `P` are transposed into the block of `X`, and those of `Q` go into the block of
`X''`. -/
lemma arrowProduct_integrated_polyVector (P : MvPolynomial (NumberField.InfinitePlace E × X' × X) ℂ)
    (Q : MvPolynomial (NumberField.InfinitePlace E × X'' × X') ℂ)
    (Φ : ((stdSpace E X).hom (stdSpace E X')).finitePart)
    (Φ' : ((stdSpace E X').hom (stdSpace E X'')).finitePart) :
    arrowProduct
        (integrated ((stdSpace E X).hom (stdSpace E X'))
          (polyVector (realSigns E (homSigns (1 : X → ℤˣ) (1 : X' → ℤˣ))) P) Φ)
        (integrated ((stdSpace E X').hom (stdSpace E X''))
          (polyVector (realSigns E (homSigns (1 : X' → ℤˣ) (1 : X'' → ℤˣ))) Q) Φ') =
      integrated ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X'')))
        (polyVector (realSigns E (homSigns (1 : X' → ℤˣ) (-(1 : X → ℤˣ) ⊕ᵥ (1 : X'' → ℤˣ))))
          (rename (fun (v, j, i) ↦ (v, Sum.inl i, j)) P *
            rename (fun (v, i, j) ↦ (v, Sum.inr i, j)) Q))
        (arrowTensor (Φ ⊗ₜ Φ')) := by
  simp [arrowProduct, flipPoly, pairSign, rename_eq_aeval, bind₁_bind₁, map_integrated,
    realMap_flipCoords_polyVector, boxProd_integrated, realBoxProd_polyVector]
  -- the two descriptions of the renamed variables of `P` and `Q` agree by definition
  rfl

/-- Write U(X) for the adelic unitary group of the standard definite space `stdSpace E X`, and
`flipSum` for the sum X⁻ ⊕ X'' of X with its form negated and X''. Let the families `k`, `k'`
compute the theta lifts of algebraic forms from `X` to `X'` and from `X'` to `X''` (`IsThetaLift`)
for the characters `rankTwist (a o)` and `rankTwist (b o)`, the twists of the automorphic characters
`a o`, `b o` of U(1) by a power of a fixed character that depends on the rank. Let `L o` be the
composite lift, which sends `Φ ⊗ Φ'` to `k' o Φ' ∘ k o Φ`. For every vector `u` of the Fock space of
`Hom(X', X⁻ ⊕ X'')` and every linear form `t` there is a linear form `t''` with the following
property for all `o`, finite data `y`, forms `φ` and points `g` of U(X''). Carry `y` to
`Hom(X', X⁻ ⊕ X'')` by `arrowTensor`, tensor it with `u` (`integrated`), and move it by `(x, r, g)`
under the Weil action `tripleWeil (a o) (b o)` of U(X) × U(X') × U(X''). Integrate its theta value
over `r`, and then over `x` against the coefficient of `φ` at `t`, both modulo rational points. The
result is the coefficient of `L o y φ` at `t''`, taken at `g`. -/
lemma integral_theta_tripleWeil_eq_lift_comp {κ : NumberField.InfinitePlace E → ℕ → ℕ}
    {e e' e'' : NumberField.InfinitePlace E → ℤ} {O : Type*}
    {k : O → ↥((stdSpace E X).hom (stdSpace E X')).finitePart →ₗ[ℂ]
      ↥(AlgForm X κ e) →ₗ[ℂ] ↥(AlgForm X' κ e')}
    {k' : O → ↥((stdSpace E X').hom (stdSpace E X'')).finitePart →ₗ[ℂ]
      ↥(AlgForm X' κ e') →ₗ[ℂ] ↥(AlgForm X'' κ e'')}
    {a b : O → AutChar E} (hk : IsThetaLift κ e e' (fun o : O ↦ rankTwist (a o)) k)
    (hk' : IsThetaLift κ e' e'' (fun o : O ↦ rankTwist (b o)) k')
    (u : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E
      (homSigns (1 : X' → ℤˣ) (-(1 : X → ℤˣ) ⊕ᵥ (1 : X'' → ℤˣ))))))
    (t : (WeylIndex X κ → ℂ) →ₗ[ℂ] ℂ) :
    -- the composite lift: `L o (Φ ⊗ₜ Φ')` is `k' o Φ'` after `k o Φ`
    let L (o : O) : TensorProduct ℂ ↥((stdSpace E X).hom (stdSpace E X')).finitePart
        ↥((stdSpace E X').hom (stdSpace E X'')).finitePart →ₗ[ℂ]
          ↥(AlgForm X κ e) →ₗ[ℂ] ↥(AlgForm X'' κ e'') :=
      TensorProduct.lift (LinearMap.flip
        (compl₁₂ (llcomp ℂ (AlgForm X κ e) (AlgForm X' κ e') (AlgForm X'' κ e'')) (k' o) (k o)))
    ∃ t'' : (WeylIndex X'' κ → ℂ) →ₗ[ℂ] ℂ, ∀ (o : O)
      (y : TensorProduct ℂ ↥((stdSpace E X).hom (stdSpace E X')).finitePart
        ↥((stdSpace E X').hom (stdSpace E X'')).finitePart)
      (φ : ↥(AlgForm X κ e)) (g : G E (1 : X'' → ℤˣ)),
      ∫ x : G E (1 : X → ℤˣ), algFormCoeff 1 t φ x *
          ∫ r : G E (1 : X' → ℤˣ),
            θ ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X'')))
              (tripleWeil (V'' := stdSpace E X'') (a o) (b o) (x, r, g)
                (integrated ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X''))) u
                  (arrowTensor y))) ∂(stdSpace E X').quotMeasure
        ∂(stdSpace E X).quotMeasure =
      algFormCoeff 1 t'' (L o y φ) g := by
  -- The families given by a linear form `t''` make up a finite-dimensional, hence closed, space,
  -- and the family of integrals `J u` is continuous in `u`. So it suffices to take for `u` a Fock
  -- polynomial, a sum of products `P Q`, and then the double integral is an iterated theta lift.
  intro L
  obtain ⟨z, -, hz⟩ := theta_arrowProduct (stdSpace E X) (stdSpace E X') (stdSpace E X'')
  let F (o : O) (φ : AlgForm X κ e) (g : G E (1 : X'' → ℤˣ))
      (x : G E (1 : X → ℤˣ) × G E (1 : X' → ℤˣ)) :
      𝒮 ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X''))) →L[ℂ] ℂ :=
    algFormCoeff 1 t φ x.1 •
      θ ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X''))) ∘L
        tripleWeil (V'' := stdSpace E X'') (a o) (b o) (x.1, x.2, g)
  have hF {o : O} {φ : AlgForm X κ e} {g : G E (1 : X'' → ℤˣ)}
      (f : 𝒮 ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X'')))) :
      Integrable (F o φ g · f) ((stdSpace E X).quotMeasure.prod (stdSpace E X').quotMeasure) := by
    simpa [F] using integrable_algFormCoeff_mul_theta_tripleWeil (a o) (b o) t φ g f
  let J (u : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E
        (homSigns (1 : X' → ℤˣ) (-(1 : X → ℤˣ) ⊕ᵥ (1 : X'' → ℤˣ)))))) (o : O)
      (y : TensorProduct ℂ ↥((stdSpace E X).hom (stdSpace E X')).finitePart
        ↥((stdSpace E X').hom (stdSpace E X'')).finitePart)
      (φ : AlgForm X κ e) (g : G E (1 : X'' → ℤˣ)) : ℂ :=
    strongIntegral ((stdSpace E X).quotMeasure.prod (stdSpace E X').quotMeasure) (F o φ g)
      (integrated ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X''))) u (arrowTensor y))
  have hJ (u) (o : O) (y) (φ : AlgForm X κ e) (g : G E (1 : X'' → ℤˣ)) : J u o y φ g =
      ∫ x : G E (1 : X → ℤˣ) × G E (1 : X' → ℤˣ), F o φ g x
        (integrated ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X''))) u
          (arrowTensor y)) ∂(stdSpace E X).quotMeasure.prod (stdSpace E X').quotMeasure := by
    simp [J, strongIntegral_apply, hF]
  -- `Λ t''` is the family on the right side of the claim, a linear function of `t''`.
  let Λ := IsLinearMap.mk' (R := ℂ)
    (fun (t'' : (WeylIndex X'' κ → ℂ) →ₗ[ℂ] ℂ) (o : O) y (φ : AlgForm X κ e) ↦
      algFormCoeff 1 t'' (L o y φ))
    ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  suffices h_mem : ∀ u, J u ∈ Λ.range by
    obtain ⟨t'', ht''⟩ := h_mem u
    refine ⟨t'', fun o y φ g ↦ ?_⟩
    have h_eq : J u o y φ g = algFormCoeff 1 t'' (L o y φ) g := by
      rw [← ht'']
      rfl
    rw [← h_eq, hJ, integral_prod _ (hF _)]
    simp [F, integral_const_mul]
  refine isClosed_property denseRange_polyVector
    (Λ.range.closed_of_finiteDimensional.preimage_of_continuous (f := J)) fun R ↦ ?_
  -- `R` is a sum of products of a polynomial on `Hom(X, X')` and one on `Hom(X', X'')`.
  let inl : NumberField.InfinitePlace E × X' × X → NumberField.InfinitePlace E × (X ⊕ X'') × X' :=
    fun (v, j, i) ↦ (v, Sum.inl i, j)
  let inr : NumberField.InfinitePlace E × X'' × X' → NumberField.InfinitePlace E × (X ⊕ X'') × X' :=
    fun (v, i, j) ↦ (v, Sum.inr i, j)
  have hR : R ∈ (rename inl).range.toSubmodule * (rename (R := ℂ) inr).range.toSubmodule :=
    mem_rename_range_mul inl inr (by simp [inl, inr]) R
  -- the polynomials that satisfy the claim are closed under addition, so products suffice
  have h_add (u₁ u₂) : J (u₁ + u₂) = J u₁ + J u₂ := by
    ext
    simp [J]
  refine Submodule.mul_induction_on hR ?_ fun P₁ P₂ h₁ h₂ ↦ by
    simpa only [Set.mem_preimage, SetLike.mem_coe, map_add, h_add] using add_mem h₁ h₂
  rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩
  obtain ⟨t', ht'⟩ := hk P t
  obtain ⟨t'', ht''⟩ := hk' (z • Q) t'
  use t''
  ext o y φ g
  change algFormCoeff 1 t'' (L o y φ) g = _
  induction y with
  | tmul Φ Φ' =>
    -- Unfold the left side by `ht''` and `ht'`: both sides are iterated integrals, and by `hz`
    -- the kernel of `P Q` is `z` times the product of the two theta kernels.
    have h_lift : L o (Φ ⊗ₜ Φ') φ = k' o Φ' (k o Φ φ) := by simp [L]
    rw [h_lift, ← ht'', hJ, integral_prod_symm _ (hF _)]
    refine integral_congr_ae (.of_forall fun r ↦ ?_)
    simp only [← ht', ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [F, map_smul, smul_eq_mul, mul_assoc, _root_.smul_apply,
      ContinuousLinearMap.comp_apply]
    have h_reorder (θQ θP c : ℂ) : z * (θQ * (θP * c)) = c * (z * (θP * θQ)) := by ring
    rw [h_reorder, ← hz, arrowProduct_twistedPairWeil, arrowProduct_integrated_polyVector]
    rfl
  | add y y' ih ih' =>
    rw [map_add, LinearMap.add_apply, map_add, Pi.add_apply, ih, ih']
    simp [J]

/-- Let `Y, Y', Y''` be gradings of the hermitian spaces `V, V', V''`, and let `D` be data for two
consecutive lifts. The constant term `Y.constTerm Y'.gradeOf f w` is the mean of the theta function
of `f`, Heisenberg translated by `w` (`homHeisenbergOp w`), over the maps `V → V'` that raise
grades. The datum `arrowProduct f f'` on `Hom(V', V⁻ ⊕ V'')` joins `f` and `f'`, where `V⁻` is `V`
with its form negated; by `hθ` its theta value is `z ≠ 0` times the product of those of `f` and
`f'`. The splitting `D.homZeroPart.splitting` cuts `Hom(V', V⁻ ⊕ V'')` down to its part of degree
zero, and its zero term is the mean over the maps of positive degree. Then the product of the
constant terms of `f` at `w` and of `f'` at `w'` is `z⁻¹` times the value at 0 of the zero term of
the join of the two translates. -/
lemma DoubleLiftData.constTerm_mul_constTerm_eq_inv_mul_zeroTerm (D : DoubleLiftData X'' q Y Y' Y'')
    {z : ℂ} (hz : z ≠ 0)
    (hθ : ∀ (f : 𝒮 (V.hom V')) (f' : 𝒮 (V'.hom V'')),
      θ (V'.hom (flipSum V V'')) (arrowProduct f f') = z * ((V.hom V').θ f * (V'.hom V'').θ f'))
    (f : 𝒮 (V.hom V')) (f' : 𝒮 (V'.hom V'')) (w : Matrix ι' ι (𝔸 E)) (w' : Matrix ι'' ι' (𝔸 E)) :
    Y.constTerm Y'.gradeOf f w * Y'.constTerm Y''.gradeOf f' w' = z⁻¹ *
      D.homZeroPart.splitting.zeroTerm
        (arrowProduct (homHeisenbergOp w f) (homHeisenbergOp w' f')) 0 := by
  -- The right side is a mean over the maps V' → V⁻ ⊕ V'' of positive degree. Such a map is a pair
  -- (a*, a') with a : V → V' and a' : V' → V'', so the mean is an iterated mean over a and a',
  -- and `hθ` factors the integrand.
  -- `φ (a, a')` is the map (a*, a'), cut down to its entries of positive degree
  let φ : (ι' × ι → 𝔸 E) × (ι'' × ι' → 𝔸 E) →+
      ({r : (ι ⊕ ι'') × ι' // 0 < (Y.gradeOf ⊕ᵥ Y''.gradeOf) r.1 - Y'.gradeOf r.2} → 𝔸 E) :=
    .mk' (fun a ↦ matrixToVec ((V.formAdjoint V' (vecToMatrix a.1)).fromRows (vecToMatrix a.2)) ∘
      val)
      (by simp [funext_iff, Y.formAdjoint_apply Y', mul_add, add_mul, vecToMatrix, matrixToVec])
  have h_cont : Continuous φ := by
    simp [continuous_pi_iff, φ, Y.formAdjoint_apply Y', -continuous_prodMk, vecToMatrix,
      matrixToVec, mul_assoc]
    exact ⟨by fun_prop, by fun_prop⟩
  have h_rat : ∀ᵉ (a ∈ ratVectors E (ι' × ι)) (a' ∈ ratVectors E (ι'' × ι')),
      φ (a, a') ∈ ratVectors E _ := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    simp [mem_ratVectors, φ, Y.formAdjoint_apply Y', ← map_mul, ratAdeles, vecToMatrix, matrixToVec]
  have h_onto : Function.Surjective φ := by
    intro b₀
    obtain ⟨b, rfl⟩ := val_injective.surjective_comp_right b₀
    -- every entry comes from the pair (rows₁ b)*, rows₂ b
    use (matrixToVec (V'.formAdjoint V (vecToMatrix b).toRows₁),
      matrixToVec (vecToMatrix b).toRows₂)
    change matrixToVec (fromRows _ _) ∘ val = _
    simp [formAdjoint_formAdjoint]
  rw [eq_inv_mul_iff_mul_eq₀ hz, Splitting.zeroTerm_apply,
    ← quotMean_quotMean (ratVectors E (ι' × ι)) (isContPeriodic_along_k ..)
      (ratVectors E (ι'' × ι')) φ h_cont h_rat h_onto]
  -- both sides become double integrals of `θ` of one translate of `arrowProduct f f'`
  simp_rw [constTerm, quotMean, ← integral_mul_const, ← integral_const_mul, ← theta_rho, ← hθ,
    ← homHeisenbergOp_arrowProduct, homHeisenbergOp, ← x_inv_mulVec_matrixToVec, mulVec_zero,
    zero_add]
  congr! with a a'
  -- the translation vectors agree: (a*, a') has positive degree when a and a' have
  rw [← kAdelic_mulVec D.homZeroPart.splitting rfl]
  · congr 1
    simp +contextual [_root_.funext_iff, φ, Y.formAdjoint_apply Y', matrixToVec, vecToMatrix]
  · simp +contextual [Y.formAdjoint_apply Y', matrixToVec, vecToMatrix, LE.le.not_gt]

/-- The adjoint of a map (A, B) into V⁻ ⊕ V'' is (−A*, B*). -/
lemma formAdjoint_fromRows (A : Matrix ι ι' (𝔸 E)) (B : Matrix ι'' ι' (𝔸 E)) :
    V'.formAdjoint (flipSum V V'') (A.fromRows B) =
      (-V'.formAdjoint V A).fromCols (V'.formAdjoint V'' B) := by
  simp [formAdjoint, flipSpace, ← Matrix.ext_iff, Matrix.mul_apply]

/-- Let `D` be data for the two consecutive lifts `Y → Y' → Y''`, and let `n` be a unipotent element
of U(V'), with matrix `V'.ratCoordMatrix n` in rational coordinates. Let
`S = stackedStringMap Y Y' Y''` be the map (T*, T') from V' to V⁻ ⊕ V'' made of the maps `T`, `T'`
between consecutive strings. As a vector of `Hom(V', V⁻ ⊕ V'')` in adelic coordinates
(`homAtPoint`), the map `S (n - 1)` is a sum of two parts. The first is a map of positive degree,
with entries `y`. The second is a map of degree zero that sends `X'` into an isotropic half of the
hyperbolic planes indexed by `q`. Its matrix is `Y'.genericConst`, the constant of the grading,
times the block of `n - 1` whose rows are the basis vectors `D.gradeOne` of grade one and whose
columns are `X'`. -/
lemma DoubleLiftData.exists_add_eq_homAtPoint_stackedStringMap (D : DoubleLiftData X'' q Y Y' Y'')
    {n : G E ε'} (hn : n ∈ Y'.unipotent) :
    ∃ y : { i : (ι ⊕ ι'') × ι' // 0 < (Y.gradeOf ⊕ᵥ Y''.gradeOf) i.1 - Y'.gradeOf i.2 } → 𝔸 E,
      D.homZeroPart.splitting.kAdelic *ᵥ y +
          D.homZeroPart.splitting.iAdelic *ᵥ ((removePlanes q (flipSum (stdSpace E X)
            (stdSpace E X''))).homTarget (stdSpace E X')).kAdelic *ᵥ (fun p : q × X' ↦
            ↑Y'.genericConst * (V'.ratCoordMatrix n - 1) (D.gradeOne p.1)
              (Y'.indexEquiv (Sum.inl p.2))) =
        V'.homAtPoint (flipSum V V'') (stackedStringMap Y Y' Y'' * (V'.ratCoordMatrix n - 1)) := by
  obtain rfl : s' = s - 1 := D.length_middle
  obtain rfl : s'' = s - 1 - 1 := D.length_last
  -- in rational coordinates, the difference u of the two vectors lives in positive degree
  let σ := D.homZeroPart.splitting
  let planes := (removePlanes q (flipSum (stdSpace E X) (stdSpace E X''))).homTarget (stdSpace E X')
  let u : (ι ⊕ ι'') × ι' → 𝔸 E :=
    matrixToVec (stackedStringMap Y Y' Y'' * (V'.ratCoordMatrix n - 1)) -
      (σ.i.map toAdele *
        ((stdSpace E X').hom (hyperbolicSum q (flipSum (stdSpace E X) (stdSpace E X'')))).x.val) *ᵥ
        planes.kAdelic *ᵥ fun p : q × X' ↦
          ↑Y'.genericConst * (V'.ratCoordMatrix n - 1) (D.gradeOne p.1) (Y'.indexEquiv (.inl p.2))
  have hu (p) (hp : ¬0 < (Y.gradeOf ⊕ᵥ Y''.gradeOf) p.1 - Y'.gradeOf p.2) : u p = 0 := by
    obtain h_ne | ⟨⟨i, l⟩, rfl⟩ := not_or_of_imp (D.homZeroPart.mem_range_index p).mpr
    · -- negative degree: `stackedStringMap` has degree ≥ -1 and n - 1 has degree ≥ 1, so the first
      -- term vanishes; the second term lives in degree zero
      have h_deg : HasDegreeGe (Y.gradeOf ⊕ᵥ Y''.gradeOf) Y'.gradeOf (-1)
          (stackedStringMap Y Y' Y'') := by
        rintro (i | i)
        · simp +contextual [stackedStringMap, Y.formAdjoint_apply Y',
            Y.hasDegreeGe_neg_one_stringMap _, add_comm]
        · exact Y'.hasDegreeGe_neg_one_stringMap i
      simp [u, σ, D.homZeroPart.incl_eq_zero, h_ne,
        ↓h_deg.mul (Y'.mem_unipotent.mp hn) le_rfl p.1 p.2 (by omega), GradeZeroPart.splitting,
        matrixToVec, Matrix.mul_apply, mulVec, dotProduct]
    · -- degree zero: p is a basis vector of the weight-zero part; compute the entry by
      -- `D.stackedStringMap_apply`
      simp [u, σ, planes, homZeroPart, GradeZeroPart.hom, D.stackedStringMap_apply, homTarget,
        removePlanes, inclMatrix, sum_prod_type, apply_ite toAdele, sum_mul, sum_comm, kAdelic,
        Matrix.mul_assoc, GradeZeroPart.splitting, Matrix.one_apply, matrixToVec, Matrix.mul_apply,
        mulVec, dotProduct, mul_assoc]
  -- the frame `k` returns `u`, and the frame `i` adds back what was subtracted
  use u ∘ val
  rw [show σ.kAdelic *ᵥ u ∘ val = (↑(V'.hom (flipSum V V'')).x⁻¹ : Matrix _ _ _) *ᵥ u from
    kAdelic_mulVec σ rfl hu, iAdelic, Space.ratMap, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_add,
    sub_add_cancel, x_inv_mulVec_matrixToVec]

/-- The stacked map `stackedStringMap Y Y' Y''` = (T*, T'), with `T = Y.stringMap Y'` and
`T' = Y'.stringMap Y''`, is isotropic. Its `formAdjoint` for `flipSum V V''` times it is -T T* + T'*
T' = 0: given the double-lift data `D`, both products depend only on `Y'` and the common constant
`genericConst`. -/
lemma formAdjoint_stackedStringMap_mul_stackedStringMap (D : DoubleLiftData X'' q Y Y' Y'') :
    V'.formAdjoint (flipSum V V'') (stackedStringMap Y Y' Y'') * stackedStringMap Y Y' Y'' = 0 := by
  obtain rfl : s' = s - 1 := D.length_middle
  obtain rfl : s'' = s - 1 - 1 := D.length_last
  rw [stackedStringMap, formAdjoint_fromRows]
  simp [formAdjoint_stringMap_mul_stringMap, D.c_eq, formAdjoint_formAdjoint, fromCols_mul_fromRows]

/-- In the second argument `h` of `constTermAtStringMap`, a unipotent `n` in `Y'.unipotent` moves
into the map at which `constTerm` is taken: `Y.stringMap Y'` is multiplied on the left by the matrix
of `n⁻¹` in rational coordinates. -/
lemma constTermAtStringMap_unipotent_mul_right {Y' : Grading V' N X' (s - 1)}
    (α : (n : Type) → [Fintype n] → AutChar E) (f : 𝒮 (V.hom V')) {n : G E ε'}
    (hn : n ∈ Y'.unipotent) (g : G E ε) (h : G E ε') :
    Y.constTermAtStringMap Y' α f g (n * h) = Y.constTerm Y'.gradeOf
      (twistedPairWeil α (g, h) f) (V'.ratCoordMatrix n⁻¹ * Y.stringMap Y') := by
  simpa using Y.constTerm_mul (Y' := Y') Y'.gradeOf_stringReversal
    (.inr ⟨one_mem _, Y'.mem_unipotent.1 hn⟩) g h _

/-- For `n` in `Y.unipotent`, `Y.constTermAtStringMap Y' α f (n * g) h` is `Y.constTerm` for the
weights `Y'.gradeOf` of `twistedPairWeil α (g, h) f` at `Y.stringMap Y' * V.ratCoordMatrix n`: the
factor `n` moves into the point of the constant term, on the right. -/
lemma constTermAtStringMap_unipotent_mul_left {Y' : Grading V' N X' (s - 1)}
    (α : (n : Type) → [Fintype n] → AutChar E) (f : 𝒮 (V.hom V')) {n : G E ε}
    (hn : n ∈ Y.unipotent) (g : G E ε) (h : G E ε') :
    Y.constTermAtStringMap Y' α f (n * g) h = Y.constTerm Y'.gradeOf
      (twistedPairWeil α (g, h) f) (Y.stringMap Y' * V.ratCoordMatrix n) := by
  simpa using Y.constTerm_mul (Y' := Y') Y'.gradeOf_stringReversal
    (.inr ⟨hn, Y'.mem_unipotent.1 (one_mem _)⟩) g h _

/-- For odd `s` and `W` equivariant for `Y` (left translation by unipotents acts by a character),
the product of `W` and the constant term at `Y.stringMap Y'`, with the characters `rankTwist a`, is
invariant under the unipotent group of `Y`: the two characters cancel. -/
lemma mul_constTermAtStringMap_unipotent_mul {Y' : Grading V' N X' (s - 1)} (h_odd : Odd s)
    (a : AutChar E) (f : 𝒮 (V.hom V')) {W : Y.besselGroup → ℂ} (hW : Y.IsEquivariant W) {n : G E ε}
    (hn : n ∈ Y.unipotent) (g : Y.besselGroup) (r : G E ε') :
    W (⟨n, Y.unipotent_le_besselGroup hn⟩ * g) *
        Y.constTermAtStringMap Y' (rankTwist a) f (n * g.1) r =
      W g * Y.constTermAtStringMap Y' (rankTwist a) f g.1 r := by
  have h_deg : HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix n - 1) :=
    Y.hasDegreeGe_two_of_odd h_odd hn
  simp [constTermAtStringMap, homBicharacter_eq, hW.unipotent_mul_constTerm
    Y'.gradeOf_stringReversal (u := ⟨n, Y.unipotent_le_besselGroup hn⟩) h_deg
    (Y.hasDegreeGe_neg_one_stringMap.mul h_deg (by omega))]

/-- Let `D` be data for the two consecutive lifts `Y → Y' → Y''`. Let `n` be a unipotent element of
U(V'), with matrix `V'.ratCoordMatrix n` in rational coordinates, and put `T = Y.stringMap Y'`,
`T' = Y'.stringMap Y''`. Join `f` and `f'` to the datum `arrowProduct f f'` on `Hom(V', V⁻ ⊕ V'')`;
by `hθ`, its theta value is `z ≠ 0` times the product of those of `f` and `f'`. Translate this datum
by the map `stackedStringMap Y Y' Y''` = (T*, T'). Then take the zero term along
`D.homZeroPart.splitting`, which is the mean over the maps of positive degree. Evaluate the result
at the map from `X'` to an isotropic half of the hyperbolic planes indexed by `q`. Its matrix is
`Y'.genericConst` times the block of `n - 1` whose rows are the basis vectors `D.gradeOne` of grade
one and whose columns are `X'`. Then `z⁻¹` times this value is the product of the constant terms of
`f` at `n⁻¹ T` and of `f'` at `T' n`. -/
lemma DoubleLiftData.zeroTerm_stackedStringMap_planes (D : DoubleLiftData X'' q Y Y' Y'') {z : ℂ}
    (hz : z ≠ 0)
    (hθ : ∀ (f : 𝒮 (V.hom V')) (f' : 𝒮 (V'.hom V'')),
      θ (V'.hom (flipSum V V'')) (arrowProduct f f') = z * ((V.hom V').θ f * (V'.hom V'').θ f'))
    (f : 𝒮 (V.hom V')) (f' : 𝒮 (V'.hom V'')) {n : G E ε'} (hn : n ∈ Y'.unipotent) :
    let planes : Splitting
        ((stdSpace E X').hom (hyperbolicSum q (flipSum (stdSpace E X) (stdSpace E X''))))
        ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X''))) (q × X') :=
      (removePlanes q (flipSum (stdSpace E X) (stdSpace E X''))).homTarget (stdSpace E X')
    z⁻¹ * D.homZeroPart.splitting.zeroTerm
        (homHeisenbergOp (stackedStringMap Y Y' Y'') (arrowProduct f f'))
        (planes.kAdelic *ᵥ fun p : q × X' ↦
          ↑Y'.genericConst * (V'.ratCoordMatrix n - 1) (D.gradeOne p.1)
            (Y'.indexEquiv (Sum.inl p.2))) =
      Y.constTerm Y'.gradeOf f (V'.ratCoordMatrix n⁻¹ * Y.stringMap Y') *
        Y'.constTerm Y''.gradeOf f' (Y'.stringMap Y'' * V'.ratCoordMatrix n) := by
  intro planes
  -- The zero term ignores translations along `kAdelic`; add the one that completes the
  -- translation vector to `stackedStringMap * (n - 1)`. The two translations compose without a
  -- phase.
  obtain ⟨y, hy⟩ := D.exists_add_eq_homAtPoint_stackedStringMap hn
  have h_beta (v : ((q ⊕ q) ⊕ X ⊕ X'') × X' → 𝔸 E) :
      (adelicHeisenberg E (homSigns ε' (-ε ⊕ᵥ ε''))).β
      (D.homZeroPart.splitting.kAdelic *ᵥ y) (D.homZeroPart.splitting.iAdelic *ᵥ v) = 1 := by
    simp [D.homZeroPart.splitting.beta_eq_coords]
  rw [← theta_rho, ← zeroTerm_rho_iAdelic, ← zeroTerm_rho_kAdelic y, (heisenbergRep _).mul, h_beta,
    one_smul, hy]
  -- Compose with the translation by `stackedStringMap`, which gives `stackedStringMap * n`. The
  -- phase is 1, because (T*, T')* (T*, T') = -T T* + T'* T' = 0.
  rw [(heisenbergRep _).mul, ← homBicharacter, homBicharacter_eq, ← Matrix.mul_assoc,
    formAdjoint_stackedStringMap_mul_stackedStringMap D]
  simp [D.constTerm_mul_constTerm_eq_inv_mul_zeroTerm hz hθ, stackedStringMap, Matrix.mul_sub,
    ← homHeisenbergOp_arrowProduct, formAdjoint_ratCoordMatrix_mul, GradeZeroPart.splitting]

/-- Let `Y, Y', Y''` be gradings of the hermitian spaces `V, V', V''` over `E` with definite parts
`X, X', X₀`, and let `D` be data for two consecutive lifts. There is a constant `z` with the
following property. Let `a`, `b` be automorphic characters of U(1), which normalise the two Weil
actions; let `f`, `f'` be data on `Hom(V, V')` and `Hom(V', V'')`, and `k` a point of U(X₀). Let `W`
be a continuous function on the Bessel (Fourier–Jacobi) subgroup of `Y`, invariant under rational
points and equivariant for the unipotent character (`Y.IsEquivariant W`). Let `F g r` be `W g` times
the constant terms of the Weil translates of `f` by `(g, r)` and of `f'` by `(r, Y''.inclX k)`. The
integral of `F` over the Bessel subgroups of `Y` and `Y'` is the integral over `g` in U(X) of
`W (Y.inclX g)` times `z` times a theta integral over `r` in U(X'), all modulo rational points. Its
datum is made from the join `arrowProduct f f'` on `Hom(V', V⁻ ⊕ V'')`: translate by
`stackedStringMap Y Y' Y''`, the map V' → V⁻ ⊕ V'' along the strings; cut down to
`Hom(X', X⁻ ⊕ X'')` by the mean over the isotropic part of `D.splitting` (`zeroTerm`); and act by
`(g, r, D.embX k)` under the joint Weil action `tripleWeil a b`. -/
lemma DoubleLiftData.exists_integral_constTermAtStringMap_mul_eq
    (D : DoubleLiftData X'' q Y Y' Y'') :
    ∃ z : ℂ, ∀ (a b : AutChar E) (f : 𝒮 (V.hom V')) (f' : 𝒮 (V'.hom V''))
      (k : G E (1 : X₀ → ℤˣ)) (W : Y.besselGroup → ℂ), Y.IsEquivariant W →
      let F (g : Y.besselGroup) (r : Y'.besselGroup) :=
        W g * Y.constTermAtStringMap Y' (rankTwist a) f g r *
          Y'.constTermAtStringMap Y'' (rankTwist b) f' r (Y''.inclX k)
      ∫ r : Y'.besselGroup, ∫ g : Y.besselGroup, F g r ∂Y.besselMeasure ∂Y'.besselMeasure =
        ∫ g : G E (1 : X → ℤˣ), W ⟨Y.inclX g, Y.inclX_mem_besselGroup g⟩ *
          (z * ∫ r : G E (1 : X' → ℤˣ),
            θ ((stdSpace E X').hom (flipSum (stdSpace E X) (stdSpace E X'')))
            (tripleWeil a b (g, r, D.embX k)
              (D.splitting.zeroTerm (homHeisenbergOp (stackedStringMap Y Y' Y'')
                (arrowProduct f f'))))
            ∂(stdSpace E X').quotMeasure) ∂(stdSpace E X).quotMeasure := by
  -- Apply `integral_besselMeasure_eq_of_mean` twice. Over the unipotent group of `Y` the character
  -- of the kernel cancels that of `W`. Over that of `Y'` the mean turns the zero term along
  -- `D.homZeroPart.splitting` into the zero term along `D.splitting`.
  obtain ⟨z, hz_ne, hθ⟩ := theta_arrowProduct V V' V''
  have h_odd : Odd s := D.odd_length
  obtain rfl : s' = s - 1 := D.length_middle
  obtain rfl : s'' = s - 1 - 1 := D.length_last
  -- `hκ`, `hκ'`: if `φ (n * x) = f x (row n)` for unipotent n and x in U(X) or U(X'), where the
  -- row is a block of `n - 1`, and `f x` has mean `M x`, then `∫ φ = κ * ∫ M` (under continuity and
  -- invariance hypotheses)
  obtain ⟨κ, hκ⟩ := Y.integral_besselMeasure_eq_of_mean (.refl _)
  obtain ⟨κ', hκ'⟩ := Y'.integral_besselMeasure_eq_of_mean D.gradeOne
  refine ⟨κ * κ' * z⁻¹, fun a b f f' k W hW ↦ ?_⟩
  intro F
  have h_cont : Continuous ↿F := by
    have := hW.continuous
    simp only [F, mul_assoc, D.constTerm_mul_constTerm_eq_inv_mul_zeroTerm hz_ne hθ]
    fun_prop
  have h_fix_left (r : Y'.besselGroup) :
      (Y.ratBessel.subgroupOf Y.besselGroup).FixesLeft (fun g ↦ F g r) := fun γ hγ g ↦ by
    simp [F, hW.rat_mul γ hγ.1, ← constTermAtStringMap_rat_mul ⟨γ.1, hγ⟩ 1 g.1]
  have h_fix_right (g : Y.besselGroup) :
      (Y'.ratBessel.subgroupOf Y'.besselGroup).FixesLeft (F g) := fun δ hδ r ↦ by
    simp [F, ← constTermAtStringMap_rat_mul 1 ⟨δ.1, hδ⟩ g.1 r.1,
      ← constTermAtStringMap_rat_mul ⟨δ.1, hδ⟩ 1 r.1]
  let ι₀ := Y.inclX.codRestrict Y.besselGroup Y.inclX_mem_besselGroup
  have ι₀_cont : Continuous ι₀ := Y.continuous_inclX.subtype_mk _
  have h_fix_levi (r : Y'.besselGroup) :
      (stdSpace E X).Γ.FixesLeft fun x ↦ F (ι₀ x) r := fun γ hγ x ↦ by
    simpa only [map_mul] using h_fix_left r (ι₀ γ) (Y.inclX_mem_ratBessel hγ) (ι₀ x)
  -- for odd `s` the characters of `W` and of the kernel cancel on unipotent elements
  have h_unip (r : Y'.besselGroup) (n : G E ε) (hn : n ∈ Y.unipotent) (x : G E 1) :
      F (⟨n, Y.unipotent_le_besselGroup hn⟩ * ι₀ x) r = F (ι₀ x) r := by
    simp [F, mul_constTermAtStringMap_unipotent_mul h_odd a f hW hn (ι₀ x) r.1]
  have h_inner (r : Y'.besselGroup) :
      ∫ g, F g r ∂Y.besselMeasure = κ * ∫ x, F (ι₀ x) r ∂(stdSpace E X).quotMeasure :=
    hκ (f := fun x _ ↦ F (ι₀ x) r) (h_fix_left r) h_cont.along_fst (h_unip r)
      (by simp [IsContPeriodic, continuous_const]) (by fun_prop) (h_fix_levi r)
  have h_int : Integrable (Function.uncurry fun r x ↦ F (ι₀ x) r)
      (Y'.besselMeasure.prod (stdSpace E X).quotMeasure) :=
    integrable_of_isCocompact
      (isCocompact_prod Y'.isCocompact_ratBessel (stdSpace E X).isCocompact_Gamma)
      (by fun_prop) (by simp +contextual [h_fix_levi, h_fix_right, -map_mul, mem_prod])
  rw [funext h_inner, integral_const_mul, integral_integral_swap h_int]
  -- pull the constants `κ`, `κ'` and `z⁻¹` to where they arise
  simp_rw [mul_assoc, ← integral_const_mul z⁻¹, mul_left_comm (W _), ← integral_const_mul (W _),
    integral_const_mul κ]
  congr with x
  -- `hκ'` applies to the integral over the Bessel group of `Y'`
  -- `Φ g`: the zero term along `D.homZeroPart.splitting` of the joined datum, moved by (x, g, k)
  -- through `ω g` and `ω' g`, scaled and translated by `stackedStringMap`
  let ω g := twistedPairWeil (rankTwist a) (Y.inclX x, Y'.inclX g) (V := V) (V' := V')
  let ω' g := twistedPairWeil (rankTwist b) (Y'.inclX g, Y''.inclX k) (V := V') (V' := V'')
  let Φ g := D.homZeroPart.splitting.zeroTerm <| homHeisenbergOp (stackedStringMap Y Y' Y'') <|
    arrowProduct (ω g f) (ω' g (W (ι₀ x) • z⁻¹ • f'))
  let planes := (removePlanes q (flipSum (stdSpace E X) (stdSpace E X''))).homTarget (stdSpace E X')
  refine hκ' (f := fun g y ↦ Φ g (planes.iAdelic *ᵥ 0 + planes.kAdelic *ᵥ y))
    (φ_inv := h_fix_right _) (φ_cont := h_cont.along_snd) (φ_eq := fun n hn g ↦ ?_)
    (f_mean := fun g ↦ ⟨isContPeriodic_along_k .., ?_⟩) (M_cont := ?_) (M_inv := fun γ hγ g ↦ ?_)
  · -- `F (ι₀ x) (n * Y'.inclX g)` is a value of `Φ g`. Both constant terms absorb n into their
    -- frequency.
    simpa [F, ι₀, Φ, planes, ω, ω', constTermAtStringMap_unipotent_mul_right (hn := hn),
      constTermAtStringMap_unipotent_mul_left (hn := hn), mul_assoc] using congrArg (W (ι₀ x) * ·)
        (D.zeroTerm_stackedStringMap_planes hz_ne hθ (ω g f) (ω' g f') hn).symm
  · -- the mean over the planes is the zero term along `D.splitting`, which intertwines the actions
    rw [← Splitting.zeroTerm_apply, ← D.zeroTerm_splitting_tripleWeil]
    -- split the triple action into the two pair actions, which commute with `stackedStringMap`
    simp_rw [stackedStringMap, homHeisenbergOp_arrowProduct, ← arrowProduct_twistedPairWeil,
      pairWeil_homHeisenbergOp, inclX_mul_stringMap_mul_inclX_inv, ← homHeisenbergOp_arrowProduct,
      ← smul_eq_mul, ← map_smul, splitting, zeroTerm_comp]
    rfl
  · -- the mean is continuous in the point of U(X')
    simp [tripleWeil, -circleChar_inv_apply, pairChar, mul_assoc]
    fun_prop
  · -- and invariant under its rational points
    congr 2
    simpa only [one_mul] using theta_tripleWeil_rat_mul a b _ 1 (one_mem _) γ hγ x g _

end New.Seesaw

/-! ## The functions produced by the unfolding -/

namespace New.Data

open scoped Pointwise

open MeasureTheory Function UniqueFactorizationMonoid Multiset IsDedekindDomain.HeightOneSpectrum
  Seesaw Space Grading stdLattice Rows Prod Modulus ProbabilityTheory TensorChain
variable {P : Parameters} {D : Data P}

section Stages

variable (ϑ : D.TameChar) (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
  (ξ : ∀ k : ℕ, GInf D.E (D.signsY k)) (y : ∀ k : ℕ, Gf D.E (D.Y k))

/-- The embedding `inclXFin` of the finite points of `U(X_k)` in those of `U(Y_k)` maps the level
`D.levelX k` into the level `D.chosenLevel`. -/
lemma inclXFin_mem_chosenLevel {k : ℕ} {hk : k ≤ 2 * D.ϱ + 1} {a : Gf D.E (D.X k)}
    (ha : a ∈ D.levelX k) : (D.gradingY k hk).inclXFin a ∈ D.chosenLevel := by
  -- The chosen places and their conjugates do not lie above `N`.
  have not_chosen {w : FinPlace D.E} (hw : w ∈ D.piNPlaces) :
      ¬D.IsChosen w ∧ ¬D.IsChosen (star w) :=
    D.not_isChosen_of_N_mem (D.isSplitLevel_piNPlaces.natCast_level_mem w hw)
  have is_chosen (i : Σ i : Fin 2, D.ChosenPlace i) : D.IsChosen (D.chosenPlace i) := by
    obtain ⟨-, -, h_chosen, -⟩ := i
    exact h_chosen
  exact inclXFin_mem_levelOf _ (D.spansLattice_gradingY k hk) D.isSplitSquarefree_piNIdele ha.2
    (fun i hi ↦ (not_chosen hi).1 (is_chosen i))
    (fun i hi ↦ (not_chosen hi).2 (by simpa using is_chosen i)) ha.1

/-- The datum of lift `k + 1` (`New.Data.datumY`) moved by the outer variable `g_k = (ξ k, y k)`,
which acts on `Y_k`. -/
noncomputable def movedDatum (k : ℕ) : 𝒮 ((D.spaceY k).hom (D.spaceY (k + 1))) :=
  twistedPairWeil (rankTwist (D.chainChar ϑ (k + 1))) ((ξ k, y k), 1) (datumY ϑ k)

/-- The action of `(g, h)` on the moved datum of lift `k + 1` is that of `(g * g_k, h)` on the
original datum, where `g_k = (ξ k, y k)`. -/
lemma twistedPairWeil_movedDatum (k : ℕ) (g : New.G D.E (D.signsY k))
    (h : New.G D.E (D.signsY (k + 1))) :
    twistedPairWeil (rankTwist (D.chainChar ϑ (k + 1))) (g, h) (movedDatum ϑ ξ y k) =
      twistedPairWeil (rankTwist (D.chainChar ϑ (k + 1))) (g * (ξ k, y k), h) (datumY ϑ k) := by
  rw [movedDatum, rep_apply_apply, mk_mul_mk, mul_one]

/-- In the constant term `constTermAtStringMap` of the moved datum at `(g, g' * a)`, the point `a`
may be moved into the datum: it is the constant term at `(g, g')` of `datumY` acted on by
`(g_k, a)`, where `g_k = (ξ k, y k)`. -/
lemma constTermAtStringMap_movedDatum {k : ℕ} {hk : k ≤ 2 * D.ϱ + 1} {X : Type} {s : ℕ} [Fintype X]
    [DecidableEq X] (Y' : Grading (D.spaceY (k + 1)) D.N X s) (g : New.G D.E (D.signsY k))
    (g' a : New.G D.E (D.signsY (k + 1))) :
    (D.gradingY k hk).constTermAtStringMap Y' (rankTwist (D.chainChar ϑ (k + 1)))
        (movedDatum ϑ ξ y k) g (g' * a) =
      (D.gradingY k hk).constTermAtStringMap Y' (rankTwist (D.chainChar ϑ (k + 1)))
        (twistedPairWeil (rankTwist (D.chainChar ϑ (k + 1))) ((ξ k, y k), a) (datumY ϑ k))
        g g' := by
  simp only [constTermAtStringMap, twistedPairWeil_movedDatum, rep_apply_apply, mk_mul_mk]

/-- The function on `R_k` that enters step `k + 1` of the unfolding: `𝒲_φ` for `k = 0`, and
`γ ↦ 𝒲_k (γ g_k)` with `g_k = (ξ k, y k)` for `k > 0`. -/
noncomputable def unfoldStageOn :
    ∀ (k : ℕ) (hk : k ≤ 2 * D.ϱ + 1), (D.gradingY k hk).besselGroup → ℂ
  | 0, _ => (D.gradingY 0).sourceFn t φ.1
  | k + 1, hk => fun γ ↦
    (D.gradingY k).unfoldStep (D.gradingY (k + 1) hk) (rankTwist (D.chainChar ϑ (k + 1)))
      (movedDatum ϑ ξ y k) (unfoldStageOn k (by omega)) (γ.1 * (ξ (k + 1), y (k + 1)))

/-- The function `𝒲_{k+1}` on `U(Y_{k+1})` that the first `k + 1` unfolding steps leave. -/
noncomputable def unfoldStage (k : ℕ) (hk : k ≤ 2 * D.ϱ + 1) {X : Type} {s : ℕ} [Fintype X]
    [DecidableEq X] (Y' : Grading (D.spaceY (k + 1)) D.N X s) : New.G D.E (D.signsY (k + 1)) → ℂ :=
  (D.gradingY k hk).unfoldStep Y' (rankTwist (D.chainChar ϑ (k + 1))) (movedDatum ϑ ξ y k)
    (unfoldStageOn ϑ t φ ξ y k hk)

lemma unfoldStageOn_zero (hk : 0 ≤ 2 * D.ϱ + 1) :
    unfoldStageOn ϑ t φ ξ y 0 hk = (D.gradingY 0).sourceFn t φ.1 := rfl

/-- On `R_{k+1}`, the Bessel group of `D.gradingY (k + 1) hk`, the function `unfoldStageOn` of the
unfolding is `γ ↦ 𝒲_{k+1} (γ g_{k+1})`, where `𝒲_{k+1}` is `unfoldStage` at `k` and
`g_{k+1} = (ξ (k + 1), y (k + 1))`. -/
lemma unfoldStageOn_succ (k : ℕ) (hk : k + 1 ≤ 2 * D.ϱ + 1)
    (γ : (D.gradingY (k + 1) hk).besselGroup) :
    unfoldStageOn ϑ t φ ξ y (k + 1) hk γ =
      unfoldStage ϑ t φ ξ y k (by omega) (D.gradingY (k + 1) hk) (γ.1 * (ξ (k + 1), y (k + 1))) :=
  rfl

/-- For `k < l`, the function `unfoldStageOn` on `R_k` does not change when the points `ξ l` and
`y l` of stage `l` are replaced by any `a` and `b`. -/
lemma unfoldStageOn_update {l : ℕ} (a : GInf D.E (D.signsY l)) (b : Gf D.E (D.Y l)) (k : ℕ)
    (hk : k ≤ 2 * D.ϱ + 1) (hkl : k < l) :
    unfoldStageOn ϑ t φ (update ξ l a) (update y l b) k hk = unfoldStageOn ϑ t φ ξ y k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [unfoldStageOn, movedDatum, ih _ (by omega), update_of_ne hkl.ne,
      update_of_ne (by omega : k ≠ l)]

/-- The function `𝒲_{k+1}` (`unfoldStage`) depends only on the outer variables `g_j = (ξ j, y j)`
for `j ≤ k`: changing `ξ` and `y` at an index `l > k` does not change it. -/
lemma unfoldStage_update {l : ℕ} (a : GInf D.E (D.signsY l)) (b : Gf D.E (D.Y l)) (k : ℕ)
    (hk : k ≤ 2 * D.ϱ + 1) (hkl : k < l) {X : Type} {s : ℕ} [Fintype X] [DecidableEq X]
    (Y' : Grading (D.spaceY (k + 1)) D.N X s) :
    unfoldStage ϑ t φ (update ξ l a) (update y l b) k hk Y' = unfoldStage ϑ t φ ξ y k hk Y' := by
  simp only [unfoldStage, movedDatum, unfoldStageOn_update ϑ t φ ξ y a b k hk hkl,
    update_of_ne hkl.ne]

/-- The function `unfoldStageOn` on the Bessel group `R_k` of `D.gradingY k hk` is equivariant under
the unipotent character and invariant under the rational points (`New.Grading.IsEquivariant`). -/
lemma isEquivariant_unfoldStageOn (k : ℕ) (hk : k ≤ 2 * D.ϱ + 1) :
    (D.gradingY k hk).IsEquivariant (unfoldStageOn ϑ t φ ξ y k hk) := by
  induction k with
  | zero => exact (D.gradingY 0).isEquivariant_sourceFn (by simp) t φ.1
  | succ k ih => exact isEquivariant_unfoldStep (ih (by omega)) rfl (ξ (k + 1), y (k + 1))

section

variable (k : ℕ) (hk : k ≤ 2 * D.ϱ + 1) {X : Type} [Fintype X] [DecidableEq X]
  (Y' : Grading (D.spaceY (k + 1)) D.N X (2 * D.ϱ + 1 - (k + 1)))

lemma continuous_unfoldStage : Continuous (unfoldStage ϑ t φ ξ y k hk Y') :=
  continuous_unfoldStep (isEquivariant_unfoldStageOn ϑ t φ ξ y k hk)

/-- The function `𝒲_{k+1}` is invariant on the left under the rational points of `R_{k+1}`, the
Bessel group of `Y'`. -/
lemma fixesLeft_ratBessel_unfoldStage : Y'.ratBessel.FixesLeft (unfoldStage ϑ t φ ξ y k hk Y') :=
  unfoldStep_rat_mul

end

/-- Fix a tame character `ϑ`, a source form `φ` on U(X_0) with a linear form `t` on its values, and
adelic points `g_k = (ξ k, y k)` of the unitary groups U(Y_k). Let `Y'` be a grading of `Y_{k+1}`
with a string of length `2 ϱ + 1 - (k + 1)`, and let `𝒲_{k+1}` be the function `unfoldStage` on
U(Y_{k+1}) that `k + 1` unfolding steps leave, the last one with `Y'`. Let `z` be automorphic and
rapidly decreasing on U(Y_{k+1}). Take the theta lift of `z` to U(Y_k) with the datum `datumY ϑ k`
on `Hom(Y_k, Y_{k+1})` and the Weil action `twistedPairWeil` normalised by the character
`D.chainChar ϑ (k + 1)`, and translate the lift on the right by `g_k`. Its integral against the
function `unfoldStageOn` of the previous stage, over the Bessel group `R_k` of `D.gradingY k` modulo
rational points, is the integral of `𝒲_{k+1} z` over U(Y_{k+1}) modulo the rational points
`Y'.ratBessel` of the Bessel group of `Y'`. The latter integral converges absolutely. -/
lemma integral_unfoldStageOn (ϑ : D.TameChar)
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
    (ξ : ∀ k : ℕ, GInf D.E (D.signsY k)) (y : ∀ k : ℕ, Gf D.E (D.Y k))
    (k : ℕ) (hk : k ≤ 2 * D.ϱ + 1) {X : Type} [Fintype X] [DecidableEq X]
    (Y' : Grading (D.spaceY (k + 1)) D.N X (2 * D.ϱ + 1 - (k + 1)))
    {z : New.G D.E (D.signsY (k + 1)) → ℂ}
    (hz_aut : (D.spaceY (k + 1)).IsAutomorphic z) (hz_rapid : (D.spaceY (k + 1)).IsRapid z) :
    Integrable (unfoldStage ϑ t φ ξ y k hk Y' * z) Y'.ratBessel.quotMeasure ∧
      ∫ r : (D.gradingY k hk).besselGroup, unfoldStageOn ϑ t φ ξ y k hk r *
        ∫ h : New.G D.E (D.signsY (k + 1)), θ ((D.spaceY k).hom (D.spaceY (k + 1)))
          (twistedPairWeil (rankTwist (D.chainChar ϑ (k + 1))) (r.1 * (ξ k, y k), h) (datumY ϑ k)) *
            z h ∂(D.spaceY (k + 1)).quotMeasure ∂(D.gradingY k hk).besselMeasure =
      Y'.ratBessel.quotMeasure[unfoldStage ϑ t φ ξ y k hk Y' * z] := by
  simpa only [unfoldStage, twistedPairWeil_movedDatum, Pi.mul_def]
    using integral_besselGroup_unfold Y' (rankTwist (D.chainChar ϑ (k + 1))) (movedDatum ϑ ξ y k)
      (isEquivariant_unfoldStageOn ϑ t φ ξ y k hk) hz_aut hz_rapid

set_option synthInstance.maxSize 512 in
/-- Let `R` be data for the two lifts `Y_{2i} → Y_{2i+1} → Y_{2i+2}`, the last space with the
grading `Y`. Suppose that the linear map `D.doubleLiftEvalY i` on finite data is `R.finEval`, the
finite analogue of the translation and zero term below. Fix archimedean points `ξ k` of U(Y_k) and
`x` of U(Y_{2i+2}). Move the data `datumY` of lifts `2 i + 1` and `2 i + 2` under the Weil action by
`(ξ k, y k)` for `k = 2 i, 2 i + 1` and by `(x, y (2 i + 2))`. Join them (`arrowProduct`), translate
by the map `stackedStringMap` along the strings, and cut down to
`Hom(X_{2i+1}, X_{2i}⁻ ⊕ X_{2i+2})` by the mean over the isotropic part of `R.splitting`
(`zeroTerm`). The result is a pure tensor (`integrated`) of a vector `v` of the Fock space,
independent of the tame character `ϑ` and the finite points `y`, and of `evaluatedDatum ϑ y i`, the
value of `D.doubleLiftEvalY i` on the finite factors, carried to this space by `arrowTensor`. -/
lemma exists_zeroTerm_eq_integrated (ξ : ∀ k : ℕ, GInf D.E (D.signsY k))
    (i : ℕ) (hi : 2 * i < 2 * D.ϱ + 1) {X q : Type} {s : ℕ}
    [Fintype X] [DecidableEq X] [Fintype q] [DecidableEq q]
    {Y : Grading (D.spaceY (2 * i + 2)) D.N X s}
    (R : DoubleLiftData (D.X (2 * i + 2)) q (D.gradingY (2 * i) hi.le) (D.gradingY (2 * i + 1) hi)
      Y)
    (hR : D.doubleLiftEvalY i = R.finEval) (x : GInf D.E (D.signsY (2 * i + 2))) :
    ∃ v : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns D.E
      (homSigns (1 : D.X (2 * i + 1) → ℤˣ)
        (Sum.elim (-(1 : D.X (2 * i) → ℤˣ)) (1 : D.X (2 * i + 2) → ℤˣ))))),
      ∀ (ϑ : D.TameChar) (y : ∀ k : ℕ, Gf D.E (D.Y k)),
      R.splitting.zeroTerm (homHeisenbergOp
        (stackedStringMap (D.gradingY (2 * i) hi.le) (D.gradingY (2 * i + 1) hi) Y)
        (arrowProduct
          (twistedPairWeil (rankTwist (D.chainChar ϑ (2 * i + 1)))
            ((ξ (2 * i), y (2 * i)), ξ (2 * i + 1), y (2 * i + 1)) (datumY ϑ (2 * i)))
          (twistedPairWeil (rankTwist (D.chainChar ϑ (2 * i + 1 + 1)))
            ((ξ (2 * i + 1), y (2 * i + 1)), x, y (2 * i + 2)) (datumY ϑ (2 * i + 1))))) =
        integrated ((stdSpace D.E (D.X (2 * i + 1))).hom
            (flipSum (stdSpace D.E (D.X (2 * i))) (stdSpace D.E (D.X (2 * i + 2))))) v
          (arrowTensor (evaluatedDatum ϑ y i)) := by
  -- Each operation acts separately on the real and on the finite factor. On the real factor the
  -- characters act through their weights, which do not depend on `ϑ`.
  -- The zero term of a translated pure tensor has real factor `u w v`.
  choose u ev_eq using exists_zeroTerm_rho_integrated_eq R.splitting
  simp only [evaluatedDatum, hR, R.arrowTensor_finEval]
  simp +instances only [pairWeil_integrated_all, arrowProduct, ContinuousLinearMap.comp_apply,
    CoordChange.map_integrated, boxProd_integrated, ev_eq]
  -- Both sides are now pure tensors with one finite factor; `v` is the real factor on the left.
  exact ⟨_, fun _ _ ↦ rfl⟩

-- Without this, comparing the index types of neighbouring stages unfolds `Finset.univ`.
seal Finset.univ in
/-- A double unfolding step. Let `R` be data for the two lifts `Y_{2i} → Y_{2i+1} → Y_{2i+2}`, the
last space with a grading `Y` of definite part `X`. Suppose that `D.doubleLiftEvalY i`, the linear
map that turns finite data for the spaces `Y_k` into finite data for their definite parts `X_k`, is
the map `R.finEval` of `R`. Fix archimedean points `ξ k` of U(Y_k) and `x` of U(Y_{2i+2}), and a
linear form `l` on the values of algebraic forms on U(X_{2i}). There is a linear form `l''`,
independent of `ϑ`, `t`, `φ`, `y` and `ψ`, with the following property. Suppose the function
`unfoldStageOn` on the Bessel group of the grading of `Y_{2i}` is `sourceFn l ψ`. This is the
function that is equivariant for the unipotent character and equals the coefficient
`algFormCoeff 1 l ψ` of the form `ψ` on U(X_{2i}). Then for `g` in U(X), the value of `𝒲_{2i+2}` at
`Y.inclX g * (x, y (2 i + 2))` is the coefficient at `l''` of `Θ ψ`, taken at the image `R.embX g`
of `g` in U(X_{2i+2}). Here `Θ` is the composite (`liftInPairs`) of the theta lifts
`X_{2i} → X_{2i+1} → X_{2i+2}`, with kernels `D.liftKernel ϑ` and datum `evaluatedDatum ϑ y i`. -/
lemma exists_unfoldStage_eq_algFormCoeff_of_sourceFn (ξ : ∀ k : ℕ, GInf D.E (D.signsY k))
    (i : ℕ) (hi : 2 * i < 2 * D.ϱ + 1)
    {X q : Type} {s : ℕ} [Fintype X] [DecidableEq X] [Fintype q] [DecidableEq q]
    {Y : Grading (D.spaceY (2 * i + 2)) D.N X s}
    (R : DoubleLiftData (D.X (2 * i + 2)) q (D.gradingY (2 * i) hi.le) (D.gradingY (2 * i + 1) hi)
      Y)
    (hR : D.doubleLiftEvalY i = R.finEval) (x : GInf D.E (D.signsY (2 * i + 2)))
    (l : (WeylIndex (D.X (2 * i)) D.columnCount → ℂ) →ₗ[ℂ] ℂ) :
    ∃ l'' : (WeylIndex (D.X (2 * i + 2)) D.columnCount → ℂ) →ₗ[ℂ] ℂ,
      ∀ (ϑ : D.TameChar) (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
        (y : ∀ k : ℕ, Gf D.E (D.Y k))
        (ψ : AlgForm (E := D.E) (D.X (2 * i)) D.columnCount (D.lastEntry (2 * i))),
      unfoldStageOn ϑ t φ ξ y (2 * i) hi.le = (D.gradingY (2 * i) hi.le).sourceFn l ψ →
      ∀ g : New.G D.E (1 : X → ℤˣ),
        unfoldStage ϑ t φ ξ y (2 * i + 1) hi Y (Y.inclX g * (x, y (2 * i + 2))) =
        algFormCoeff 1 l'' (liftInPairs (fun j : ℕ ↦ (D.liftKernel ϑ j).lift) i
          (evaluatedDatum ϑ y i) ψ) (R.embX g) := by
  -- The integrals over the two unipotent groups leave `z` times a double theta integral over
  -- U(X_{2i}) × U(X_{2i+1}) (`h_mean`). Its datum is a real vector `v` times the evaluated finite
  -- datum (`hv`), and such an integral against the coefficient `l` is a coefficient `l''` of the
  -- double lift (`hl''`).
  choose z h_mean using R.exists_integral_constTermAtStringMap_mul_eq
  choose v hv using exists_zeroTerm_eq_integrated ξ i hi R hR x
  have lift (j : ℕ) : IsThetaLift D.columnCount (D.lastEntry j) (D.lastEntry (j + 1))
      (fun ϑ : D.TameChar ↦ rankTwist (D.chainChar ϑ (j + 1)))
      fun ϑ : D.TameChar ↦ (D.liftKernel ϑ j).lift :=
    isThetaLift_thetaKernel (by simp)
  choose l'' hl'' using
    integral_theta_tripleWeil_eq_lift_comp (lift (2 * i)) (lift (2 * i + 1)) (z • v) l
  refine ⟨l'', fun ϑ t φ y ψ hψ g ↦ ?_⟩
  refine .trans ?_ (hl'' ϑ (evaluatedDatum ϑ y i) ψ (R.embX g))
  -- Write the two steps as an iterated integral of a product of two constant terms and apply
  -- `h_mean`.
  simp only [unfoldStage, unfoldStageOn_succ, unfoldStep, constTermAtStringMap_movedDatum,
    ← integral_mul_const]
  refine (h_mean _ _ _ _ _ _ (isEquivariant_unfoldStageOn ϑ t φ ξ y (2 * i) hi.le)).trans ?_
  simp [hψ, hv, sourceFn_inclX, integral_const_mul]

-- Without this, comparing the index types of neighbouring stages unfolds `Finset.univ`.
seal Finset.univ in
/-- At an even stage `2 i` there is a linear form `l`, independent of the tame character `ϑ`, the
source form `φ` and the finite points `y`, such that the function `unfoldStageOn` that `2 i`
unfolding steps leave on the Bessel group `R_{2i}` is `sourceFn l (Θ φ)`: it is equivariant for the
unipotent character and equals the coefficient of `Θ φ` at `l` on U(X_{2i}). Here `Θ` is the
composite `doubleLiftChain` of the first `i` pairs of theta lifts between the definite spaces `X_k`,
with kernels `D.liftKernel ϑ` and finite data `evaluatedDatum ϑ y`. -/
lemma exists_unfoldStageOn_even_eq_sourceFn (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ)
    (ξ : ∀ k : ℕ, GInf D.E (D.signsY k)) (i : ℕ) (hi : 2 * i ≤ 2 * D.ϱ + 1) :
    ∃ l : (WeylIndex (D.X (2 * i)) D.columnCount → ℂ) →ₗ[ℂ] ℂ,
      ∀ (ϑ : D.TameChar) (φ : D.SourceForm) (y : ∀ k : ℕ, Gf D.E (D.Y k)),
        unfoldStageOn ϑ t φ ξ y (2 * i) hi =
          (D.gradingY (2 * i) hi).sourceFn l
            (doubleLiftChain (D.liftKernel ϑ) (evaluatedDatum ϑ y) i φ) := by
  induction i with
  | zero => exact ⟨t, fun _ _ _ ↦ rfl⟩
  | succ i ih =>
    choose l hl using ih (by omega)
    choose l'' hl'' using exists_unfoldStage_eq_algFormCoeff_of_sourceFn ξ i
      (show 2 * i < 2 * D.ϱ + 1 by omega) _ (dite_eq_left (by omega)) (ξ (2 * i + 2)) l
    -- The function is equivariant for the unipotent character (`IsEquivariant`), so it is
    -- determined by its values on the image of U(X_{2i+2}) under `inclX`.
    exact ⟨l'', fun ϑ φ y ↦ (isEquivariant_unfoldStageOn ϑ t φ ξ y _ hi).eq_sourceFn
      ⟨D.ϱ - (i + 1), by omega⟩ (hl'' ϑ t φ y _ (hl ϑ φ y))⟩

-- Without this, comparing the index types of neighbouring stages unfolds `Finset.univ`.
seal Finset.univ in
set_option synthInstance.maxSize 512 in
/-- Let `R` be data for the two lifts `Y_{2i} → Y_{2i+1} → Y_{2i+2}`, the last space with a grading
`Y` of definite part `X`. Suppose that `D.doubleLiftEvalY i`, the linear map that turns finite data
for the spaces `Y_k` into finite data for their definite parts `X_k`, is the map `R.finEval` of `R`.
Fix a linear form `t` on the values of source forms and archimedean points `ξ k` of U(Y_k) and `x`
of U(Y_{2i+2}). There is a linear form `l`, independent of `ϑ`, `φ` and `y`, such that for `g` in
U(X) the value of `𝒲_{2i+2}` (`unfoldStage`) at `Y.inclX g * (x, y (2 i + 2))` is the coefficient
`algFormCoeff 1 l (Θ φ)` of `Θ φ` at `l`, taken at `R.embX g`. Here `Y.inclX` and `R.embX` map U(X)
to U(Y_{2i+2}) and to U(X_{2i+2}), and `Θ` is the composite `doubleLiftChain` of the first `i + 1`
pairs of theta lifts between the spaces `X_k`, with kernels `D.liftKernel ϑ` and finite data
`evaluatedDatum ϑ y`. -/
lemma exists_unfoldStage_eq_algFormCoeff (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ)
    (ξ : ∀ k : ℕ, GInf D.E (D.signsY k)) (i : ℕ) (hi : 2 * i < 2 * D.ϱ + 1) {X q : Type} {s : ℕ}
    [Fintype X] [DecidableEq X] [Fintype q] [DecidableEq q]
    {Y : Grading (D.spaceY (2 * i + 2)) D.N X s}
    (R : DoubleLiftData (D.X (2 * i + 2)) q (D.gradingY (2 * i) hi.le) (D.gradingY (2 * i + 1) hi)
      Y)
    (hR : D.doubleLiftEvalY i = R.finEval) (x : GInf D.E (D.signsY (2 * i + 2))) :
    ∃ l : (WeylIndex (D.X (2 * i + 2)) D.columnCount → ℂ) →ₗ[ℂ] ℂ,
      ∀ (ϑ : D.TameChar) (φ : D.SourceForm) (y : ∀ k : ℕ, Gf D.E (D.Y k))
        (g : New.G D.E (1 : X → ℤˣ)),
      unfoldStage ϑ t φ ξ y (2 * i + 1) hi Y (Y.inclX g * (x, y (2 * i + 2))) =
        algFormCoeff 1 l (doubleLiftChain (D.liftKernel ϑ) (evaluatedDatum ϑ y) (i + 1) φ)
          (R.embX g) := by
  choose l hl using exists_unfoldStageOn_even_eq_sourceFn t ξ i hi.le
  choose l'' hl'' using exists_unfoldStage_eq_algFormCoeff_of_sourceFn ξ i hi R hR x l
  exact ⟨l'', fun ϑ φ y ↦ hl'' ϑ t φ y _ (hl ϑ φ y)⟩

/-- Elements of the levels at `Y_k` and `Y_{k+1}` fix the datum `pointDatumY ϑ k` of lift `k + 1` of
the lower chain. -/
lemma liftWeilFin_pointDatumY (k : ℕ) {u : Gf D.E (D.Y k)} {u' : Gf D.E (D.Y (k + 1))}
    (hu : u ∈ levelY ϑ k) (hu' : u' ∈ levelY ϑ (k + 1)) :
    liftWeilFin (D.chainChar ϑ (k + 1)) (u, u') (pointDatumY ϑ k) = pointDatumY ϑ k := by
  -- `u` and `u'` reduce to 1 at every place of the level, so the factor in the action is 1.
  obtain ⟨hu_int, hu_red⟩ := mem_levelOf.1 hu
  obtain ⟨hu'_int, hu'_red⟩ := mem_levelOf.1 hu'
  ext1
  simpa using! thetaKernelY_omega_pointDatumY_eq_smul ϑ k hu_red hu'_red fun _ ↦
    (Matrix.mul_one _).symm

/-- The map `D.doubleLiftEvalY i` sends the join `arrowProduct Φ Φ'` of finite data `Φ`, `Φ'` on
`Hom(Y_{2i}, Y_{2i+1})` and `Hom(Y_{2i+1}, Y_{2i+2})` to a tensor of finite data on
`Hom(X_{2i}, X_{2i+1})` and `Hom(X_{2i+1}, X_{2i+2})`. If `2 i + 2 ≤ 2 ϱ + 1`, so that `Y_{2i+2}` is
graded by `D.gradingY`, it is equivariant for the finite points `u` of U(X_{2i+2}): acting on `Φ'`
by the image of `u` in U(Y_{2i+2}) before the map is acting by `u` on the second factor after it. -/
lemma doubleLiftEvalY_inclXFin (i : ℕ) (hi : 2 * i + 1 + 1 ≤ 2 * D.ϱ + 1) (b : AutChar D.E)
    (u : Gf D.E (D.X (2 * i + 1 + 1)))
    (Φ : ((D.spaceY (2 * i)).hom (D.spaceY (2 * i + 1))).finitePart)
    (Φ' : ((D.spaceY (2 * i + 1)).hom (D.spaceY (2 * i + 1 + 1))).finitePart) :
    D.doubleLiftEvalY i
        (arrowProduct Φ.1 (liftWeilFin b (1, (D.gradingY (2 * i + 1 + 1) hi).inclXFin u) Φ').1) =
      TensorProduct.map .id (liftWeilFin b (1, u))
        (D.doubleLiftEvalY i (arrowProduct Φ.1 Φ'.1)) := by
  -- Before the last pair, `doubleLiftEvalY i` is by definition the evaluation of a double lift
  -- datum `R`.
  obtain ⟨q, _, _, R, hR, h_emb⟩ : ∃ (q : Type) (_ : Fintype q) (_ : DecidableEq q)
      (R : DoubleLiftData (D.X (2 * i + 1 + 1)) q
        (D.gradingY (2 * i)) (D.gradingY (2 * i + 1)) (D.gradingY _ hi)),
      D.doubleLiftEvalY i = R.finEval ∧ R.embX (1, u) = (1, u) :=
    ⟨_, _, _, _, dite_eq_left (by omega), rfl⟩
  -- `using!`: the two index types `2 * i + 1 + 1` and `2 * i + 2` agree only after unfolding.
  simpa only [hR, MonoidHom.map_one, Prod.mk_one_one, Module.End.one_apply] using!
    R.finEval_arrowProduct_equivariant 1 b (g := 1) (g' := 1) h_emb Φ Φ'

/-- If `z`, conjugated by `y (j + 1)`, lies in the level `levelY ϑ (j + 1)`, then `(1, z)` fixes the
translated datum `translatedPointDatumY ϑ y j` of lift `j + 1` under the finite Weil representation
`liftWeilFin` with the character `D.chainChar ϑ (j + 1)`. -/
lemma liftWeilFin_translatedPointDatumY (j : ℕ) {z : Gf D.E (D.Y (j + 1))}
    (hz : (y (j + 1))⁻¹ * (z * y (j + 1)) ∈ levelY ϑ (j + 1)) :
    liftWeilFin (D.chainChar ϑ (j + 1)) (1, z) (translatedPointDatumY ϑ y j) =
      translatedPointDatumY ϑ y j := by
  have h_conj : (1, z) * (y j, y (j + 1)) =
      (y j, y (j + 1)) * (1, (y (j + 1))⁻¹ * (z * y (j + 1))) := by simp
  rw [translatedPointDatumY, ← Module.End.mul_apply, ← map_mul, h_conj, map_mul,
    Module.End.mul_apply,
    liftWeilFin_pointDatumY ϑ _ (one_mem _) hz]

/-- Let `ϑ` be a tame character and `y k` finite points of U(Y_k). The tensor
`evaluatedDatum ϑ y i` is the finite datum of the two theta lifts `X_{2i} → X_{2i+1} → X_{2i+2}`.
Let `u` be a finite point of U(X_{2i+2}) whose image in U(Y_{2i+2}), conjugated by `y (2 * i + 2)`,
lies in `levelY ϑ`: it is integral and reduces to `1` at the chosen places and at those of `ϑ.Q`.
Then `(1, u)`, acting on the second tensor factor through the Weil action `ω` of the theta kernel
`D.liftKernel ϑ (2 * i + 1)`, fixes `evaluatedDatum ϑ y i`. -/
lemma map_evaluatedDatum_of_conj_mem (ϑ : D.TameChar) (y : ∀ k : ℕ, Gf D.E (D.Y k)) (i : ℕ)
    (hi : 2 * i + 1 + 1 ≤ 2 * D.ϱ + 1) {u : Gf D.E (D.X (2 * i + 1 + 1))}
    (hu : (y (2 * i + 1 + 1))⁻¹ * ((D.gradingY (2 * i + 1 + 1) hi).inclXFin u * y (2 * i + 1 + 1)) ∈
      levelY ϑ (2 * i + 1 + 1)) :
    TensorProduct.map .id ((D.liftKernel ϑ (2 * i + 1)).ω (1, u)) (evaluatedDatum ϑ y i) =
      evaluatedDatum ϑ y i := by
  -- The evaluation carries `ω(1, z)` on the data for the `Y_k` to `ω(1, u)`, where `z` is the image
  -- of `u`; the former fixes the translated datum, as the level fixes `pointDatumY`.
  let Φ (j : ℕ) : ((D.spaceY j).hom (D.spaceY (j + 1))).finitePart := translatedPointDatumY ϑ y j
  let z : Gf D.E (D.Y (2 * i + 1 + 1)) := (D.gradingY _ hi).inclXFin u
  have fix_lower :
      liftWeilFin (D.chainChar ϑ (2 * i + 1 + 1)) (1, z) (Φ (2 * i + 1)) = Φ (2 * i + 1) :=
    liftWeilFin_translatedPointDatumY ϑ y (2 * i + 1) hu
  have equivariant :
      D.doubleLiftEvalY i (arrowProduct (Φ (2 * i)).1
          (liftWeilFin (D.chainChar ϑ (2 * i + 1 + 1)) (1, z) (Φ (2 * i + 1))).1) =
        TensorProduct.map .id (liftWeilFin (D.chainChar ϑ (2 * i + 1 + 1)) (1, u))
          (D.doubleLiftEvalY i (arrowProduct (Φ (2 * i)).1 (Φ (2 * i + 1)).1)) :=
    doubleLiftEvalY_inclXFin i hi (D.chainChar ϑ (2 * i + 1 + 1)) u (Φ (2 * i)) (Φ (2 * i + 1))
  rw [fix_lower] at equivariant
  exact equivariant.symm

/-- The evaluated data do not change if each `y k` is replaced by the chosen representative of its
class modulo the level `levelY ϑ k`. -/
lemma evaluatedDatum_out :
    evaluatedDatum ϑ (fun k : ℕ ↦ (y k : Gf D.E (D.Y k) ⧸ levelY ϑ k).out) =
      evaluatedDatum ϑ y := by
  -- Each representative is `y k * u k` with `u k ∈ levelY ϑ k`, and such elements fix the data.
  choose u out_eq using fun k : ℕ ↦ QuotientGroup.mk_out_eq_mul (levelY ϑ k) (y k)
  simp [funext_iff, evaluatedDatum, translatedPointDatumY, out_eq, ← mk_mul_mk,
    liftWeilFin_pointDatumY ϑ _ (u _).2 (u _).2]

/-- An idele that generates the ideal `Q`: the generator of `π_M Q` divided by that of `π_M`. -/
noncomputable def twistIdele : (𝔸f D.E)ˣ := (D.twistModulus ϑ 1).generator / D.chosenIdele

open scoped Classical in
/-- At the places of `ϑ.Q` the idele `twistIdele ϑ` has the valuation of a uniformiser, and at all
other places it is a unit. -/
lemma valued_twistIdele (w : FinPlace D.E) :
    Valued.v ((twistIdele ϑ).val w) = if w ∈ ϑ.Q then WithZero.exp (-1) else 1 := by
  -- The modulus is `D.piM` times the product of the distinct primes of `ϑ.Q`.
  let 𝔪 : Modulus D.E := D.twistModulus ϑ 1
  have h_mult : multiplicity w.asIdeal 𝔪.ideal =
      multiplicity w.asIdeal (Ideal.span {D.piM}) + if w ∈ ϑ.Q then 1 else 0 := by
    have h_Q : multiplicity w.asIdeal (∏ v ∈ ϑ.Q, v.asIdeal) = if w ∈ ϑ.Q then 1 else 0 := by
      rw [← count_normalizedFactors_eq_multiplicity
        (Finset.prod_ne_zero_iff.2 fun v _ ↦ v.prime.ne_zero), Finset.prod,
        normalizedFactors_prod_of_prime (by simp [prime])]
      -- the places of `ϑ.Q` are distinct, so `w` occurs in their product at most once
      simp [count_map_eq_count', asIdeal_injective, count_eq_of_nodup ϑ.Q.nodup]
    erw [multiplicity_mul w.prime (.of_prime_left w.prime 𝔪.ne_bot), ← span_piM,
      ϑ.Q.prod_coe_sort]
    simp [h_Q]
  have h_mul : (twistIdele ϑ).val * D.chosenIdele.val = 𝔪.generator.val := by
    rw [← Units.val_mul, twistIdele, div_mul_cancel]
  have h_val : Valued.v ((twistIdele ϑ).val w) * Valued.v (D.chosenIdele.val w) =
      Valued.v (𝔪.generator.val w) := by
    rw [← h_mul, ← map_mul]
    rfl
  rw [valued_chosenIdele, valued_generator, h_mult, Nat.cast_add, neg_add, WithZero.exp_add,
    mul_comm, mul_right_inj' WithZero.exp_ne_zero] at h_val
  split_ifs at h_val ⊢ with hw <;> simp [h_val]

/-- The modulus `D.twistModulus ϑ 1` is the product of the chosen places and the places of `ϑ.Q`.
The finite datum `pointDatumY ϑ k` on `Hom(Y_k, Y_{k+1})` is the indicator function of the inclusion
matrix modulo it, and the vacuum at the other places. This datum is fixed by the Heisenberg
translation `finHeisenbergOp` by the generator of the modulus times any integral vector `x`. -/
lemma finHeisenbergOp_generator_smul_pointDatumY (k : ℕ) {x : D.Y (k + 1) × D.Y k → 𝔸f D.E}
    (hx : x ∈ stdLattice D.E (D.Y (k + 1) × D.Y k)) :
    finHeisenbergOp ((D.spaceY k).hom (D.spaceY (k + 1))) ((D.twistModulus ϑ 1).generator.val • x)
      (pointDatumY ϑ k).val = (pointDatumY ϑ k).val := by
  set 𝔪 : Modulus D.E := D.twistModulus ϑ 1
  -- The datum is a combination of translates `finHeisenbergOp t vacElem` of the vacuum, with
  -- `star 𝔪.generator • t` integral.
  obtain ⟨c, hc, h_sum⟩ : IsAdmissibleCombination
      (fun t : D.Y (k + 1) × D.Y k → 𝔸f D.E ↦
        finHeisenbergOp ((D.spaceY k).hom (D.spaceY (k + 1))) t
          ((D.spaceY k).hom (D.spaceY (k + 1))).vacElem)
      (translations (D.Y (k + 1) × D.Y k) 1 (star 𝔪.generator.val)) 1 _ _ 0 (pointDatumY ϑ k).val :=
    isAdmissibleCombination_schrodingerOp_of_reduction _ _ (g := 0) (hg := by simp)
      (hΨ_int := by simp [ite_mem, Pi.single_apply]) (hΨ_size := id) (huv := projOn_vacElem _)
      (d := ⟨𝔪.generator.val, 𝔪.generator_mem⟩)
      (hd := by simp [𝔪, reduction_eq_zero_iff_generator_inv_mul_mem])
  rw [h_sum, map_finsuppSum]
  refine Finsupp.sum_congr fun t ht ↦ ?_
  have h_int : star 𝔪.generator.val • t ∈ stdLattice D.E (D.Y (k + 1) × D.Y k) := fun i ↦
    mem_Ô.mpr (hc.support_subset t ht i · (mod_cast Ideal.one_notMem _))
  -- So the translation by `𝔪.generator • x` commutes with the one by `t`, and it fixes the vacuum.
  have h_comm : stdLattice.selfDualAddChar D.E (𝔪.generator.val * star t ⬝ᵥ x) = 1 := by
    simpa using mem_stdLattice_iff_selfDualAddChar.mp hx (star 𝔪.generator.val • t) h_int
  simp [finHeisenbergOp_comm _ (_ • x), h_comm,
    finHeisenbergOp_vacElem (smul_mem_stdLattice 𝔪.generator_mem hx)]

end Stages

/-- Let `𝒲_{2j+2}` be the function `unfoldStage` on `U(Y_{2j+2})` built from a ramified source form
`φ`, the linear form `t` and the points `(ξ k, y k)` of U(Y_k). Let `w` be a place dividing
`π_N = D.piN`. View the chosen scaling `z_w = D.scalingGenerator w`, a finite adele of norm one, as
the point `inclXFin (scalarFin z_w)` of `U(Y_{2j+2})` that is the scalar `z_w` on the definite part
`X_{2j+2}` and the identity on the string. Suppose `x⁻¹ z_w x` lies in `levelY`: it is integral and
reduces to `1` at the chosen places and at those of `ϑ.Q`. Then `𝒲_{2j+2}` vanishes at `γ (a, x)`
for every `γ` in the Bessel group `R_{2j+2}` and every archimedean point `a`. -/
lemma unfoldStage_eq_zero_of_scalingGenerator (ϑ : D.TameChar)
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
    (ξ : ∀ k : ℕ, GInf D.E (D.signsY k)) (y : ∀ k : ℕ, Gf D.E (D.Y k))
    (hφ : φ ∈ D.ramifiedSourceForms) (j : ℕ)
    (hj : 2 * j + 1 + 1 ≤ 2 * D.ϱ + 1) (w : D.piNPlaces)
    (γ : (D.gradingY (2 * j + 1 + 1) hj).besselGroup)
    (a : GInf D.E (D.signsY (2 * j + 1 + 1))) {x : Gf D.E (D.Y (2 * j + 1 + 1))}
    (hx : x⁻¹ * ((D.gradingY (2 * j + 1 + 1) hj).inclXFin
      (scalarFin (D.X (2 * j + 1 + 1)) (D.scalingGenerator w)) * x) ∈ levelY ϑ (2 * j + 1 + 1)) :
    unfoldStage ϑ t φ ξ y (2 * j + 1) (by omega) (D.gradingY (2 * j + 1 + 1) hj) (γ.val * (a, x)) =
      0 := by
  -- Take `(a, x)` as the outer variable: the function is a coefficient of a chain of lifts of `φ`.
  let y' : ∀ k : ℕ, Gf D.E (D.Y k) := update y (2 * j + 1 + 1) x
  let ξ' : ∀ k : ℕ, GInf D.E (D.signsY k) := update ξ (2 * j + 1 + 1) a
  choose l hl using exists_unfoldStageOn_even_eq_sourceFn t ξ' (j + 1) hj
  have h_succ : unfoldStageOn ϑ t φ ξ' y' (2 * j + 1 + 1) hj γ =
      unfoldStage ϑ t φ ξ' y' (2 * j + 1) (by omega) (D.gradingY _ hj) (γ.1 * (a, x)) := by
    simp only [unfoldStageOn_succ, ξ', y', update_self]
  have value : unfoldStage ϑ t φ ξ y (2 * j + 1) (by omega) (D.gradingY _ hj) (γ.1 * (a, x)) =
      (D.gradingY _ hj).sourceFn l
        (doubleLiftChain (D.liftKernel ϑ) (evaluatedDatum ϑ y') (j + 1) φ.1) γ := by
    rw [← unfoldStage_update ϑ t φ ξ y a x _ _ (Nat.lt_add_one _), ← h_succ]
    exact congrFun (hl ϑ φ y') γ
  -- `ω(1, z_w)`, acting on the last lift alone, fixes the data, so the chain annihilates `φ`.
  have h_fix := map_evaluatedDatum_of_conj_mem ϑ y' j hj (by simpa only [y', update_self] using hx)
  rw [value, D.doubleLiftChain_eq_zero_of_ramified ϑ w j.lt_succ_self h_fix hφ]
  simp [sourceFn, algFormCoeff_apply]

/-- For consecutive gradings `D.gradingY k` and `D.gradingY (k + 1)`, the finite string map
`stringMapFin` between them sends `latticePlus 1` of `Y_k` (the projection `Λ_k⁺` of the standard
lattice to the span of the string) onto `D.ideleA • latticeMinus 1` of `Y_{k+1}`, that is onto
`𝔞 Λ_{k+1}⁻`, where the idele `D.ideleA` generates `𝔞`. -/
lemma map_stringMapFin_latticePlus_gradingY (k : ℕ) (hk : k + 1 ≤ 2 * D.ϱ + 1) :
    ((D.gradingY k).latticePlus 1).map
        (((D.gradingY k).stringMapFin (D.gradingY (k + 1) hk)).restrictScalars (Ô D.E)) =
      D.ideleA.val • (D.gradingY (k + 1) hk).latticeMinus 1 := by
  have h_spans (j : ℕ) (hj : j ≤ 2 * D.ϱ + 1) : (D.gradingY j hj).SpansLattice D.ideleA D.piNIdele
      (divStar D.ideleA ^ ((2 * D.ϱ + 1 - j + 2) / 2)) := by
    rw [show 2 * D.ϱ + 1 - j + 2 = D.m - j + 1 by have := D.m_eq_two_mul_varrho_add_two; omega]
    exact D.spansLattice_gradingY j hj
  exact (h_spans k _).map_stringMapFin_latticePlus (h_spans (k + 1) hk)
    D.isSplitSquarefree_piNIdele rfl D.v_gradingY_genericConst_eq_ideleA_mul_star

/-- A place `w` with `w` or its conjugate `star w` in `D.piNPlaces` (the places dividing `D.piN`) is
not among the places `ϑ.Q` of the tame character `ϑ`. -/
lemma notMem_Q_of_mem_piNPlaces (ϑ : D.TameChar) {w : FinPlace D.E}
    (hw : w ∈ D.piNPlaces ∨ star w ∈ D.piNPlaces) : w ∉ ϑ.Q := by
  intro hQ
  obtain ⟨-, -, hN⟩ := D.normQ_mem_and_notMem_of_mem_Q ϑ (.inl hQ)
  exact hN ((D.isSplitLevel_piNPlaces.natCast_mem_iff w).2 hw)

/-- Let `𝒲_{2j+2}` be the function `unfoldStage` on `U(Y_{2j+2})` built from the character `ϑ`, a
ramified source form `φ`, the linear form `t` and the archimedean and finite points `(ξ k, y k)` of
U(Y_k). Let `w` be a place dividing `π_N = D.piN`, and let `x` be a finite point whose lattice `Λ'`
splits along `X_{2j+2}` at `w`: there the projection of `Λ'` to the span of the string lies in `Λ'`.
Then `𝒲_{2j+2}` vanishes at `γ (a, x)` for every `γ` in the Bessel group `R_{2j+2}` and every
archimedean point `a`. -/
lemma unfoldStage_eq_zero_of_latticeSplitsAt (ϑ : D.TameChar)
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
    (ξ : ∀ k : ℕ, GInf D.E (D.signsY k)) (y : ∀ k : ℕ, Gf D.E (D.Y k))
    (hφ : φ ∈ D.ramifiedSourceForms) (j : ℕ)
    (hj : 2 * j + 1 + 1 ≤ 2 * D.ϱ + 1) (w : D.piNPlaces)
    (γ : (D.gradingY (2 * j + 1 + 1) hj).besselGroup)
    (a : GInf D.E (D.signsY (2 * j + 1 + 1))) {x : Gf D.E (D.Y (2 * j + 1 + 1))}
    (hx : (D.gradingY (2 * j + 1 + 1) hj).LatticeSplitsAt w x) :
    unfoldStage ϑ t φ ξ y (2 * j + 1) (by omega) (D.gradingY (2 * j + 1 + 1) hj) (γ.val * (a, x)) =
      0 := by
  obtain ⟨hz_int, hz_off⟩ := D.isScalingAt_scalingGenerator w
  have hw_ne : star w.1 ≠ w.1 := fun h ↦
    D.isSplitSquarefree_piNIdele.star_notMem w w.2 (by simp [h])
  -- The level is maximal above `w`.
  have w_notMem : w.1 ∉ (Set.range (D.levelPlaces ϑ).placeAt).conjClosure := by
    suffices (¬D.IsChosen w.1 ∧ w.1 ∉ ϑ.Q) ∧ ¬D.IsChosen (star w.1) ∧ star w.1 ∉ ϑ.Q by
      simpa [levelPlaces, range_chosenPlace]
    obtain ⟨h_chosen, h_chosen_star⟩ :=
      D.not_isChosen_of_N_mem (D.isSplitLevel_piNPlaces.natCast_level_mem w.1 w.2)
    exact ⟨⟨h_chosen, notMem_Q_of_mem_piNPlaces ϑ (.inl w.2)⟩, h_chosen_star,
      notMem_Q_of_mem_piNPlaces ϑ (.inr (by simp))⟩
  exact unfoldStage_eq_zero_of_scalingGenerator ϑ t φ ξ y hφ j hj w γ a
    (maxCompactAt_le_levelOf w_notMem (hx.conj_scalarFin_mem hw_ne hz_int hz_off))

/-- **Support**. Let `j = k + 1 ≤ 2 ϱ + 1`, so that `D.gradingY j` presents the hermitian space
`Y_j` as a definite part `X_j` of grade zero plus a string of `2 ϱ + 1 - j` graded basis vectors.
Let `𝒲_j` be the function `unfoldStage` on U(Y_j) that `j` unfolding steps leave. It is built from a
tame character `ϑ` of modulus `ϑ.Q`, a source form `φ` on U(X_0) with a linear form `t` on its
values, and adelic points `(ξ i, y i)` of U(Y_i). Assume that `φ` is ramified and that `y 0` is
integral and reduces to `1` at the chosen places (`D.chosenLevel`). Suppose `𝒲_j (a, x) ≠ 0` for an
archimedean point `a` and a finite point `x`, and let `r'` be a finite point of the Bessel subgroup
of the grading such that the lattice `Λ'` of `r' x` is graded: it contains the part in each grade of
each of its vectors. Then `q̄ ^ j Λ⁻ ⊆ Λ'⁻` and `q ^ j Λ'⁻ ⊆ Λ⁻`. Here the idele `q = twistIdele ϑ`
generates the product of the places of `ϑ.Q`, `q̄` is its complex conjugate, `Λ` is the lattice of
`1` in `Y_j`, and `Λ⁻`, `Λ'⁻` (`latticeMinus`) are the intersections with the span of the string. -/
lemma hasLatticeBounds_of_unfoldStage_ne_zero (ϑ : D.TameChar)
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (φ : D.SourceForm)
    (ξ : ∀ k : ℕ, GInf D.E (D.signsY k)) (y : ∀ k : ℕ, Gf D.E (D.Y k))
    (hφ : φ ∈ D.ramifiedSourceForms)
    (hy₀ : y 0 ∈ D.chosenLevel) (k : ℕ) (hk : k + 1 ≤ 2 * D.ϱ + 1)
    (a : GInf D.E (D.signsY (k + 1))) (x : Gf D.E (D.Y (k + 1)))
    (h_ne : unfoldStage ϑ t φ ξ y k (by omega) (D.gradingY (k + 1) hk) (a, x) ≠ 0)
    {r' : Gf D.E (D.Y (k + 1))} (hr' : r' ∈ (D.gradingY (k + 1) hk).besselFin)
    (h_graded' : (D.gradingY (k + 1) hk).IsGraded ((D.spaceY (k + 1)).lattice (r' * x))) :
    (D.gradingY (k + 1) hk).HasLatticeBounds (twistIdele ϑ).val (k + 1) (r' * x) := by
  induction k using Nat.strongRec with | ind k ih =>
  -- At some point `γ g_k` the function of the previous stage and the partial theta sum are both
  -- non-zero. The orbit of this point has a graded lattice with the bounds for `k`.
  obtain ⟨γ, hγ⟩ : ∃ γ : (D.gradingY k).besselGroup,
      unfoldStageOn ϑ t φ ξ y k (by omega) γ *
        (D.gradingY k).constTermAtStringMap (D.gradingY (k + 1) hk)
          (rankTwist (D.chainChar ϑ (k + 1))) (movedDatum ϑ ξ y k) γ.1 (a, x) ≠ 0 :=
    exists_ne_zero_of_integral_ne_zero h_ne
  obtain ⟨r, hr, h_graded, h_bounds⟩ :
      (D.gradingY k).HasBoundedOrbit (twistIdele ϑ).val k (γ.1 * (ξ k, y k)).2 := by
    cases k with
    | zero =>
      exact (D.spansLattice_gradingY 0 _).hasBoundedOrbit_zero _ (snd_mem_besselFin _ γ⁻¹.2)
        (by simpa using levelOf_le_stdLevel hy₀)
    | succ k =>
      -- `unfoldStageOn` at stage `k + 1` is a value of `𝒲_{k+1}`, so the induction hypothesis
      -- applies to every graded lattice in the orbit.
      let g : New.G D.E (D.signsY (k + 1)) := γ.1 * (ξ (k + 1), y (k + 1))
      have h_prev : unfoldStage ϑ t φ ξ y k (by omega) (D.gradingY (k + 1) (by omega)) g ≠ 0 :=
        left_ne_zero_of_mul hγ
      exact .of_forall fun r ↦ ih k .refl _ g.1 g.2 h_prev
  have term_ne : (D.gradingY k).constTermAtStringMap (D.gradingY (k + 1) hk)
      (rankTwist (D.chainChar ϑ (k + 1))) (datumY ϑ k) (γ.1 * (ξ k, y k)) (a, x) ≠ 0 := by
    simpa only [constTermAtStringMap, twistedPairWeil_movedDatum] using right_ne_zero_of_mul hγ
  -- Frequency: a non-zero term forces the shifted projection `Λ⁺`, scaled by
  -- `star (twistIdele ϑ) / D.ideleA`, of the lattice at stage `k` into `latticeMinus` at stage
  -- `k + 1`.
  have h_freq : (star (twistIdele ϑ) / D.ideleA).val •
      ((D.gradingY k).latticePlus (r * (γ.1 * (ξ k, y k)).2)).map
        (((D.gradingY k).stringMapFin (D.gradingY (k + 1) hk)).restrictScalars (Ô D.E)) ≤
      (D.gradingY (k + 1) hk).latticeMinus (r' * x) := by
    rw [ideleA, twistIdele, star_div, div_div_div_cancel_right]
    exact smul_map_stringMapFin_latticePlus_le term_ne (D.twistModulus ϑ 1).generator
      (fun _ ↦ finHeisenbergOp_generator_smul_pointDatumY ϑ k) hr h_graded hr' h_graded'
  -- Sandwich: with the upper bound at stage `k` this gives the lower bound at stage `k + 1`.
  have h_lower : star (twistIdele ϑ).val ^ (k + 1) • (D.gradingY (k + 1) hk).latticeMinus 1 ≤
      (D.gradingY (k + 1) hk).latticeMinus (r' * x) :=
    smul_latticeMinus_le_of_map_latticePlus (map_stringMapFin_latticePlus_gradingY k hk)
      h_bounds.upper
      h_freq
  have hq_unit (w : FinPlace D.E) (hw : w ∈ D.piNPlaces ∨ star w ∈ D.piNPlaces) :
      Valued.v ((twistIdele ϑ).val w) = 1 := by
    rw [valued_twistIdele, ite_eq_right (notMem_Q_of_mem_piNPlaces ϑ hw)]
  obtain h_bounds' | ⟨h_odd, w, hw, h_split⟩ :=
    (D.spansLattice_gradingY (k + 1) hk).hasLatticeBounds_or_latticeSplitsAt
      D.isSplitSquarefree_piNIdele
      hq_unit h_lower
  · exact h_bounds'
  -- Otherwise the lattice splits at a place above `π_N`, where ramification makes `𝒲_j` vanish.
  obtain ⟨j, rfl⟩ : Odd k := ⟨k / 2, h_odd.elim (by omega)⟩
  let r₀ : (D.gradingY (2 * j + 1 + 1) hk).besselGroup := ⟨(1, r'), hr'⟩
  have h_zero : unfoldStage ϑ t φ ξ y (2 * j + 1) (by omega) (D.gradingY (2 * j + 1 + 1) hk)
      (a, x) = 0 := by
    simpa [r₀] using unfoldStage_eq_zero_of_latticeSplitsAt ϑ t φ ξ y hφ j hk ⟨w, hw⟩ r₀⁻¹ a h_split
  exact absurd h_zero h_ne

end New.Data
