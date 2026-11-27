import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalFiniteRadius
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.DirectionSelection.GaussianDominantPairAlgebra
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaEncodingRescaling
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaInputProperness

/-!
# Rational representation independence of the finite Barnes product

Equal canonical Gaussian values give the same polynomial base and
quadratic exponential correction at each literal factor index.
The original prefactor datum is also a function of that canonical
value. The actual product names may retain distinct certifications,
including distinct disk radii and observation clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteProperness

open_ipra
open ComplexLogarithmRemainder (scale)
open GaussianBarnesCanonicalFiniteRadius (prefixData)
open GaussianBarnesCanonicalHead (source)
open GaussianBarnesCanonicalValue (prefixF)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addData multiplyData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedFiniteProductFamilyCongruence (equalRows family_product_cross)
open GaussianRationalHorner (ofGaussian represents ofGaussian_represents ofGaussian_canonical represents_congr
  represents_rescale canonical_unique positive_product qmul)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBarnesCanonicalFactor.nameF
local notation "fd" => GaussianBarnesCanonicalFactor.data
local notation "E" => GaussianBarnesCanonicalFactor.exponentialF
local notation "ed" => GaussianBarnesCanonicalFactor.exponentialData
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "pd" => GaussianBarnesCanonicalPrefactor.data
local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "hd" => GaussianBarnesCanonicalHead.data
local notation "params" => GaussianBarnesCanonicalHead.parameters
local notation "body" => GaussianBarnesCanonicalHead.body

theorem scaled_fraction_equal (z w B D k : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le one k)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] ofGaussian z (B*k) ≐ ofGaussian w (D*k) := by
  let u := ofGaussian z (B*k)
  let v := ofGaussian w (D*k)
  have baseZ := ofGaussian_represents z B hB
  have baseW : Γ ⊢[PRAAx] represents (ofGaussian z B) w D :=
    represents_congr he.eqSymm (GaussianRootAlgebra.equal_refl w) (.eqRefl _) (ofGaussian_represents w D hD)
  have same := GaussianDominantPairAlgebra.represents_cross (ofGaussian z B) z w B D baseZ baseW
  have bk := positive_product B k hB hk
  have dk := positive_product D k hD hk
  have repZ := represents_rescale u z (B*k) D (ofGaussian_represents z (B*k) bk)
  have repW := represents_rescale v w (D*k) B (ofGaussian_represents w (D*k) dk)
  exact canonical_unique u v (scale B w) ((D*k)*B) (ofGaussian_canonical z (B*k) bk)
    (ofGaussian_canonical w (D*k) dk) (positive_product _ _ dk hB)
    (represents_congr (.eqRefl _) same (by ipra_ring) repZ) repW

private theorem correction_equal (z w B D k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le one k)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.correction z B k ≐ GaussianBarnesCanonicalFactor.correction w D k := by
  have h2 := positive_product two k (le_succ_self one) hk
  have v := scaled_fraction_equal z w B D (two*k) hB hD h2 he
  have a := GaussianGammaEncodingRescaling.fraction_denominator_congr (Γ := Γ) z (two*(B*k)) (B*(two*k)) (by ipra_ring)
  have b := GaussianGammaEncodingRescaling.fraction_denominator_congr (Γ := Γ) w (D*(two*k)) (two*(D*k)) (by ipra_ring)
  exact qsub_congr (qmul_congr he (a.eqTrans (v.eqTrans b))) he

theorem factor_cross (z w R S B D k : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.source z R B k)
    (hw : Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.source w S D k)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent F F (fd z R B k) (fd w S D k) := by
  let a := GaussianBarnesCanonicalFactor.powerValue z B k
  let b := GaussianBarnesCanonicalFactor.powerValue w D k
  let c := GaussianBarnesCanonicalFactor.correction z B k
  let d := GaussianBarnesCanonicalFactor.correction w D k
  let X := GaussianBarnesCanonicalFactor.exponentRadius R
  let Y := GaussianBarnesCanonicalFactor.exponentRadius S
  have hk := hz.andE₂.andE₁
  have eBase := qadd_congr (.eqRefl GaussianRationalSyntheticDivision.qone)
    (scaled_fraction_equal z w B D k hz.andE₁ hw.andE₁ hk he)
  have ea : Γ ⊢[PRAAx] a ≐ b := congrAp2 GaussianRationalReciprocal.powerF (.eqRefl k) eBase
  have ec := correction_equal z w B D k hz.andE₁ hw.andE₁ hk he
  have x := GaussianBarnesCanonicalFactor.exponential_input z R B k hz
  have y := GaussianBarnesCanonicalFactor.exponential_input w S D k hw
  have exp := GaussianExponentialRadiusIndependence.independent_radii_proper constantF constantF X Y c d x y
    (GaussianSignedNameExponentialOrder.constant_equal_cross c d ec)
  exact GaussianGammaAdjacentCutoff.multiply_cross constantF constantF E E a b (ed z R B k) (ed w S D k)
    (constant_regular a) (constant_regular b) (GaussianRadiusExponentialName.name_regular constantF X c x)
    (GaussianRadiusExponentialName.name_regular constantF Y d y)
    (GaussianSignedNameExponentialOrder.constant_equal_cross a b ea) exp

theorem rows_cross (z w R S B D N r : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w S D)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] equalRows F F body body r (params z R B N) (params w S D N) := by
  refine .allI (.impI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  let k := succ (sh N+i)
  have l : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift.wk
  have r' : Δ ⊢[PRAAx] source (sh w) (sh S) (sh D) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hw.shift.wk
  have eq : Δ ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh D) :=
    by simpa [Fm.shift,Syn.shift,sh,Δ] using he.shift.wk
  have e := factor_cross (sh z) (sh w) (sh R) (sh S) (sh B) (sh D) k
    (.andI l.andE₁ (.andI (zero_lt_succ _) l.andE₂))
    (.andI r'.andE₁ (.andI (zero_lt_succ _) r'.andE₂)) eq
  have dR := GaussianBarnesCanonicalHead.body_at (Γ := Δ) i (sh z) (sh R) (sh B) (sh N)
  have dS := GaussianBarnesCanonicalHead.body_at (Γ := Δ) i (sh w) (sh S) (sh D) (sh N)
  simpa only [equalRows,GaussianBarnesCanonicalHead.subst_parameters,Syn.shift,Δ,sh,i] using
    GaussianGammaCompactCutoffAlignment.cross_data_congr F F _ _ _ _ dR.eqSymm dS.eqSymm e

theorem segment_cross (z w R S B D N r : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w S D)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent H H (hd z R B N r) (hd w S D N r) :=
  family_product_cross F F body body r (params z R B N) (params w S D N)
    (GaussianBarnesCanonicalHead.rows_regular z R B N r hz)
    (GaussianBarnesCanonicalHead.rows_regular w S D N r hw)
    (rows_cross z w R S B D N r hz hw he)

private def prefactorDataAt (x : PTm n) : PTm n :=
  let lin := multiplyData constantF GaussianStirlingConstant.nameF x (GaussianStirlingConstant.nameData zero)
  let quad := multiplyData constantF GaussianBarnesCanonicalPrefactor.quadraticCoefficientF (qmul x x)
    GaussianBarnesCanonicalPrefactor.quadraticCoefficientData
  let cor := multiplyData constantF GaussianBarnesCanonicalPrefactor.polynomialF
    GaussianBarnesCanonicalPrefactor.negativeHalf (addData x quad)
  let R := U GaussianBarnesCanonicalPrefactor.linearF lin+U GaussianBarnesCanonicalPrefactor.correctionF cor
  GaussianExponentialAddition.productData GaussianBarnesCanonicalPrefactor.linearF GaussianBarnesCanonicalPrefactor.correctionF R lin cor

@[simp] private theorem subst_prefactorDataAt {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (prefactorDataAt x) = prefactorDataAt (Syn.subst σ x) := by
  simp [prefactorDataAt,GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,
    GaussianBarnesCanonicalPrefactor.negativeHalf,one,two]

theorem prefactor_data_equal (z w B D : PTm n) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] pd z B ≐ pd w D := by
  change Γ ⊢[PRAAx] prefactorDataAt (ofGaussian z B) ≐ prefactorDataAt (ofGaussian w D)
  ipra_congr (prefactorDataAt (var 0) : PTm 1) with [he]

theorem prefactor_cross (z w B D : PTm n) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent P P (pd z B) (pd w D) :=
  GaussianGammaInputProperness.code_data_cross P (pd z B) (pd w D)
    (GaussianBarnesCanonicalPrefactor.regular z B) (GaussianBarnesCanonicalPrefactor.regular w D)
    (prefactor_data_equal z w B D he)

theorem prefix_cross (z w R S B D r : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w S D)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent prefixF prefixF (prefixData z R B r) (prefixData w S D r) :=
  GaussianGammaAdjacentCutoff.multiply_cross P P H H (pd z B) (pd w D) (hd z R B zero r) (hd w S D zero r)
    (GaussianBarnesCanonicalPrefactor.regular z B) (GaussianBarnesCanonicalPrefactor.regular w D)
    (GaussianBarnesCanonicalHead.regular z R B zero r hz) (GaussianBarnesCanonicalHead.regular w S D zero r hw)
    (prefactor_cross z w B D he) (segment_cross z w R S B D zero r hz hw he)

theorem actual_Barnes_factor_rational_proper_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (GaussianBarnesCanonicalFactor.source (var 0) (var 2) (var 4) (var 6) ⟶
        GaussianBarnesCanonicalFactor.source (var 1) (var 3) (var 5) (var 6) ⟶
        ofGaussian (var 0) (var 4) ≐ ofGaussian (var 1) (var 5) ⟶
        crossEquivalent F F (fd (var 0) (var 2) (var 4) (var 6)) (fd (var 1) (var 3) (var 5) (var 6))) :=
  closeUniv 7 (.impI (.impI (.impI (factor_cross _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0))))

theorem actual_Barnes_prefactor_rational_proper_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (ofGaussian (var 0) (var 2) ≐ ofGaussian (var 1) (var 3) ⟶
        crossEquivalent P P (pd (var 0) (var 2)) (pd (var 1) (var 3))) :=
  closeUniv 4 (.impI (prefactor_cross _ _ _ _ Prf.hyp0))

theorem actual_original_Barnes_finite_product_rational_proper_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (source (var 0) (var 2) (var 4) ⟶ source (var 1) (var 3) (var 5) ⟶
        ofGaussian (var 0) (var 4) ≐ ofGaussian (var 1) (var 5) ⟶
        crossEquivalent prefixF prefixF (prefixData (var 0) (var 2) (var 4) (var 6))
          (prefixData (var 1) (var 3) (var 5) (var 6))) :=
  closeUniv 7 (.impI (.impI (.impI (prefix_cross _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteProperness
