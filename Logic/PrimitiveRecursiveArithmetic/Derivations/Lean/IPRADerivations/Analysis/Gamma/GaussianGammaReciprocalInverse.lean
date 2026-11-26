import IPRADerivations.Analysis.FiniteOperations.GaussianBoundedInverseApartness
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerHeadLower
import IPRADerivations.Analysis.Gamma.GaussianGammaC9Bound
import IPRADerivations.Analysis.Exponential.GaussianExponentialInverse

/-!
# The original Gamma reciprocal on a disk with the C12 pole guard

The rational reciprocal of the literal Euler head and the actual
exponential of the negative C7 exponent give a regular inverse. The
exact C9 radius and the C12 head separation bound its observations by
the reciprocal of the displayed C13 constant. This bounded inverse
supplies the finite anchor of the original named reciprocal program.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaReciprocalInverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiply_equivalent)
open GaussianNameRingLaws (oneF one_at one_fast multiply_associative multiply_commutative negativeF negativeData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_to_diagonal cross_symm cross_trans cross_at diagonal_refl)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular exponentF exponentData exponentRadius)
open GaussianGammaCanonicalExponentBound (numericalRadius exact_exponential_input)
open GaussianGammaC9Bound (exponentialMajorant)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (qone reciprocal bounded_product bound_congr)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianExponentialSmallPerturbation (smallSamples)
open GaussianBoundedInverseApartness (ones_equivalent)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem named_product_exchange (a b c d : PR 2) (w x y z : PTm n)
    (ha : Γ ⊢[PRAAx] pointCN a w) (hb : Γ ⊢[PRAAx] pointCN b x)
    (hc : Γ ⊢[PRAAx] pointCN c y) (hd : Γ ⊢[PRAAx] pointCN d z) :
    Γ ⊢[PRAAx] crossEquivalent
      (multiplyF (multiplyF a b) (multiplyF c d))
      (multiplyF (multiplyF a c) (multiplyF b d))
      (multiplyData (multiplyF a b) (multiplyF c d) (multiplyData a b w x) (multiplyData c d y z))
      (multiplyData (multiplyF a c) (multiplyF b d) (multiplyData a c w y) (multiplyData b d x z)) := by
  let CD := multiplyF c d
  let BC := multiplyF b c
  let CB := multiplyF c b
  let BD := multiplyF b d
  let cd := multiplyData c d y z
  let bc := multiplyData b c x y
  let cb := multiplyData c b y x
  let bd := multiplyData b d x z
  have cdN := multiply_fast c d y z hc hd
  have bcN := multiply_fast b c x y hb hc
  have cbN := multiply_fast c b y x hc hb
  have bdN := multiply_fast b d x z hb hd
  have bcSwap := multiply_equivalent BC CB d d bc cb z z bcN cbN hd hd
    (cross_to_diagonal _ _ _ _ (multiply_commutative b c x y hb hc)) (diagonal_refl d z)
  have middle : Γ ⊢[PRAAx] crossEquivalent (multiplyF b CD) (multiplyF c BD)
      (multiplyData b CD x cd) (multiplyData c BD y bd) :=
    cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative b c d x y z hb hc hd))
      (cross_trans _ _ _ _ _ _ bcSwap (multiply_associative c b d y x z hc hb hd))
  have lift := multiply_equivalent a a (multiplyF b CD) (multiplyF c BD) w w
    (multiplyData b CD x cd) (multiplyData c BD y bd) ha ha
    (multiply_fast b CD x cd hb cdN) (multiply_fast c BD y bd hc bdN)
    (diagonal_refl a w) (cross_to_diagonal _ _ _ _ middle)
  exact cross_trans _ _ _ _ _ _ (multiply_associative a b CD w x cd ha hb cdN)
    (cross_trans _ _ _ _ _ _ lift (cross_symm _ _ _ _ (multiply_associative a c BD w y bd ha hc bdN)))

theorem inverse_pairs (a b c d : PR 2) (w x y z ref : PTm n)
    (ha : Γ ⊢[PRAAx] pointCN a w) (hb : Γ ⊢[PRAAx] pointCN b x)
    (hc : Γ ⊢[PRAAx] pointCN c y) (hd : Γ ⊢[PRAAx] pointCN d z)
    (hac : Γ ⊢[PRAAx] crossEquivalent (multiplyF a c) oneF (multiplyData a c w y) ref)
    (hbd : Γ ⊢[PRAAx] crossEquivalent (multiplyF b d) oneF (multiplyData b d x z) ref) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (multiplyF a b) (multiplyF c d)) oneF
      (multiplyData (multiplyF a b) (multiplyF c d) (multiplyData a b w x) (multiplyData c d y z)) ref := by
  have hf := one_fast (Γ := Γ) ref
  exact cross_trans _ _ _ _ _ _ (named_product_exchange a b c d w x y z ha hb hc hd)
    (cross_trans _ _ _ _ _ _
      (multiply_equivalent (multiplyF a c) oneF (multiplyF b d) oneF
        (multiplyData a c w y) ref (multiplyData b d x z) ref (multiply_fast a c w y ha hc) hf
        (multiply_fast b d x z hb hd) hf (cross_to_diagonal _ _ _ _ hac) (cross_to_diagonal _ _ _ _ hbd))
      (GaussianNameRingLaws.multiply_one oneF ref hf))

theorem constant_product_sample (p x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (multiplyF constantF constantF) p (multiplyData constantF constantF x y)
      ≐ GaussianFastValueCut.recode (qmul x y) :=
  (GaussianNameArithmetic.multiply_at constantF constantF x y p).eqTrans
    (GaussianNameArithmetic.recode_congr
      (GaussianRationalSyntheticDivision.qmul_congr (constant_at _ _) (constant_at _ _)))

theorem constant_inverse (x y ref : PTm n) (h : Γ ⊢[PRAAx] qmul x y ≐ qone) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF constantF) oneF
      (multiplyData constantF constantF x y) ref := by
  refine .allI (.allI ?_)
  let C := (Γ.map Fm.shift).map Fm.shift
  let x' := Syn.shift (Syn.shift x)
  let y' := Syn.shift (Syn.shift y)
  let r := Syn.shift (Syn.shift ref)
  have hs : C ⊢[PRAAx] qmul x' y' ≐ qone := by
    simpa [C,x',y',Fm.shift,Syn.shift] using h.shift.shift
  have e : C ⊢[PRAAx] ap2 (multiplyF constantF constantF) (var 1) (multiplyData constantF constantF x' y') ≐ qone :=
    (constant_product_sample (var 1) x' y').eqTrans
      ((GaussianNameArithmetic.recode_congr hs).eqTrans
        (GaussianExponentialReference.recode_fixed _ GaussianRationalSyntheticDivision.qone_canonical))
  have href := cross_at (Γ := C) _ _ _ _ (var 1) (var 0) (cross_refl oneF r (one_fast r))
  have res := distance_congr (e.eqTrans (one_at (var 1) r).eqSymm).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) href
  simpa only [crossEquivalent,Syn.shift,GaussianNameArithmetic.subst_multiplyData,C,x',y',r] using res

def source (z R B a d : PTm n) : Fm PTm n :=
  GaussianGammaCanonicalExponent.source z R B ⋏ (le one a ⋏
    (le one d ⋏ GaussianGammaEulerHeadLower.poleGuard z B a d (two*R)))

def lambdaNumerator (R a : PTm n) : PTm n := pw a (succ (two*R))
def lambdaDenominator (R d : PTm n) : PTm n :=
  (pw d (succ (two*R))*Products.fact (two*R))*exponentialMajorant R
def headInverse (z R B : PTm n) : PTm n := reciprocal (GaussianGammaC7Name.head z R B)
def negExpF : PR 2 := GaussianRadiusExponentialName.nameF (negativeF exponentF)
def negExpData (z R B : PTm n) : PTm n :=
  GaussianRadiusExponentialName.data (numericalRadius R) (negativeData (exponentData z R B))
def inverseF : PR 2 := multiplyF constantF negExpF
def inverseData (z R B : PTm n) : PTm n := multiplyData constantF negExpF (headInverse z R B) (negExpData z R B)

@[simp] theorem subst_source {l : ℕ} (σ : Fin n → PTm l) (z R B a d : PTm n) :
    (source z R B a d).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ d) := by
  simp [source]
@[simp] theorem subst_lambdaNumerator {l : ℕ} (σ : Fin n → PTm l) (R a : PTm n) :
    Syn.subst σ (lambdaNumerator R a) = lambdaNumerator (Syn.subst σ R) (Syn.subst σ a) := by simp [lambdaNumerator]
@[simp] theorem subst_lambdaDenominator {l : ℕ} (σ : Fin n → PTm l) (R d : PTm n) :
    Syn.subst σ (lambdaDenominator R d) = lambdaDenominator (Syn.subst σ R) (Syn.subst σ d) := by
  simp [lambdaDenominator,Products.fact]
@[simp] theorem subst_inverseData {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (inverseData z R B) = inverseData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [inverseData,headInverse,negExpData]

theorem lambda_positive (R a d : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] le one (lambdaNumerator R a) ⋏ le one (lambdaDenominator R d) :=
  .andI (GaussianFactorBudget.power_positive _ _ ha)
    (positive_product _ _ (GaussianGammaEulerHeadLower.prefix_denominator_positive d (two*R) hd)
      (GaussianFactorBudget.power_positive _ _ (le_of_eq_add (d := two) (by ipra_ring))))

theorem negative_exponential_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] pointCN negExpF (negExpData z R B) :=
  GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianExponentialInverse.negative_input _ _ _ (exact_exponential_input z R B h))

theorem negative_exponential_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] bounded (ap2 negExpF p (negExpData z R B)) (exponentialMajorant R) one := by
  let G := negativeF exponentF
  let T := numericalRadius R
  let X := negativeData (exponentData z R B)
  have ng := GaussianExponentialInverse.negative_input _ _ _ (exact_exponential_input z R B h)
  exact bound_congr (GaussianRadiusExponentialName.sample_at G T p X).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveExponentialMajorant.disk_bound _ T _ (GaussianRadiusExponentialName.query_bound G T X p ng))

theorem inverse_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] pointCN inverseF (inverseData z R B) :=
  multiply_fast _ _ _ _ (constant_regular _) (negative_exponential_regular z R B h)

theorem inverse_sample_bound (p z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) :
    Γ ⊢[PRAAx] bounded (ap2 inverseF p (inverseData z R B)) (lambdaDenominator R d) (lambdaNumerator R a) := by
  let U := headInverse z R B
  let V := negExpData z R B
  let t := GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus constantF negExpF U V) p
  have hs := GaussianGammaEulerHeadLower.returned_inverse_bound z B a d (two*R)
    h.andE₁.andE₂.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂
  have e := (GaussianNameArithmetic.multiply_at (Γ := Γ) constantF negExpF U V p).eqTrans
    (GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (constant_at t U) (.eqRefl _)))
  have den := (lambda_positive R a d h.andE₂.andE₁ h.andE₂.andE₂.andE₁).andE₁
  exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff _ _ _ den).iffMpr
      (bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
        (bounded_product _ _ _ _ _ _ den (le_refl _) hs (negative_exponential_bound t z R B h.andE₁))))

theorem inverse_disk (z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) :
    Γ ⊢[PRAAx] smallSamples inverseF (inverseData z R B) (lambdaDenominator R d) (lambdaNumerator R a) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift d) := by
    simpa only [Fm.shift,Syn.shift,subst_source] using h.shift
  simpa only [smallSamples,Syn.shift,subst_inverseData,subst_lambdaNumerator,subst_lambdaDenominator] using
    inverse_sample_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift d) hs

theorem exponential_pair (z R B ref : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF GaussianGammaCanonicalExponent.exponentialF negExpF) oneF
      (multiplyData GaussianGammaCanonicalExponent.exponentialF negExpF (GaussianGammaCanonicalExponent.exponentialData z R B)
        (negExpData z R B)) ref := by
  let T := numericalRadius R
  let X := exponentData z R B
  let D := GaussianRadiusExponentialName.data T X
  let F := GaussianGammaCanonicalExponent.exponentialF
  let V := negExpData z R B
  have given := GaussianGammaCanonicalExponent.exponential_input z R B h
  have exact := exact_exponential_input z R B h
  have moved := GaussianExponentialRadiusIndependence.same_input_cross exponentF (exponentRadius z R B) T X given exact
  have neg := negative_exponential_regular z R B h
  have mul := multiply_equivalent F F negExpF negExpF (GaussianGammaCanonicalExponent.exponentialData z R B) D V V
    (GaussianGammaCanonicalExponent.exponential_regular z R B h)
    (GaussianRadiusExponentialName.name_regular _ _ _ exact) neg neg (cross_to_diagonal _ _ _ _ moved) (diagonal_refl _ _)
  exact cross_trans _ _ _ _ _ _ mul
    (cross_trans _ _ _ _ _ _ (GaussianExponentialInverse.exponential_inverse exponentF T X exact) (ones_equivalent X ref))

theorem inverse_product (z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF GaussianGammaC7Name.nameF inverseF) oneF
      (multiplyData GaussianGammaC7Name.nameF inverseF (GaussianGammaC7Name.data z R B) (inverseData z R B))
      (GaussianGammaC7Name.data z R B) :=
  inverse_pairs constantF GaussianGammaCanonicalExponent.exponentialF constantF negExpF
    (GaussianGammaC7Name.head z R B) (GaussianGammaCanonicalExponent.exponentialData z R B)
    (headInverse z R B) (negExpData z R B) (GaussianGammaC7Name.data z R B)
    (constant_regular _) (GaussianGammaCanonicalExponent.exponential_regular z R B h.andE₁)
    (constant_regular _) (negative_exponential_regular z R B h.andE₁)
    (constant_inverse _ _ _ (GaussianGammaEulerHeadLower.returned_inverse_identity z B a d (two*R)
      h.andE₁.andE₂.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂))
    (exponential_pair z R B _ h.andE₁)

def gammaHeight (z R B d : PTm n) : PTm n :=
  GaussianBoundedInverseApartness.height GaussianGammaC7Name.nameF inverseF
    (GaussianGammaC7Name.data z R B) (inverseData z R B) (lambdaDenominator R d)
def gammaF : PR 2 := GaussianNameReciprocal.nameF GaussianGammaC7Name.nameF
def gammaData (z R B d : PTm n) : PTm n := GaussianNameReciprocal.nameData (gammaHeight z R B d) (GaussianGammaC7Name.data z R B)

theorem original_gamma_inverse (z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.input GaussianGammaC7Name.nameF (gammaHeight z R B d) (GaussianGammaC7Name.data z R B) ⋏
      crossEquivalent gammaF inverseF (gammaData z R B d) (inverseData z R B) := by
  have l := lambda_positive R a d h.andE₂.andE₁ h.andE₂.andE₂.andE₁
  exact GaussianBoundedInverseApartness.bounded_inverse_correct _ _ _ _ _ _
    l.andE₂ l.andE₁ (GaussianGammaC7Name.name_regular z R B h.andE₁)
    (inverse_regular z R B h.andE₁) (inverse_disk z R B a d h) (inverse_product z R B a d h)

theorem gamma_regular (z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) :
    Γ ⊢[PRAAx] pointCN gammaF (gammaData z R B d) := by
  have hi := (original_gamma_inverse z R B a d h).andE₁
  exact GaussianNameReciprocal.name_fast _ _ _ hi.andE₁ hi.andE₂

theorem gamma_product (z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF GaussianGammaC7Name.nameF gammaF) oneF
      (multiplyData GaussianGammaC7Name.nameF gammaF (GaussianGammaC7Name.data z R B) (gammaData z R B d))
      (GaussianGammaC7Name.data z R B) := by
  have hi := (original_gamma_inverse z R B a d h).andE₁
  exact GaussianNameReciprocal.product_one _ _ _ hi.andE₁ hi.andE₂

theorem actual_gamma_observation_bound (p z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) :
    Γ ⊢[PRAAx] bounded (ap2 gammaF p (gammaData z R B d))
      (lambdaDenominator R d*GaussianCoefficientNameBounds.unit p+two*lambdaNumerator R a)
      (lambdaNumerator R a*GaussianCoefficientNameBounds.unit p) := by
  let x := ap2 gammaF p (gammaData z R B d)
  let y := ap2 inverseF p (inverseData z R B)
  have e := GaussianNameEquivalence.diagonal_at _ _ _ _ p
    (cross_to_diagonal _ _ _ _ (original_gamma_inverse z R B a d h).andE₂)
  have cx : Γ ⊢[PRAAx] GaussianRationalHorner.canonical x := GaussianNameReciprocal.name_canonical _ _ _ _
  have den := (lambda_positive R a d h.andE₂.andE₁ h.andE₂.andE₂.andE₁).andE₁
  exact bound_congr (GaussianRationalLinearProduct.add_sub_right y x cx) (.eqRefl _) (.eqRefl _)
    (GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _ den (GaussianCoefficientNameBounds.unit_positive p)
      (inverse_sample_bound p z R B a d h) e)

theorem actual_C13_lambda_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶
      le one (lambdaNumerator (var 0) (var 1)) ⋏ le one (lambdaDenominator (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (lambda_positive _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_pole_free_gamma_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      GaussianNameReciprocal.input GaussianGammaC7Name.nameF (gammaHeight (var 0) (var 1) (var 2) (var 4))
        (GaussianGammaC7Name.data (var 0) (var 1) (var 2)) ⋏
      crossEquivalent gammaF inverseF (gammaData (var 0) (var 1) (var 2) (var 4)) (inverseData (var 0) (var 1) (var 2))) :=
  closeUniv 5 (.impI (original_gamma_inverse _ _ _ _ _ Prf.hyp0))

theorem original_pole_free_gamma_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ pointCN gammaF (gammaData (var 0) (var 1) (var 2) (var 4))) :=
  closeUniv 5 (.impI (gamma_regular _ _ _ _ _ Prf.hyp0))

theorem original_gamma_C14_bounded_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      pointCN inverseF (inverseData (var 0) (var 1) (var 2)) ⋏
        (smallSamples inverseF (inverseData (var 0) (var 1) (var 2))
          (lambdaDenominator (var 1) (var 4)) (lambdaNumerator (var 1) (var 3)) ⋏
        crossEquivalent (multiplyF GaussianGammaC7Name.nameF inverseF) oneF
          (multiplyData GaussianGammaC7Name.nameF inverseF (GaussianGammaC7Name.data (var 0) (var 1) (var 2))
            (inverseData (var 0) (var 1) (var 2))) (GaussianGammaC7Name.data (var 0) (var 1) (var 2)))) := by
  refine closeUniv 5 (.impI ?_)
  have h : [source (var 0 : PTm 5) (var 1) (var 2) (var 3) (var 4)] ⊢[PRAAx]
      source (var 0) (var 1) (var 2) (var 3) (var 4) :=
    Prf.hyp0
  exact .andI (inverse_regular _ _ _ h.andE₁) (.andI (inverse_disk _ _ _ _ _ h) (inverse_product _ _ _ _ _ h))

theorem original_pole_free_gamma_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      crossEquivalent (multiplyF GaussianGammaC7Name.nameF gammaF) oneF
        (multiplyData GaussianGammaC7Name.nameF gammaF (GaussianGammaC7Name.data (var 0) (var 1) (var 2))
          (gammaData (var 0) (var 1) (var 2) (var 4))) (GaussianGammaC7Name.data (var 0) (var 1) (var 2))) :=
  closeUniv 5 (.impI (gamma_product _ _ _ _ _ Prf.hyp0))

theorem original_pole_free_gamma_observation_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      bounded (ap2 gammaF (var 0) (gammaData (var 1) (var 2) (var 3) (var 5)))
        (lambdaDenominator (var 2) (var 5)*GaussianCoefficientNameBounds.unit (var 0)+two*lambdaNumerator (var 2) (var 4))
        (lambdaNumerator (var 2) (var 4)*GaussianCoefficientNameBounds.unit (var 0))) :=
  closeUniv 6 (.impI (actual_gamma_observation_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaReciprocalInverse
