import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.ExponentNormalization.GaussianBarnesCanonicalNormalizedMultiplier
import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.GaussRecurrence.GaussianBarnesCanonicalGaussDenominator
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.Reflection.GaussianGammaGaussReflectionCancellation

/-!
# The original finite Barnes recurrence with the Euler Gamma head

A common cutoff compares both literal Barnes truncations and the actual
reciprocal-Gamma Euler approximant. Extending the plain polynomial by
one terminal factor leaves `1+w/K` times the normalized exponential.
Only a positive integer factorial is cancelled.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteGaussIdentity

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianBarnesCanonicalHead (source)
open GaussianBarnesCanonicalPolynomialShift (plain)
open GaussianBarnesCanonicalProduct (literalData)
open GaussianBarnesCanonicalValue (prefixF)
open GaussianBarnesCanonicalDeflatedFactor (translatedValue)
open GaussianBarnesCanonicalNormalizedMultiplier (gaussF gaussData)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaFiniteApproximantName (qF qData q_regular logExponentF logExponentData log_exponent_regular exponential_input)
open GaussianGammaWeierstrassApproximant (constant_data_cross constant_product_cross)
open GaussianNameArithmetic (add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative multiply_commutative multiply_one oneF one_fast)
open GaussianRationalHorner (qmul positive_product canonical_unique ofGaussian ofGaussian_represents qmul_represents
  qmul_canonical represents_congr)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents natural_product_value)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (qone qone_represents_scaled)
open GaussianRationalSyntheticDivision (qmul_congr qone_canonical)
open GaussianReciprocalHorner (qmul_associative)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "P" => prefixF
local notation "M" => GaussianBarnesCanonicalPrefixShift.multiplierF
local notation "md" => GaussianBarnesCanonicalPrefixShift.multiplierData
local notation "E" => GaussianBarnesCanonicalNormalizedMultiplier.nameF
local notation "ed" => GaussianBarnesCanonicalNormalizedMultiplier.data

def base (z B K : PTm n) : PTm n := GaussianBarnesCanonicalFactor.base (translated z B one) B K
abbrev leftF : PR 2 := multiplyF P qF
def leftData (z S B K : PTm n) : PTm n :=
  multiplyData P qF (literalData (translated z B one) S B K) (qData (translated z B one) B K)
abbrev rightF : PR 2 := multiplyF (multiplyF P E) C
def rightData (z R S B K : PTm n) : PTm n := multiplyData (multiplyF P E) C
  (multiplyData P E (literalData z R B K) (ed z S B K)) (base z B K)

private theorem product_plain (z B K : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (plain z B K) (translatedValue z B (succ K)) ≐
      qmul (GaussianGammaEulerHead.run (translated z B one) B K) (naturalPoint (fact K)) := by
  let t := GaussianBarnesWeightedProductShift.unweighted GaussianBarnesCanonicalPolynomialShift.rowF
  let x := GaussianBarnesCanonicalPolynomialShift.data z B
  have row : Γ ⊢[PRAAx] inst2 t K x ≐ translatedValue z B (succ K) := by
    simpa [t,x,GaussianBarnesWeightedProductShift.unweighted,inst2] using GaussianBarnesCanonicalPolynomialShift.row_at z B K
  have p := (GaussianRationalFiniteProduct.product_succ (Γ := Γ) t K x).eqTrans (qmul_congr (.eqRefl _) row)
  exact p.eqSymm.eqTrans ((GaussianBarnesCanonicalGaussDenominator.original_head z B K hB).eqTrans (qmul_commutative _ _))

private theorem terminal_fact (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (naturalPoint (fact N)) (translatedValue z B (succ (succ N))) ≐
      qmul (base z B (succ N)) (naturalPoint (fact (succ N))) := by
  let w := translated z B one
  let k := succ N
  let a := naturalPoint (fact N)
  let b := naturalPoint k
  let c := base z B k
  have y := GaussianBarnesCanonicalPolynomialShift.row_at (Γ := Γ) z B k
  have r := GaussianBarnesCanonicalPolynomialShift.row_at (Γ := Γ) w B N
  have row := y.eqSymm.eqTrans ((GaussianBarnesCanonicalPolynomialShift.shifted_row_equal z B N hB).eqTrans r)
  have norm := GaussianGammaEulerDenominator.factor_scaled w B N hB
  have factCode := (GaussianGammaEulerDenominator.natural_multiply (Γ := Γ) (fact N) k).eqTrans
    (GaussianGammaEulerDenominator.natural_congr (fact_succ N zero).eqSymm)
  exact (qmul_congr (.eqRefl a) (row.eqTrans norm.eqSymm)).eqTrans
    ((qmul_associative a b c).eqSymm.eqTrans ((qmul_congr factCode (.eqRefl c)).eqTrans (qmul_commutative _ _)))

private theorem right_inverse (j : PTm n) (h : Γ ⊢[PRAAx] le one j) : Γ ⊢[PRAAx]
    qmul (naturalPoint j) (ofGaussian oneCode j) ≐ qone := by
  have raw := qmul_represents (naturalPoint j) (ofGaussian oneCode j)
    (ComplexLogarithmRemainder.scale j oneCode) oneCode one j (le_refl _) h
    (natural_point_represents (Γ := Γ) j) (ofGaussian_represents _ _ h)
  exact canonical_unique _ _ _ j (qmul_canonical _ _) qone_canonical h
    (represents_congr (.eqRefl _) (natural_product_value j oneCode) (by ipra_ring) raw) (qone_represents_scaled j)

private theorem move_last (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h z) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (multiplyF f g) h) (multiplyF (multiplyF f h) g)
      (multiplyData (multiplyF f g) h (multiplyData f g x y) z)
      (multiplyData (multiplyF f h) g (multiplyData f h x z) y) := by
  have mid := multiply_cross f f (multiplyF g h) (multiplyF h g) x x (multiplyData g h y z) (multiplyData h g z y)
    hf hf (multiply_fast _ _ _ _ hg hh) (multiply_fast _ _ _ _ hh hg) (cross_refl _ _ hf)
    (multiply_commutative g h y z hg hh)
  exact cross_trans _ _ _ _ _ _ (multiply_associative f g h x y z hf hg hh)
    (cross_trans _ _ _ _ _ _ mid (cross_symm _ _ _ _ (multiply_associative f h g x z y hf hh hg)))

private theorem collect (f : PR 2) (x a b : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (multiplyF f C) C) (multiplyF f C)
      (multiplyData (multiplyF f C) C (multiplyData f C x a) b) (multiplyData f C x (qmul a b)) := by
  have ha := constant_regular (Γ := Γ) a
  have hb := constant_regular (Γ := Γ) b
  exact cross_trans _ _ _ _ _ _ (multiply_associative f C C x a b hf ha hb)
    (multiply_cross f f (multiplyF C C) C x x (multiplyData C C a b) (qmul a b) hf hf
      (multiply_fast _ _ _ _ ha hb) (constant_regular _) (cross_refl _ _ hf) (constant_product_cross a b))

private theorem cancel_common (f g : PR 2) (x y j : PTm n) (hj : Γ ⊢[PRAAx] le one j)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (e : Γ ⊢[PRAAx] crossEquivalent (multiplyF f C) (multiplyF g C)
      (multiplyData f C x (naturalPoint j)) (multiplyData g C y (naturalPoint j))) : Γ ⊢[PRAAx]
    crossEquivalent f g x y := by
  let a := naturalPoint j
  let b := ofGaussian oneCode j
  let Y := multiplyData g C y a
  have ha := constant_regular (Γ := Γ) a
  have hb := constant_regular (Γ := Γ) b
  have undo := GaussianGammaGaussReflectionCancellation.cancel_right_constant f (multiplyF g C) x Y a b hf
    (multiply_fast _ _ _ _ hg ha) (right_inverse j hj) e
  have oneEq := GaussianGammaReciprocalInverse.constant_inverse a b y (right_inverse j hj)
  have drop := multiply_cross g g (multiplyF C C) oneF y y (multiplyData C C a b) y hg hg
    (multiply_fast _ _ _ _ ha hb) (one_fast y) (cross_refl _ _ hg) oneEq
  exact cross_trans _ _ _ _ _ _ undo (cross_trans _ _ _ _ _ _ (multiply_associative g C C y a b hg ha hb)
    (cross_trans _ _ _ _ _ _ drop (multiply_one g y hg)))

private theorem extend_right (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h z)
    (e : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF f h) (multiplyF g h) (multiplyData f h x z) (multiplyData g h y z) :=
  multiply_cross f g h h x y z z hf hg hh hh e (cross_refl _ _ hh)

private theorem extend_left (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h z)
    (e : Γ ⊢[PRAAx] crossEquivalent g h y z) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF f g) (multiplyF f h) (multiplyData f g x y) (multiplyData f h x z) :=
  multiply_cross f f g h x x y z hf hf hg hh (cross_refl _ _ hf) e

private abbrev liftedLeftF : PR 2 := multiplyF (multiplyF (multiplyF P C) C) gaussF
private abbrev liftedRightF : PR 2 := multiplyF (multiplyF (multiplyF P M) C) gaussF
private def liftedLeftData (z S B K : PTm n) : PTm n := multiplyData (multiplyF (multiplyF P C) C) gaussF
  (multiplyData (multiplyF P C) C (GaussianBarnesCanonicalPrefixShift.leftData z S B K) (translatedValue z B (succ K)))
  (gaussData z B K)
private def liftedRightData (z R B K : PTm n) : PTm n := multiplyData (multiplyF (multiplyF P M) C) gaussF
  (multiplyData (multiplyF P M) C (GaussianBarnesCanonicalPrefixShift.rightData z R B K) (translatedValue z B (succ K)))
  (gaussData z B K)

private theorem gauss_regular (z B K : PTm n) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx] pointCN gaussF (gaussData z B K) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input logExponentF (logExponentData (translated z B one) B K)
    (log_exponent_regular (translated z B one) B K hK))

private theorem normalized_regular (z R B K : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBarnesCanonicalTerminalRemainder.source (translated z B one) R B K) :
    Γ ⊢[PRAAx] pointCN E (ed z R B K) := by
  let X := GaussianBarnesCanonicalNormalizedExponent.nameF
  let F := GaussianBarnesCanonicalPrefixShift.exponentF
  let a := GaussianBarnesCanonicalPrefixShift.exponentData z B K
  let T := GaussianBarnesCanonicalTerminalRemainder.scaledF
  let t := GaussianBarnesCanonicalTerminalRemainder.scaledData (translated z B one) R B K
  let OF := GaussianBarnesCanonicalNormalizedExponent.offsetF
  let o := GaussianBarnesCanonicalNormalizedExponent.offsetData z B K
  let offset := GaussianBarnesCanonicalNormalizedExponent.offset z B K
  let g := GaussianStirlingGammaLogarithm.logGammaData K one
  let hK := h.andE₂.andE₁
  have ha : Γ ⊢[PRAAx] pointCN F a := add_fast _ _ _ _
    (GaussianBarnesCanonicalPrefactorShift.difference_regular z B) (constant_regular _)
  have ht := GaussianBarnesCanonicalTerminalRemainder.scaled_regular (translated z B one) R B K h
  have ho : Γ ⊢[PRAAx] pointCN OF o := multiply_fast C _ offset K (constant_regular offset)
    (GaussianGammaFiniteApproximantName.log_regular K hK)
  have hg := GaussianStirlingGammaLogarithm.log_gamma_regular K one (.andI hK (le_refl one))
  have hx : Γ ⊢[PRAAx] pointCN X (GaussianBarnesCanonicalNormalizedExponent.data z R B K) :=
    GaussianNamedDifference.name_regular (GaussianNameArithmetic.addF (GaussianNameArithmetic.addF F T) OF) _
      (GaussianNameArithmetic.addData (GaussianNameArithmetic.addData a t) o) g (add_fast _ _ _ _ (add_fast _ _ _ _ ha ht) ho) hg
  exact GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ hx)

private theorem align_left (z S B K : PTm n) (hw : Γ ⊢[PRAAx] source (translated z B one) S B)
    (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    crossEquivalent liftedLeftF (multiplyF leftF C) (liftedLeftData z S B K)
      (multiplyData leftF C (leftData z S B K) (naturalPoint (fact K))) := by
  let w := translated z B one
  let y := literalData w S B K
  let a := translatedValue z B (succ K)
  let p := plain z B K
  let g := gaussData z B K
  let f := naturalPoint (fact K)
  let c := GaussianGammaEulerHead.run w B K
  let b := multiplyData C C c f
  let v := multiplyData P C y c
  have hy := GaussianBarnesCanonicalProduct.literal_regular w S B K hw
  have hc := constant_regular (Γ := Γ) c
  have hf := constant_regular (Γ := Γ) f
  have ha := constant_regular (Γ := Γ) a
  have hp := constant_regular (Γ := Γ) p
  have hg := gauss_regular z B K hK
  have hb := multiply_fast C C c f hc hf
  have hv := multiply_fast P C y c hy hc
  have constEq := cross_trans _ _ _ _ _ _ (constant_data_cross _ _ (product_plain z B K hw.andE₁))
    (cross_symm _ _ _ _ (constant_product_cross c f))
  have inner := cross_trans _ _ _ _ _ _ (collect P y p a hy)
    (cross_trans _ _ _ _ _ _ (extend_left P C (multiplyF C C) y (qmul p a) b hy (constant_regular _) hb constEq)
      (cross_symm _ _ _ _ (multiply_associative P C C y c f hy hc hf)))
  have ext := extend_right _ _ gaussF _ _ g (multiply_fast _ _ _ _ (multiply_fast _ _ _ _ hy hp) ha)
    (multiply_fast _ _ _ _ hv hf) hg inner
  have move := move_last (multiplyF P C) C gaussF v f g hv hf hg
  have fold := extend_right _ _ C _ _ f (multiply_fast _ _ _ _ hv hg)
    (multiply_fast _ _ _ _ hy (multiply_fast _ _ _ _ hc hg)) hf (multiply_associative P C gaussF y c g hy hc hg)
  exact cross_trans _ _ _ _ _ _ ext (cross_trans _ _ _ _ _ _ move fold)

private theorem align_right (z R S B N : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalTerminalRemainder.source (translated z B one) S B (succ N))
    (hm : Γ ⊢[PRAAx] pointCN M (md z B (succ N))) : Γ ⊢[PRAAx]
    crossEquivalent liftedRightF (multiplyF rightF C) (liftedRightData z R B (succ N))
      (multiplyData rightF C (rightData z R S B (succ N)) (naturalPoint (fact (succ N)))) := by
  let K := succ N
  let x := literalData z R B K
  let m := md z B K
  let a := translatedValue z B (succ K)
  let g := gaussData z B K
  let e := ed z S B K
  let i := naturalPoint (fact N)
  let j := naturalPoint (fact K)
  let c := base z B K
  let t := multiplyData M gaussF m g
  let t' := multiplyData E C e i
  let y := multiplyData P E x e
  let b := multiplyData C C c j
  have hx := GaussianBarnesCanonicalProduct.literal_regular z R B K hz
  have ha := constant_regular (Γ := Γ) a
  have hi := constant_regular (Γ := Γ) i
  have hj := constant_regular (Γ := Γ) j
  have hc := constant_regular (Γ := Γ) c
  have hg := gauss_regular z B K hs.andE₂.andE₁
  have he := normalized_regular z S B K hs
  have ht := multiply_fast M gaussF m g hm hg
  have ht' := multiply_fast E C e i he hi
  have hy := multiply_fast P E x e hx he
  have hb := multiply_fast C C c j hc hj
  have move := move_last (multiplyF P M) C gaussF (multiplyData P M x m) a g (multiply_fast _ _ _ _ hx hm) ha hg
  have left := multiply_associative P M gaussF x m g hx hm hg
  have bind := extend_left P (multiplyF M gaussF) (multiplyF E C) x t t' hx ht ht'
    (GaussianBarnesCanonicalNormalizedMultiplier.multiplier_cross z S B N hs)
  have right := cross_symm _ _ _ _ (multiply_associative P E C x e i hx he hi)
  have inside := cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ bind right)
  have rearrange := extend_right _ _ C _ _ a
    (multiply_fast _ _ _ _ (multiply_fast _ _ _ _ hx hm) hg) (multiply_fast _ _ _ _ hy hi) ha inside
  have constEq := cross_trans _ _ _ _ _ _ (constant_data_cross _ _ (terminal_fact z B N hz.andE₁))
    (cross_symm _ _ _ _ (constant_product_cross c j))
  have last := extend_left (multiplyF P E) C (multiplyF C C) y (qmul i a) b hy (constant_regular _) hb constEq
  exact cross_trans _ _ _ _ _ _ move (cross_trans _ _ _ _ _ _ rearrange
    (cross_trans _ _ _ _ _ _ (collect (multiplyF P E) y i a hy)
      (cross_trans _ _ _ _ _ _ last (cross_symm _ _ _ _ (multiply_associative (multiplyF P E) C C y c j hy hc hj)))))

theorem original_finite_recurrence (z R S B N : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (translated z B one) S B) (hN : Γ ⊢[PRAAx] le (two*S) (succ N)) : Γ ⊢[PRAAx]
    crossEquivalent leftF rightF (leftData z S B (succ N)) (rightData z R S B (succ N)) := by
  let K := succ N
  let t := translatedValue z B (succ K)
  let w := translated z B one
  let g := gaussData z B K
  let a := GaussianBarnesCanonicalPrefixShift.leftData z S B K
  let b := GaussianBarnesCanonicalPrefixShift.rightData z R B K
  let x := literalData z R B K
  let y := literalData w S B K
  let m := md z B K
  let F := multiplyF P C
  let G := multiplyF P M
  have hK := zero_lt_succ (Γ := Γ) N
  have hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalTerminalRemainder.source w S B K := .andI hw.andE₁ (.andI hK (.andI hw.andE₂ hN))
  have hm : Γ ⊢[PRAAx] pointCN M m := multiply_fast _ _ _ _ (constant_regular _)
    (GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _
      (GaussianNameArithmetic.add_fast _ _ _ _ (GaussianBarnesCanonicalPrefactorShift.difference_regular z B) (constant_regular _))))
  have ht := constant_regular (Γ := Γ) t
  have ha : Γ ⊢[PRAAx] pointCN F a := multiply_fast _ _ _ _ (GaussianBarnesCanonicalProduct.literal_regular w S B K hw) (constant_regular _)
  have hb : Γ ⊢[PRAAx] pointCN G b := multiply_fast _ _ _ _ (GaussianBarnesCanonicalProduct.literal_regular z R B K hz) hm
  have e := extend_right F G C a b t ha hb ht (GaussianBarnesCanonicalPrefixShift.prefix_shift z R S B K hz hw)
  have finite := extend_right _ _ gaussF _ _ g (multiply_fast _ _ _ _ ha ht) (multiply_fast _ _ _ _ hb ht)
    (gauss_regular z B K hK) e
  have eq := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (align_left z S B K hw hK))
    (cross_trans _ _ _ _ _ _ finite (align_right z R S B N hz hs hm))
  refine cancel_common leftF rightF (leftData z S B K) (rightData z R S B K) (fact K) (GammaEulerMesh.factorial_positive K) ?_ ?_ eq
  · exact multiply_fast _ _ _ _ (GaussianBarnesCanonicalProduct.literal_regular w S B K hw) (q_regular w B K hK)
  · exact multiply_fast _ _ _ _ (multiply_fast _ _ _ _ (GaussianBarnesCanonicalProduct.literal_regular z R B K hz)
      (normalized_regular z S B K hs)) (constant_regular _)

theorem actual_Barnes_finite_Gauss_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let R := var 1
     let S := var 2
     let B := var 3
     let N := var 4
     source z R B ⟶ source (translated z B one) S B ⟶ le (two*S) (succ N) ⟶
       crossEquivalent leftF rightF (leftData z S B (succ N)) (rightData z R S B (succ N))) :=
  closeUniv 5 (.impI (.impI (.impI (original_finite_recurrence _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteGaussIdentity
