import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialReference

/-!
# Addition for independently sampled Gaussian exponential names

A common later input query and one computed rectangular cutoff compare
the actual multiplication of the two exponential names with the actual
exponential of their sum. The original multiplication clock absorbs the
product errors, and the finite product tail supplies the remaining
comparison. Regularity upgrades the diagonal comparison to independent
output precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianExponentialAddition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd qmul canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPolynomialExponential (scalarSum)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRadiusExponentialName (input nameF inputPrecision index sample bounded_samples_at)
open GaussianExponentialReference (finite_reference dyadic_weaken index_below_rectangle recode_fixed add_input add_sample)
open GaussianScalarExponentialProductTail (rectangleCutoff actual_scalar_product_dyadic)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (diagonalEquivalent crossEquivalent)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def productF (f g : PR 2) : PR 2 := GaussianNameArithmetic.multiplyF (nameF f) (nameF g)
def productData (f g : PR 2) (R x y : PTm n) : PTm n :=
  GaussianNameArithmetic.multiplyData (nameF f) (nameF g)
    (GaussianRadiusExponentialName.data R x) (GaussianRadiusExponentialName.data R y)
def sumF (f g : PR 2) : PR 2 := nameF (GaussianNameArithmetic.addF f g)
def sumData (R x y : PTm n) : PTm n :=
  GaussianRadiusExponentialName.data (R+R) (GaussianNameArithmetic.addData x y)

@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2) (R x y : PTm n) :
    Syn.subst σ (productData f g R x y) = productData f g (Syn.subst σ R) (Syn.subst σ x) (Syn.subst σ y) := by
  simp [productData]

@[simp] theorem subst_sumData {m : ℕ} (σ : Fin n → PTm m) (R x y : PTm n) :
    Syn.subst σ (sumData R x y) = sumData (Syn.subst σ R) (Syn.subst σ x) (Syn.subst σ y) := by
  simp [sumData]

/-- Use the full factor four in the existing multiplication normalization. -/
theorem product_precision_budget (L p : PTm n) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] le ((L+one)*unit (succ p)) (unit (GaussianFastValueCut.exponent L p)) := by
  let a := GaussianRootSchedule.binaryLength L
  have hlen : Γ ⊢[PRAAx] le L (unit a) := (GaussianRootSchedule.binary_length_correct L).andE₁
  have htwo : Γ ⊢[PRAAx] unit two ≐ two*two :=
    (pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _))
  have e : Γ ⊢[PRAAx] unit (GaussianFastValueCut.exponent L p) ≐
      unit p*(unit a*(two*two)) :=
    (GaussianFastValueCut.exponent_unit L p).eqTrans
      (congrMul (.eqRefl _) ((pw_add two a two).eqTrans (congrMul (.eqRefl _) htwo)))
  have step := natEq (pw_succ (Γ := Γ) two p)
  apply le_congr (.eqRefl _) e.eqSymm
  ipra_le 4*𝔟 (unit p)*sl hlen+2*𝔟 (unit p)*sl hL using
    unfold unit
    rw [step]
    ring

theorem unit_near_bound (q r A p : PTm n) (hc : Γ ⊢[PRAAx] canonical q)
    (hr : Γ ⊢[PRAAx] bounded r A one) (h : Γ ⊢[PRAAx] distanceBounded q r one (unit p)) :
    Γ ⊢[PRAAx] bounded q (A+one) one := by
  have d := distance_radius_mono _ _ _ _ _ _ (unit_positive p) (le_refl one)
    (le_congr (by ipra_ring) (one_mul _).eqSymm (unit_positive p)) h
  have sum := GaussianRationalReciprocal.bounded_sum r (GaussianRationalMetric.qsub q r)
    A one one one (le_refl _) (le_refl _) hr d
  exact bound_congr (GaussianRationalLinearProduct.add_sub_right r q hc) (by ipra_ring) (one_mul _) sum

theorem same_precision (f g : PR 2) (R x y p : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (productF f g) p (productData f g R x y))
      (ap2 (sumF f g) p (sumData R x y)) two (unit p) := by
  let F := nameF f
  let G := nameF g
  let X := GaussianRadiusExponentialName.data R x
  let Y := GaussianRadiusExponentialName.data R y
  let W := GaussianNameArithmetic.addF f g
  let Z := GaussianNameArithmetic.addData x y
  let L := GaussianNameArithmetic.multiplyModulus F G X Y
  let s := GaussianFastValueCut.exponent L p
  let T := succ (p+s)
  let K := rectangleCutoff R T
  let j := inputPrecision R s+inputPrecision (R+R) p
  let i := GaussianFastValueCut.exponent two j
  let u := ap2 f i x
  let v := ap2 g i y
  let A := scalarSum u K
  let B := scalarSum v K
  let a := sample f R s x
  let b := sample g R s y
  let U := GaussianNameBounds.U F X
  let V := GaussianNameBounds.U G Y
  have hp : Γ ⊢[PRAAx] le (succ p) T := by
    change Γ ⊢[PRAAx] le (succ p) (succ (p+s))
    exact le_congr (.eqRefl _) (succ_add p s) (le_add_right _ _)
  have hp' := le_trans (le_succ_self p) hp
  have hs : Γ ⊢[PRAAx] le s T := by
    change Γ ⊢[PRAAx] le s (succ (p+s))
    apply le_trans ?_ (le_succ_self (p+s))
    ipra_le 𝔟 p
  have hR2 : Γ ⊢[PRAAx] le R (R+R) := le_add_right _ _
  have hK := index_below_rectangle R R s T hR2 hs
  have hKsum := index_below_rectangle R (R+R) p T (le_refl _) hp'
  have hi : Γ ⊢[PRAAx] le (inputPrecision R s) i :=
    le_trans (le_add_right (inputPrecision R s) (inputPrecision (R+R) p))
      (le_add_right _ _)
  have hj : Γ ⊢[PRAAx] le (inputPrecision (R+R) p) j := by
    change Γ ⊢[PRAAx] le (inputPrecision (R+R) p) (inputPrecision R s+inputPrecision (R+R) p)
    ipra_le 𝔟 (inputPrecision R s)
  have hu := bounded_samples_at f R x i hf.andE₂
  have hv := bounded_samples_at g R y i hg.andE₂
  have da := finite_reference f R x s i K hf hi hK
  have db := finite_reference g R y s i K hg hi hK
  have fa := GaussianRadiusExponentialName.name_regular f R x hf
  have gb := GaussianRadiusExponentialName.name_regular g R y hg
  have ha : Γ ⊢[PRAAx] bounded a U one := GaussianNameBounds.sample_bound F X s fa
  have hb : Γ ⊢[PRAAx] bounded b V one := GaussianNameBounds.sample_bound G Y s gb
  have hB : Γ ⊢[PRAAx] bounded B (V+one) one :=
    unit_near_bound B b V s (GaussianRationalFiniteSum.sum_canonical _ _ _) hb db
  have error := GaussianNameArithmetic.product_distance A a B b one one (unit s) (V+one) U
    (unit_positive s) da db hB ha
  have positive : Γ ⊢[PRAAx] le one L := le_trans (GaussianNameBounds.U_positive F X) (le_add_right _ _)
  have magnitude : Γ ⊢[PRAAx] distanceBounded (qmul A B) (qmul a b) (L+one) (unit s) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by dsimp [L,U,V,GaussianNameArithmetic.multiplyModulus]; ipra_ring)
      (.eqRefl _) error
  have closer := distance_radius_mono _ _ _ _ _ _ (unit_positive s) (unit_positive (succ p))
    (le_congr (.eqRefl _) (one_mul _).eqSymm (product_precision_budget L p positive)) magnitude
  have oldProduct : Γ ⊢[PRAAx] ap2 (productF f g) p (productData f g R x y) ≐ qmul a b :=
    (GaussianNameArithmetic.multiply_at F G X Y p).eqTrans (recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _))
  have first := distance_symmetric _ _ _ _ (unit_positive (succ p))
    (distance_congr (.eqRefl _) oldProduct.eqSymm (.eqRefl _) (.eqRefl _) closer)
  have middle := dyadic_weaken _ _ _ (succ p) T hp (actual_scalar_product_dyadic u v R T hR hu hv)
  have close := distance_triangle_same _ _ _ _ _ _ (unit_positive (succ p)) first middle
  have twounit : Γ ⊢[PRAAx] le ((one+one)*unit p) (one*unit (succ p)) := by
    have e := natEq (pw_succ (Γ := Γ) two p)
    apply le_of_eq_add (d := LeanProofs.ConciseIPRA.PTm.zero)
    apply deriveNat
    unfold unit
    ipra_simps
    rw [e]
    ring
  have fm := distance_radius_mono _ _ _ _ _ _ (unit_positive (succ p)) (unit_positive p) twounit close
  have raw := finite_reference W (R+R) Z p j K (add_input f g R x y hf hg) hj hKsum
  have exactSum : Γ ⊢[PRAAx] scalarSum (ap2 W j Z) K ≐ scalarSum (qadd u v) K :=
    GaussianRationalFiniteSum.sum_index_congr _ (.eqRefl _) (add_sample f g x y j)
  have last : Γ ⊢[PRAAx] distanceBounded (scalarSum (qadd u v) K)
      (ap2 (sumF f g) p (sumData R x y)) one (unit p) :=
    distance_congr exactSum (.eqRefl _) (.eqRefl _) (.eqRefl _) raw
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) fm last)

theorem exponential_add_diagonal (f g : PR 2) (R x y : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y) :
    Γ ⊢[PRAAx] diagonalEquivalent (productF f g) (sumF f g) (productData f g R x y) (sumData R x y) := by
  have hR' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hR.shift
  have hf' : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRadiusExponentialName.subst_input,Syn.shift] using hf.shift
  have hg' : Γ.map Fm.shift ⊢[PRAAx] input g (Syn.shift R) (Syn.shift y) := by
    simpa only [Fm.shift,GaussianRadiusExponentialName.subst_input,Syn.shift] using hg.shift
  refine .allI ?_
  simpa only [diagonalEquivalent,Syn.shift,subst_productData,subst_sumData,GaussianEuclideanPointDistance.unit,unit] using
    same_precision f g (Syn.shift R) (Syn.shift x) (Syn.shift y) (var 0) hR' hf' hg'

theorem exponential_add_cross (f g : PR 2) (R x y : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y) :
    Γ ⊢[PRAAx] crossEquivalent (productF f g) (sumF f g) (productData f g R x y) (sumData R x y) :=
  GaussianNameEquivalence.diagonal_to_cross _ _ _ _
    (GaussianNameArithmetic.multiply_fast _ _ _ _ (GaussianRadiusExponentialName.name_regular f R x hf)
      (GaussianRadiusExponentialName.name_regular g R y hg))
    (GaussianRadiusExponentialName.name_regular (GaussianNameArithmetic.addF f g) (R+R)
      (GaussianNameArithmetic.addData x y) (add_input f g R x y hf hg))
    (exponential_add_diagonal f g R x y hR hf hg)

theorem original_named_exponential_addition_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ input f (var 0) (var 1) ⟶ input g (var 0) (var 2) ⟶
      crossEquivalent (productF f g) (sumF f g) (productData f g (var 0) (var 1) (var 2))
        (sumData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (exponential_add_cross f g _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianExponentialAddition
