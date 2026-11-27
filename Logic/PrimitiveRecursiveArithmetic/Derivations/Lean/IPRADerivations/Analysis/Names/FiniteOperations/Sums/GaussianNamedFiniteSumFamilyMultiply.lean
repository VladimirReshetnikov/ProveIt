import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedFiniteSumFamilyAdd
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient

/-!
# Factoring a common multiplier from a finite sum of Gaussian names

The number of summands is an internal term. The proof uses exact rational
finite-sum distributivity and controls the actual read clocks of both names.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteSumFamilyMultiply

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent exponent_unit query_budget)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiplyModulus)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianNamedFiniteProductFamily (regularRows regular_at radius family_radius_at)
open GaussianNamedFiniteSumFamily (body data finite nameF term_at sample_at regular)
open GaussianNameRingLaws (multiply_sample_error equivalent_of_envelope)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same distance_radius_mono_same)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum_multiply)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def mixedBody (f g : PR 2) (t : PTm 2) (u : PTm 1) : PTm 2 :=
  multiplyData f g t (inst1 u (var 1))

@[simp] theorem inst2_mixedBody (f g : PR 2) (t : PTm 2) (u : PTm 1) (i x : PTm n) :
    inst2 (mixedBody f g t u) i x = multiplyData f g (inst2 t i x) (inst1 u x) := by
  simp only [mixedBody,inst2,GaussianNameArithmetic.subst_multiplyData]
  congr 1
  simp only [inst1,Syn.subst_subst]
  congr 1
  funext j
  fin_cases j
  rfl

@[simp] theorem subst_inst1 {m : ℕ} (σ : Fin n → PTm m) (u : PTm 1) (x : PTm n) :
    Syn.subst σ (inst1 u x) = inst1 u (Syn.subst σ x) := by
  simp only [inst1,Syn.subst_subst]
  congr 1
  funext j
  fin_cases j
  rfl

theorem mixed_regular (f g : PR 2) (t : PTm 2) (u : PTm 1) (N x : PTm n)
    (hf : Γ ⊢[PRAAx] regularRows f t N x) (hg : Γ ⊢[PRAAx] pointCN g (inst1 u x)) :
    Γ ⊢[PRAAx] regularRows (multiplyF f g) (mixedBody f g t u) N x := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  let X := Syn.shift x
  have hf' : Δ ⊢[PRAAx] regularRows f t (Syn.shift N) X := by
    simpa only [Fm.shift,GaussianNamedFiniteProductFamily.subst_regularRows,Syn.shift,Δ,X] using hf.shift.wk
  have hg' : Δ ⊢[PRAAx] pointCN g (inst1 u X) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,subst_inst1,Syn.shift,Δ,X] using hg.shift.wk
  rw [inst2_mixedBody]
  exact multiply_fast _ _ _ _ (regular_at f t _ _ (var 0) hf' Prf.hyp0) hg'

def rowCost (f g : PR 2) (t : PTm 2) (u : PTm 1) (N x : PTm n) : PTm n :=
  (radius f t N x+U g (inst1 u x))+one

theorem finite_multiply_distance (f g : PR 2) (t : PTm 2) (u : PTm 1) (k N x : PTm n)
    (hf : Γ ⊢[PRAAx] regularRows f t N x) (hg : Γ ⊢[PRAAx] pointCN g (inst1 u x)) :
    Γ ⊢[PRAAx] distanceBounded (finite (multiplyF f g) (mixedBody f g t u) k N x)
      (qmul (finite f t k N x) (ap2 g k (inst1 u x))) (N*rowCost f g t u N x) (unit k) := by
  let F := body (multiplyF f g) (mixedBody f g t u)
  let G := multiplyBody (body f t)
  let y := pairT k x
  let c := ap2 g k (inst1 u x)
  have rows : Γ ⊢[PRAAx] termsDistance F G N y (pairT c y) (rowCost f g t u N x) (unit k) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    let X := Syn.shift x
    let p := Syn.shift k
    let i : PTm (n+1) := var 0
    have hf' : Δ ⊢[PRAAx] regularRows f t (Syn.shift N) X := by
      simpa only [Fm.shift,GaussianNamedFiniteProductFamily.subst_regularRows,Syn.shift,Δ,X] using hf.shift.wk
    have hg' : Δ ⊢[PRAAx] pointCN g (inst1 u X) := by
      simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,subst_inst1,Syn.shift,Δ,X] using hg.shift.wk
    have rowR := family_radius_at (Γ := Δ) f t (Syn.shift N) X i Prf.hyp0
    have e := multiply_sample_error f g (inst2 t i X) (inst1 u X) p
      (regular_at f t _ _ i hf' Prf.hyp0) hg'
    have readL := term_at (Γ := Δ) (multiplyF f g) (mixedBody f g t u) i p X
    rw [inst2_mixedBody] at readL
    have readR : Δ ⊢[PRAAx] inst2 G i (pairT (ap2 g p (inst1 u X)) (pairT p X)) ≐
        qmul (ap2 f p (inst2 t i X)) (ap2 g p (inst1 u X)) :=
      (multiply_body_at (body f t) _ i _).eqTrans
        ((qmul_congr (.eqRefl _) (term_at f t i p X)).eqTrans (qmul_commutative _ _))
    have widen := distance_radius_mono_same (unit_positive p) (add_le_add_right one (add_le_add_right (U g (inst1 u X)) rowR)) e
    change Δ ⊢[PRAAx] distanceBounded (inst2 F i (Syn.shift y)) (inst2 G i (Syn.shift (pairT c y)))
      (Syn.shift (rowCost f g t u N x)) (Syn.shift (unit k))
    simpa only [y,c,p,X,Syn.shift,subst_pairT,subst_ap2,subst_inst1,rowCost,PTm.subst_add,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,one,
      GaussianNamedFiniteProductFamily.subst_radius,GaussianNameBounds.subst_U,GaussianCoefficientNameBounds.subst_unit]
      using distance_congr readL.eqSymm readR.eqSymm (.eqRefl _) (.eqRefl _) widen
  exact distance_congr (.eqRefl _) ((sum_multiply (body f t) c N y).eqTrans (qmul_commutative _ _))
    (.eqRefl _) (.eqRefl _) (sum_distance F G N y (pairT c y) _ (unit k) (unit_positive k) rows)

def cost (f g : PR 2) (t : PTm 2) (u : PTm 1) (N x : PTm n) : PTm n :=
  let F := nameF f t
  let y := data N x
  (rowCost f g t u N x+U F y*two)+(multiplyModulus F g y (inst1 u x)+one)

theorem original_multiply_distance (f g : PR 2) (t : PTm 2) (u : PTm 1) (p N x : PTm n)
    (hf : Γ ⊢[PRAAx] regularRows f t N x) (hg : Γ ⊢[PRAAx] pointCN g (inst1 u x)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF (multiplyF f g) (mixedBody f g t u)) p (data N x))
      (ap2 (multiplyF (nameF f t) g) p (multiplyData (nameF f t) g (data N x) (inst1 u x)))
      (cost f g t u N x) (unit p) := by
  let k := exponent N p
  let F := nameF f t
  let y := data N x
  let b := inst1 u x
  let hF := regular f t N x hf
  have hk := unit_positive (Γ := Γ) k
  have hp := unit_positive (Γ := Γ) p
  have hb := query_budget (Γ := Γ) N p
  have hle : Γ ⊢[PRAAx] le (unit p) (unit k) :=
    le_congr (.eqRefl _) (exponent_unit N p).eqSymm
      (le_congr (one_mul (unit p)) (mul_comm _ _) (mul_le_mul_right (unit p) (unit_positive (GaussianFastValueCut.normalizer N))))
  have h1 := distance_radius_mono _ _ _ _ (rowCost f g t u N x) (unit p) hk hp
    (by ipra_le 𝔞(rowCost f g t u N x)*sl hb)
    (finite_multiply_distance f g t u k N x hf hg)
  have read := distance_congr (sample_at (multiplyF f g) (mixedBody f g t u) p N x).eqSymm
    (qmul_congr (sample_at f t p N x).eqSymm (.eqRefl _)) (.eqRefl _) (.eqRefl _) h1
  have close := point_at g b k p hg
  have close' := distance_radius_mono _ _ _ _ two (unit p)
    (GaussianRationalHorner.positive_product _ _ hk hp) hp
    (by ipra_le 𝔞(unit p)*sl hle) close
  let a := ap2 F p y
  have shiftProduct := GaussianNamedDifferenceQuotient.scale_distance a (ap2 g k b) (ap2 g p b)
    (U F y) two (unit p) hp (sample_bound F y p hF) close'
  have final := multiply_sample_error F g y b p hF hg
  exact distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp read shiftProduct)
    (distance_symmetric _ _ _ _ hp final)

theorem family_multiply_cross (f g : PR 2) (t : PTm 2) (u : PTm 1) (N x : PTm n)
    (hf : Γ ⊢[PRAAx] regularRows f t N x) (hg : Γ ⊢[PRAAx] pointCN g (inst1 u x)) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (multiplyF f g) (mixedBody f g t u)) (multiplyF (nameF f t) g)
      (data N x) (multiplyData (nameF f t) g (data N x) (inst1 u x)) := by
  refine equivalent_of_envelope _ _ _ _ (cost f g t u N x) ?_ ?_ (.allI ?_)
  · exact regular (multiplyF f g) (mixedBody f g t u) N x (mixed_regular f g t u N x hf hg)
  · exact multiply_fast _ _ _ _ (regular f t N x hf) hg
  · have hf' : Γ.map Fm.shift ⊢[PRAAx] regularRows f t (Syn.shift N) (Syn.shift x) := by
      simpa only [Fm.shift,GaussianNamedFiniteProductFamily.subst_regularRows,Syn.shift] using hf.shift
    have hg' : Γ.map Fm.shift ⊢[PRAAx] pointCN g (inst1 u (Syn.shift x)) := by
      simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,subst_inst1,Syn.shift] using hg.shift
    simpa only [Syn.shift,GaussianNamedFiniteSumFamily.subst_data,GaussianNameArithmetic.subst_multiplyData,
      subst_inst1,cost,rowCost,multiplyModulus,PTm.subst_add,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,one,
      GaussianNamedFiniteProductFamily.subst_radius,GaussianNameBounds.subst_U,LeanProofs.IPRA.PTm.subst_num,two]
      using original_multiply_distance f g t u (var 0) (Syn.shift N) (Syn.shift x) hf' hg'

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteSumFamilyMultiply
