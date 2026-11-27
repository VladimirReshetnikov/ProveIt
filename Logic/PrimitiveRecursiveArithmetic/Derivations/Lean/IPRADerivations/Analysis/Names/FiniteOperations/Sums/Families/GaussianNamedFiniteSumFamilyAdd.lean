import IPRADerivations.Analysis.Names.FiniteOperations.Sums.Families.GaussianNamedFiniteSumFamily
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws

/-!
# Addition within a finite family of Gaussian names

At a common internal row clock, the actual name addition in each row
has a fixed finite readback error. The original finite sums absorb the
number of rows. The remaining diagonal error yields exact equivalence
to the actual addition of the two sums.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteSumFamilyAdd

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent query_budget)
open GaussianNamedFiniteProductFamily (regularRows regular_at)
open GaussianNamedFiniteSumFamily (body data finite nameF term_at sample_at regular)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (add_sample_error equivalent_of_envelope three)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def mixedBody (t u : PTm 2) : PTm 2 := addData t u

@[simp] theorem inst2_mixedBody (t u : PTm 2) (i x : PTm n) :
    inst2 (mixedBody t u) i x = addData (inst2 t i x) (inst2 u i x) := by simp [mixedBody,inst2]

theorem mixed_regular (f g : PR 2) (t u : PTm 2) (N x : PTm n)
    (hf : Γ ⊢[PRAAx] regularRows f t N x) (hg : Γ ⊢[PRAAx] regularRows g u N x) :
    Γ ⊢[PRAAx] regularRows (addF f g) (mixedBody t u) N x := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  let X := Syn.shift x
  have hf' : Δ ⊢[PRAAx] regularRows f t (Syn.shift N) X := by simpa [Fm.shift,Syn.shift,Δ,X] using hf.shift.wk
  have hg' : Δ ⊢[PRAAx] regularRows g u (Syn.shift N) X := by simpa [Fm.shift,Syn.shift,Δ,X] using hg.shift.wk
  rw [inst2_mixedBody]
  exact add_fast _ _ _ _ (regular_at f t _ _ (var 0) hf' Prf.hyp0) (regular_at g u _ _ (var 0) hg' Prf.hyp0)

theorem finite_add_distance (f g : PR 2) (t u : PTm 2) (k N x : PTm n)
    (hf : Γ ⊢[PRAAx] regularRows f t N x) (hg : Γ ⊢[PRAAx] regularRows g u N x) :
    Γ ⊢[PRAAx] distanceBounded (finite (addF f g) (mixedBody t u) k N x)
      (qadd (finite f t k N x) (finite g u k N x)) (N*three) (unit k) := by
  let F := body (addF f g) (mixedBody t u)
  let G := GaussianRationalFiniteSum.addBody (body f t) (body g u)
  let y := pairT k x
  have rows : Γ ⊢[PRAAx] termsDistance F G N y y three (unit k) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    let X := Syn.shift x
    let p := Syn.shift k
    let i : PTm (n+1) := var 0
    have hf' : Δ ⊢[PRAAx] regularRows f t (Syn.shift N) X := by simpa [Fm.shift,Syn.shift,Δ,X] using hf.shift.wk
    have hg' : Δ ⊢[PRAAx] regularRows g u (Syn.shift N) X := by simpa [Fm.shift,Syn.shift,Δ,X] using hg.shift.wk
    have hF := regular_at f t _ _ i hf' Prf.hyp0
    have hG := regular_at g u _ _ i hg' Prf.hyp0
    have e := add_sample_error f g (inst2 t i X) (inst2 u i X) p hF hG
    have readL := term_at (Γ := Δ) (addF f g) (mixedBody t u) i p X
    rw [inst2_mixedBody] at readL
    have readR : Δ ⊢[PRAAx] inst2 G i (pairT p X) ≐ qadd (ap2 f p (inst2 t i X)) (ap2 g p (inst2 u i X)) := by
      rw [show G = GaussianRationalFiniteSum.addBody (body f t) (body g u) from rfl,
        GaussianRationalFiniteSum.inst2_addBody]
      exact qadd_congr (term_at f t i p X) (term_at g u i p X)
    change Δ ⊢[PRAAx] distanceBounded (inst2 F i (Syn.shift y)) (inst2 G i (Syn.shift y))
      (Syn.shift (three : PTm n)) (Syn.shift (unit k))
    simpa only [y,p,X,Syn.shift,subst_pairT,GaussianCoefficientNameBounds.subst_unit,three,PTm.subst_add,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      distance_congr readL.eqSymm readR.eqSymm (.eqRefl _) (.eqRefl _) e
  exact distance_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_add (body f t) (body g u) N y)
    (.eqRefl _) (.eqRefl _) (sum_distance F G N y y three (unit k) (unit_positive k) rows)

theorem original_add_distance (f g : PR 2) (t u : PTm 2) (p N x : PTm n)
    (hf : Γ ⊢[PRAAx] regularRows f t N x) (hg : Γ ⊢[PRAAx] regularRows g u N x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF (addF f g) (mixedBody t u)) p (data N x))
      (ap2 (addF (nameF f t) (nameF g u)) p (addData (data N x) (data N x))) (num 6) (unit p) := by
  let k := exponent N p
  have hk := unit_positive (Γ := Γ) k
  have hp := unit_positive (Γ := Γ) p
  have rate : Γ ⊢[PRAAx] le ((N*three)*unit p) (three*unit k) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right three (query_budget N p))
  have e := distance_radius_mono _ _ _ _ three (unit p) hk hp rate (finite_add_distance f g t u k N x hf hg)
  have readback := distance_congr (sample_at (addF f g) (mixedBody t u) p N x).eqSymm
    (qadd_congr (sample_at f t p N x).eqSymm (sample_at g u p N x).eqSymm) (.eqRefl _) (.eqRefl _) e
  have addError := add_sample_error (nameF f t) (nameF g u) (data N x) (data N x) p (regular f t N x hf) (regular g u N x hg)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp readback (distance_symmetric _ _ _ _ hp addError))

theorem family_add_cross (f g : PR 2) (t u : PTm 2) (N x : PTm n)
    (hf : Γ ⊢[PRAAx] regularRows f t N x) (hg : Γ ⊢[PRAAx] regularRows g u N x) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (addF f g) (mixedBody t u)) (addF (nameF f t) (nameF g u))
      (data N x) (addData (data N x) (data N x)) := by
  refine equivalent_of_envelope _ _ _ _ (num 6) ?_ ?_ (.allI ?_)
  · exact regular (addF f g) (mixedBody t u) N x (mixed_regular f g t u N x hf hg)
  · exact add_fast _ _ _ _ (regular f t N x hf) (regular g u N x hg)
  · have hf' : Γ.map Fm.shift ⊢[PRAAx] regularRows f t (Syn.shift N) (Syn.shift x) := by
      simpa [Fm.shift,Syn.shift] using hf.shift
    have hg' : Γ.map Fm.shift ⊢[PRAAx] regularRows g u (Syn.shift N) (Syn.shift x) := by
      simpa [Fm.shift,Syn.shift] using hg.shift
    simpa only [Syn.shift,GaussianNamedFiniteSumFamily.subst_data,GaussianNameArithmetic.subst_addData,PTm.subst_num]
      using original_add_distance f g t u (var 0) (Syn.shift N) (Syn.shift x) hf' hg'

theorem actual_named_finite_family_add_closed (f g : PR 2) (t u : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((regularRows f t (var 0) (var 1) ⋏ regularRows g u (var 0) (var 1)) ⟶
        crossEquivalent (nameF (addF f g) (mixedBody t u)) (addF (nameF f t) (nameF g u))
          (data (var 0) (var 1)) (addData (data (var 0) (var 1)) (data (var 0) (var 1)))) :=
  closeUniv 2 (.impI (family_add_cross f g t u _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteSumFamilyAdd
