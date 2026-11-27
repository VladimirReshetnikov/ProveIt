import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.Covers.GaussianSuperellipticCoverMembership
import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.Covers.GaussianSuperellipticCoverPoints

/-!
# The finite covering consequence of the superelliptic norm bound

Every first-cover group consists of original distinct curve points
whose original monomial evaluation vectors lie in the selected proper
row span. The exact norm bound limits each actual group to the weight
cutoff. The cardinal sum gives the bound for the entire supplied list.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSuperellipticCoverBound

open_ipra
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.FiniteCoverAssignment (groupBounds groupSize group_length cover_count)
open GaussianRationalOriginalSpanRank (proper_subspace_bound)
open GaussianSuperellipticSubspaceWitness (curveInput points)
open GaussianSuperellipticCoverMembership
  (data testBody family covered matrix rows group family_at generic_cover pointMembership_groups)
open GaussianSuperellipticCoverPoints (group_points)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem group_bound (f m c L P D g : PTm n)
    (hCurve : Γ ⊢[PRAAx] curveInput f m c) (hPoints : Γ ⊢[PRAAx] points f m P)
    (hFamily : Γ ⊢[PRAAx] family f m c L D) (hCovered : Γ ⊢[PRAAx] covered f m c L P D)
    (hg : Γ ⊢[PRAAx] lt g (length D)) :
    Γ ⊢[PRAAx] le (length (group f m c L P D g)) L := by
  have hSpan := family_at f m c L D g hFamily hg
  exact proper_subspace_bound f m c L (group f m c L P D g) (matrix D g) (rows D g) hCurve
    (.andE₁ hSpan) (.andE₂ hSpan)
    (group_points testBody f m P (length D) (data f m c L D) g hPoints)
    (pointMembership_groups f m c L P D g hFamily hCovered)

theorem group_bounds (f m c L P D : PTm n)
    (hCurve : Γ ⊢[PRAAx] curveInput f m c) (hPoints : Γ ⊢[PRAAx] points f m P)
    (hFamily : Γ ⊢[PRAAx] family f m c L D) (hCovered : Γ ⊢[PRAAx] covered f m c L P D) :
    Γ ⊢[PRAAx] groupBounds testBody P (length D) (data f m c L D) L := by
  have hCs : Γ.map Fm.shift ⊢[PRAAx] curveInput (Syn.shift f) (Syn.shift m) (Syn.shift c) := by
    simpa [Fm.shift, Syn.shift] using hCurve.shift
  have hPs : Γ.map Fm.shift ⊢[PRAAx] points (Syn.shift f) (Syn.shift m) (Syn.shift P) := by
    simpa [points, Fm.shift, Syn.shift] using hPoints.shift
  have hFs : Γ.map Fm.shift ⊢[PRAAx] family (Syn.shift f) (Syn.shift m) (Syn.shift c)
      (Syn.shift L) (Syn.shift D) := by
    simpa [Fm.shift, Syn.shift] using hFamily.shift
  have hCovs : Γ.map Fm.shift ⊢[PRAAx] covered (Syn.shift f) (Syn.shift m) (Syn.shift c)
      (Syn.shift L) (Syn.shift P) (Syn.shift D) := by
    simpa [Fm.shift, Syn.shift] using hCovered.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift D)) :: Γ.map Fm.shift
  have b := group_bound (Γ := Δ) (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift P)
    (Syn.shift D) (var 0) hCs.wk hPs.wk hFs.wk hCovs.wk Prf.hyp0
  have lengthGroup := group_length (Γ := Δ) testBody (Syn.shift P) (length (Syn.shift D))
    (data (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift D)) (var 0)
  simpa [Δ, Syn.shift] using le_congr lengthGroup (.eqRefl _) b

theorem bound (f m c L P D : PTm n)
    (hCurve : Γ ⊢[PRAAx] curveInput f m c) (hPoints : Γ ⊢[PRAAx] points f m P)
    (hFamily : Γ ⊢[PRAAx] family f m c L D) (hCovered : Γ ⊢[PRAAx] covered f m c L P D) :
    Γ ⊢[PRAAx] le (length P) (length D * L) :=
  cover_count testBody P (length D) (data f m c L D) L
    (generic_cover f m c L P D hFamily hCovered) (group_bounds f m c L P D hCurve hPoints hFamily hCovered)

theorem bound_at_most (f m c L P D M : PTm n)
    (hCurve : Γ ⊢[PRAAx] curveInput f m c) (hPoints : Γ ⊢[PRAAx] points f m P)
    (hFamily : Γ ⊢[PRAAx] family f m c L D) (hCovered : Γ ⊢[PRAAx] covered f m c L P D)
    (hM : Γ ⊢[PRAAx] le (length D) M) :
    Γ ⊢[PRAAx] le (length P) (M * L) :=
  le_trans (bound f m c L P D hCurve hPoints hFamily hCovered) (mul_le_mul_right L hM)

theorem actual_proper_cover_count_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (curveInput (var 0) (var 1) (var 2) ⟶ points (var 0) (var 1) (var 4) ⟶
      family (var 0) (var 1) (var 2) (var 3) (var 5) ⟶ covered (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      le (length (var 4)) (length (var 5) * var 3)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (bound _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_proper_cover_at_most_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (curveInput (var 0) (var 1) (var 2) ⟶ points (var 0) (var 1) (var 4) ⟶
      family (var 0) (var 1) (var 2) (var 3) (var 5) ⟶ covered (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      le (length (var 5)) (var 6) ⟶ le (length (var 4)) (var 6 * var 3)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI
    (bound_at_most _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianSuperellipticCoverBound
