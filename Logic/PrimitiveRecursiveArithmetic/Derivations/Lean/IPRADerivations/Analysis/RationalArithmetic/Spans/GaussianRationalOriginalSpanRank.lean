import IPRADerivations.Analysis.RationalArithmetic.Spans.GaussianRationalFullReducedSpan
import IPRADerivations.Analysis.RationalArithmetic.Spans.GaussianRationalProperSpanWitness
import IPRADerivations.Analysis.RationalArithmetic.Spans.GaussianRationalRowSpanRewind
import IPRADerivations.Analysis.Polynomials.Elimination.GaussianSuperellipticSubspaceTheorem

/-!
# Full rank and properness of the original Gaussian-rational span

Full pivot count gives a spanning witness in the reduced rows. The
backward coefficient recursion transfers it to the original rows.
Strict deficiency gives a vector with no representation in those rows.
These two constructions identify the full and proper spans of the
original matrix.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalOriginalSpanRank

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalRowElimination (shape)
open GaussianRationalRankNullityCriterion (rank rank_bound finalMatrix)
open GaussianRationalRowSpan (membership witness)
open GaussianSuperellipticSubspaceFromSpan (hasCoefficients pointMembership)
open GaussianSuperellipticSubspaceWitness (curveInput basisCount points)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def weights (A R N v : PTm n) : PTm n :=
  GaussianRationalRowSpanRewind.originalWeights A R N N (GaussianRationalFullReducedSpan.weights A R N v)

def fullSpan (A R N : PTm n) : Fm PTm n := .all
  (length (var 0) ≐ Syn.shift N ⟶ hasCoefficients (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0))

def properSpan (A R N : PTm n) : Fm PTm n := .ex
  ((length (var 0) ≐ Syn.shift N) ⋏ neg (hasCoefficients (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)))

@[simp] theorem subst_weights {k : ℕ} (σ : Fin n → PTm k) (A R N v : PTm n) :
    Syn.subst σ (weights A R N v) = weights (Syn.subst σ A) (Syn.subst σ R)
      (Syn.subst σ N) (Syn.subst σ v) := by simp [weights]
@[simp] theorem subst_fullSpan {k : ℕ} (σ : Fin n → PTm k) (A R N : PTm n) :
    (fullSpan A R N).subst σ = fullSpan (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) := by
  simp [fullSpan,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_properSpan {k : ℕ} (σ : Fin n → PTm k) (A R N : PTm n) :
    (properSpan A R N).subst σ = properSpan (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) := by
  simp [properSpan,Syn.subst_shift,Syn.shift_subst]

theorem weights_length (A R N v : PTm n) : Γ ⊢[PRAAx] length (weights A R N v) ≐ R :=
  GaussianRationalRowSpanRewind.rewind_length A R N N (GaussianRationalFullReducedSpan.weights A R N v) N
    (GaussianRationalFullReducedSpan.weights_length _ _ _ _)

theorem original_witness (A R N v : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hRank : Γ ⊢[PRAAx] rank A R N ≐ N) (hv : Γ ⊢[PRAAx] length v ≐ N) :
    Γ ⊢[PRAAx] witness A R N (weights A R N v) v := by
  have reduced := GaussianRationalFullReducedSpan.full_reduced_witness A R N v hA hRank hv
  have rep : Γ ⊢[PRAAx] membership (finalMatrix A R N) R N (GaussianRationalFullReducedSpan.weights A R N v) v :=
    .andE₂ (.andE₂ (.andE₂ reduced))
  exact .andI hA (.andI (weights_length _ _ _ _) (.andI hv
    (GaussianRationalRowSpanRewind.membership_original A R N N _ v rep)))

theorem original_member (A R N v : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hRank : Γ ⊢[PRAAx] rank A R N ≐ N) (hv : Γ ⊢[PRAAx] length v ≐ N) :
    Γ ⊢[PRAAx] hasCoefficients A R N v := by
  have actual := original_witness A R N v hA hRank hv
  refine .exI (weights A R N v) ?_
  simpa [hasCoefficients] using Prf.andI (.andE₁ (.andE₂ actual)) (.andE₂ (.andE₂ (.andE₂ actual)))

theorem full_of_count (A R N : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hRank : Γ ⊢[PRAAx] rank A R N ≐ N) :
    Γ ⊢[PRAAx] fullSpan A R N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hA.shift
  have hr : Γ.map Fm.shift ⊢[PRAAx] rank (Syn.shift A) (Syn.shift R) (Syn.shift N) ≐ Syn.shift N := by
    simpa [Fm.shift,Syn.shift] using hRank.shift
  exact .allI (.impI (original_member (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) hs.wk hr.wk Prf.hyp0))

theorem full_at (A R N v : PTm n) (h : Γ ⊢[PRAAx] fullSpan A R N) (hv : Γ ⊢[PRAAx] length v ≐ N) :
    Γ ⊢[PRAAx] hasCoefficients A R N v := by
  have rule : Γ ⊢[PRAAx] length v ≐ N ⟶ hasCoefficients A R N v := by simpa [fullSpan] using h.allE v
  exact .impE rule hv

theorem free_witness_missing (A R N : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hRank : Γ ⊢[PRAAx] lt (rank A R N) N) :
    Γ ⊢[PRAAx] neg (hasCoefficients A R N (GaussianRationalProperSpanWitness.witness A R N)) := by
  have hInput : Γ ⊢[PRAAx] GaussianRationalProperSpanWitness.input A R N := .andI hA hRank
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalProperSpanWitness.input (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hInput.shift
  let v := GaussianRationalProperSpanWitness.witness A R N
  refine .impI (.exE Prf.hyp0 ?_)
  let Δ := ((length (var 0) ≐ Syn.shift R) ⋏ membership (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)
    (Syn.shift v)) :: (hasCoefficients A R N v).shift :: Γ.map Fm.shift
  have forbidden := GaussianRationalProperSpanWitness.coefficient_impossible (Γ := Δ)
    (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) hs.wk.wk
  have forbidden' : Δ ⊢[PRAAx] neg (membership (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) (Syn.shift v)) := by
    simpa [v,Syn.shift] using forbidden
  have contradiction : Δ ⊢[PRAAx] .bot := .impE forbidden' (.andE₂ (Prf.hyp0 : Δ ⊢[PRAAx] _))
  simpa [Δ,v,Fm.shift] using contradiction

theorem proper_of_deficit (A R N : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (hRank : Γ ⊢[PRAAx] lt (rank A R N) N) :
    Γ ⊢[PRAAx] properSpan A R N := by
  refine .exI (GaussianRationalProperSpanWitness.witness A R N) ?_
  simpa [properSpan] using Prf.andI (GaussianRationalProperSpanWitness.witness_length A R N)
    (free_witness_missing A R N hA hRank)

theorem full_proper_absurd (A R N : PTm n) (hF : Γ ⊢[PRAAx] fullSpan A R N) (hP : Γ ⊢[PRAAx] properSpan A R N) :
    Γ ⊢[PRAAx] .bot := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] fullSpan (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hF.shift
  refine .exE hP ?_
  let Δ := ((length (var 0) ≐ Syn.shift N) ⋏ neg (hasCoefficients (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0))) ::
    Γ.map Fm.shift
  have w : Δ ⊢[PRAAx] (length (var 0) ≐ Syn.shift N) ⋏ neg (hasCoefficients (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0)) :=
    Prf.hyp0
  exact .impE (.andE₂ w) (full_at _ _ _ _ hs.wk (.andE₁ w))

theorem proper_implies_deficit (A R N : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (h : Γ ⊢[PRAAx] properSpan A R N) :
    Γ ⊢[PRAAx] lt (rank A R N) N := by
  refine .orE (lt_or_eq_of_le (rank_bound A R N)) Prf.hyp0 ?_
  exact .botE _ (full_proper_absurd A R N (full_of_count _ _ _ hA.wk Prf.hyp0) h.wk)

theorem full_implies_count (A R N : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) (h : Γ ⊢[PRAAx] fullSpan A R N) :
    Γ ⊢[PRAAx] rank A R N ≐ N := by
  refine .orE (lt_or_eq_of_le (rank_bound A R N)) ?_ Prf.hyp0
  exact .botE _ (full_proper_absurd A R N h.wk (proper_of_deficit _ _ _ hA.wk Prf.hyp0))

theorem full_iff_count (A R N : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) :
    Γ ⊢[PRAAx] Fm.iff (fullSpan A R N) (rank A R N ≐ N) :=
  .andI (.impI (full_implies_count _ _ _ hA.wk Prf.hyp0)) (.impI (full_of_count _ _ _ hA.wk Prf.hyp0))

theorem proper_iff_deficit (A R N : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) :
    Γ ⊢[PRAAx] Fm.iff (properSpan A R N) (lt (rank A R N) N) :=
  .andI (.impI (proper_implies_deficit _ _ _ hA.wk Prf.hyp0)) (.impI (proper_of_deficit _ _ _ hA.wk Prf.hyp0))

theorem proper_subspace_bound (f m c L P A R : PTm n) (hF : Γ ⊢[PRAAx] curveInput f m c)
    (hA : Γ ⊢[PRAAx] shape A R (basisCount f m c L)) (h : Γ ⊢[PRAAx] properSpan A R (basisCount f m c L))
    (hPts : Γ ⊢[PRAAx] points f m P) (hSpan : Γ ⊢[PRAAx] pointMembership f m c L P A R) :
    Γ ⊢[PRAAx] le (length P) L :=
  GaussianSuperellipticSubspaceTheorem.subspace_bound f m c L P A R
    (.andI hF (.andI hA (proper_implies_deficit _ _ _ hA h))) hPts hSpan

theorem actual_original_span_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (shape (var 0) (var 1) (var 2) ⟶ rank (var 0) (var 1) (var 2) ≐ var 2 ⟶ length (var 3) ≐ var 2 ⟶
      witness (var 0) (var 1) (var 2) (weights (var 0) (var 1) (var 2) (var 3)) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (original_witness _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_full_span_iff_count_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (shape (var 0) (var 1) (var 2) ⟶ Fm.iff (fullSpan (var 0) (var 1) (var 2)) (rank (var 0) (var 1) (var 2) ≐ var 2)) :=
  closeUniv 3 (.impI (full_iff_count _ _ _ Prf.hyp0))

theorem actual_proper_span_iff_deficit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (shape (var 0) (var 1) (var 2) ⟶ Fm.iff (properSpan (var 0) (var 1) (var 2)) (lt (rank (var 0) (var 1) (var 2)) (var 2))) :=
  closeUniv 3 (.impI (proper_iff_deficit _ _ _ Prf.hyp0))

theorem actual_proper_subspace_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (curveInput (var 0) (var 1) (var 2) ⟶ shape (var 5) (var 6) (basisCount (var 0) (var 1) (var 2) (var 3)) ⟶
      properSpan (var 5) (var 6) (basisCount (var 0) (var 1) (var 2) (var 3)) ⟶
      points (var 0) (var 1) (var 4) ⟶ pointMembership (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      le (length (var 4)) (var 3)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI
    (proper_subspace_bound _ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianRationalOriginalSpanRank
