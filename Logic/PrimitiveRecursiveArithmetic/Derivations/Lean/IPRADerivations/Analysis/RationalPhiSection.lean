import IPRADerivations.Analysis.RationalPhiSectionNonzero
import IPRADerivations.Analysis.RationalPhiSectionZero

/-!
# The original finite section theorem for rational superelliptic points

The zero and nonzero ordinate-coefficient branches use the same exact
source dot product and the same original point list. The first branch
counts actual fibers and the second uses the actual collapse polynomial.
A proper rational span provides the same computed nonzero annihilator
for every point. The exponent is any positive natural number.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPhiSection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalPhiFeatures (dimension equation dot annihilator free)
open RationalPhiSectionNonzero (curveInput lineEquations members)
open RationalPhiSectionZero (nonzero)
open RationalGaussianEmbedding (embed scalarOne scalarZero embed_equal)
open RationalArgmin (rationalEq rationalEq_congr)
open RationalCurvePointsGaussianEmbedding (distinct)
open RationalSuperellipticNormDegree (pointPowers)
open RationalSuperellipticSubspace (properSpan)
open GaussianRationalFiberGrouping (abscissa ordinate)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def dotEquations (a s L : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift L)) ⟶ rationalEq
    (dot (Syn.shift a) (Syn.shift s) (abscissa (Syn.shift L) (var 0)) (ordinate (Syn.shift L) (var 0))) scalarZero)

@[simp] theorem subst_dotEquations {k : ℕ} (σ : Fin n → PTm k) (a s L : PTm n) :
    (dotEquations a s L).subst σ = dotEquations (Syn.subst σ a) (Syn.subst σ s) (Syn.subst σ L) := by
  simp [dotEquations,Syn.subst_shift,Syn.shift_subst]

theorem lines_of_dot_equations (a s L : PTm n) (h : Γ ⊢[PRAAx] dotEquations a s L) :
    Γ ⊢[PRAAx] lineEquations a s L := by
  refine .allI (.impI ?_)
  let i : PTm (n+1) := var 0
  let a' := Syn.shift a
  let s' := Syn.shift s
  let L' := Syn.shift L
  let x := abscissa L' i
  let y := ordinate L' i
  let Δ := lt i (length L') :: Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] dotEquations a' s' L' := by
    simpa [Δ,a',s',L',Fm.shift,Syn.shift] using h.shift.wk
  have gate : Δ ⊢[PRAAx] lt i (length L') ⟶ rationalEq (dot a' s' x y) scalarZero := by
    simpa [dotEquations,x,y] using h'.allE i
  have he := rationalEq_congr (RationalPhiFeatures.dot_identity (Γ := Δ) a' s' x y) (.eqRefl _)
    (.impE gate Prf.hyp0)
  exact RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _
    (RationalArithmetic.add_guard _ _) (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) (embed_equal _ _ he)

theorem ordinate_cases (a : PTm n) : Γ ⊢[PRAAx]
    rationalEq a scalarZero ⋎ RationalSectionCollapse.nonzero a := by
  have e := RationalGaussianEmbedding.zero_iff (Γ := Γ) a
  refine .orE (eq_or_ne (embed a) GaussianRationalHorner.qzero) ?_ ?_
  · exact .orI₁ (e.wk.iffMp Prf.hyp0)
  · exact .orI₂ (.impI (.impE Prf.hyp1 (e.wk.wk.iffMpr Prf.hyp0)))

theorem section_from_lines (a f s r m L : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (ha : Γ ⊢[PRAAx] nonzero a s) (hd : Γ ⊢[PRAAx] distinct L)
    (hl : Γ ⊢[PRAAx] lineEquations a s L) (hc : Γ ⊢[PRAAx] pointPowers f r L) : Γ ⊢[PRAAx] le (length L) m := by
  refine .orE (ordinate_cases (entry a (succ s))) ?_ ?_
  · have le := RationalPhiSectionZero.zero_section_bound f a r m s L
      (.andE₁ h.wk) (.andE₁ (.andE₂ h.wk)) ha.wk Prf.hyp0 hd.wk hc.wk hl.wk
    exact le_trans le (le_of_lt (.andE₂ (.andE₂ (.andE₂ h.wk))))
  · exact RationalPhiSectionNonzero.section_bound a f s r m L h.wk Prf.hyp0 hd.wk hl.wk hc.wk

theorem section_bound (a f s r m L : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (ha : Γ ⊢[PRAAx] nonzero a s) (hd : Γ ⊢[PRAAx] distinct L)
    (hl : Γ ⊢[PRAAx] dotEquations a s L) (hc : Γ ⊢[PRAAx] pointPowers f r L) : Γ ⊢[PRAAx] le (length L) m :=
  section_from_lines a f s r m L h ha hd (lines_of_dot_equations a s L hl) hc

theorem unit_nonzero : Γ ⊢[PRAAx] neg (rationalEq (scalarOne : PTm n) scalarZero) :=
  .impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero
    (RationalGaussianEmbedding.embed_one.eqSymm.eqTrans ((embed_equal _ _ Prf.hyp0).eqTrans RationalGaussianEmbedding.embed_zero)))

theorem computed_nonzero (A R s : PTm n) (hp : Γ ⊢[PRAAx] properSpan A R (dimension s)) :
    Γ ⊢[PRAAx] nonzero (annihilator A R s) s := by
  let a := annihilator A R s
  let j := free A R s
  have cert := RationalPhiFeatures.computed_certificate A R s hp
  have hj : Γ ⊢[PRAAx] lt j (dimension s) := .andE₁ (.andE₂ cert)
  have he : Γ ⊢[PRAAx] entry a j ≐ scalarOne := .andE₁ (.andE₂ (.andE₂ cert))
  have hn : Γ ⊢[PRAAx] neg (rationalEq (entry a j) scalarZero) :=
    .impI (.impE unit_nonzero (rationalEq_congr he.wk (.eqRefl _) Prf.hyp0))
  refine .exI j ?_
  simpa [RationalPhiSectionZero.nonzero] using Prf.andI hj hn

theorem proper_span_bound (A R f s r m L : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (hp : Γ ⊢[PRAAx] properSpan A R (dimension s)) (hd : Γ ⊢[PRAAx] distinct L)
    (hc : Γ ⊢[PRAAx] pointPowers f r L) (hm : Γ ⊢[PRAAx] members A R s L) :
    Γ ⊢[PRAAx] le (length L) m :=
  section_from_lines _ _ _ _ _ _ h (computed_nonzero A R s hp) hd
    (RationalPhiSectionNonzero.computed_lines A R s L hp hm) hc

theorem actual_original_rational_section_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (curveInput (var 1) (var 2) (var 3) (var 4) ⟶ nonzero (var 0) (var 2) ⟶ distinct (var 5) ⟶
      dotEquations (var 0) (var 2) (var 5) ⟶ pointPowers (var 1) (var 3) (var 5) ⟶ le (length (var 5)) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (section_bound _ _ _ _ _ _
    (.hyp (by simp)) (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0))))))

theorem actual_original_proper_span_section_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (curveInput (var 2) (var 3) (var 4) (var 5) ⟶ properSpan (var 0) (var 1) (dimension (var 3)) ⟶
      distinct (var 6) ⟶ pointPowers (var 2) (var 4) (var 6) ⟶ members (var 0) (var 1) (var 3) (var 6) ⟶
      le (length (var 6)) (var 5)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (proper_span_bound _ _ _ _ _ _ _
    (.hyp (by simp)) (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.RationalPhiSection
