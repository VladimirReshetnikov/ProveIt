import IPRADerivations.Analysis.RationalPhiFeatures
import IPRADerivations.Analysis.RationalSectionCollapse

/-!
# The finite rational section bound with nonzero ordinate coefficient

Every original point on the computed line has an abscissa that is a root
of the actual collapse polynomial. Two distinct points on that line have
distinct rational abscissae. The exact runtime-degree root bound applies to
the actual produced list. No irreducibility or coprimality is needed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPhiSectionNonzero

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalArgmin (rationalEq rationalEq_congr)
open RationalGaussianEmbedding (embed scalarZero embed_canonical rational_equal_of_embed)
open GaussianRationalFiberGrouping (abscissa ordinate)
open GaussianRationalHorner (qzero)
open GaussianRationalSyntheticDivision (qsub_congr)
open RationalCurvePointsGaussianEmbedding (distinct distinct_at)
open RationalSuperellipticNormDegree (pointPowers point_power_at)
open RationalPhiFeatures (dimension annihilator equation features)
open RationalSectionCollapse (nonzero line curve)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def abscissaBody : PTm 2 := embed (abscissa (var 1) (var 0))
def abscissae (L : PTm n) : PTm n := sequence abscissaBody (length L) L

def lineEquations (a s L : PTm n) : Fm PTm n := .all (lt (var 0) (length (Syn.shift L)) ⟶
  equation (Syn.shift a) (Syn.shift s) (abscissa (Syn.shift L) (var 0)) (ordinate (Syn.shift L) (var 0)) ≐ scalarZero)

def members (A R s L : PTm n) : Fm PTm n := .all (lt (var 0) (length (Syn.shift L)) ⟶
  RationalRowSpanGaussianEmbedding.hasCoefficients (Syn.shift A) (Syn.shift R) (dimension (Syn.shift s))
    (features (Syn.shift s) (abscissa (Syn.shift L) (var 0)) (ordinate (Syn.shift L) (var 0))))

@[simp] theorem subst_abscissae {k : ℕ} (σ : Fin n → PTm k) (L : PTm n) :
    Syn.subst σ (abscissae L) = abscissae (Syn.subst σ L) := by simp [abscissae]
@[simp] theorem subst_lineEquations {k : ℕ} (σ : Fin n → PTm k) (a s L : PTm n) :
    (lineEquations a s L).subst σ = lineEquations (Syn.subst σ a) (Syn.subst σ s) (Syn.subst σ L) := by
  simp [lineEquations,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_members {k : ℕ} (σ : Fin n → PTm k) (A R s L : PTm n) :
    (members A R s L).subst σ = members (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ s) (Syn.subst σ L) := by
  simp [members,Syn.subst_shift,Syn.shift_subst]

theorem abscissae_length (L : PTm n) : Γ ⊢[PRAAx] length (abscissae L) ≐ length L :=
  sequence_length _ _ _
theorem abscissae_lookup (L i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    entry (abscissae L) i ≐ embed (abscissa L i) := by
  simpa [abscissae,abscissaBody,inst2] using
    sequence_decode (Γ := Γ) abscissaBody (x := L) hi

theorem line_at (a s L i : PTm n) (h : Γ ⊢[PRAAx] lineEquations a s L) (hi : Γ ⊢[PRAAx] lt i (length L)) :
    Γ ⊢[PRAAx] line (RationalPhiFeatures.polynomial a s) (entry a (succ s)) (abscissa L i) (ordinate L i) := by
  have gate : Γ ⊢[PRAAx] lt i (length L) ⟶ equation a s (abscissa L i) (ordinate L i) ≐ scalarZero := by
    simpa [lineEquations] using h.allE i
  exact rationalEq_congr (Prf.impE gate hi).eqSymm (.eqRefl _) (.eqRefl _)

theorem member_at (A R s L i : PTm n) (h : Γ ⊢[PRAAx] members A R s L) (hi : Γ ⊢[PRAAx] lt i (length L)) :
    Γ ⊢[PRAAx] RationalRowSpanGaussianEmbedding.hasCoefficients A R (dimension s)
      (features s (abscissa L i) (ordinate L i)) := by
  have gate : Γ ⊢[PRAAx] lt i (length L) ⟶ RationalRowSpanGaussianEmbedding.hasCoefficients A R
      (dimension s) (features s (abscissa L i) (ordinate L i)) := by
    simpa [members] using h.allE i
  exact .impE gate hi

theorem computed_lines (A R s L : PTm n)
    (hp : Γ ⊢[PRAAx] RationalSuperellipticSubspace.properSpan A R (dimension s))
    (hm : Γ ⊢[PRAAx] members A R s L) : Γ ⊢[PRAAx] lineEquations (annihilator A R s) s L := by
  refine .allI (.impI ?_)
  let A' := Syn.shift A
  let R' := Syn.shift R
  let s' := Syn.shift s
  let L' := Syn.shift L
  have p : Γ.map Fm.shift ⊢[PRAAx] RationalSuperellipticSubspace.properSpan A' R' (dimension s') := by
    simpa [A',R',s',Fm.shift,Syn.shift] using hp.shift
  have m : Γ.map Fm.shift ⊢[PRAAx] members A' R' s' L' := by
    simpa [A',R',s',L',Fm.shift,Syn.shift] using hm.shift
  simpa [A',R',s',L',Syn.shift] using RationalPhiFeatures.computed_equation A' R' s'
    (abscissa L' (var 0)) (ordinate L' (var 0)) p.wk (member_at A' R' s' L' (var 0) m.wk Prf.hyp0)

theorem original_abscissae_distinct_at (a s L i j : PTm n) (ha : Γ ⊢[PRAAx] nonzero (entry a (succ s)))
    (hd : Γ ⊢[PRAAx] distinct L) (hl : Γ ⊢[PRAAx] lineEquations a s L)
    (hi : Γ ⊢[PRAAx] lt i (length L)) (hj : Γ ⊢[PRAAx] lt j (length L)) (hij : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] neg (rationalEq (abscissa L j) (abscissa L i)) := by
  refine .impI (.impE (distinct_at L i j hd hi hj hij).wk (.andI Prf.hyp0 ?_))
  exact RationalSectionCollapse.ordinate_unique _ _ _ _ _ _ ha.wk
    (line_at a s L j hl hj).wk (line_at a s L i hl hi).wk Prf.hyp0

private theorem abscissae_difference_distinct_at (a s L i j : PTm n) (ha : Γ ⊢[PRAAx] nonzero (entry a (succ s)))
    (hd : Γ ⊢[PRAAx] distinct L) (hl : Γ ⊢[PRAAx] lineEquations a s L)
    (hi : Γ ⊢[PRAAx] lt i (length (abscissae L))) (hj : Γ ⊢[PRAAx] lt j (length (abscissae L)))
    (hij : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx]
    neg (GaussianRationalMetric.qsub (entry (abscissae L) j) (entry (abscissae L) i) ≐ qzero) := by
  have oldi := lt_congr (.eqRefl _) (abscissae_length L) hi
  have oldj := lt_congr (.eqRefl _) (abscissae_length L) hj
  have he := qsub_congr (abscissae_lookup L j oldj) (abscissae_lookup L i oldi)
  have ne := original_abscissae_distinct_at a s L i j ha hd hl oldi oldj hij
  let x := embed (abscissa L j)
  let y := embed (abscissa L i)
  refine .impI (.impE ne.wk (rational_equal_of_embed _ _ ?_))
  have eq := (GaussianRationalValueEquality.recode_eq_iff_difference_zero x y).wk.iffMpr
    (he.wk.eqSymm.eqTrans Prf.hyp0)
  exact (GaussianTranslatedNonconstant.recode_eq x (embed_canonical _)).wk.eqSymm.eqTrans
    (eq.eqTrans (GaussianTranslatedNonconstant.recode_eq y (embed_canonical _)).wk)

theorem abscissae_distinct (a s L : PTm n) (ha : Γ ⊢[PRAAx] nonzero (entry a (succ s)))
    (hd : Γ ⊢[PRAAx] distinct L) (hl : Γ ⊢[PRAAx] lineEquations a s L) : Γ ⊢[PRAAx]
    GaussianRationalFiniteRoots.distinct (abscissae L) := by
  refine .allI (.impI (.allI (.impI (.impI ?_))))
  let a' := Syn.shift (Syn.shift a)
  let s' := Syn.shift (Syn.shift s)
  let L' := Syn.shift (Syn.shift L)
  let Δ := lt (var 1) (length (abscissae L')) :: (Γ.map Fm.shift).map Fm.shift
  have q : Δ ⊢[PRAAx] nonzero (entry a' (succ s')) := by
    simpa [Δ,a',s',Fm.shift,Syn.shift] using ha.shift.shift.wk
  have d : Δ ⊢[PRAAx] distinct L' := by
    simpa [Δ,L',Fm.shift,Syn.shift] using hd.shift.shift.wk
  have l : Δ ⊢[PRAAx] lineEquations a' s' L' := by
    simpa [Δ,a',s',L',Fm.shift,Syn.shift] using hl.shift.shift.wk
  simpa [Δ,L',a',s',Fm.shift,Syn.shift] using
    (abscissae_difference_distinct_at a' s' L' (var 1) (var 0) q.wk.wk d.wk.wk l.wk.wk
      Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)

def collapse (a f s r m : PTm n) : PTm n :=
  RationalSectionCollapse.polynomial (RationalPhiFeatures.polynomial a s) f (entry a (succ s)) s r m

@[simp] theorem subst_collapse {k : ℕ} (σ : Fin n → PTm k) (a f s r m : PTm n) :
    Syn.subst σ (collapse a f s r m) = collapse (Syn.subst σ a) (Syn.subst σ f) (Syn.subst σ s) (Syn.subst σ r) (Syn.subst σ m) := by
  simp [collapse]

theorem collapsed_root_at (a f s r m L i : PTm n) (hdeg : Γ ⊢[PRAAx] le (r*s) m)
    (hf : Γ ⊢[PRAAx] length f ≐ succ m) (hl : Γ ⊢[PRAAx] lineEquations a s L) (hc : Γ ⊢[PRAAx] pointPowers f r L)
    (hi : Γ ⊢[PRAAx] lt i (length (abscissae L))) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (collapse a f s r m) (entry (abscissae L) i) ≐ qzero := by
  have oldi := lt_congr (.eqRefl _) (abscissae_length L) hi
  exact (GaussianRationalMonicReduction.evaluate_congr (.eqRefl _) (abscissae_lookup L i oldi)).eqTrans
    (RationalSectionCollapse.polynomial_root _ _ _ _ _ _ _ _ hdeg (RationalPhiFeatures.polynomial_length a s)
      hf (line_at a s L i hl oldi) (point_power_at f r L i hc oldi))

theorem collapsed_roots (a f s r m L : PTm n) (hdeg : Γ ⊢[PRAAx] le (r*s) m)
    (hf : Γ ⊢[PRAAx] length f ≐ succ m) (hl : Γ ⊢[PRAAx] lineEquations a s L) (hc : Γ ⊢[PRAAx] pointPowers f r L) :
    Γ ⊢[PRAAx] GaussianRationalFiniteRoots.roots (collapse a f s r m) (abscissae L) := by
  refine .allI (.impI ?_)
  let a' := Syn.shift a
  let f' := Syn.shift f
  let s' := Syn.shift s
  let r' := Syn.shift r
  let m' := Syn.shift m
  let L' := Syn.shift L
  have gd : Γ.map Fm.shift ⊢[PRAAx] le (r'*s') m' := by
    simpa [r',s',m',Syn.shift,Fm.shift] using hdeg.shift
  have shape : Γ.map Fm.shift ⊢[PRAAx] length f' ≐ succ m' := by
    simpa [f',m',Syn.shift,Fm.shift] using hf.shift
  have lines : Γ.map Fm.shift ⊢[PRAAx] lineEquations a' s' L' := by
    simpa [a',s',L',Syn.shift,Fm.shift] using hl.shift
  have curves : Γ.map Fm.shift ⊢[PRAAx] pointPowers f' r' L' := by
    simpa [f',r',L',Syn.shift,Fm.shift] using hc.shift
  simpa [a',f',s',r',m',L',Syn.shift] using
    collapsed_root_at a' f' s' r' m' L' (var 0) gd.wk shape.wk lines.wk curves.wk Prf.hyp0

def curveInput (f s r m : PTm n) : Fm PTm n := le one r ⋏ (length f ≐ succ m ⋏
  (nonzero (entry f zero) ⋏ lt (r*s) m))

theorem section_bound (a f s r m L : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (ha : Γ ⊢[PRAAx] nonzero (entry a (succ s))) (hd : Γ ⊢[PRAAx] distinct L)
    (hl : Γ ⊢[PRAAx] lineEquations a s L) (hc : Γ ⊢[PRAAx] pointPowers f r L) : Γ ⊢[PRAAx] le (length L) m := by
  have hdeg : Γ ⊢[PRAAx] lt (r*s) m := .andE₂ (.andE₂ (.andE₂ h))
  have hf : Γ ⊢[PRAAx] length f ≐ succ m := .andE₁ (.andE₂ h)
  have hHead := RationalSectionCollapse.nonzero_leading_coefficient (RationalPhiFeatures.polynomial a s) f
    (entry a (succ s)) s r m hdeg ha (.andE₁ (.andE₂ (.andE₂ h)))
  exact le_congr (abscissae_length L) (.eqRefl _) (GaussianRationalFiniteRoots.finite_root_bound _ _ _
    (RationalSectionCollapse.polynomial_length _ _ _ _ _ _) hHead
    (collapsed_roots _ _ _ _ _ _ (le_of_lt hdeg) hf hl hc)
    (abscissae_distinct _ _ _ ha hd hl))

theorem computed_section_bound (A R f s r m L : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (hp : Γ ⊢[PRAAx] RationalSuperellipticSubspace.properSpan A R (dimension s))
    (ha : Γ ⊢[PRAAx] nonzero (entry (annihilator A R s) (succ s)))
    (hd : Γ ⊢[PRAAx] distinct L) (hc : Γ ⊢[PRAAx] pointPowers f r L)
    (hm : Γ ⊢[PRAAx] members A R s L) : Γ ⊢[PRAAx] le (length L) m :=
  section_bound _ _ _ _ _ _ h ha hd (computed_lines _ _ _ _ hp hm) hc

def output (a f s r m L : PTm n) : PTm n := pairT (collapse a f s r m) (abscissae L)
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (a f s r m L : PTm n) : PTm n := ConciseIPRA.PTm.app outputF ![a,f,s,r,m,L]

theorem program_at (a f s r m L : PTm n) : Γ ⊢[PRAAx] run a f s r m L ≐ output a f s r m L := by
  simpa [run,outputF,output] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![a,f,s,r,m,L]

theorem returned_polynomial (a f s r m L : PTm n) : Γ ⊢[PRAAx]
    fstT (run a f s r m L) ≐ collapse a f s r m :=
  (congrFst (program_at _ _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_roots (a f s r m L : PTm n) : Γ ⊢[PRAAx]
    sndT (run a f s r m L) ≐ abscissae L :=
  (congrSnd (program_at _ _ _ _ _ _)).eqTrans (snd_pair _ _)

theorem actual_section_nonzero_abscissae_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (nonzero (entry (var 0) (succ (var 1))) ⟶ distinct (var 2) ⟶ lineEquations (var 0) (var 1) (var 2) ⟶
      GaussianRationalFiniteRoots.distinct (abscissae (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (abscissae_distinct _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem actual_section_nonzero_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (curveInput (var 1) (var 2) (var 3) (var 4) ⟶ nonzero (entry (var 0) (succ (var 2))) ⟶ distinct (var 5) ⟶
      lineEquations (var 0) (var 2) (var 5) ⟶ pointPowers (var 1) (var 3) (var 5) ⟶
      le (length (var 5)) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (section_bound _ _ _ _ _ _
    (.hyp (by simp)) (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0))))))

theorem actual_computed_section_nonzero_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (curveInput (var 2) (var 3) (var 4) (var 5) ⟶ RationalSuperellipticSubspace.properSpan (var 0) (var 1) (dimension (var 3)) ⟶
      nonzero (entry (annihilator (var 0) (var 1) (var 3)) (succ (var 3))) ⟶ distinct (var 6) ⟶
      pointPowers (var 2) (var 4) (var 6) ⟶ members (var 0) (var 1) (var 3) (var 6) ⟶ le (length (var 6)) (var 5)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI (computed_section_bound _ _ _ _ _ _ _
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))))

theorem actual_returned_section_nonzero_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ collapse (var 0) (var 1) (var 2) (var 3) (var 4) ⋏
      sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ abscissae (var 5)) :=
  closeUniv 6 (.andI (returned_polynomial _ _ _ _ _ _) (returned_roots _ _ _ _ _ _))

end LeanProofs.IPRA.Analysis.RationalPhiSectionNonzero
