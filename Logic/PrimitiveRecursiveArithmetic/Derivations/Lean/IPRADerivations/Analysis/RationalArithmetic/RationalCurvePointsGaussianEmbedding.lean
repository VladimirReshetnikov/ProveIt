import IPRADerivations.Analysis.Polynomials.Elimination.RationalBivariateGaussianEmbedding
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalCurveFibers
import IPRADerivations.Core.CongruenceTactic

/-!
# Transport of finite rational curve points

The list embedding retains every original index and normalizes the two
rational coordinates independently. Rational-value distinctness and the
two original rational polynomial-zero conditions give the predicates on
the actual embedded list required by the Gaussian norm bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCurvePointsGaussianEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed scalarZero)
open RationalPolynomialGaussianEmbedding (embed_congr)
open RationalRowSpanGaussianEmbedding (matrix)
open RationalBivariateGaussianEmbedding (monic bivariate)
open RationalArgmin (rationalEq)
open GaussianRationalFiberGrouping (abscissa ordinate)
open GaussianRationalHorner (qzero evaluate)
open GaussianRationalValueEquality (valueEqual)
open GaussianPolynomialMonicCompanion (rowShape monicValues values)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def mapPoint (p : PTm n) : PTm n := pairT (embed (fstT p)) (embed (sndT p))
def pointBody : PTm 2 := mapPoint (entry (var 1) (var 0))
def points (L : PTm n) : PTm n := sequence pointBody (length L) L

@[simp] theorem subst_mapPoint {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (mapPoint p) = mapPoint (Syn.subst σ p) := by simp [mapPoint]
@[simp] theorem subst_points {l : ℕ} (σ : Fin n → PTm l) (L : PTm n) :
    Syn.subst σ (points L) = points (Syn.subst σ L) := by simp [points]

theorem points_length (L : PTm n) : Γ ⊢[PRAAx] length (points L) ≐ length L :=
  sequence_length _ _ _
theorem points_lookup (L i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L)) :
    Γ ⊢[PRAAx] entry (points L) i ≐ mapPoint (entry L i) := by
  simpa only [points,pointBody,inst2,subst_mapPoint,subst_entry,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    sequence_decode (Γ := Γ) pointBody (x := L) hi

theorem abscissa_at (L i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L)) :
    Γ ⊢[PRAAx] abscissa (points L) i ≐ embed (abscissa L i) :=
  (congrFst (points_lookup L i hi)).eqTrans (fst_pair _ _)
theorem ordinate_at (L i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length L)) :
    Γ ⊢[PRAAx] ordinate (points L) i ≐ embed (ordinate L i) :=
  (congrSnd (points_lookup L i hi)).eqTrans (snd_pair _ _)

def distinctFrom (L i : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift L)) ⟶ lt (Syn.shift i) (var 0) ⟶
    neg (rationalEq (abscissa (Syn.shift L) (var 0)) (abscissa (Syn.shift L) (Syn.shift i)) ⋏
      rationalEq (ordinate (Syn.shift L) (var 0)) (ordinate (Syn.shift L) (Syn.shift i))))
def distinct (L : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift L)) ⟶ distinctFrom (Syn.shift L) (var 0))
def curveZeros (F m L : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift L)) ⟶
    rationalEq (monic (Syn.shift F) (Syn.shift m) (abscissa (Syn.shift L) (var 0))
      (ordinate (Syn.shift L) (var 0))) scalarZero)
def functionZeros (G m L : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift L)) ⟶
    rationalEq (bivariate (Syn.shift G) (Syn.shift m) (abscissa (Syn.shift L) (var 0))
      (ordinate (Syn.shift L) (var 0))) scalarZero)
def sourceInput (F G m L : PTm n) : Fm PTm n := distinct L ⋏ (curveZeros F m L ⋏ functionZeros G m L)

@[simp] theorem subst_distinctFrom {l : ℕ} (σ : Fin n → PTm l) (L i : PTm n) :
    (distinctFrom L i).subst σ = distinctFrom (Syn.subst σ L) (Syn.subst σ i) := by
  simp [distinctFrom,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_distinct {l : ℕ} (σ : Fin n → PTm l) (L : PTm n) :
    (distinct L).subst σ = distinct (Syn.subst σ L) := by
  simp [distinct,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_curveZeros {l : ℕ} (σ : Fin n → PTm l) (F m L : PTm n) :
    (curveZeros F m L).subst σ = curveZeros (Syn.subst σ F) (Syn.subst σ m) (Syn.subst σ L) := by
  simp [curveZeros,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_functionZeros {l : ℕ} (σ : Fin n → PTm l) (G m L : PTm n) :
    (functionZeros G m L).subst σ = functionZeros (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ L) := by
  simp [functionZeros,Syn.subst_shift,Syn.shift_subst]

theorem distinct_at (L i j : PTm n) (h : Γ ⊢[PRAAx] distinct L)
    (hi : Γ ⊢[PRAAx] lt i (length L)) (hj : Γ ⊢[PRAAx] lt j (length L)) (hij : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] neg (rationalEq (abscissa L j) (abscissa L i) ⋏ rationalEq (ordinate L j) (ordinate L i)) := by
  have outer : Γ ⊢[PRAAx] lt i (length L) ⟶ distinctFrom L i := by simpa [distinct] using h.allE i
  have rule : Γ ⊢[PRAAx] lt j (length L) ⟶ lt i j ⟶
      neg (rationalEq (abscissa L j) (abscissa L i) ⋏ rationalEq (ordinate L j) (ordinate L i)) := by
    simpa [distinctFrom,neg] using (Prf.impE outer hi).allE j
  exact .impE (.impE rule hj) hij

private theorem rational_equal_of_embedded {u v a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ embed u) (hb : Γ ⊢[PRAAx] b ≐ embed v)
    (h : Γ ⊢[PRAAx] valueEqual a b) : Γ ⊢[PRAAx] rationalEq u v := by
  have left := (GaussianTranslatedNonconstant.recode_congr ha).eqTrans
    (GaussianTranslatedNonconstant.recode_eq _ (RationalGaussianEmbedding.embed_canonical u))
  have right := (GaussianTranslatedNonconstant.recode_congr hb).eqTrans
    (GaussianTranslatedNonconstant.recode_eq _ (RationalGaussianEmbedding.embed_canonical v))
  exact (RationalGaussianEmbedding.embed_eq_iff u v).iffMp
    (left.eqSymm.eqTrans ((GaussianRationalValueEquality.recode_equal_of_equal_values a b h).eqTrans right))

theorem mapped_distinct_at (L i j : PTm n) (h : Γ ⊢[PRAAx] distinct L)
    (hi : Γ ⊢[PRAAx] lt i (length (points L))) (hj : Γ ⊢[PRAAx] lt j (length (points L))) (hij : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] neg (valueEqual (abscissa (points L) j) (abscissa (points L) i) ⋏
      valueEqual (ordinate (points L) j) (ordinate (points L) i)) := by
  have oldi := lt_congr (.eqRefl _) (points_length L) hi
  have oldj := lt_congr (.eqRefl _) (points_length L) hj
  exact .impI (.impE (distinct_at L i j h oldi oldj hij).wk (.andI
    (rational_equal_of_embedded (abscissa_at L j oldj).wk (abscissa_at L i oldi).wk (.andE₁ Prf.hyp0))
    (rational_equal_of_embedded (ordinate_at L j oldj).wk (ordinate_at L i oldi).wk (.andE₂ Prf.hyp0))))

theorem mapped_distinct (L : PTm n) (h : Γ ⊢[PRAAx] distinct L) :
    Γ ⊢[PRAAx] GaussianRationalCurveFibers.pointDistinct (points L) := by
  refine .allI (.impI (.allI (.impI (.impI ?_))))
  let K := Syn.shift (Syn.shift L)
  let Δ := (lt (var 1) (length (points K))) :: (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] distinct K := by
    simpa only [Δ,K,Fm.shift,subst_distinct,Syn.shift] using h.shift.shift.wk
  have hz : (lt (var 1) (var 0) :: lt (var 0) (length (points K)) :: Δ) ⊢[PRAAx]
      neg (valueEqual (abscissa (points K) (var 0)) (abscissa (points K) (var 1)) ⋏
        valueEqual (ordinate (points K) (var 0)) (ordinate (points K) (var 1))) :=
    mapped_distinct_at K (var 1) (var 0) hs.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0
  simpa [Δ,K,Syn.shift,Fm.shift] using hz

theorem curve_at (F m L i : PTm n) (h : Γ ⊢[PRAAx] curveZeros F m L) (hi : Γ ⊢[PRAAx] lt i (length L)) :
    Γ ⊢[PRAAx] rationalEq (monic F m (abscissa L i) (ordinate L i)) scalarZero := by
  have rule : Γ ⊢[PRAAx] lt i (length L) ⟶ rationalEq (monic F m (abscissa L i) (ordinate L i)) scalarZero :=
    by simpa [curveZeros] using h.allE i
  exact .impE rule hi

theorem function_at (G m L i : PTm n) (h : Γ ⊢[PRAAx] functionZeros G m L) (hi : Γ ⊢[PRAAx] lt i (length L)) :
    Γ ⊢[PRAAx] rationalEq (bivariate G m (abscissa L i) (ordinate L i)) scalarZero := by
  have rule : Γ ⊢[PRAAx] lt i (length L) ⟶ rationalEq (bivariate G m (abscissa L i) (ordinate L i)) scalarZero :=
    by simpa [functionZeros] using h.allE i
  exact .impE rule hi

private theorem monic_values_congr (F m : PTm n) {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] monicValues F m x ≐ monicValues F m y := by
  ipra_congr (monicValues (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl F, .eqRefl m, h]

theorem mapped_curve_at (F m c L i : PTm n) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (h : Γ ⊢[PRAAx] curveZeros F m L) (hi : Γ ⊢[PRAAx] lt i (length (points L))) :
    Γ ⊢[PRAAx] evaluate (monicValues (matrix F m (succ c)) m (abscissa (points L) i)) (ordinate (points L) i) ≐ qzero := by
  have old := lt_congr (.eqRefl _) (points_length L) hi
  exact (GaussianRationalMonicReduction.evaluate_congr
    (monic_values_congr _ _ (abscissa_at L i old)) (ordinate_at L i old)).eqTrans
    ((RationalBivariateGaussianEmbedding.monic_zero_iff F m c (abscissa L i) (ordinate L i) hF).iffMp (curve_at F m L i h old))

theorem mapped_function_at (G m a L i : PTm n) (hG : Γ ⊢[PRAAx] rowShape G m a)
    (h : Γ ⊢[PRAAx] functionZeros G m L) (hi : Γ ⊢[PRAAx] lt i (length (points L))) :
    Γ ⊢[PRAAx] evaluate (values (matrix G m (succ a)) m (abscissa (points L) i)) (ordinate (points L) i) ≐ qzero := by
  have old := lt_congr (.eqRefl _) (points_length L) hi
  exact (GaussianRationalMonicReduction.evaluate_congr
    (GaussianPolynomialMonicCompanion.values_congr (.eqRefl _) (.eqRefl _) (abscissa_at L i old))
    (ordinate_at L i old)).eqTrans
    ((RationalBivariateGaussianEmbedding.bivariate_zero_iff G m a (abscissa L i) (ordinate L i) hG).iffMp
      (function_at G m L i h old))

theorem mapped_source (F G m a c L : PTm n) (hF : Γ ⊢[PRAAx] rowShape F m c)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (h : Γ ⊢[PRAAx] sourceInput F G m L) :
    Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput (matrix F m (succ c)) (matrix G m (succ a)) m (points L) := by
  refine .andI (mapped_distinct L (.andE₁ h)) (.andI (.allI (.impI ?_)) (.allI (.impI ?_)))
  · have shape : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift F) (Syn.shift m) (Syn.shift c) := by
      simpa only [Fm.shift,GaussianPolynomialMonicCompanion.subst_rowShape,Syn.shift] using hF.shift
    have source : Γ.map Fm.shift ⊢[PRAAx] curveZeros (Syn.shift F) (Syn.shift m) (Syn.shift L) := by
      simpa only [Fm.shift,subst_curveZeros,Syn.shift] using (Prf.andE₁ (Prf.andE₂ h)).shift
    simpa [Syn.shift] using mapped_curve_at (Syn.shift F) (Syn.shift m) (Syn.shift c) (Syn.shift L) (var 0)
      shape.wk source.wk Prf.hyp0
  · have shape : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by
      simpa only [Fm.shift,GaussianPolynomialMonicCompanion.subst_rowShape,Syn.shift] using hG.shift
    have source : Γ.map Fm.shift ⊢[PRAAx] functionZeros (Syn.shift G) (Syn.shift m) (Syn.shift L) := by
      simpa only [Fm.shift,subst_functionZeros,Syn.shift] using (Prf.andE₂ (Prf.andE₂ h)).shift
    simpa [Syn.shift] using mapped_function_at (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift L) (var 0)
      shape.wk source.wk Prf.hyp0

def pointsF : PR 1 := PTm.toPR (points (var 0) : PTm 1)

theorem points_at (L : PTm n) : Γ ⊢[PRAAx] ap1 pointsF L ≐ points L := by
  simpa [ap1,pointsF] using toPR_eq (Γ := Γ) (points (var 0) : PTm 1) ![L]

theorem actual_rational_point_list_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (length (var 0)) ⟶
      entry (ap1 pointsF (var 0)) (var 1) ≐ mapPoint (entry (var 0) (var 1))) :=
  closeUniv 2 (.impI ((entry_congr (points_at _) (.eqRefl _)).eqTrans (points_lookup _ _ Prf.hyp0)))

theorem actual_rational_curve_points_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (rowShape (var 0) (var 2) (var 4) ⟶ rowShape (var 1) (var 2) (var 3) ⟶
      sourceInput (var 0) (var 1) (var 2) (var 5) ⟶
      GaussianRationalCurveFibers.sourceInput (matrix (var 0) (var 2) (succ (var 4)))
        (matrix (var 1) (var 2) (succ (var 3))) (var 2) (points (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (mapped_source _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalCurvePointsGaussianEmbedding
