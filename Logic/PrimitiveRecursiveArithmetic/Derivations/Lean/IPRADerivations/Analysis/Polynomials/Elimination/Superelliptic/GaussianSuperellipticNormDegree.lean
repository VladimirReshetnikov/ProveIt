import IPRADerivations.Analysis.RationalArithmetic.Norms.PolynomialNorms.GaussianNormFiniteZeroBound
import IPRADerivations.Analysis.Polynomials.Determinants.Coefficients.GaussianPolynomialDeterminantDegreeDominance
import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.GaussianSuperellipticCyclicLeading
import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.GaussianSuperellipticWordTerms

/-!
# Exact degree of the original superelliptic norm

Coprimality selects one retained cyclic word. Its actual successful term
has the weighted degree, and every other successful term has smaller
degree. The original norm therefore has the selected signed leading
coefficient. Its nonzero flag gives the weighted bound on the original
list of distinct common zeros.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSuperellipticNormDegree

open_ipra
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminant (wordCode)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (stage stage_congr signPoint)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTermDegree (degree_congr flag_congr leading_congr)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMonicCompanion (rowShape)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMultiplicationMatrix (width)
open LeanProofs.IPRA.Analysis.GaussianPolynomialWeightedDegree (weightedDegree nonzeroRows)
open LeanProofs.IPRA.Analysis.GaussianRationalCurveFibers (curveZeros pointDistinct functionZeros)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberGrouping (abscissa ordinate)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qmul)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree (degree flag nonzeroCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProductDegree (leading)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianSuperellipticCyclicLeading (k rotation expected)
open LeanProofs.IPRA.Analysis.GaussianSuperellipticMatrixEntries (matrix)
open LeanProofs.IPRA.Analysis.GaussianSuperellipticTail (tailRows)
open LeanProofs.IPRA.Foundations.RuntimeCyclicPermutation (rotationTable)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (count position)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (f G m a c : PTm n) : Fm PTm n := le (succ one) m ⋏ (le one (degree f c) ⋏
  (gcd m (degree f c) ≐ one ⋏ (length f ≐ succ c ⋏ (nonzeroCoefficients f c ⋏ (rowShape G m a ⋏ nonzeroRows G m a)))))

def cyclicRank (f G m a c : PTm n) : PTm n := position (rotationTable m (k f G m a c)) m

def originalNorm (f G m a c : PTm n) : PTm n := fstT (GaussianPolynomialMonicNorm.run (tailRows f m c) G m a c)

def sourceLeading (f G m a c : PTm n) : PTm n := qmul (signPoint m (rotation f G m a c)) (expected f G m a c)

def certificate (f G m a c : PTm n) : Fm PTm n := flag (originalNorm f G m a c) (m*width m a c) ≐ one ⋏
  (degree (originalNorm f G m a c) (m*width m a c) ≐ weightedDegree G m a (degree f c) ⋏
    leading (originalNorm f G m a c) (m*width m a c) ≐ sourceLeading f G m a c)

@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (f G m a c : PTm n) :
    (input f G m a c).subst σ = input (Syn.subst σ f) (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by
  have hg (u v : PTm n) : Syn.subst σ (gcd u v) = gcd (Syn.subst σ u) (Syn.subst σ v) := by
    simp only [gcd,subst_ex2,ConciseIPRA.PTm.subst_succ]
  simp only [input,Fm.subst_and,Fm.subst_eq,subst_le,hg,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero,GaussianRationalPolynomialDegree.subst_degree,
    GaussianRationalPolynomialDegree.subst_nonzeroCoefficients,Foundations.SequenceComposition.subst_length,
    GaussianPolynomialMonicCompanion.subst_rowShape,GaussianPolynomialWeightedDegree.subst_nonzeroRows]

theorem word_input (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) :
    Γ ⊢[PRAAx] GaussianSuperellipticWordTerms.input f G m a c := by
  have hm := le_trans (le_succ_self one) (Prf.andE₁ h)
  have inputs := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))
  have shape := Prf.andE₂ (Prf.andE₂ inputs)
  exact .andI (Prf.andE₁ inputs) (.andI (Prf.andE₁ (Prf.andE₂ inputs)) (.andI hm shape))

theorem monic_input (f G m a c : PTm n) (h : Γ ⊢[PRAAx] GaussianSuperellipticWordTerms.input f G m a c) :
    Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input (tailRows f m c) G m a c := by
  have rows := GaussianSuperellipticWordTerms.rows_input f G m a c h
  exact .andI (Prf.andE₁ rows) (.andI (GaussianSuperellipticTail.tail_shape f m c (Prf.andE₁ (Prf.andE₂ rows)))
    (Prf.andE₂ (Prf.andE₂ rows)))

theorem cyclic_retained (f G m a c : PTm n) (h : Γ ⊢[PRAAx] GaussianSuperellipticWordTerms.input f G m a c) :
    Γ ⊢[PRAAx] lt (cyclicRank f G m a c) (count m) ⋏ (wordCode m (cyclicRank f G m a c) ≐ rotation f G m a c) :=
  Foundations.RuntimeCyclicPermutation.rotation_listed m (k f G m a c)
    (GaussianSuperellipticCyclicLeading.index_bound f G m a c h)

theorem retained_cyclic_stage (f G m a c : PTm n) (h : Γ ⊢[PRAAx] GaussianSuperellipticWordTerms.input f G m a c) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantDegreeDominance.retainedStage (matrix f G m a c) m (width m a c) (cyclicRank f G m a c) ≐
      stage (matrix f G m a c) m (width m a c) (rotation f G m a c) m :=
  stage_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (Prf.andE₂ (cyclic_retained f G m a c h)) (.eqRefl _)

private theorem different_retained_word (f G m a c r : PTm n)
    (h : Γ ⊢[PRAAx] GaussianSuperellipticWordTerms.input f G m a c)
    (hr : Γ ⊢[PRAAx] lt r (count m)) (hne : Γ ⊢[PRAAx] neg (r ≐ cyclicRank f G m a c)) :
    Γ ⊢[PRAAx] neg (wordCode m r ≐ rotation f G m a c) := by
  have listed := cyclic_retained f G m a c h
  refine .impI (.impE hne.wk ?_)
  exact Foundations.RuntimePermutationWords.retained_position_unique m r (cyclicRank f G m a c)
    hr.wk (Prf.andE₁ listed).wk (Prf.hyp0.eqTrans (Prf.andE₂ listed).wk.eqSymm)

theorem strictly_smaller_stage (f G m a c r : PTm n)
    (h : Γ ⊢[PRAAx] input f G m a c) (hr : Γ ⊢[PRAAx] lt r (count m))
    (hne : Γ ⊢[PRAAx] neg (r ≐ cyclicRank f G m a c))
    (hf : Γ ⊢[PRAAx] flag (GaussianPolynomialDeterminantDegreeDominance.retainedStage
      (matrix f G m a c) m (width m a c) r) (m*width m a c) ≐ one) : Γ ⊢[PRAAx]
    lt (degree (GaussianPolynomialDeterminantDegreeDominance.retainedStage (matrix f G m a c) m (width m a c) r) (m*width m a c))
      (degree (GaussianPolynomialDeterminantDegreeDominance.retainedStage (matrix f G m a c) m (width m a c)
        (cyclicRank f G m a c)) (m*width m a c)) := by
  have frame := word_input f G m a c h
  have coprime := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have wordBound := Foundations.RuntimePermutationWords.retained_bound m r hr
  have valid := (Foundations.RuntimePermutationWords.checker_reflection m (wordCode m r)).iffMpr
    (GaussianPolynomialDeterminant.retained_word m r hr)
  have strict := GaussianSuperellipticWordTerms.stage_degree_strict f G m a c (wordCode m r) frame coprime
    wordBound valid hf (different_retained_word f G m a c r frame hr hne)
  have cyclicDegree := (degree_congr (retained_cyclic_stage f G m a c frame) (.eqRefl _)).eqTrans
    (GaussianSuperellipticWordTerms.rotation_stage_degree f G m a c frame)
  exact lt_congr (.eqRefl _) cyclicDegree.eqSymm strict

theorem original_strict_dominance (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantDegreeDominance.strictDominance (matrix f G m a c) m (width m a c) (cyclicRank f G m a c) := by
  have shifted : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift f) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI (.impI (.impI ?_)))
  simpa [Syn.shift,cyclicRank] using strictly_smaller_stage (Syn.shift f) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c)
    (var 0) shifted.wk.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0

private theorem sign_congr (m : PTm n) {u v : PTm n} (h : Γ ⊢[PRAAx] u ≐ v) :
    Γ ⊢[PRAAx] signPoint m u ≐ signPoint m v := by
  ipra_congr (signPoint (var 0) (var 1) : PTm 2) with [.eqRefl m, h]

theorem original_norm_degree (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) :
    Γ ⊢[PRAAx] certificate f G m a c := by
  let M := matrix f G m a c
  let B := width m a c
  let r := cyclicRank f G m a c
  have frame := word_input f G m a c h
  have listed := cyclic_retained f G m a c frame
  have stageEq := retained_cyclic_stage f G m a c frame
  have flagEq := (flag_congr stageEq (.eqRefl _)).eqTrans (GaussianSuperellipticWordTerms.rotation_stage_success f G m a c frame)
  have exactDegree := (degree_congr stageEq (.eqRefl _)).eqTrans (GaussianSuperellipticWordTerms.rotation_stage_degree f G m a c frame)
  have actualLeading := qmul_congr (sign_congr m (Prf.andE₂ listed))
    ((leading_congr stageEq (.eqRefl _)).eqTrans (GaussianSuperellipticCyclicLeading.cyclic_stage_leading f G m a c frame))
  have dominance := GaussianPolynomialDeterminantDegreeDominance.determinant_dominance M m B r
    (.andI (Prf.andE₁ listed) (.andI flagEq (original_strict_dominance f G m a c h)))
  have returned := GaussianPolynomialMonicNorm.returned_norm (Γ := Γ) (tailRows f m c) G m a c
  exact .andI ((flag_congr returned (.eqRefl _)).eqTrans (Prf.andE₁ dominance))
    (.andI ((degree_congr returned (.eqRefl _)).eqTrans ((Prf.andE₁ (Prf.andE₂ dominance)).eqTrans exactDegree))
      ((leading_congr returned (.eqRefl _)).eqTrans ((Prf.andE₂ (Prf.andE₂ dominance)).eqTrans actualLeading)))

def pointPowers (f m L : PTm n) : Fm PTm n := .all (lt (var 0) (length (Syn.shift L)) ⟶
  power (ordinate (Syn.shift L) (var 0)) (Syn.shift m) ≐ evaluate (Syn.shift f) (abscissa (Syn.shift L) (var 0)))

ipra_subst pointPowers [Syn.subst_shift, Syn.shift_subst]

theorem point_power_at (f m L i : PTm n) (h : Γ ⊢[PRAAx] pointPowers f m L) (hi : Γ ⊢[PRAAx] lt i (length L)) :
    Γ ⊢[PRAAx] power (ordinate L i) m ≐ evaluate f (abscissa L i) := by
  have atPoint : Γ ⊢[PRAAx] lt i (length L) ⟶ power (ordinate L i) m ≐ evaluate f (abscissa L i) := by
    simpa [pointPowers] using h.allE i
  exact .impE atPoint hi

theorem monic_curve_zeros (f m c L : PTm n) (hm : Γ ⊢[PRAAx] le one m) (h : Γ ⊢[PRAAx] pointPowers f m L) :
    Γ ⊢[PRAAx] curveZeros (tailRows f m c) m L := by
  have hmShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hm.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointPowers (Syn.shift f) (Syn.shift m) (Syn.shift L) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa [Syn.shift] using (GaussianSuperellipticTail.curve_equality (Syn.shift f) (Syn.shift m) (Syn.shift c)
    (abscissa (Syn.shift L) (var 0)) (ordinate (Syn.shift L) (var 0)) hmShift.wk).iffMpr
      (point_power_at (Syn.shift f) (Syn.shift m) (Syn.shift L) (var 0) hs.wk Prf.hyp0)

def pointInput (f G m L : PTm n) : Fm PTm n := pointDistinct L ⋏ (pointPowers f m L ⋏ functionZeros G m L)

theorem weighted_zero_bound (f G m a c L : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hPoints : Γ ⊢[PRAAx] pointInput f G m L) : Γ ⊢[PRAAx] le (length L) (weightedDegree G m a (degree f c)) := by
  have frame := word_input f G m a c h
  have monic := monic_input f G m a c frame
  have curve := monic_curve_zeros f m c L (Prf.andE₁ monic) (Prf.andE₁ (Prf.andE₂ hPoints))
  have norm := original_norm_degree f G m a c h
  have sourcePoints := Prf.andI (Prf.andE₁ hPoints) (Prf.andI curve (Prf.andE₂ (Prf.andE₂ hPoints)))
  have bound := GaussianNormFiniteZeroBound.finite_norm_zero_bound (tailRows f m c) G m a c L zero
    (.andI monic (.andI sourcePoints (Prf.andE₁ norm)))
  exact le_congr (.eqRefl _) (Prf.andE₁ (Prf.andE₂ norm)) bound

theorem actual_superelliptic_norm_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ certificate (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (original_norm_degree _ _ _ _ _ Prf.hyp0))

theorem actual_weighted_zero_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ pointInput (var 0) (var 1) (var 2) (var 5) ⟶
      le (length (var 5)) (weightedDegree (var 1) (var 2) (var 3) (degree (var 0) (var 4)))) :=
  closeUniv 6 (.impI (.impI (weighted_zero_bound _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSuperellipticNormDegree
