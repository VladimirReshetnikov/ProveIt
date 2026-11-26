import IPRADerivations.Analysis.Polynomials.Annihilators.GaussianAnnihilatorPolynomial
import IPRADerivations.Analysis.Polynomials.Elimination.Bivariate.GaussianBivariateFlatSum
import IPRADerivations.Analysis.Polynomials.Elimination.RowReduction.GaussianRationalRowElimination

/-!
# Evaluation of the compiled annihilator

The original bivariate evaluator sums over the full rectangle of
exponents. The coefficient compiler vanishes on rejected labels and
reads the coefficient vector at the enumeration rank on retained
labels. Filtering the full sum therefore gives the ordinary dot
product with the actual weighted monomial evaluation vector.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianAnnihilatorPolynomialEvaluation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianAnnihilatorPolynomial
  (polynomial polynomial_shape polynomial_coefficient coefficient_kept coefficient_rejected)
open GaussianBivariateFlatSum (flatBody flat_body_at flat_expansion)
open GaussianRationalBlockSums (filteredData selectedBody maskBody mask_zero mask_kept filtered_sum selected_list_at)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (evaluate qmul qzero)
open GaussianRationalMonicReduction (singleton singleton_lookup)
open GaussianRationalReciprocal (power powerF)
open GaussianRationalRowElimination (rowDot dotData dotBody dot_body_at)
open GaussianRationalSyntheticCoefficientValues (qmul_recode_left)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_left)
open GaussianPolynomialMonicCompanion (values)
open GaussianWeightedMonomialBasis (horizon decodeX decodeY keep keepBody count labels evaluationVector)
open LeanProofs.IPRA.Foundations.BoundedReflection (sgB)
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def valueData (a m d L x y : PTm n) : PTm n :=
  pairT (GaussianAnnihilatorPolynomial.data a m d L) (pairT x y)

def valueTerm (a m d L x y h : PTm n) : PTm n :=
  qmul (entry a (rank keepBody h (GaussianWeightedMonomialBasis.data m d L)))
    (qmul (power x (decodeX L h)) (power y (decodeY L h)))

def valueBody : PTm 2 :=
  valueTerm (GaussianAnnihilatorPolynomial.fields (fstT (var 1)) 0)
    (GaussianAnnihilatorPolynomial.fields (fstT (var 1)) 1)
    (GaussianAnnihilatorPolynomial.fields (fstT (var 1)) 2)
    (GaussianAnnihilatorPolynomial.fields (fstT (var 1)) 3)
    (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)

@[simp] theorem subst_valueData {k : ℕ} (σ : Fin n → PTm k) (a m d L x y : PTm n) :
    Syn.subst σ (valueData a m d L x y) = valueData (Syn.subst σ a) (Syn.subst σ m)
      (Syn.subst σ d) (Syn.subst σ L) (Syn.subst σ x) (Syn.subst σ y) := by simp [valueData]

@[simp] theorem subst_valueTerm {k : ℕ} (σ : Fin n → PTm k) (a m d L x y h : PTm n) :
    Syn.subst σ (valueTerm a m d L x y h) = valueTerm (Syn.subst σ a) (Syn.subst σ m)
      (Syn.subst σ d) (Syn.subst σ L) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ h) := by
  simp [valueTerm,rank]

private theorem value_parameters {a a' m m' d d' L L' x x' y y' : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hm : Γ ⊢[PRAAx] m ≐ m') (hd : Γ ⊢[PRAAx] d ≐ d')
    (hL : Γ ⊢[PRAAx] L ≐ L') (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') (h : PTm n) :
    Γ ⊢[PRAAx] valueTerm a m d L x y h ≐ valueTerm a' m' d' L' x' y' h := by
  have datum := congrPairT hm (congrPairT hd hL)
  have xExponent := congrAp2 remF (.eqRefl h) (congrSucc hL)
  have yExponent := congrAp2 quoF (.eqRefl h) (congrSucc hL)
  exact qmul_congr (entry_congr ha (congrAp2 (sumF (sgB keepBody)) (.eqRefl h) datum))
    (qmul_congr (congrAp2 powerF xExponent hx) (congrAp2 powerF yExponent hy))

theorem value_body_at (a m d L x y h : PTm n) : Γ ⊢[PRAAx]
    inst2 valueBody h (valueData a m d L x y) ≐ valueTerm a m d L x y h := by
  have field (i : Fin 4) : Γ ⊢[PRAAx]
      GaussianAnnihilatorPolynomial.fields (fstT (valueData a m d L x y)) i ≐ ![a,m,d,L] i :=
    (GaussianAnnihilatorPolynomial.field_congr i (fst_pair _ _)).eqTrans
      (GaussianAnnihilatorPolynomial.fields_at a m d L i)
  have xy : Γ ⊢[PRAAx] sndT (valueData a m d L x y) ≐ pairT x y := snd_pair _ _
  simpa only [valueBody,inst2,subst_valueTerm,GaussianAnnihilatorPolynomial.subst_fields,subst_fstT,
    subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons] using
      value_parameters (field 0) (field 1) (field 2) (field 3)
        ((congrFst xy).eqTrans (fst_pair x y)) ((congrSnd xy).eqTrans (snd_pair x y)) h

theorem flat_body_is_masked (a m d L x y h : PTm n) (hh : Γ ⊢[PRAAx] lt h (horizon m L)) :
    Γ ⊢[PRAAx] inst2 flatBody h (GaussianBivariatePowerExpansion.data (polynomial a m d L) m L x y) ≐
      inst2 (maskBody keepBody valueBody) h (pairT (GaussianWeightedMonomialBasis.data m d L) (valueData a m d L x y)) := by
  let p := GaussianWeightedMonomialBasis.data m d L
  let i := decodeY L h
  let j := decodeX L h
  let u := qmul (power x j) (power y i)
  have bounds := GaussianWeightedMonomialBasis.decode_bounds m L h hh
  have read : Γ ⊢[PRAAx] inst2 flatBody h (GaussianBivariatePowerExpansion.data (polynomial a m d L) m L x y) ≐
      qmul (GaussianAnnihilatorPolynomial.coefficient a m d L i j) u :=
    (flat_body_at (polynomial a m d L) m L x y h).eqTrans
      (qmul_congr (polynomial_coefficient a m d L i j (.andE₁ bounds) (.andE₂ bounds)) (.eqRefl u))
  have flag := GaussianWeightedMonomialBasis.keep_body_at (Γ := Γ) m d L h
  have labelEq := GaussianWeightedMonomialBasis.label_decode (Γ := Γ) L h
  have labelFlag := GaussianWeightedMonomialBasis.keep_congr (.eqRefl m) (.eqRefl d) (.eqRefl L) labelEq
  refine .orE (eq_or_ne (keep m d L h) zero) ?_ ?_
  · have termZero := coefficient_rejected a m d L i j (labelFlag.wk.eqTrans Prf.hyp0)
    have maskedZero := mask_zero keepBody valueBody p (valueData a m d L x y) h (flag.wk.eqTrans Prf.hyp0)
    exact read.wk.eqTrans ((qmul_congr termZero (.eqRefl u)).eqTrans ((qmul_zero_left u).eqTrans maskedZero.eqSymm))
  · have valid := Prf.andI (Prf.andE₁ bounds).wk (GaussianWeightedMonomialBasis.keep_bound m d L h Prf.hyp0)
    have coefficient := coefficient_kept a m d L i j valid
    have rankEq := congrAp2 (sumF (sgB keepBody)) labelEq (.eqRefl p)
    have entryEq := entry_congr (.eqRefl a) rankEq
    have kept := mask_kept keepBody valueBody p (valueData a m d L x y) h
      (.impI (.impE Prf.hyp1 (flag.wk.wk.eqSymm.eqTrans Prf.hyp0)))
    exact read.wk.eqTrans ((qmul_congr coefficient (.eqRefl u)).eqTrans
      ((qmul_recode_left _ u).eqTrans ((qmul_congr entryEq.wk (.eqRefl u)).eqTrans
        ((value_body_at a m d L x y h).eqSymm.eqTrans kept.eqSymm))))

theorem selected_body_is_dot (a m d L x y r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) :
    Γ ⊢[PRAAx] inst2 (selectedBody keepBody valueBody) r
      (filteredData (horizon m L) (GaussianWeightedMonomialBasis.data m d L) (valueData a m d L x y)) ≐
      inst2 dotBody r (dotData (singleton (evaluationVector m d L x y)) a zero) := by
  let h := entry (labels m d L) r
  let u := qmul (power x (decodeX L h)) (power y (decodeY L h))
  let v := evaluationVector m d L x y
  have xp := GaussianWeightedMonomialBasis.basis_X m d L r hr
  have yp := GaussianWeightedMonomialBasis.basis_Y m d L r hr
  have evalEntry : Γ ⊢[PRAAx] entry v r ≐ u :=
    (GaussianWeightedMonomialBasis.evaluation_lookup m d L x y r hr).eqTrans
      (qmul_congr (congrAp2 powerF xp (.eqRefl x)) (congrAp2 powerF yp (.eqRefl y)))
  have rankEntry := entry_congr (.eqRefl a) (GaussianWeightedMonomialBasis.label_rank m d L r hr)
  have matrixEntry := entry_congr (singleton_lookup (Γ := Γ) v) (.eqRefl r)
  exact (selected_list_at keepBody valueBody (horizon m L) (GaussianWeightedMonomialBasis.data m d L)
    (valueData a m d L x y) r hr).eqTrans ((value_body_at a m d L x y h).eqTrans
    ((qmul_congr rankEntry (.eqRefl u)).eqTrans ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      ((qmul_congr (matrixEntry.eqTrans evalEntry).eqSymm (.eqRefl _)).eqTrans
        (dot_body_at (singleton v) a zero r).eqSymm))))

theorem evaluation_equals_dot (a m d L x y : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    evaluate (values (polynomial a m d L) m x) y ≐ rowDot (singleton (evaluationVector m d L x y)) (count m d L) a zero := by
  let p := GaussianWeightedMonomialBasis.data m d L
  have masked : Γ ⊢[PRAAx] GaussianBivariateFlatSum.flatSum (polynomial a m d L) m L x y ≐
      sum (maskBody keepBody valueBody) (horizon m L) (pairT p (valueData a m d L x y)) := by
    refine GaussianRationalFiniteSum.sum_congr_bounded flatBody (maskBody keepBody valueBody) (horizon m L)
      (GaussianBivariatePowerExpansion.data (polynomial a m d L) m L x y)
      (pairT p (valueData a m d L x y)) (.allI (.impI ?_))
    simpa [Syn.shift,p] using flat_body_is_masked (Syn.shift a) (Syn.shift m) (Syn.shift d) (Syn.shift L)
      (Syn.shift x) (Syn.shift y) (var 0) Prf.hyp0
  have selected : Γ ⊢[PRAAx] sum (selectedBody keepBody valueBody) (count m d L)
      (filteredData (horizon m L) p (valueData a m d L x y)) ≐
      rowDot (singleton (evaluationVector m d L x y)) (count m d L) a zero := by
    refine GaussianRationalFiniteSum.sum_congr_bounded (selectedBody keepBody valueBody) dotBody (count m d L)
      (filteredData (horizon m L) p (valueData a m d L x y))
      (dotData (singleton (evaluationVector m d L x y)) a zero) (.allI (.impI ?_))
    simpa [Syn.shift,p] using selected_body_is_dot (Syn.shift a) (Syn.shift m) (Syn.shift d) (Syn.shift L)
      (Syn.shift x) (Syn.shift y) (var 0) Prf.hyp0
  exact (flat_expansion (polynomial a m d L) m L x y hm (polynomial_shape a m d L)).eqTrans
    (masked.eqTrans ((filtered_sum keepBody valueBody (horizon m L) p (valueData a m d L x y)).eqSymm.eqTrans selected))

theorem actual_compiled_evaluation_equals_dot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ evaluate (values (polynomial (var 0) (var 1) (var 2) (var 3)) (var 1) (var 4)) (var 5) ≐
      rowDot (singleton (evaluationVector (var 1) (var 2) (var 3) (var 4) (var 5)))
        (count (var 1) (var 2) (var 3)) (var 0) zero) :=
  closeUniv 6 (.impI (evaluation_equals_dot _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianAnnihilatorPolynomialEvaluation
