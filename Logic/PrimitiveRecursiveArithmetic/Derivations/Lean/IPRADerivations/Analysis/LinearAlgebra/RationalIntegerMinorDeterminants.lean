import IPRADerivations.Analysis.RationalArithmetic.RationalSelectedMinors
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianL1
import IPRADerivations.Foundations.RuntimePermutationFactorialBound

/-!
# Integer values and size bounds for the actual minor determinants

The original rational determinant program uses the same finite
permutation products and signed sums when every matrix entry is integral.
Its output is a denominator-one rational. The signed numerator bound is
proved from the original integer entry bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalIntegerMinorDeterminants

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_neg zabs_tri)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalIntegerNormalization (normalize integerCode)
open RationalArithmetic (represents)
open RationalGaussianEmbedding (scalarOne)
open GaussianRationalHorner (scalar_congr)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def content (q B : PTm n) : Fm PTm n := denominatorOf q ≐ one ⋏ le (zabs (numeratorOf q)) B

@[simp] theorem subst_content {k : ℕ} (σ : Fin n → PTm k) (q B : PTm n) :
    (content q B).subst σ = content (Syn.subst σ q) (Syn.subst σ B) := by
  simp only [content,Fm.subst_and,Fm.subst_eq,subst_le,RationalSupMetric.subst_denominatorOf,
    Foundations.GapDecision.subst_zabs,RationalSupMetric.subst_numeratorOf,one,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]

theorem denominator_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] denominatorOf a ≐ denominatorOf b :=
  congrSucc (congrSnd h)

theorem numerator_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] ZT.eq (numeratorOf a) (numeratorOf b) := by
  apply ZT.derive
  simp only [numeratorOf,ZT.toZ]
  rw [natEq (congrFst (congrFst h)),natEq (congrSnd (congrFst h))]

theorem content_congr {a b A B : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) (he : Γ ⊢[PRAAx] A ≐ B)
    (ha : Γ ⊢[PRAAx] content a A) : Γ ⊢[PRAAx] content b B :=
  .andI ((denominator_congr h).eqSymm.eqTrans (.andE₁ ha))
    (le_congr (zabs_congr (ZT.toZ_eq (numerator_congr h))) he (.andE₂ ha))

theorem integer_code_denominator (a : ZT n) : Γ ⊢[PRAAx] denominatorOf (integerCode a) ≐ one :=
  congrSucc (snd_pair _ zero)

theorem normalize_unit_denominator (a : ZT n) : Γ ⊢[PRAAx] denominatorOf (normalize a one) ≐ one := by
  have e : Γ ⊢[PRAAx] ZT.eq a (ZT.ofNat one*a) := by
    apply ZT.derive
    simp [ZT.toZ_mul]
  exact (denominator_congr (RationalIntegerNormalization.normalize_integer a a one (le_refl one) e)).eqTrans
    (integer_code_denominator a)

theorem represented_integer_numerator (q : PTm n) (a : ZT n) (h : Γ ⊢[PRAAx] represents q a one)
    (hu : Γ ⊢[PRAAx] denominatorOf q ≐ one) : Γ ⊢[PRAAx] ZT.eq (numeratorOf q) a := by
  apply ZT.derive
  have e := ZT.toZ_eq h
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,natEq hu,Q.mk_one,map_one,mul_one] at e
  exact e.symm

theorem normalize_content (a : ZT n) (B : PTm n) (h : Γ ⊢[PRAAx] le (zabs a) B) :
    Γ ⊢[PRAAx] content (normalize a one) B := by
  have hd := normalize_unit_denominator (Γ := Γ) a
  have v := represented_integer_numerator _ _ (RationalIntegerNormalization.normalize_preserves_value a one (le_refl one)) hd
  exact .andI hd (le_congr (zabs_congr (ZT.toZ_eq v)).eqSymm (.eqRefl _) h)

theorem content_of_integer_representation (q B : PTm n) (a : ZT n) (hq : Γ ⊢[PRAAx] RationalNormalForm.wellFormed q)
    (rep : Γ ⊢[PRAAx] represents q a one) (h : Γ ⊢[PRAAx] le (zabs a) B) : Γ ⊢[PRAAx] content q B := by
  have e : Γ ⊢[PRAAx] normalize a one ≐ q :=
    RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
      hq (RationalIntegerNormalization.normalize_preserves_value a one (le_refl one)) rep
      (le_refl one) (le_refl one) (ZT.derive rfl)
  exact content_congr e (.eqRefl _) (normalize_content a B h)

theorem denominator_one_representation (q : PTm n) (h : Γ ⊢[PRAAx] denominatorOf q ≐ one) :
    Γ ⊢[PRAAx] represents q (numeratorOf q) one :=
  scalar_congr (.eqRefl _) (ZT.derive rfl) h (RationalRepresentations.represents_self q)

theorem one_content : Γ ⊢[PRAAx] content (scalarOne : PTm n) one := by
  apply normalize_content (ZT.ofNat one) one
  exact le_congr (GaussianL1.abs_ofNat one).eqSymm (.eqRefl _) (le_refl _)

theorem zero_sum_content (t : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] content (RationalFiniteSum.sum t zero x) zero := by
  have zeroNorm : Γ ⊢[PRAAx] normalize (ZT.ofNat zero) one ≐ integerCode (ZT.ofNat zero) :=
    RationalIntegerNormalization.normalize_integer _ _ _ (le_refl _) (by apply ZT.derive; simp [ZT.toZ_mul])
  exact content_congr (zeroNorm.eqTrans (RationalFiniteSum.sum_zero t x).eqSymm) (.eqRefl _)
    (normalize_content (ZT.ofNat zero) zero (le_congr (GaussianL1.abs_ofNat zero).eqSymm (.eqRefl _) (le_refl _)))

theorem add_content (a b A B : PTm n) (ha : Γ ⊢[PRAAx] content a A) (hb : Γ ⊢[PRAAx] content b B) :
    Γ ⊢[PRAAx] content (RationalArithmetic.add a b) (A+B) := by
  have rep := RationalRepresentations.represents_add a b _ _ one one
    (denominator_one_representation a (.andE₁ ha)) (denominator_one_representation b (.andE₁ hb))
  have r : Γ ⊢[PRAAx] represents (RationalArithmetic.add a b) (numeratorOf a+numeratorOf b) one :=
    scalar_congr (.eqRefl _) (by apply ZT.derive; simp [ZT.toZ_mul,ZT.toZ_add]) (one_mul one) rep
  exact content_of_integer_representation _ _ _ (RationalArithmetic.add_guard a b) r
    (le_trans (zabs_tri (ZT.toZ_add _ _)) (add_le_add₂ (.andE₂ ha) (.andE₂ hb)))

theorem multiply_content (a b A B : PTm n) (ha : Γ ⊢[PRAAx] content a A) (hb : Γ ⊢[PRAAx] content b B) :
    Γ ⊢[PRAAx] content (RationalArithmetic.multiply a b) (A*B) := by
  have rep := RationalRepresentations.represents_multiply a b _ _ one one
    (denominator_one_representation a (.andE₁ ha)) (denominator_one_representation b (.andE₁ hb))
  have r : Γ ⊢[PRAAx] represents (RationalArithmetic.multiply a b) (numeratorOf a*numeratorOf b) one :=
    scalar_congr (.eqRefl _) (ZT.derive rfl) (one_mul one) rep
  exact content_of_integer_representation _ _ _ (RationalArithmetic.multiply_guard a b) r
    (le_congr (GaussianL1.abs_multiply _ _).eqSymm (.eqRefl _) (le_mul_mono (.andE₂ ha) (.andE₂ hb)))

theorem negative_content (a A : PTm n) (ha : Γ ⊢[PRAAx] content a A) :
    Γ ⊢[PRAAx] content (RationalArithmetic.negative a) A :=
  content_of_integer_representation _ _ _ (RationalArithmetic.negative_guard a)
    (RationalRepresentations.represents_negative a _ one (denominator_one_representation a (.andE₁ ha)))
    (le_congr (zabs_neg _).eqSymm (.eqRefl _) (.andE₂ ha))

open RationalScalarDeterminantGaussianEmbedding (product rawProduct sign signedTerm determinant signedBody)
open RationalFiniteSum (sum)

def termBounds (t : PTm 2) (N x B : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ content (inst2 t (var 0) (Syn.shift x)) (Syn.shift B))

theorem product_content (t : PTm 2) (N x B : PTm n) (h : Γ ⊢[PRAAx] termBounds t N x B) :
    Γ ⊢[PRAAx] content (product t N x) (pw B N) := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      content (product t (var 0) (Syn.shift x)) (pw (Syn.shift B) (var 0))) := by
    refine PRA.qfInd _ ⟨le_QF _ _,⟨trivial,le_QF _ _⟩⟩ ?_ ?_
    · simp only [Fm.subst_imp,subst_le,subst_content,RationalScalarDeterminantGaussianEmbedding.subst_product,
        subst_ap2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (content_congr (RationalScalarDeterminantGaussianEmbedding.product_zero _ _).eqSymm
        (pw_zero _).eqSymm one_content)
    · simp only [Fm.subst_imp,subst_le,subst_content,RationalScalarDeterminantGaussianEmbedding.subst_product,
        subst_ap2,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let i : PTm (n+1) := var 0
      let Δ := le (succ i) (Syn.shift N) ::
        (le i (Syn.shift N) ⟶ content (product t i (Syn.shift x)) (pw (Syn.shift B) i)) :: Γ.map Fm.shift
      have next : Δ ⊢[PRAAx] content (inst2 t i (Syn.shift x)) (Syn.shift B) := Prf.impE h.allOpen.wk.wk Prf.hyp0
      have previous : Δ ⊢[PRAAx] content (product t i (Syn.shift x)) (pw (Syn.shift B) i) :=
        Prf.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      exact content_congr (RationalScalarDeterminantGaussianEmbedding.product_succ _ _ _).eqSymm (pw_succ _ _).eqSymm
        (multiply_content _ _ _ _ previous next)
  have atN : Γ ⊢[PRAAx] le N N ⟶ content (product t N x) (pw B N) := by
    simpa only [Fm.subst_imp,subst_le,subst_content,RationalScalarDeterminantGaussianEmbedding.subst_product,
      subst_ap2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact .impE atN (le_refl _)

theorem sum_content (t : PTm 2) (N x B : PTm n) (h : Γ ⊢[PRAAx] termBounds t N x B) :
    Γ ⊢[PRAAx] content (sum t N x) (N*B) := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      content (sum t (var 0) (Syn.shift x)) (var 0*Syn.shift B)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,⟨trivial,le_QF _ _⟩⟩ ?_ ?_
    · simp only [Fm.subst_imp,subst_le,subst_content,RationalFiniteSum.subst_sum,
        PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (content_congr (.eqRefl _) (zero_mul _).eqSymm (zero_sum_content _ _))
    · simp only [Fm.subst_imp,subst_le,subst_content,RationalFiniteSum.subst_sum,
        PTm.subst_mul,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let i : PTm (n+1) := var 0
      let Δ := le (succ i) (Syn.shift N) ::
        (le i (Syn.shift N) ⟶ content (sum t i (Syn.shift x)) (i*Syn.shift B)) :: Γ.map Fm.shift
      have next : Δ ⊢[PRAAx] content (RationalFiniteSum.term t i (Syn.shift x)) (Syn.shift B) :=
        Prf.impE h.allOpen.wk.wk Prf.hyp0
      have previous : Δ ⊢[PRAAx] content (sum t i (Syn.shift x)) (i*Syn.shift B) :=
        Prf.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      exact content_congr (RationalFiniteSum.sum_succ _ _ _).eqSymm (succ_mul _ _).eqSymm
        (add_content _ _ _ _ previous next)
  have atN : Γ ⊢[PRAAx] le N N ⟶ content (sum t N x) (N*B) := by
    simpa only [Fm.subst_imp,subst_le,subst_content,RationalFiniteSum.subst_sum,
      PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact .impE atN (le_refl _)

open GaussianPolynomialDeterminantTerms (cell)
open GaussianPolynomialDeterminant (wordCode)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (count digit digit_bound parity_cases)
open LeanProofs.IPRA.Foundations.RuntimePermutationFactorialBound (factorial count_factorial_bound)

def rowBounds (A m B i : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift m) ⟶ content (cell (Syn.shift A) (Syn.shift i) (var 0)) (Syn.shift B))
def matrixBounds (A m B : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift m) ⟶ rowBounds (Syn.shift A) (Syn.shift m) (Syn.shift B) (var 0))

@[simp] theorem subst_rowBounds {k : ℕ} (σ : Fin n → PTm k) (A m B i : PTm n) :
    (rowBounds A m B i).subst σ = rowBounds (Syn.subst σ A) (Syn.subst σ m) (Syn.subst σ B) (Syn.subst σ i) := by
  simp [rowBounds,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_matrixBounds {k : ℕ} (σ : Fin n → PTm k) (A m B : PTm n) :
    (matrixBounds A m B).subst σ = matrixBounds (Syn.subst σ A) (Syn.subst σ m) (Syn.subst σ B) := by
  simp [matrixBounds,Syn.subst_shift,Syn.shift_subst]

theorem matrix_bound_at (A m B i j : PTm n) (h : Γ ⊢[PRAAx] matrixBounds A m B)
    (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] content (cell A i j) B := by
  have r : Γ ⊢[PRAAx] lt i m ⟶ rowBounds A m B i := by simpa [matrixBounds] using h.allE i
  have c : Γ ⊢[PRAAx] lt j m ⟶ content (cell A i j) B := by simpa [rowBounds] using (Prf.impE r hi).allE j
  exact .impE c hj

theorem raw_product_content (A m w B : PTm n) (h : Γ ⊢[PRAAx] matrixBounds A m B) :
    Γ ⊢[PRAAx] content (rawProduct A m w) (pw B m) := by
  refine product_content GaussianScalarDeterminant.factorBody m (GaussianScalarDeterminant.factorData A m w) B ?_
  refine .allI (.impI ?_)
  let a := Syn.shift A
  let k := Syn.shift m
  let b := Syn.shift B
  let u := Syn.shift w
  let Δ := lt (var 0) k :: Γ.map Fm.shift
  have hx : Δ ⊢[PRAAx] matrixBounds a k b := by simpa [Δ,a,k,b,Fm.shift,Syn.shift] using h.shift.wk
  have hi : Δ ⊢[PRAAx] lt (var 0) k := Prf.hyp0
  have cellB := matrix_bound_at a k b (digit k u (var 0)) (var 0) hx (digit_bound k u _ hi) hi
  have actual := content_congr (GaussianScalarDeterminant.factor_body_at a k u (var 0)).eqSymm (.eqRefl _) cellB
  simpa [Δ,a,k,b,u,Syn.shift] using actual

theorem sign_content (m w : PTm n) : Γ ⊢[PRAAx] content (sign m w) one := by
  refine .orE (parity_cases m w) ?_ ?_
  · exact content_congr (RationalScalarDeterminantGaussianEmbedding.sign_even m w Prf.hyp0).eqSymm (.eqRefl _) one_content
  · exact content_congr (RationalScalarDeterminantGaussianEmbedding.sign_odd m w Prf.hyp0).eqSymm (.eqRefl _)
      (negative_content _ _ one_content)

theorem signed_term_content (A m t B : PTm n) (h : Γ ⊢[PRAAx] matrixBounds A m B) :
    Γ ⊢[PRAAx] content (signedTerm A m t) (pw B m) :=
  content_congr (.eqRefl _) (one_mul _)
    (multiply_content _ _ _ _ (sign_content m (wordCode m t)) (raw_product_content A m (wordCode m t) B h))

theorem determinant_content (A m B : PTm n) (h : Γ ⊢[PRAAx] matrixBounds A m B) :
    Γ ⊢[PRAAx] content (determinant A m) (factorial m*pw B m) := by
  have terms : Γ ⊢[PRAAx] termBounds signedBody (count m) (pairT A m) (pw B m) := by
    refine .allI (.impI ?_)
    let a := Syn.shift A
    let k := Syn.shift m
    let b := Syn.shift B
    let Δ := lt (var 0) (count k) :: Γ.map Fm.shift
    have hx : Δ ⊢[PRAAx] matrixBounds a k b := by simpa [Δ,a,k,b,Fm.shift,Syn.shift] using h.shift.wk
    have e := RationalScalarDeterminantGaussianEmbedding.signed_body_at (Γ := Δ) a k (var 0)
    simpa [Δ,a,k,b,Syn.shift,RationalFiniteSum.term] using
      content_congr e.eqSymm (.eqRefl _) (signed_term_content a k (var 0) b hx)
  have s := sum_content _ _ _ _ terms
  exact .andI (.andE₁ s) (le_trans (.andE₂ s) (mul_le_mul_right _ (count_factorial_bound m)))

open RationalSelectedMinors (index normalized normalized_lookup)
open RationalMatrixClearingBounds (inputMatrix entryCap cleared_entry_bound)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

theorem cleared_minor_matrix_bounds (P d R C k H : PTm n) (h : Γ ⊢[PRAAx] inputMatrix P d H)
    (hR : Γ ⊢[PRAAx] k ≐ RationalSelectedMinors.count (length P) R) (hC : Γ ⊢[PRAAx] k ≐ RationalSelectedMinors.count d C) :
    Γ ⊢[PRAAx] matrixBounds (normalized P d R C) k (entryCap P d H) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let shift2 (t : PTm n) := Syn.shift (Syn.shift t)
  let W := shift2 P
  let D := shift2 d
  let K := shift2 k
  let L := shift2 R
  let M := shift2 C
  let B := shift2 H
  let Δ := lt (var 0) K :: lt (var 1) K :: (Γ.map Fm.shift).map Fm.shift
  have hb : Δ ⊢[PRAAx] inputMatrix W D B := by simpa [Δ,W,D,B,K,shift2,Fm.shift,Syn.shift] using h.shift.shift.wk.wk
  have hr : Δ ⊢[PRAAx] K ≐ RationalSelectedMinors.count (length W) L := by
    simpa [Δ,W,L,K,shift2,Fm.shift,Syn.shift] using hR.shift.shift.wk.wk
  have hc : Δ ⊢[PRAAx] K ≐ RationalSelectedMinors.count D M := by
    simpa [Δ,D,M,K,shift2,Fm.shift,Syn.shift] using hC.shift.shift.wk.wk
  have ri : Δ ⊢[PRAAx] lt (var 1) (RationalSelectedMinors.count (length W) L) := lt_congr (.eqRefl _) hr Prf.hyp1
  have ci : Δ ⊢[PRAAx] lt (var 0) (RationalSelectedMinors.count D M) := lt_congr (.eqRefl _) hc Prf.hyp0
  have bound := cleared_entry_bound W D B (index (length W) L (var 1)) (index D M (var 0)) hb
    (RationalSelectedMinors.index_bound _ _ _ ri) (RationalSelectedMinors.index_bound _ _ _ ci)
  have e := normalized_lookup W D L M (var 1) (var 0) ri ci
  simpa [Δ,W,D,L,M,B,K,shift2,Fm.shift,Syn.shift] using content_congr e.eqSymm (.eqRefl _) (normalize_content _ _ bound)

theorem cleared_minor_determinant_content (P d R C k H : PTm n) (h : Γ ⊢[PRAAx] inputMatrix P d H)
    (hR : Γ ⊢[PRAAx] k ≐ RationalSelectedMinors.count (length P) R) (hC : Γ ⊢[PRAAx] k ≐ RationalSelectedMinors.count d C) :
    Γ ⊢[PRAAx] content (determinant (normalized P d R C) k) (factorial k*pw (entryCap P d H) k) :=
  determinant_content _ _ _ (cleared_minor_matrix_bounds P d R C k H h hR hC)

theorem actual_integer_minor_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (inputMatrix (var 0) (var 1) (var 5) ⟶ var 4 ≐ RationalSelectedMinors.count (length (var 0)) (var 2) ⟶
      var 4 ≐ RationalSelectedMinors.count (var 1) (var 3) ⟶
      content (determinant (normalized (var 0) (var 1) (var 2) (var 3)) (var 4))
        (factorial (var 4)*pw (entryCap (var 0) (var 1) (var 5)) (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (cleared_minor_determinant_content (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
    (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalIntegerMinorDeterminants
