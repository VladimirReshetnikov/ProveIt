import IPRADerivations.Foundations.RuntimePermutationSums
import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.GaussianSuperellipticMatrixEntries
import IPRADerivations.Analysis.Polynomials.Representation.GaussianPolynomialWeightedDegree
import IPRADerivations.Foundations.AuxiliaryEnvelope

/-!
# Actual weighted degree budgets along numerical permutation words

The matrix row is the actual word digit and the column is its position.
The inverse coefficient indices can repeat; only the word digits are
permutation-reindexed. All sums and the least mismatch are actual numeric
programs. No polynomial degree, leading coefficient or determinant output
law is assumed or proved by this native arithmetic module.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSuperellipticWordWeights

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowIndex (m w j : PTm n) : PTm n := Foundations.RuntimeCyclicPermutation.inverseIndex m j (Foundations.RuntimePermutationWords.digit m w j)
def wrapAt (m w j : PTm n) : PTm n := Foundations.RuntimeCyclicPermutation.wrap m (rowIndex m w j) j
def candidate (G m a d w j : PTm n) : PTm n := GaussianPolynomialWeightedDegree.rowDegree G m a (rowIndex m w j)+d*wrapAt m w j
def rowWeight (G m a d w j : PTm n) : PTm n := GaussianPolynomialWeightedDegree.weight G m a d (rowIndex m w j)
def data (G m a d w : PTm n) : PTm n := pairT (GaussianPolynomialWeightedDegree.data G m a d) w
def fields (p : PTm n) : Fin 5 → PTm n := ![GaussianPolynomialWeightedDegree.fields (fstT p) 0,GaussianPolynomialWeightedDegree.fields (fstT p) 1,
  GaussianPolynomialWeightedDegree.fields (fstT p) 2,GaussianPolynomialWeightedDegree.fields (fstT p) 3,sndT p]
def reader (f : PTm 6) : PTm 2 := Syn.subst
  ![fields (var 1) 0,fields (var 1) 1,fields (var 1) 2,fields (var 1) 3,fields (var 1) 4,var 0] f
def prefixSum (f : PTm 6) (G m a d w j : PTm n) : PTm n := ap2 (sumF (reader f)) j (data G m a d w)
def candidateSchema : PTm 6 := candidate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
def weightSchema : PTm 6 := rowWeight (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
def digitSchema : PTm 6 := var 3*Foundations.RuntimePermutationWords.digit (var 1) (var 4) (var 5)
def positionSchema : PTm 6 := var 3*var 5
def wrapSchema : PTm 6 := wrapAt (var 1) (var 4) (var 5)
def candidatePrefix (G m a d w j : PTm n) : PTm n := prefixSum candidateSchema G m a d w j
def weightPrefix (G m a d w j : PTm n) : PTm n := prefixSum weightSchema G m a d w j
def digitPrefix (G m a d w j : PTm n) : PTm n := prefixSum digitSchema G m a d w j
def positionPrefix (G m a d w j : PTm n) : PTm n := prefixSum positionSchema G m a d w j
def wrapPrefix (m w j : PTm n) : PTm n := prefixSum wrapSchema zero m zero zero w j
def rowFlags (G m a w : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ GaussianPolynomialWeightedDegree.rowFlag (Syn.shift G) (Syn.shift m) (Syn.shift a)
    (rowIndex (Syn.shift m) (Syn.shift w) (var 0)) ≐ one)

ipra_subst rowIndex
ipra_subst wrapAt
ipra_subst candidate
ipra_subst rowWeight
ipra_subst data
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 5) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
@[simp] theorem subst_prefix {l : ℕ} (σ : Fin n → PTm l) (f : PTm 6) (G m a d w j : PTm n) :
    Syn.subst σ (prefixSum f G m a d w j) = prefixSum f (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ w) (Syn.subst σ j) := by simp [prefixSum]
ipra_subst candidatePrefix
ipra_subst weightPrefix
ipra_subst digitPrefix
ipra_subst positionPrefix
ipra_subst wrapPrefix
ipra_subst rowFlags [Syn.subst_shift, Syn.shift_subst]

theorem fields_at (G m a d w : PTm n) (i : Fin 5) : Γ ⊢[PRAAx]
    fields (data G m a d w) i ≐ ![G,m,a,d,w] i := by
  have old (k : Fin 4) : Γ ⊢[PRAAx]
      GaussianPolynomialWeightedDegree.fields (fstT (data G m a d w)) k ≐ ![G,m,a,d] k :=
    pairVectorField_eq 3 ![G,m,a,d] (fst_pair _ _) k
  fin_cases i
  · exact old 0
  · exact old 1
  · exact old 2
  · exact old 3
  · exact snd_pair _ _

private theorem val_five {α : Type} (a b c d e f : α) : ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

theorem reader_at (f : PTm 6) (G m a d w j : PTm n) : Γ ⊢[PRAAx]
    inst2 (reader f) j (data G m a d w) ≐ Syn.subst ![G,m,a,d,w,j] f := by
  have env : (fun i => Syn.subst ![j,data G m a d w]
      (![fields (var 1) 0,fields (var 1) 1,fields (var 1) 2,fields (var 1) 3,fields (var 1) 4,var 0] i)) =
      ![fields (data G m a d w) 0,fields (data G m a d w) 1,fields (data G m a d w) 2,
        fields (data G m a d w) 3,fields (data G m a d w) 4,j] := by
    funext i
    fin_cases i <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',subst_fields,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [reader,inst2,Syn.subst_subst]
  rw [env]
  exact Prf.eqCongr (Γ := Γ) f
    (σ := ![fields (data G m a d w) 0,fields (data G m a d w) 1,fields (data G m a d w) 2,
      fields (data G m a d w) 3,fields (data G m a d w) 4,j])
    (σ' := ![G,m,a,d,w,j]) (fun i => by
      fin_cases i <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ']
      · exact fields_at _ _ _ _ _ 0
      · exact fields_at _ _ _ _ _ 1
      · exact fields_at _ _ _ _ _ 2
      · exact fields_at _ _ _ _ _ 3
      · exact fields_at _ _ _ _ _ 4
      · exact .eqRefl _)

theorem prefix_zero (f : PTm 6) (G m a d w : PTm n) : Γ ⊢[PRAAx] prefixSum f G m a d w zero ≐ zero := sum_zero _ _
theorem prefix_succ (f : PTm 6) (G m a d w j : PTm n) : Γ ⊢[PRAAx]
    prefixSum f G m a d w (succ j) ≐ prefixSum f G m a d w j+Syn.subst ![G,m,a,d,w,j] f :=
  (sum_succ' _ _ _).eqTrans (congrAdd (.eqRefl _) (reader_at _ _ _ _ _ _ _))

theorem candidate_succ (G m a d w j : PTm n) : Γ ⊢[PRAAx]
    candidatePrefix G m a d w (succ j) ≐ candidatePrefix G m a d w j+candidate G m a d w j := by
  simpa only [candidatePrefix,candidateSchema,subst_candidate,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    val_five,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons]
    using prefix_succ (Γ := Γ) candidateSchema G m a d w j
theorem weight_succ (G m a d w j : PTm n) : Γ ⊢[PRAAx]
    weightPrefix G m a d w (succ j) ≐ weightPrefix G m a d w j+rowWeight G m a d w j := by
  simpa only [weightPrefix,weightSchema,subst_rowWeight,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    val_five,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons]
    using prefix_succ (Γ := Γ) weightSchema G m a d w j
theorem digit_succ (G m a d w j : PTm n) : Γ ⊢[PRAAx]
    digitPrefix G m a d w (succ j) ≐ digitPrefix G m a d w j+d*Foundations.RuntimePermutationWords.digit m w j := by
  simpa only [digitPrefix,digitSchema,Foundations.RuntimePermutationWords.subst_digit,PTm.subst_mul,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    val_five,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons]
    using prefix_succ (Γ := Γ) digitSchema G m a d w j
theorem position_succ (G m a d w j : PTm n) : Γ ⊢[PRAAx]
    positionPrefix G m a d w (succ j) ≐ positionPrefix G m a d w j+d*j := by
  simpa only [positionPrefix,positionSchema,PTm.subst_mul,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    val_five,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons]
    using prefix_succ (Γ := Γ) positionSchema G m a d w j

theorem index_bound (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] lt (rowIndex m w j) m :=
  .andE₁ (Foundations.RuntimeCyclicPermutation.inverse_correct _ _ _ hj (Foundations.RuntimePermutationWords.digit_bound _ _ _ hj))
theorem point_balance (G m a d w j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    m*candidate G m a d w j+d*Foundations.RuntimePermutationWords.digit m w j ≐ rowWeight G m a d w j+d*j := by
  unfold candidate rowWeight GaussianPolynomialWeightedDegree.weight wrapAt rowIndex
  ipra_lc -(Groth.ι (IPRA.Q.mk _ d))*natEq (GaussianSuperellipticMatrixEntries.index_equation m (Foundations.RuntimePermutationWords.digit m w j) j (Foundations.RuntimePermutationWords.digit_bound _ _ _ hj) hj)

theorem prefix_balance (G m a d w j : PTm n) (hj : Γ ⊢[PRAAx] le j m) : Γ ⊢[PRAAx]
    m*candidatePrefix G m a d w j+digitPrefix G m a d w j ≐
      weightPrefix G m a d w j+positionPrefix G m a d w j := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift m) ⟶
      Syn.shift m*candidatePrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0)+
        digitPrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0) ≐
      weightPrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0)+
        positionPrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_le, subst_candidatePrefix, subst_digitPrefix, subst_weightPrefix,
        subst_positionPrefix]
    · refine .impI ?_
      unfold candidatePrefix digitPrefix weightPrefix positionPrefix
      have z : (le zero m :: Γ) ⊢[PRAAx] m*zero+zero ≐ zero+zero := by ipra_ring
      exact (congrAdd (congrMul (.eqRefl _) (prefix_zero _ _ _ _ _ _)) (prefix_zero _ _ _ _ _ _)).eqTrans
        (z.eqTrans (congrAdd (prefix_zero _ _ _ _ _ _).eqSymm (prefix_zero _ _ _ _ _ _).eqSymm))
    · refine .impI ?_
      let Δ := (le (succ (var 0)) (Syn.shift m)) ::
        (le (var 0) (Syn.shift m) ⟶ Syn.shift m*candidatePrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0)+
            digitPrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0) ≐
          weightPrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0)+
            positionPrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0)) :: Γ.map Fm.shift
      have h : Δ ⊢[PRAAx] Syn.shift m*candidatePrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0)+
            digitPrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0) ≐
          weightPrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0)+
            positionPrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0) :=
        Prf.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have e := point_balance (Γ := Δ) (Syn.shift G) (Syn.shift m)
        (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0) Prf.hyp0
      have sc := candidate_succ (Γ := Δ) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0)
      have sd := digit_succ (Γ := Δ) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0)
      have sw := weight_succ (Γ := Δ) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0)
      have sp := position_succ (Γ := Δ) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0)
      change Δ ⊢[PRAAx] Syn.shift m*candidatePrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (succ (var 0))+
        digitPrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (succ (var 0)) ≐
        weightPrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (succ (var 0))+
        positionPrefix (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (succ (var 0))
      ipra_lc natEq h+natEq e+(Groth.ι (IPRA.Q.mk _ (Syn.shift m)))*natEq sc+natEq sd-natEq sw-natEq sp
  have endp := all.allE j
  simp only [Fm.subst_imp,Fm.subst_eq,subst_le,PTm.subst_add,PTm.subst_mul,
    subst_candidatePrefix,subst_digitPrefix,subst_weightPrefix,subst_positionPrefix,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] at endp
  exact .impE endp hj

def linearBody : PTm 2 := var 1*var 0

theorem digit_position (G m a d w : PTm n)
    (hw : Γ ⊢[PRAAx] lt w (Foundations.RuntimePermutationWords.horizon m))
    (hp : Γ ⊢[PRAAx] Foundations.RuntimePermutationWords.permutationBit m w ≐ one) : Γ ⊢[PRAAx]
    digitPrefix G m a d w m ≐ positionPrefix G m a d w m := by
  have lo : Γ ⊢[PRAAx] digitPrefix G m a d w m ≐
      Foundations.RuntimePermutationSums.total linearBody m w d := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have e := reader_at (Γ := Δ) digitSchema (Syn.shift G) (Syn.shift m) (Syn.shift a)
      (Syn.shift d) (Syn.shift w) (var 0)
    have u := Foundations.RuntimePermutationSums.reader_at (Γ := Δ) linearBody (Syn.shift m)
      (Syn.shift w) (Syn.shift d) (var 0)
    have leq : Δ ⊢[PRAAx] inst2 (reader digitSchema) (var 0)
        (data (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w)) ≐
        Syn.shift d*Foundations.RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (var 0) := by
      simpa only [digitSchema,Foundations.RuntimePermutationWords.subst_digit,PTm.subst_mul,Syn.subst_var,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.cons_val_four,val_five,Matrix.head_cons,Matrix.tail_cons] using e
    have ueq : Δ ⊢[PRAAx] inst2 (Foundations.RuntimePermutationSums.reader linearBody) (var 0)
        (Foundations.RuntimePermutationSums.data (Syn.shift m) (Syn.shift w) (Syn.shift d)) ≐
        Syn.shift d*Foundations.RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (var 0) := by
      simpa only [Foundations.RuntimePermutationSums.read,linearBody,inst2,PTm.subst_mul,
        Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using u
    simpa only [Δ,Syn.shift,Foundations.RuntimePermutationSums.subst_data,subst_data]
      using leq.eqTrans ueq.eqSymm
  have hi : Γ ⊢[PRAAx] positionPrefix G m a d w m ≐
      Foundations.RuntimePermutationSums.ordinary linearBody m d := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    have e := reader_at (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) positionSchema
      (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0)
    simpa only [positionSchema,linearBody,subst_data,Syn.shift,PTm.subst_mul,inst2,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,val_five,Matrix.head_cons,Matrix.tail_cons] using e
  exact lo.eqTrans ((Foundations.RuntimePermutationSums.permutation_sum _ _ _ _ hw hp).eqTrans hi.eqSymm)

theorem word_balance (G m a d w : PTm n)
    (hw : Γ ⊢[PRAAx] lt w (Foundations.RuntimePermutationWords.horizon m))
    (hp : Γ ⊢[PRAAx] Foundations.RuntimePermutationWords.permutationBit m w ≐ one) : Γ ⊢[PRAAx]
    m*candidatePrefix G m a d w m ≐ weightPrefix G m a d w m :=
  add_right_cancel ((congrAdd (.eqRefl _) (digit_position _ _ _ _ _ hw hp).eqSymm).eqTrans
    (prefix_balance _ _ _ _ _ _ (le_refl _)))

theorem row_flags_at (G m a w j : PTm n) (h : Γ ⊢[PRAAx] rowFlags G m a w)
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    GaussianPolynomialWeightedDegree.rowFlag G m a (rowIndex m w j) ≐ one := by
  have rule : Γ ⊢[PRAAx] lt j m ⟶ GaussianPolynomialWeightedDegree.rowFlag G m a (rowIndex m w j) ≐ one := by
    simpa only [rowFlags,Fm.subst_imp,Fm.subst_eq,subst_lt,GaussianPolynomialWeightedDegree.subst_rowFlag,
      subst_rowIndex,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using h.allE j
  exact .impE rule hj

theorem weight_body_at (G m a d w j : PTm n) : Γ ⊢[PRAAx]
    inst2 (reader weightSchema) j (data G m a d w) ≐ rowWeight G m a d w j := by
  simpa only [weightSchema,subst_rowWeight,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,val_five,Matrix.head_cons,Matrix.tail_cons]
    using reader_at (Γ := Γ) weightSchema G m a d w j

theorem weight_sum_bound (G m a d w : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.input G m a)
    (hRows : Γ ⊢[PRAAx] rowFlags G m a w) : Γ ⊢[PRAAx]
    le (weightPrefix G m a d w m) (m*GaussianPolynomialWeightedDegree.weightedDegree G m a d) := by
  apply Foundations.AuxiliaryEnvelope.sum_le_const (reader weightSchema)
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianPolynomialWeightedDegree.input (Syn.shift G) (Syn.shift m) (Syn.shift a) := by
    simpa only [Fm.shift,GaussianPolynomialWeightedDegree.subst_input,Syn.shift] using hInput.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] rowFlags (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift w) := by
    simpa only [Fm.shift,subst_rowFlags,Syn.shift] using hRows.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have b := GaussianPolynomialWeightedDegree.weight_le_max (Γ := Δ) (Syn.shift G) (Syn.shift m) (Syn.shift a)
    (Syn.shift d) (rowIndex (Syn.shift m) (Syn.shift w) (var 0)) (.andE₂ (.andE₂ hs.wk))
    (index_bound _ _ _ Prf.hyp0) (row_flags_at _ _ _ _ _ rs.wk Prf.hyp0)
  simpa only [Δ,Syn.shift,subst_data,GaussianPolynomialWeightedDegree.subst_weightedDegree] using
    le_congr (weight_body_at (Γ := Δ) (Syn.shift G) (Syn.shift m) (Syn.shift a)
      (Syn.shift d) (Syn.shift w) (var 0)).eqSymm (.eqRefl _) b

theorem word_degree_le (G m a d w : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.input G m a)
    (hw : Γ ⊢[PRAAx] lt w (Foundations.RuntimePermutationWords.horizon m))
    (hp : Γ ⊢[PRAAx] Foundations.RuntimePermutationWords.permutationBit m w ≐ one)
    (hRows : Γ ⊢[PRAAx] rowFlags G m a w) : Γ ⊢[PRAAx]
    le (candidatePrefix G m a d w m) (GaussianPolynomialWeightedDegree.weightedDegree G m a d) := by
  have h := le_congr (word_balance G m a d w hw hp).eqSymm (.eqRefl _) (weight_sum_bound G m a d w hInput hRows)
  have form := RationalIntegerNormalization.positive_form (.andE₁ hInput)
  exact mul_le_cancel (le_congr (congrMul form (.eqRefl _)) (congrMul form (.eqRefl _)) h)

def matchSchema : PTm 6 := eqb (rowIndex (var 1) (var 4) (var 5))
  (GaussianPolynomialWeightedDegree.index (var 0) (var 1) (var 2) (var 3))
def firstBad (G m a d w : PTm n) : PTm n := Search.mu (reader matchSchema) m (data G m a d w)
ipra_subst firstBad
theorem match_body_at (G m a d w j : PTm n) : Γ ⊢[PRAAx]
    inst2 (reader matchSchema) j (data G m a d w) ≐
      eqb (rowIndex m w j) (GaussianPolynomialWeightedDegree.index G m a d) := by
  simpa only [matchSchema,subst_eqb,subst_rowIndex,GaussianPolynomialWeightedDegree.subst_index,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,val_five,Matrix.head_cons,Matrix.tail_cons]
    using reader_at (Γ := Γ) matchSchema G m a d w j

theorem no_bad_index (G m a d w j : PTm n)
    (hBad : Γ ⊢[PRAAx] firstBad G m a d w ≐ m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    rowIndex m w j ≐ GaussianPolynomialWeightedDegree.index G m a d := by
  have h := Search.search_minimal (f := reader matchSchema)
    (lt_congr (.eqRefl _) hBad.eqSymm hj)
  apply AnalyticNumberTheory.Valuation.eq_of_eqb_ne
  exact .impI (.impE h.wk ((match_body_at _ _ _ _ _ _).wk.eqTrans Prf.hyp0))

theorem no_bad_rotation (G m a d w : PTm n)
    (hw : Γ ⊢[PRAAx] lt w (Foundations.RuntimePermutationWords.horizon m))
    (hBad : Γ ⊢[PRAAx] firstBad G m a d w ≐ m) : Γ ⊢[PRAAx]
    w ≐ Foundations.RuntimeCyclicPermutation.rotationCode m (GaussianPolynomialWeightedDegree.index G m a d) := by
  apply Foundations.RuntimeCyclicPermutation.rotation_unique _ _ _ hw
  have hs : Γ.map Fm.shift ⊢[PRAAx] firstBad (Syn.shift G) (Syn.shift m) (Syn.shift a)
      (Syn.shift d) (Syn.shift w) ≐ Syn.shift m := by
    simpa only [Fm.shift,Fm.subst_eq,subst_firstBad,Syn.shift] using hBad.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have e := no_bad_index (Γ := Δ) (Syn.shift G) (Syn.shift m) (Syn.shift a)
    (Syn.shift d) (Syn.shift w) (var 0) hs.wk Prf.hyp0
  have inv := GaussianSuperellipticMatrixEntries.inverse_row (Γ := Δ) (Syn.shift m)
    (Foundations.RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (var 0)) (var 0)
    (Foundations.RuntimePermutationWords.digit_bound _ _ _ Prf.hyp0) Prf.hyp0
  have r : Δ ⊢[PRAAx] Foundations.RuntimeCyclicPermutation.rotation (Syn.shift m)
      (rowIndex (Syn.shift m) (Syn.shift w) (var 0)) (var 0) ≐
    Foundations.RuntimeCyclicPermutation.rotation (Syn.shift m)
      (GaussianPolynomialWeightedDegree.index (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d)) (var 0) := by
    ipra_congr (Foundations.RuntimeCyclicPermutation.rotation (var 0) (var 1) (var 2) : PTm 3) with
      [.eqRefl (Syn.shift m), e, .eqRefl (var 0)]
  simpa only [Δ,Syn.shift,GaussianPolynomialWeightedDegree.subst_index] using inv.eqSymm.eqTrans r

theorem first_bad_found (G m a d w : PTm n)
    (hw : Γ ⊢[PRAAx] lt w (Foundations.RuntimePermutationWords.horizon m))
    (hne : Γ ⊢[PRAAx] neg (w ≐ Foundations.RuntimeCyclicPermutation.rotationCode m
      (GaussianPolynomialWeightedDegree.index G m a d))) : Γ ⊢[PRAAx]
    lt (firstBad G m a d w) m ⋏ neg (rowIndex m w (firstBad G m a d w) ≐ GaussianPolynomialWeightedDegree.index G m a d) := by
  have hb : Γ ⊢[PRAAx] lt (firstBad G m a d w) m := by
    refine .orE (lt_or_eq_of_le (.andE₁ (Search.search_spec (f := reader matchSchema) m zero (data G m a d w)))) Prf.hyp0 ?_
    exact .botE _ (.impE hne.wk (no_bad_rotation _ _ _ _ _ hw.wk Prf.hyp0))
  have hz := Prf.impE (.andE₁ (.andE₂ (Search.search_spec (f := reader matchSchema) m zero (data G m a d w)))) hb
  exact .andI hb (AnalyticNumberTheory.Valuation.ne_of_eqb_zero ((match_body_at _ _ _ _ _ _).eqSymm.eqTrans hz))

theorem row_weight_index_congr (G m a d w i j : PTm n) (h : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx]
    rowWeight G m a d w i ≐ rowWeight G m a d w j := by
  simpa only [subst_rowWeight,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,val_five,Matrix.head_cons,Matrix.tail_cons]
    using Prf.eqCongr (Γ := Γ) (rowWeight (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![G,m,a,d,w,i]) (σ' := ![G,m,a,d,w,j]) (fun k => by
        fin_cases k <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ']
        · exact .eqRefl _
        · exact .eqRefl _
        · exact .eqRefl _
        · exact .eqRefl _
        · exact .eqRefl _
        · exact h)

def liftedWeight : PTm 2 := inst2 (reader weightSchema) (var 0) (sndT (var 1))
def bonusBody : PTm 2 := liftedWeight+dB (one : PTm 2)

private theorem lifted_inst (j b p : PTm n) : inst2 liftedWeight j (pairT b p) =
    inst2 (reader weightSchema) j (sndT (pairT b p)) := by
  simp only [liftedWeight,inst2,Syn.subst_subst]
  congr 1
  funext i
  fin_cases i <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]

theorem lifted_at (j b p : PTm n) : Γ ⊢[PRAAx]
    inst2 liftedWeight j (pairT b p) ≐ inst2 (reader weightSchema) j p := by
  rw [lifted_inst]
  exact congrInst2 _ (.eqRefl _) (snd_pair _ _)

theorem bonus_body_at (G m a d w b j : PTm n) : Γ ⊢[PRAAx]
    inst2 bonusBody j (pairT b (data G m a d w)) ≐ rowWeight G m a d w j+eqb b j := by
  have e := (lifted_at (Γ := Γ) j b (data G m a d w)).eqTrans (weight_body_at G m a d w j)
  have de : Γ ⊢[PRAAx] inst2 (dB (one : PTm 2)) j (pairT b (data G m a d w)) ≐ eqb b j := by
    rw [inst2_dB]
    simp only [inst2,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
    change Γ ⊢[PRAAx] eqb (fstT (pairT b (data G m a d w))) j*one ≐ eqb b j
    exact (congrMul (AnalyticNumberTheory.Euler.congrEqb (fst_pair b (data G m a d w)) (.eqRefl j))
      (.eqRefl one)).eqTrans (by ipra_ring)
  simpa only [bonusBody,inst2,PTm.subst_add] using congrAdd e de

theorem bonus_sum (G m a d w b : PTm n) (hb : Γ ⊢[PRAAx] lt b m) : Γ ⊢[PRAAx]
    ap2 (sumF bonusBody) m (pairT b (data G m a d w)) ≐ weightPrefix G m a d w m+one := by
  have old : Γ ⊢[PRAAx] ap2 (sumF liftedWeight) m (pairT b (data G m a d w)) ≐ weightPrefix G m a d w m := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_pairT,subst_data] using
      lifted_at (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) (var 0) (Syn.shift b)
        (data (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w))
  exact (sum_add liftedWeight (dB (one : PTm 2)) _ _).eqTrans
    (congrAdd old (by simpa only [inst2,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using sum_delta (one : PTm 2) (x := data G m a d w) hb))

theorem strict_weight_sum (G m a d w b : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.input G m a)
    (hg : Γ ⊢[PRAAx] gcd m d ≐ one) (hRows : Γ ⊢[PRAAx] rowFlags G m a w)
    (hb : Γ ⊢[PRAAx] lt b m)
    (hne : Γ ⊢[PRAAx] neg (rowIndex m w b ≐ GaussianPolynomialWeightedDegree.index G m a d)) : Γ ⊢[PRAAx]
    le (weightPrefix G m a d w m+one) (m*GaussianPolynomialWeightedDegree.weightedDegree G m a d) := by
  have hi : Γ.map Fm.shift ⊢[PRAAx] GaussianPolynomialWeightedDegree.input (Syn.shift G) (Syn.shift m) (Syn.shift a) := by
    simpa only [Fm.shift,GaussianPolynomialWeightedDegree.subst_input,Syn.shift] using hInput.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] rowFlags (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift w) := by
    simpa only [Fm.shift,subst_rowFlags,Syn.shift] using hRows.shift
  have st := GaussianPolynomialWeightedDegree.strict_below G m a d (rowIndex m w b) (.andE₁ hInput) hg
    (.andE₂ (.andE₂ hInput)) (index_bound _ _ _ hb) (row_flags_at _ _ _ _ _ hRows hb) hne
  have ss : Γ.map Fm.shift ⊢[PRAAx] le (succ (rowWeight (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (Syn.shift b)))
      (GaussianPolynomialWeightedDegree.weightedDegree (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d)) := by
    simpa only [Fm.shift,subst_lt,subst_le,ConciseIPRA.PTm.subst_succ,lt,rowWeight,subst_rowWeight,GaussianPolynomialWeightedDegree.subst_weight,
      GaussianPolynomialWeightedDegree.subst_weightedDegree,subst_rowIndex,Syn.shift] using st.shift
  have bound : Γ ⊢[PRAAx] le (ap2 (sumF bonusBody) m (pairT b (data G m a d w)))
      (m*GaussianPolynomialWeightedDegree.weightedDegree G m a d) := by
    apply Foundations.AuxiliaryEnvelope.sum_le_const bonusBody
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have point : Δ ⊢[PRAAx] le
        (rowWeight (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (var 0)+eqb (Syn.shift b) (var 0))
        (GaussianPolynomialWeightedDegree.weightedDegree (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d)) := by
      refine .orE (eq_or_ne (Syn.shift b) (var 0)) ?_ ?_
      · have eqw := row_weight_index_congr (Γ := (Syn.shift b ≐ var 0) :: Δ)
          (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (Syn.shift w) (Syn.shift b) (var 0) Prf.hyp0
        exact le_congr ((succ_eq_add_one _).eqTrans (congrAdd eqw (eqb_of_eq Prf.hyp0).eqSymm))
          (.eqRefl _) ss.wk.wk
      · have bnd := GaussianPolynomialWeightedDegree.weight_le_max (Γ := neg (Syn.shift b ≐ var 0) :: Δ)
          (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d) (rowIndex (Syn.shift m) (Syn.shift w) (var 0))
          (.andE₂ (.andE₂ hi.wk.wk)) (index_bound _ _ _ Prf.hyp1) (row_flags_at _ _ _ _ _ rs.wk.wk Prf.hyp1)
        exact le_congr ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) (eqb_of_ne Prf.hyp0).eqSymm))
          (.eqRefl _) bnd
    simpa only [Δ,Syn.shift,subst_pairT,subst_data,GaussianPolynomialWeightedDegree.subst_weightedDegree] using
      le_congr (bonus_body_at (Γ := Δ) (Syn.shift G) (Syn.shift m) (Syn.shift a)
        (Syn.shift d) (Syn.shift w) (Syn.shift b) (var 0)).eqSymm (.eqRefl _) point
  exact le_congr (bonus_sum G m a d w b hb) (.eqRefl _) bound

theorem word_degree_strict (G m a d w : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.input G m a)
    (hg : Γ ⊢[PRAAx] gcd m d ≐ one)
    (hw : Γ ⊢[PRAAx] lt w (Foundations.RuntimePermutationWords.horizon m))
    (hp : Γ ⊢[PRAAx] Foundations.RuntimePermutationWords.permutationBit m w ≐ one)
    (hRows : Γ ⊢[PRAAx] rowFlags G m a w)
    (hne : Γ ⊢[PRAAx] neg (w ≐ Foundations.RuntimeCyclicPermutation.rotationCode m
      (GaussianPolynomialWeightedDegree.index G m a d))) : Γ ⊢[PRAAx]
    lt (candidatePrefix G m a d w m) (GaussianPolynomialWeightedDegree.weightedDegree G m a d) := by
  have bad := first_bad_found G m a d w hw hne
  have st := strict_weight_sum G m a d w (firstBad G m a d w) hInput hg hRows (.andE₁ bad) (.andE₂ bad)
  refine .orE (lt_or_le (candidatePrefix G m a d w m) (GaussianPolynomialWeightedDegree.weightedDegree G m a d)) Prf.hyp0 ?_
  have bk : (le (GaussianPolynomialWeightedDegree.weightedDegree G m a d) (candidatePrefix G m a d w m)) :: Γ ⊢[PRAAx]
      le (m*GaussianPolynomialWeightedDegree.weightedDegree G m a d) (m*candidatePrefix G m a d w m) :=
    AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl m) Prf.hyp0
  have bd : (le (GaussianPolynomialWeightedDegree.weightedDegree G m a d) (candidatePrefix G m a d w m)) :: Γ ⊢[PRAAx]
      le (m*GaussianPolynomialWeightedDegree.weightedDegree G m a d) (weightPrefix G m a d w m) :=
    le_congr (.eqRefl _) (word_balance G m a d w hw.wk hp.wk) bk
  exact not_succ_le_self (weightPrefix G m a d w m) _
    (le_trans (le_congr (succ_eq_add_one _).eqSymm (.eqRefl _) st.wk) bd)

theorem rotation_index (m k j : PTm n) (hk : Γ ⊢[PRAAx] lt k m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    rowIndex m (Foundations.RuntimeCyclicPermutation.rotationCode m k) j ≐ k := by
  have digit := (Foundations.RuntimeCyclicPermutation.rotation_digit m k j hj).eqTrans
    (GaussianSuperellipticMatrixEntries.rotation_comm m k j)
  have e : Γ ⊢[PRAAx] rowIndex m (Foundations.RuntimeCyclicPermutation.rotationCode m k) j ≐
      Foundations.RuntimeCyclicPermutation.inverseIndex m j (Foundations.RuntimeCyclicPermutation.rotation m j k) := by
    ipra_congr (Foundations.RuntimeCyclicPermutation.inverseIndex (var 0) (var 1) (var 2) : PTm 3) with
      [.eqRefl m, .eqRefl j, digit] using [rowIndex]
  exact e.eqTrans (Foundations.RuntimeCyclicPermutation.inverse_rotation m j k hj hk)

theorem rotation_wrap_at (m k j : PTm n) (hk : Γ ⊢[PRAAx] lt k m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    wrapAt m (Foundations.RuntimeCyclicPermutation.rotationCode m k) j ≐ Foundations.RuntimeCyclicPermutation.wrap m k j := by
  ipra_congr (Foundations.RuntimeCyclicPermutation.wrap (var 0) (var 1) (var 2) : PTm 3) with
    [.eqRefl m, rotation_index m k j hk hj, .eqRefl j] using [wrapAt]

theorem wrap_zero (m w : PTm n) : Γ ⊢[PRAAx] wrapPrefix m w zero ≐ zero := prefix_zero _ _ _ _ _ _
theorem wrap_succ (m w j : PTm n) : Γ ⊢[PRAAx]
    wrapPrefix m w (succ j) ≐ wrapPrefix m w j+wrapAt m w j := by
  simpa only [wrapPrefix,wrapSchema,subst_wrapAt,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_four,val_five,Matrix.head_cons,Matrix.tail_cons]
    using prefix_succ (Γ := Γ) wrapSchema zero m zero zero w j

theorem rotation_wrap_total (m k : PTm n) (hk : Γ ⊢[PRAAx] lt k m) : Γ ⊢[PRAAx]
    wrapPrefix m (Foundations.RuntimeCyclicPermutation.rotationCode m k) m ≐ k := by
  have eq : Γ ⊢[PRAAx] wrapPrefix m (Foundations.RuntimeCyclicPermutation.rotationCode m k) m ≐
      Foundations.RuntimeCyclicPermutation.wrapCount m k := by
    apply sum_congr_bounded
    have ks : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift k) (Syn.shift m) := by
      simpa only [Fm.shift,subst_lt,Syn.shift] using hk.shift
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have lo : Δ ⊢[PRAAx] inst2 (reader wrapSchema) (var 0)
        (data zero (Syn.shift m) zero zero (Foundations.RuntimeCyclicPermutation.rotationCode (Syn.shift m) (Syn.shift k))) ≐
        wrapAt (Syn.shift m) (Foundations.RuntimeCyclicPermutation.rotationCode (Syn.shift m) (Syn.shift k)) (var 0) := by
      simpa only [wrapSchema,subst_wrapAt,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_four,
        val_five,Matrix.head_cons,Matrix.tail_cons] using reader_at (Γ := Δ) wrapSchema zero (Syn.shift m) zero zero
          (Foundations.RuntimeCyclicPermutation.rotationCode (Syn.shift m) (Syn.shift k)) (var 0)
    simpa only [Δ,Syn.shift,subst_data,subst_pairT,ConciseIPRA.PTm.subst_zero,
      Foundations.RuntimeCyclicPermutation.subst_rotationCode] using
      lo.eqTrans ((rotation_wrap_at _ _ _ ks.wk Prf.hyp0).eqTrans
        (Foundations.RuntimeCyclicPermutation.wrap_body_at _ _ _).eqSymm)
  exact eq.eqTrans (Foundations.RuntimeCyclicPermutation.wrap_count m k hk)

theorem rotation_weight_at (G m a d k j : PTm n) (hk : Γ ⊢[PRAAx] lt k m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    rowWeight G m a d (Foundations.RuntimeCyclicPermutation.rotationCode m k) j ≐ GaussianPolynomialWeightedDegree.weight G m a d k := by
  ipra_congr (GaussianPolynomialWeightedDegree.weight (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
    [.eqRefl G, .eqRefl m, .eqRefl a, .eqRefl d, rotation_index m k j hk hj] using [rowWeight]

theorem rotation_candidate_weight (G m a d k : PTm n) (hk : Γ ⊢[PRAAx] lt k m) : Γ ⊢[PRAAx]
    candidatePrefix G m a d (Foundations.RuntimeCyclicPermutation.rotationCode m k) m ≐
      GaussianPolynomialWeightedDegree.weight G m a d k := by
  have weights : Γ ⊢[PRAAx] weightPrefix G m a d (Foundations.RuntimeCyclicPermutation.rotationCode m k) m ≐
      m*GaussianPolynomialWeightedDegree.weight G m a d k := by
    apply Probability.Variance.sum_const_of (reader weightSchema)
    have ks : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift k) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hk.shift
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    simpa only [Δ,Syn.shift,subst_data,Foundations.RuntimeCyclicPermutation.subst_rotationCode,
      GaussianPolynomialWeightedDegree.subst_weight] using
      (weight_body_at (Γ := Δ) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d)
        (Foundations.RuntimeCyclicPermutation.rotationCode (Syn.shift m) (Syn.shift k)) (var 0)).eqTrans
        (rotation_weight_at _ _ _ _ _ _ ks.wk Prf.hyp0)
  have h := (word_balance G m a d (Foundations.RuntimeCyclicPermutation.rotationCode m k)
    (Foundations.RuntimeCyclicPermutation.rotation_code_bound _ _)
    (Foundations.RuntimeCyclicPermutation.rotation_checker _ _ hk)).eqTrans weights
  exact Combinatorics.BinomialIdentities.mul_cancel
    (RationalIntegerNormalization.positive_form (lt_of_le_of_lt (zero_le k) hk)) h

theorem rotation_candidate (G m a d : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.input G m a) : Γ ⊢[PRAAx]
    candidatePrefix G m a d (Foundations.RuntimeCyclicPermutation.rotationCode m
      (GaussianPolynomialWeightedDegree.index G m a d)) m ≐ GaussianPolynomialWeightedDegree.weightedDegree G m a d :=
  (rotation_candidate_weight G m a d (GaussianPolynomialWeightedDegree.index G m a d)
    (.andE₁ (GaussianPolynomialWeightedDegree.index_attains G m a d (.andE₁ hInput)))).eqTrans
    (GaussianPolynomialWeightedDegree.maximum_eq_weight G m a d (.andE₁ hInput) (.andE₂ (.andE₂ hInput))).eqSymm

theorem rotation_row_flags (G m a d : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.input G m a) : Γ ⊢[PRAAx]
    rowFlags G m a (Foundations.RuntimeCyclicPermutation.rotationCode m (GaussianPolynomialWeightedDegree.index G m a d)) := by
  have ks : Γ.map Fm.shift ⊢[PRAAx] lt
      (GaussianPolynomialWeightedDegree.index (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d)) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,GaussianPolynomialWeightedDegree.subst_index,Syn.shift] using
      (Prf.andE₁ (GaussianPolynomialWeightedDegree.index_attains G m a d (.andE₁ hInput))).shift
  have fs : Γ.map Fm.shift ⊢[PRAAx] GaussianPolynomialWeightedDegree.rowFlag (Syn.shift G) (Syn.shift m) (Syn.shift a)
      (GaussianPolynomialWeightedDegree.index (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d)) ≐ one := by
    simpa only [Fm.shift,Fm.subst_eq,GaussianPolynomialWeightedDegree.subst_rowFlag,
      GaussianPolynomialWeightedDegree.subst_index,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
      (GaussianPolynomialWeightedDegree.selected_flag_one G m a d (.andE₁ hInput) (.andE₂ (.andE₂ hInput))).shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have e := rotation_index (Γ := Δ) (Syn.shift m)
    (GaussianPolynomialWeightedDegree.index (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d)) (var 0) ks.wk Prf.hyp0
  have fl : Δ ⊢[PRAAx] GaussianPolynomialWeightedDegree.rowFlag (Syn.shift G) (Syn.shift m) (Syn.shift a)
      (rowIndex (Syn.shift m) (Foundations.RuntimeCyclicPermutation.rotationCode (Syn.shift m)
        (GaussianPolynomialWeightedDegree.index (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d))) (var 0)) ≐
      GaussianPolynomialWeightedDegree.rowFlag (Syn.shift G) (Syn.shift m) (Syn.shift a)
        (GaussianPolynomialWeightedDegree.index (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift d)) := by
    ipra_congr (GaussianPolynomialWeightedDegree.rowFlag (var 0) (var 1) (var 2) (var 3) : PTm 4) with
      [.eqRefl (Syn.shift G), .eqRefl (Syn.shift m), .eqRefl (Syn.shift a), e]
  simpa only [Δ,Syn.shift,Foundations.RuntimeCyclicPermutation.subst_rotationCode,
    GaussianPolynomialWeightedDegree.subst_index] using fl.eqTrans fs.wk

/-! These are local native helper guards. Actual nonzero determinant terms
must derive rowFlags before applying them; no output law is a guard. -/
def wordInput (G m a _d w : PTm n) : Fm PTm n := GaussianPolynomialWeightedDegree.input G m a ⋏
  (lt w (Foundations.RuntimePermutationWords.horizon m) ⋏
    ((Foundations.RuntimePermutationWords.permutationBit m w ≐ one) ⋏ rowFlags G m a w))
def strictInput (G m a d w : PTm n) : Fm PTm n := wordInput G m a d w ⋏
  ((gcd m d ≐ one) ⋏ neg (w ≐ Foundations.RuntimeCyclicPermutation.rotationCode m
    (GaussianPolynomialWeightedDegree.index G m a d)))
ipra_subst wordInput
@[simp] theorem subst_strictInput {l : ℕ} (σ : Fin n → PTm l) (G m a d w : PTm n) :
    (strictInput G m a d w).subst σ = strictInput (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ w) := by
  have hg (u v : PTm n) : Syn.subst σ (gcd u v) = gcd (Syn.subst σ u) (Syn.subst σ v) := by
    simp only [gcd,subst_ex2,ConciseIPRA.PTm.subst_succ]
  simp only [strictInput,Fm.subst_and,Fm.subst_eq,subst_neg,subst_wordInput,hg,
    Foundations.RuntimeCyclicPermutation.subst_rotationCode,GaussianPolynomialWeightedDegree.subst_index,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
theorem weak_from_input (G m a d w : PTm n) (h : Γ ⊢[PRAAx] wordInput G m a d w) : Γ ⊢[PRAAx]
    le (candidatePrefix G m a d w m) (GaussianPolynomialWeightedDegree.weightedDegree G m a d) :=
  word_degree_le G m a d w (.andE₁ h) (.andE₁ (.andE₂ h)) (.andE₁ (.andE₂ (.andE₂ h))) (.andE₂ (.andE₂ (.andE₂ h)))
theorem strict_from_input (G m a d w : PTm n) (h : Γ ⊢[PRAAx] strictInput G m a d w) : Γ ⊢[PRAAx]
    lt (candidatePrefix G m a d w m) (GaussianPolynomialWeightedDegree.weightedDegree G m a d) :=
  word_degree_strict G m a d w (.andE₁ (.andE₁ h)) (.andE₁ (.andE₂ h))
    (.andE₁ (.andE₂ (.andE₁ h))) (.andE₁ (.andE₂ (.andE₂ (.andE₁ h))))
    (.andE₂ (.andE₂ (.andE₂ (.andE₁ h)))) (.andE₂ (.andE₂ h))

/-! Actual PR5 returns the candidate sum, original-row weight sum, actual
selected row, computed maximum and actual wrap sum. -/
def output (G m a d w : PTm n) : PTm n := pairT (candidatePrefix G m a d w m)
  (pairT (weightPrefix G m a d w m) (pairT (GaussianPolynomialWeightedDegree.index G m a d)
    (pairT (GaussianPolynomialWeightedDegree.weightedDegree G m a d) (wrapPrefix m w m))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (G m a d w : PTm n) : PTm n := app outputF ![G,m,a,d,w]
def outputField (p : PTm n) (i : Fin 5) : PTm n := ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),
  fstT (sndT (sndT (sndT p))),sndT (sndT (sndT (sndT p)))] i
ipra_subst output
ipra_subst run
@[simp] theorem subst_outputField {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 5) :
    Syn.subst σ (outputField p i) = outputField (Syn.subst σ p) i := by fin_cases i <;> simp [outputField]
theorem program_at (G m a d w : PTm n) : Γ ⊢[PRAAx] run G m a d w ≐ output G m a d w := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![G,m,a,d,w]
theorem returned_fields (G m a d w : PTm n) (i : Fin 5) : Γ ⊢[PRAAx]
    outputField (run G m a d w) i ≐ ![candidatePrefix G m a d w m,weightPrefix G m a d w m,
      GaussianPolynomialWeightedDegree.index G m a d,GaussianPolynomialWeightedDegree.weightedDegree G m a d,wrapPrefix m w m] i :=
  pairVectorField_eq 4 _ (program_at G m a d w) i
theorem returned_weak_bound (G m a d w : PTm n) (h : Γ ⊢[PRAAx] wordInput G m a d w) : Γ ⊢[PRAAx]
    le (outputField (run G m a d w) 0) (outputField (run G m a d w) 3) :=
  le_congr (returned_fields _ _ _ _ _ 0).eqSymm (returned_fields _ _ _ _ _ 3).eqSymm (weak_from_input _ _ _ _ _ h)

theorem actual_point_balance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (var 1) ⟶ var 1*candidate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)+
      var 3*Foundations.RuntimePermutationWords.digit (var 1) (var 4) (var 5) ≐
        rowWeight (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)+var 3*var 5) :=
  closeUniv 6 (.impI (point_balance _ _ _ _ _ _ Prf.hyp0))
theorem actual_prefix_balance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (var 1) ⟶ var 1*candidatePrefix (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)+
      digitPrefix (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐
        weightPrefix (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)+positionPrefix (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (prefix_balance _ _ _ _ _ _ Prf.hyp0))
theorem actual_word_balance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (Foundations.RuntimePermutationWords.horizon (var 1)) ⟶
      Foundations.RuntimePermutationWords.permutationBit (var 1) (var 4) ≐ one ⟶
        var 1*candidatePrefix (var 0) (var 1) (var 2) (var 3) (var 4) (var 1) ≐
          weightPrefix (var 0) (var 1) (var 2) (var 3) (var 4) (var 1)) :=
  closeUniv 5 (.impI (.impI (word_balance _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_weak_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (wordInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      le (candidatePrefix (var 0) (var 1) (var 2) (var 3) (var 4) (var 1))
        (GaussianPolynomialWeightedDegree.weightedDegree (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (weak_from_input _ _ _ _ _ Prf.hyp0))
theorem actual_strict_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (strictInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      lt (candidatePrefix (var 0) (var 1) (var 2) (var 3) (var 4) (var 1))
        (GaussianPolynomialWeightedDegree.weightedDegree (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (strict_from_input _ _ _ _ _ Prf.hyp0))
theorem actual_mismatch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (Foundations.RuntimePermutationWords.horizon (var 1)) ⟶
      neg (var 4 ≐ Foundations.RuntimeCyclicPermutation.rotationCode (var 1)
        (GaussianPolynomialWeightedDegree.index (var 0) (var 1) (var 2) (var 3))) ⟶
        (lt (firstBad (var 0) (var 1) (var 2) (var 3) (var 4)) (var 1) ⋏
          neg (rowIndex (var 1) (var 4) (firstBad (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
            GaussianPolynomialWeightedDegree.index (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 5 (.impI (.impI (first_bad_found _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rotation_index_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (var 0) ⟶ lt (var 2) (var 0) ⟶
      rowIndex (var 0) (Foundations.RuntimeCyclicPermutation.rotationCode (var 0) (var 1)) (var 2) ≐ var 1) :=
  closeUniv 3 (.impI (.impI (rotation_index _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rotation_wrap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (var 0) ⟶ wrapPrefix (var 0) (Foundations.RuntimeCyclicPermutation.rotationCode (var 0) (var 1)) (var 0) ≐ var 1) :=
  closeUniv 2 (.impI (rotation_wrap_total _ _ Prf.hyp0))
theorem actual_rotation_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianPolynomialWeightedDegree.input (var 0) (var 1) (var 2) ⟶
      candidatePrefix (var 0) (var 1) (var 2) (var 3)
        (Foundations.RuntimeCyclicPermutation.rotationCode (var 1)
          (GaussianPolynomialWeightedDegree.index (var 0) (var 1) (var 2) (var 3))) (var 1) ≐
            GaussianPolynomialWeightedDegree.weightedDegree (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (rotation_candidate _ _ _ _ Prf.hyp0))
theorem actual_rotation_flags_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianPolynomialWeightedDegree.input (var 0) (var 1) (var 2) ⟶
      rowFlags (var 0) (var 1) (var 2) (Foundations.RuntimeCyclicPermutation.rotationCode (var 1)
        (GaussianPolynomialWeightedDegree.index (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (rotation_row_flags _ _ _ _ Prf.hyp0))
theorem actual_empty_prefixes_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((candidatePrefix (var 0) (var 1) (var 2) (var 3) (var 4) zero ≐ zero) ⋏
      ((weightPrefix (var 0) (var 1) (var 2) (var 3) (var 4) zero ≐ zero) ⋏
        (wrapPrefix (var 1) (var 4) zero ≐ zero))) :=
  closeUniv 5 (.andI (prefix_zero _ _ _ _ _ _) (.andI (prefix_zero _ _ _ _ _ _) (wrap_zero _ _)))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (wordInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      le (outputField (run (var 0) (var 1) (var 2) (var 3) (var 4)) 0)
        (outputField (run (var 0) (var 1) (var 2) (var 3) (var 4)) 3)) :=
  closeUniv 5 (.impI (returned_weak_bound _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSuperellipticWordWeights
