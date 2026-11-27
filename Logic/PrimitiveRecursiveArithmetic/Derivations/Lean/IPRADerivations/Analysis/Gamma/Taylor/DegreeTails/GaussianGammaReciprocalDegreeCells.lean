import IPRADerivations.Analysis.Gamma.Taylor.FinitePolynomials.GaussianGammaFiniteDegreeRearrangement
import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalPowerBounds.RationalReciprocalPowerTail
import IPRADerivations.Analysis.RationalArithmetic.Embeddings.RationalGaussianRealPart
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianIntegerFractionPowers
import IPRADerivations.AnalyticNumberTheory.LocalFactor

/-!
# Original Gamma degree cells and reciprocal-power partial sums

Each actual degree column of the original canonical finite tail is the
original signed Taylor monomial times the embedding of the original
rational reciprocal-power tail. Existing actual finite-sum embedding and
multiplication laws derive this equality, with all cutoffs numerical.
The resulting finite C16 identity does not assume a coefficient law,
completed series identity or supplied zeta provider.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Analysis.GaussianGammaReciprocalDegreeCells

open_ipra
open GaussianRationalHorner (qmul ofGaussian canonical canonical_unique represents_congr positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalReciprocal (power)
open GaussianRationalFiniteSum (sum sum_congr_bounded termsEqual)
open GaussianGammaFiniteDegreeRearrangement (matrix matrixData degreeMajor original_degree_entry)
open RationalGaussianEmbedding (embed)
open RationalReciprocalPowerTail (reciprocalPower tail)
open GaussianEuclideanDistanceName (fraction fraction_represents)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def degree (j : PTm n) : PTm n := succ (succ j)
def monomial (z B j : PTm n) : PTm n :=
  qmul (GaussianFiniteLogarithmPolynomial.coefficient (succ j)) (power (ofGaussian z B) (degree j))
def sourcePart (z B N r j : PTm n) : PTm n := qmul (monomial z B j) (embed (tail (degree j) N r))
ipra_subst degree
ipra_subst monomial
ipra_subst sourcePart

theorem embedded_reciprocal (m k : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    embed (reciprocalPower m k) ≐ ofGaussian ComplexLogarithmRemainder.oneCode (pw k m) := by
  have den := GaussianFactorBudget.power_positive (Γ := Γ) k m hk
  have rep := RationalGaussianEmbedding.embed_from_representation _ _ _ (fraction_represents one (pw k m) den)
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (RationalGaussianEmbedding.native (ZT.ofNat one : ZT n))
      ComplexLogarithmRemainder.oneCode := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code,
        ComplexLogarithmRemainder.eval_im_code,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,ZT.toZ_ofNat] <;>
      (try ipra_simps) <;> ring
  exact canonical_unique _ _ _ _ (RationalGaussianEmbedding.embed_canonical _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ den) den
    (represents_congr (.eqRefl _) native (.eqRefl _) rep) (GaussianRationalHorner.ofGaussian_represents _ _ den)

/-- The denominator k is separated from the SAME original fraction z/(Bk)
inside its actual numerical power. -/
theorem separated_power (z B k m : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    power (ofGaussian z (B*k)) m ≐ qmul (power (ofGaussian z B) m) (embed (reciprocalPower m k)) := by
  have b := GaussianFactorBudget.power_positive (Γ := Γ) B m hB
  have kpos := GaussianFactorBudget.power_positive (Γ := Γ) k m hk
  have den := positive_product (Γ := Γ) _ _ b kpos
  have left := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _)
    (AnalyticNumberTheory.LocalFactor.pw_mul_base B k m)
    (GaussianIntegerFractionPowers.power_represents z (B*k) m (positive_product _ _ hB hk))
  have right := GaussianRationalHorner.qmul_represents _ _ _ _ _ _ b kpos
    (GaussianIntegerFractionPowers.power_represents z B m hB)
    (represents_congr (embedded_reciprocal m k hk).eqSymm (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
      (GaussianRationalHorner.ofGaussian_represents _ _ kpos))
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.mul (ComplexLogarithmRemainder.power z m) ComplexLogarithmRemainder.oneCode)
      (ComplexLogarithmRemainder.power z m) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ring
  exact canonical_unique _ _ _ _ (GaussianRationalReciprocal.power_canonical _ _)
    (GaussianRationalHorner.qmul_canonical _ _) den left (represents_congr (.eqRefl _) native (.eqRefl _) right)

theorem cell_separation (i j z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    inst3 matrix i j (matrixData z B N) ≐
      qmul (monomial z B j) (embed (reciprocalPower (degree j) (succ (N+i)))) :=
  (original_degree_entry i j z B N).eqTrans
    ((qmul_congr (.eqRefl _) (separated_power z B (succ (N+i)) (degree j) hB (zero_lt_succ _))).eqTrans
      (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm)

def embeddedBody : PTm 2 := RationalGaussianRealPart.embedBody RationalReciprocalPowerTail.body

theorem embedded_term_at (m N i : PTm n) : Γ ⊢[PRAAx]
    inst2 embeddedBody i (RationalReciprocalPowerTail.data m N) ≐ embed (reciprocalPower m (succ (N+i))) := by
  have code : inst2 embeddedBody i (RationalReciprocalPowerTail.data m N) =
      embed (RationalFiniteSum.term RationalReciprocalPowerTail.body i (RationalReciprocalPowerTail.data m N)) := by
    simp only [embeddedBody,RationalGaussianRealPart.embedBody,inst2,RationalGaussianEmbedding.subst_embed,RationalFiniteSum.term]
  rw [code]
  exact RationalGaussianRealPart.embed_congr (RationalReciprocalPowerTail.term_at m N i)

theorem column_separation (z B N r j : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    GaussianRationalFubini.column matrix j r (matrixData z B N) ≐ sourcePart z B N r j := by
  have aligned : Γ ⊢[PRAAx] GaussianRationalFubini.column matrix j r (matrixData z B N) ≐
      sum (GaussianRationalFiniteSum.multiplyBody embeddedBody) r
        (pairT (monomial z B j) (RationalReciprocalPowerTail.data (degree j) N)) := by
    apply GaussianRationalFiniteSum.sum_congr_bounded
    refine .allI (.impI ?_)
    have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
    have left := (GaussianRationalFubini.column_entry (Γ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift)
      matrix (var 0) (Syn.shift j) (matrixData (Syn.shift z) (Syn.shift B) (Syn.shift N))).eqTrans
      (cell_separation (var 0) (Syn.shift j) (Syn.shift z) (Syn.shift B) (Syn.shift N) bs.wk)
    have right := (GaussianRationalFiniteSum.multiply_body_at (Γ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift)
      embeddedBody (monomial (Syn.shift z) (Syn.shift B) (Syn.shift j)) (var 0)
      (RationalReciprocalPowerTail.data (degree (Syn.shift j)) (Syn.shift N))).eqTrans
      (qmul_congr (.eqRefl _) (embedded_term_at (degree (Syn.shift j)) (Syn.shift N) (var 0)))
    simpa only [termsEqual,GaussianRationalFubini.column,subst_monomial,subst_degree,
      RationalReciprocalPowerTail.subst_data,GaussianGammaFiniteDegreeRearrangement.subst_matrixData,subst_pairT,Syn.shift] using
      left.eqTrans right.eqSymm
  exact aligned.eqTrans ((GaussianRationalFiniteSum.sum_multiply embeddedBody (monomial z B j) r
    (RationalReciprocalPowerTail.data (degree j) N)).eqTrans
      (qmul_congr (.eqRefl _) (RationalGaussianRealPart.embed_sum RationalReciprocalPowerTail.body r
        (RationalReciprocalPowerTail.data (degree j) N)).eqSymm))


def separatedData (z B N r : PTm n) : PTm n := pairT z (pairT B (pairT N r))
def separatedBody : PTm 2 := sourcePart (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
def separatedSum (z B N r L : PTm n) : PTm n := sum separatedBody (succ L) (separatedData z B N r)
ipra_subst separatedData
ipra_subst separatedSum

theorem source_part_congr {z B N r j a C M s k : PTm n} (hz : Γ ⊢[PRAAx] z ≐ a) (hB : Γ ⊢[PRAAx] B ≐ C)
    (hN : Γ ⊢[PRAAx] N ≐ M) (hr : Γ ⊢[PRAAx] r ≐ s) (hj : Γ ⊢[PRAAx] j ≐ k) : Γ ⊢[PRAAx]
    sourcePart z B N r j ≐ sourcePart a C M s k := by
  ipra_congr (sourcePart (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hz, hB, hN, hr, hj]

theorem separated_term_at (z B N r j : PTm n) : Γ ⊢[PRAAx]
    inst2 separatedBody j (separatedData z B N r) ≐ sourcePart z B N r j := by
  simp only [separatedBody,inst2,subst_sourcePart,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have t₁ := snd_pair (Γ := Γ) z (pairT B (pairT N r))
  have t₂ := (congrSnd t₁).eqTrans (snd_pair B (pairT N r))
  exact source_part_congr (fst_pair _ _) t₁.fstE
    t₂.fstE t₂.sndE (.eqRefl _)

/-- Every column of the SAME finite rectangle is replaced by its proved
original rational reciprocal-power sum, with degrees exactly 2,...,L+2. -/
theorem degree_major_separation (z B N r L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    degreeMajor z B N r L ≐ separatedSum z B N r L := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have left := (GaussianRationalFubini.column_sum_at (Γ := lt (var 0) (succ (Syn.shift L)) :: Γ.map Fm.shift)
    matrix (var 0) (Syn.shift r) (matrixData (Syn.shift z) (Syn.shift B) (Syn.shift N))).eqTrans
    (column_separation (Syn.shift z) (Syn.shift B) (Syn.shift N) (Syn.shift r) (var 0) bs.wk)
  have right := separated_term_at (Γ := lt (var 0) (succ (Syn.shift L)) :: Γ.map Fm.shift)
    (Syn.shift z) (Syn.shift B) (Syn.shift N) (Syn.shift r) (var 0)
  simpa only [termsEqual,degreeMajor,GaussianRationalFubini.columnFirst,separatedSum,subst_separatedData,
    GaussianGammaFiniteDegreeRearrangement.subst_matrixData,subst_pairT,ConciseIPRA.PTm.subst_succ,Syn.shift] using
    left.eqTrans right.eqSymm

theorem original_finite_tail_separation (z B N r L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    GaussianGammaCanonicalTailFiniteSplit.value z B N r L ≐ separatedSum z B N r L :=
  (GaussianGammaFiniteDegreeRearrangement.original_finite_rearrangement z B N r L hB).eqTrans
    (degree_major_separation z B N r L hB)
theorem separated_sum_canonical (z B N r L : PTm n) : Γ ⊢[PRAAx] canonical (separatedSum z B N r L) :=
  GaussianRationalFiniteSum.sum_canonical _ _ _

/-- Actual PR5 output preserves the original finite tail code and the
literal coefficient-separated finite sum side by side. -/
def output (z B N r L : PTm n) : PTm n :=
  pairT (GaussianGammaCanonicalTailFiniteSplit.value z B N r L) (separatedSum z B N r L)
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (z B N r L : PTm n) : PTm n := PTm.app outputF ![z,B,N,r,L]
ipra_subst output
ipra_subst run
theorem program_at (z B N r L : PTm n) : Γ ⊢[PRAAx] run z B N r L ≐ output z B N r L := by
  simpa only [run,outputF,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![z,B,N,r,L]
theorem returned_original (z B N r L : PTm n) : Γ ⊢[PRAAx]
    fstT (run z B N r L) ≐ GaussianGammaCanonicalTailFiniteSplit.value z B N r L :=
  (program_at z B N r L).fstE
theorem returned_separated (z B N r L : PTm n) : Γ ⊢[PRAAx]
    sndT (run z B N r L) ≐ separatedSum z B N r L :=
  (program_at z B N r L).sndE
theorem returned_equal (z B N r L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    fstT (run z B N r L) ≐ sndT (run z B N r L) :=
  (returned_original z B N r L).eqTrans ((original_finite_tail_separation z B N r L hB).eqTrans (returned_separated z B N r L).eqSymm)

theorem original_denominator_power_separation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le one (var 2) ⟶
      power (ofGaussian (var 0) (var 1*var 2)) (var 3) ≐
        qmul (power (ofGaussian (var 0) (var 1)) (var 3)) (embed (reciprocalPower (var 3) (var 2)))) :=
  closeUniv 4 (.impI (.impI (separated_power _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_original_degree_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ inst3 matrix (var 0) (var 1) (matrixData (var 2) (var 3) (var 4)) ≐
      qmul (monomial (var 2) (var 3) (var 1)) (embed (reciprocalPower (degree (var 1)) (succ (var 4+var 0))))) :=
  closeUniv 5 (.impI (cell_separation _ _ _ _ _ Prf.hyp0))

theorem actual_column_reciprocal_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ GaussianRationalFubini.column matrix (var 4) (var 3) (matrixData (var 0) (var 1) (var 2)) ≐
      sourcePart (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (column_separation _ _ _ _ _ Prf.hyp0))

theorem actual_finite_degree_coefficient_separation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ degreeMajor (var 0) (var 1) (var 2) (var 3) (var 4) ≐
      separatedSum (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (degree_major_separation _ _ _ _ _ Prf.hyp0))

theorem original_finite_C16_reciprocal_partial_sums_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ GaussianGammaCanonicalTailFiniteSplit.value (var 0) (var 1) (var 2) (var 3) (var 4) ≐
      separatedSum (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (original_finite_tail_separation _ _ _ _ _ Prf.hyp0))

theorem actual_returned_coefficient_separation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶
      (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ GaussianGammaCanonicalTailFiniteSplit.value (var 0) (var 1) (var 2) (var 3) (var 4) ⋏
        (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ separatedSum (var 0) (var 1) (var 2) (var 3) (var 4) ⋏
          fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (.impI (.andI (returned_original _ _ _ _ _) (.andI (returned_separated _ _ _ _ _) (returned_equal _ _ _ _ _ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaReciprocalDegreeCells
