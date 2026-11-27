import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.GaussianSuperellipticWordTerms
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerProduct

/-!
# Leading value of the original cyclic determinant word

The actual leading-factor fold of the SAME determinant stage is compared
with the existing product-of-powers program at the exact numerical wrap
reader and data. Original polynomial shapes/nonzero coefficients derive
every cell leading identity and factor flag. No cyclic-product, selected
leading, degree, evaluator or output law is supplied as input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSuperellipticCyclicLeading

open_ipra
open LeanProofs.IPRA.Analysis.GaussianSuperellipticWordTerms (input)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree (degree nonzeroCoefficients nonzero_of_flag_one)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProductDegree (leading leading_nonzero)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul qzero)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power powerF)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (stage term factor signPoint)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMultiplicationMatrix (width slot)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def d (f c : PTm n) : PTm n := degree f c
def k (f G m a c : PTm n) : PTm n := GaussianPolynomialWeightedDegree.index G m a (d f c)
def rotation (f G m a c : PTm n) : PTm n := Foundations.RuntimeCyclicPermutation.rotationCode m (k f G m a c)
def matrix (f G m a c : PTm n) : PTm n := GaussianSuperellipticMatrixEntries.matrix f G m a c
def rowLeading (f G m a c : PTm n) : PTm n := GaussianPolynomialWeightedDegree.rowLeading G m a (k f G m a c)
def fLeading (f c : PTm n) : PTm n := leading f c
def expected (f G m a c : PTm n) : PTm n := qmul (power (rowLeading f G m a c) m) (power (fLeading f c) (k f G m a c))
def wrapBody : PTm 2 := GaussianSuperellipticWordWeights.reader GaussianSuperellipticWordWeights.wrapSchema
def wrapData (m w : PTm n) : PTm n := GaussianSuperellipticWordWeights.data zero m zero zero w


ipra_subst d
ipra_subst k
ipra_subst rotation
ipra_subst matrix
ipra_subst rowLeading
ipra_subst fLeading
ipra_subst expected
ipra_subst wrapData

theorem weighted_input (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) :
    Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.input G m a := .andE₂ (.andE₂ h)
theorem index_bound (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) :
    Γ ⊢[PRAAx] lt (k f G m a c) m :=
  .andE₁ (GaussianPolynomialWeightedDegree.index_attains G m a (d f c) (.andE₁ (weighted_input _ _ _ _ _ h)))

theorem selected_row (f G m a c j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    GaussianSuperellipticMatrixLeading.selectedRow G m
      (Foundations.RuntimePermutationWords.digit m (rotation f G m a c) j) j ≐
        GaussianPolynomialWeightedDegree.row G m (k f G m a c) := by
  have idx := GaussianSuperellipticWordWeights.rotation_index m (k f G m a c) j (index_bound _ _ _ _ _ h) hj
  simpa only [GaussianSuperellipticMatrixLeading.selectedRow,GaussianPolynomialWeightedDegree.row,
    slot,GaussianSuperellipticWordWeights.rowIndex,rotation] using
      entry_congr (.eqRefl G) (congrMonus (.eqRefl m) (congrSucc idx))
theorem selected_row_nonzero (f G m a c j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    nonzeroCoefficients (GaussianSuperellipticMatrixLeading.selectedRow G m
      (Foundations.RuntimePermutationWords.digit m (rotation f G m a c) j) j) a := by
  have wi := weighted_input f G m a c h
  have selected := GaussianPolynomialWeightedDegree.selected_flag_one G m a (d f c) (.andE₁ wi) (.andE₂ (.andE₂ wi))
  exact nonzero_of_flag_one _ _ ((GaussianPolynomialDeterminantTermDegree.flag_congr
    (selected_row f G m a c j h hj) (.eqRefl a)).eqTrans selected)

/-- Each original cyclic cell has the actual selected leading row value;
its wrap exponent is the original numerical wrap reader. -/
theorem cyclic_factor_leading (f G m a c j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    leading (factor (matrix f G m a c) m (rotation f G m a c) j) (width m a c) ≐
      qmul (rowLeading f G m a c) (power (fLeading f c)
        (GaussianSuperellipticWordWeights.wrapAt m (rotation f G m a c) j)) := by
  have actual := GaussianSuperellipticMatrixLeading.cell_leading f G m a c
    (Foundations.RuntimePermutationWords.digit m (rotation f G m a c) j) j
    (GaussianSuperellipticWordTerms.entry_input f G m a c (rotation f G m a c) j h hj)
    (.andE₁ (.andE₂ h)) (selected_row_nonzero f G m a c j h hj)
  have row : Γ ⊢[PRAAx] leading (GaussianSuperellipticMatrixLeading.selectedRow G m
      (Foundations.RuntimePermutationWords.digit m (rotation f G m a c) j) j) a ≐ rowLeading f G m a c := by
    simpa only [rowLeading,GaussianPolynomialWeightedDegree.rowLeading,GaussianPolynomialWeightedDegree.rowFirst,GaussianRationalPolynomialProductDegree.leading] using
      GaussianPolynomialDeterminantTermDegree.leading_congr (selected_row f G m a c j h hj) (.eqRefl a)
  have cell : Γ ⊢[PRAAx] leading (factor (matrix f G m a c) m (rotation f G m a c) j) (width m a c) ≐
      qmul (leading (GaussianSuperellipticMatrixLeading.selectedRow G m
        (Foundations.RuntimePermutationWords.digit m (rotation f G m a c) j) j) a)
        (power (fLeading f c) (GaussianSuperellipticWordWeights.wrapAt m (rotation f G m a c) j)) := by
    simpa only [factor,matrix,GaussianSuperellipticMatrixEntries.entryPolynomial,
      fLeading,GaussianSuperellipticWordWeights.wrapAt,GaussianSuperellipticWordWeights.rowIndex] using actual
  exact cell.eqTrans (qmul_congr row (.eqRefl _))

theorem vec_six_last {α : Type} (a b c d e f : α) : ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

theorem wrap_body_at (m w j : PTm n) : Γ ⊢[PRAAx]
    inst2 wrapBody j (wrapData m w) ≐ GaussianSuperellipticWordWeights.wrapAt m w j := by
  simpa only [wrapBody,wrapData,GaussianSuperellipticWordWeights.wrapSchema,GaussianSuperellipticWordWeights.subst_wrapAt,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_four,vec_six_last,Matrix.head_cons,Matrix.tail_cons] using
      GaussianSuperellipticWordWeights.reader_at (Γ := Γ) GaussianSuperellipticWordWeights.wrapSchema zero m zero zero w j

theorem leading_body_power_at (f G m a c j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    inst2 GaussianPolynomialDeterminantTermDegree.leadingBody j
      (GaussianPolynomialDeterminantTerms.data (matrix f G m a c) m (width m a c) (rotation f G m a c)) ≐
    inst2 (GaussianRationalPowerProduct.factorBody wrapBody) j
      (GaussianRationalPowerProduct.data (rowLeading f G m a c) (fLeading f c) (wrapData m (rotation f G m a c))) :=
  (GaussianPolynomialDeterminantTermDegree.leading_body_at _ _ _ _ _).eqTrans
    ((cyclic_factor_leading f G m a c j h hj).eqTrans
      ((qmul_congr (.eqRefl _) (congrAp2 powerF (wrap_body_at m (rotation f G m a c) j).eqSymm (.eqRefl _))).eqTrans
        (GaussianRationalPowerProduct.factor_at wrapBody (rowLeading f G m a c) (fLeading f c)
          (wrapData m (rotation f G m a c)) j).eqSymm))

theorem cyclic_leading_product_prefix (f G m a c j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hj : Γ ⊢[PRAAx] le j m) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTermDegree.leadingProduct (matrix f G m a c) m (width m a c) (rotation f G m a c) j ≐
      qmul (power (rowLeading f G m a c) j) (power (fLeading f c)
        (GaussianSuperellipticWordWeights.wrapPrefix m (rotation f G m a c) j)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift f) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) := by
    simpa only [Fm.shift,GaussianSuperellipticWordTerms.subst_input,Syn.shift] using h.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift j) (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hj.shift
  have eqs : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual GaussianPolynomialDeterminantTermDegree.leadingBody
      (GaussianRationalPowerProduct.factorBody wrapBody) j
      (GaussianPolynomialDeterminantTerms.data (matrix f G m a c) m (width m a c) (rotation f G m a c))
      (GaussianRationalPowerProduct.data (rowLeading f G m a c) (fLeading f c) (wrapData m (rotation f G m a c))) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift j) :: Γ.map Fm.shift
    have range : Δ ⊢[PRAAx] lt (var 0) (Syn.shift m) := lt_of_lt_of_le Prf.hyp0 js.wk
    simpa only [Syn.shift,GaussianPolynomialDeterminantTerms.subst_data,subst_matrix,subst_rotation,
      GaussianPolynomialMultiplicationMatrix.subst_width,GaussianRationalPowerProduct.data,subst_pairT,
      subst_rowLeading,subst_fLeading,subst_wrapData] using
        leading_body_power_at (Syn.shift f) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0) hs.wk range
  exact (GaussianRationalFiniteProduct.product_congr_bounded _ _ _ _ _ eqs).eqTrans
    (by simpa only [GaussianRationalPowerProduct.productLaw,wrapData,wrapBody,GaussianSuperellipticWordWeights.wrapPrefix,
      GaussianSuperellipticWordWeights.prefixSum] using (GaussianRationalPowerProduct.actual_power_product wrapBody
        (rowLeading f G m a c) (fLeading f c) (wrapData m (rotation f G m a c)) j))

theorem cyclic_leading_product (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTermDegree.leadingProduct (matrix f G m a c) m (width m a c) (rotation f G m a c) m ≐ expected f G m a c :=
  (cyclic_leading_product_prefix f G m a c m h (le_refl m)).eqTrans
    (qmul_congr (.eqRefl _) (congrAp2 powerF
      (GaussianSuperellipticWordWeights.rotation_wrap_total m (k f G m a c) (index_bound _ _ _ _ _ h)) (.eqRefl _)))
theorem cyclic_stage_leading (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    leading (stage (matrix f G m a c) m (width m a c) (rotation f G m a c) m) (m*width m a c) ≐ expected f G m a c :=
  (GaussianPolynomialDeterminantTermDegree.stage_leading _ _ _ _ _
    (GaussianSuperellipticWordTerms.rotation_factor_flags f G m a c h)).eqTrans (cyclic_leading_product f G m a c h)
theorem cyclic_signed_leading (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    leading (term (matrix f G m a c) m (width m a c) (rotation f G m a c)) (m*width m a c) ≐
      qmul (signPoint m (rotation f G m a c)) (expected f G m a c) :=
  (GaussianPolynomialDeterminantTermDegree.signed_term_leading _ _ _ _
    (GaussianSuperellipticWordTerms.rotation_factor_flags f G m a c h)).eqTrans (qmul_congr (.eqRefl _) (cyclic_leading_product f G m a c h))
theorem cyclic_leading_nonzero (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    neg (expected f G m a c ≐ qzero) := by
  have nonzero := leading_nonzero _ _ (nonzero_of_flag_one _ _
    (GaussianPolynomialDeterminantTermDegree.stage_success_of_factors _ _ _ _ _
      (GaussianSuperellipticWordTerms.rotation_factor_flags f G m a c h)))
  exact .impI (.impE nonzero.wk ((cyclic_stage_leading f G m a c h).wk.eqTrans Prf.hyp0))
theorem cyclic_signed_nonzero (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    neg (qmul (signPoint m (rotation f G m a c)) (expected f G m a c) ≐ qzero) := by
  have nonzero := leading_nonzero _ _ (nonzero_of_flag_one _ _
    ((GaussianPolynomialDeterminantTermDegree.signed_term_flag_iff _ _ _ _).iffMpr
      (GaussianSuperellipticWordTerms.rotation_factor_flags f G m a c h)))
  exact .impI (.impE nonzero.wk ((cyclic_signed_leading f G m a c h).wk.eqTrans Prf.hyp0))


/-! Original numerical input returns the SAME stage and signed term,
the computed cyclic value, both actual leading values and original word. -/
def output (f G m a c : PTm n) : PTm n :=
  pairT (stage (matrix f G m a c) m (width m a c) (rotation f G m a c) m)
    (pairT (term (matrix f G m a c) m (width m a c) (rotation f G m a c))
      (pairT (expected f G m a c)
        (pairT (leading (stage (matrix f G m a c) m (width m a c) (rotation f G m a c) m) (m*width m a c))
          (pairT (leading (term (matrix f G m a c) m (width m a c) (rotation f G m a c)) (m*width m a c))
            (pairT (rotation f G m a c) (k f G m a c))))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (f G m a c : PTm n) : PTm n := app outputF ![f,G,m,a,c]
def fields (p : PTm n) (i : Fin 7) : PTm n := ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),
  fstT (sndT (sndT (sndT p))),fstT (sndT (sndT (sndT (sndT p)))),
  fstT (sndT (sndT (sndT (sndT (sndT p))))),sndT (sndT (sndT (sndT (sndT (sndT p)))))] i
ipra_subst output
ipra_subst run
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 7) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem program_at (f G m a c : PTm n) : Γ ⊢[PRAAx] run f G m a c ≐ output f G m a c := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![f,G,m,a,c]
theorem returned_fields (f G m a c : PTm n) (i : Fin 7) : Γ ⊢[PRAAx]
    fields (run f G m a c) i ≐
      ![stage (matrix f G m a c) m (width m a c) (rotation f G m a c) m,
        term (matrix f G m a c) m (width m a c) (rotation f G m a c),expected f G m a c,
        leading (stage (matrix f G m a c) m (width m a c) (rotation f G m a c) m) (m*width m a c),
        leading (term (matrix f G m a c) m (width m a c) (rotation f G m a c)) (m*width m a c),rotation f G m a c,k f G m a c] i := by
  have e0 := program_at (Γ := Γ) f G m a c
  have e1 := e0.sndE
  have e2 := e1.sndE
  have e3 := e2.sndE
  have e4 := e3.sndE
  have e5 := e4.sndE
  fin_cases i
  · exact e0.fstE
  · exact e1.fstE
  · exact e2.fstE
  · exact e3.fstE
  · exact e4.fstE
  · exact e5.fstE
  · exact e5.sndE
theorem returned_stage_leading (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    fields (run f G m a c) 3 ≐ fields (run f G m a c) 2 :=
  (returned_fields _ _ _ _ _ 3).eqTrans ((cyclic_stage_leading f G m a c h).eqTrans (returned_fields _ _ _ _ _ 2).eqSymm)
theorem returned_signed_leading (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    fields (run f G m a c) 4 ≐ qmul (signPoint m (rotation f G m a c)) (fields (run f G m a c) 2) :=
  (returned_fields _ _ _ _ _ 4).eqTrans ((cyclic_signed_leading f G m a c h).eqTrans
    (qmul_congr (.eqRefl _) (returned_fields _ _ _ _ _ 2).eqSymm))
theorem returned_leading_nonzero (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    neg (fields (run f G m a c) 2 ≐ qzero) :=
  .impI (.impE (cyclic_leading_nonzero f G m a c h).wk ((returned_fields _ _ _ _ _ 2).wk.eqSymm.eqTrans Prf.hyp0))

theorem actual_cyclic_factor_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lt (var 5) (var 2) ⟶
      leading (factor (matrix (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2)
        (rotation (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) (width (var 2) (var 3) (var 4)) ≐
      qmul (rowLeading (var 0) (var 1) (var 2) (var 3) (var 4)) (power (fLeading (var 0) (var 4))
        (GaussianSuperellipticWordWeights.wrapAt (var 2) (rotation (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)))) :=
  closeUniv 6 (.impI (.impI (cyclic_factor_leading _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_cyclic_prefix_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le (var 5) (var 2) ⟶
      GaussianPolynomialDeterminantTermDegree.leadingProduct (matrix (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2)
        (width (var 2) (var 3) (var 4)) (rotation (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) ≐
      qmul (power (rowLeading (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) (power (fLeading (var 0) (var 4))
        (GaussianSuperellipticWordWeights.wrapPrefix (var 2) (rotation (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)))) :=
  closeUniv 6 (.impI (.impI (cyclic_leading_product_prefix _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_cyclic_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      GaussianPolynomialDeterminantTermDegree.leadingProduct (matrix (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2)
        (width (var 2) (var 3) (var 4)) (rotation (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) ≐
        expected (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (.impI (cyclic_leading_product _ _ _ _ _ Prf.hyp0))
theorem actual_cyclic_stage_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      leading (stage (matrix (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (width (var 2) (var 3) (var 4))
        (rotation (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2)) (var 2*width (var 2) (var 3) (var 4)) ≐
        expected (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (.impI (cyclic_stage_leading _ _ _ _ _ Prf.hyp0))
theorem actual_cyclic_signed_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      leading (term (matrix (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (width (var 2) (var 3) (var 4))
        (rotation (var 0) (var 1) (var 2) (var 3) (var 4))) (var 2*width (var 2) (var 3) (var 4)) ≐
      qmul (signPoint (var 2) (rotation (var 0) (var 1) (var 2) (var 3) (var 4))) (expected (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (cyclic_signed_leading _ _ _ _ _ Prf.hyp0))
theorem actual_cyclic_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      (neg (expected (var 0) (var 1) (var 2) (var 3) (var 4) ≐ qzero) ⋏
        neg (qmul (signPoint (var 2) (rotation (var 0) (var 1) (var 2) (var 3) (var 4)))
          (expected (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ qzero))) :=
  closeUniv 5 (.impI (.andI (cyclic_leading_nonzero _ _ _ _ _ Prf.hyp0) (cyclic_signed_nonzero _ _ _ _ _ Prf.hyp0)))
theorem actual_cyclic_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_cyclic_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 3 ≐
      fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 2) := closeUniv 5 (.impI (returned_stage_leading _ _ _ _ _ Prf.hyp0))
theorem actual_returned_signed_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 4 ≐
      qmul (signPoint (var 2) (rotation (var 0) (var 1) (var 2) (var 3) (var 4)))
        (fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 2)) := closeUniv 5 (.impI (returned_signed_leading _ _ _ _ _ Prf.hyp0))
theorem actual_returned_cyclic_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ neg (fields (run (var 0) (var 1) (var 2) (var 3) (var 4)) 2 ≐ qzero)) :=
  closeUniv 5 (.impI (returned_leading_nonzero _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSuperellipticCyclicLeading
