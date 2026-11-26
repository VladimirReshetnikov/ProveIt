import IPRADerivations.Analysis.Polynomials.Elimination.RationalSuperellipticTail
import IPRADerivations.Analysis.Polynomials.RationalPolynomialWeightedDegreeGaussianEmbedding
import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalScalarPowerGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.RationalPolynomialLeadingGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Elimination.GaussianSuperellipticNormDegree
import IPRADerivations.Foundations.PrimitiveScaling
import IPRADerivations.Core.CongruenceTactic

/-!
# Exact degree and leading coefficient of the original rational norm

The rational tail, matrix, determinant and coefficient scans are the
actual original programs. Their proved embeddings identify the same
cyclic leading term as in the Gaussian theorem. All numerical degrees,
weights, indices and rational coefficient codes are internal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSuperellipticNormDegree

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalPolynomialGaussianEmbedding (coefficients coefficients_length)
open RationalPolynomialLeadingGaussianEmbedding (leading coefficient_list_embedding leading_embedding)
open RationalPolynomialNonvanishing (nonzeroCoefficients flag_of_nonzero)
open RationalPolynomialWeightedDegreeGaussianEmbedding (embedded nonzeroRows weightedDegree index row)
open RationalScalarPowerGaussianEmbedding (power power_embedding)
open RationalGaussianEmbedding (embed scalarZero)
open RationalSuperellipticTail (tailRows tail_shape table_embedding)
open GaussianPolynomialMonicNorm (degreeBound)
open RationalPolynomialBuffersGaussianEmbedding (embeddedEntries)
open GaussianNormFiberDivisibility (sourceOriginal)
open GaussianPolynomialMonicCompanion (rowShape)
open GaussianPolynomialMultiplicationMatrix (slot slot_range)
open GaussianRationalFiberGrouping (abscissa ordinate)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def d (f c : PTm n) : PTm n := RationalPolynomialDegreeGaussianEmbedding.degree f c
def k (f G m a c : PTm n) : PTm n := index G m a (d f c)
def rotation (f G m a c : PTm n) : PTm n := Foundations.RuntimeCyclicPermutation.rotationCode m (k f G m a c)
def norm (f G m a c : PTm n) : PTm n := RationalPolynomialMonicNorm.norm (tailRows f m c) G m a c
def sourceLeading (f G m a c : PTm n) : PTm n :=
  RationalArithmetic.multiply (RationalScalarDeterminantGaussianEmbedding.sign m (rotation f G m a c))
    (RationalArithmetic.multiply (power (leading (row G m (k f G m a c)) a) m)
      (power (leading f c) (k f G m a c)))

def input (f G m a c : PTm n) : Fm PTm n := le (succ one) m ⋏ (le one (d f c) ⋏
  (gcd m (d f c) ≐ one ⋏ (length f ≐ succ c ⋏ (nonzeroCoefficients f c ⋏ (rowShape G m a ⋏ nonzeroRows G m a)))))
def certificate (f G m a c : PTm n) : Fm PTm n :=
  RationalPolynomialDegreeGaussianEmbedding.flag (norm f G m a c) (degreeBound m a c) ≐ one ⋏
    (RationalPolynomialDegreeGaussianEmbedding.degree (norm f G m a c) (degreeBound m a c) ≐ weightedDegree G m a (d f c) ⋏
      leading (norm f G m a c) (degreeBound m a c) ≐ sourceLeading f G m a c)

@[simp] theorem subst_norm {l : ℕ} (σ : Fin n → PTm l) (f G m a c : PTm n) :
    Syn.subst σ (norm f G m a c) = norm (Syn.subst σ f) (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by
  simp [norm]

theorem f_degree_embedding (f c : PTm n) : Γ ⊢[PRAAx] d f c ≐ GaussianRationalPolynomialDegree.degree (coefficients f (succ c)) c :=
  RationalPolynomialDegreeGaussianEmbedding.degree_conjugacy _ _ _ (coefficient_list_embedding _ _)

theorem monic_input (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    GaussianPolynomialMonicNorm.input (tailRows f m c) G m a c := by
  have source := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))
  exact .andI (le_trans (le_succ_self one) (Prf.andE₁ h))
    (.andI (tail_shape f m c (Prf.andE₁ source)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ source))))

theorem gaussian_input (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) :
    Γ ⊢[PRAAx] GaussianSuperellipticNormDegree.input (coefficients f (succ c)) (embedded G m a) m a c := by
  have source := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))
  have fnz := Prf.andE₁ (Prf.andE₂ source)
  have gnz := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ source))
  have eq := f_degree_embedding (Γ := Γ) f c
  have fflag := (RationalPolynomialDegreeGaussianEmbedding.flag_conjugacy f (coefficients f (succ c)) c
    (coefficient_list_embedding _ _)).eqSymm.eqTrans (flag_of_nonzero f c fnz)
  exact .andI (Prf.andE₁ h) (.andI (le_congr (.eqRefl _) eq (Prf.andE₁ (Prf.andE₂ h)))
    (.andI ((Foundations.PrimitiveScaling.gcd_congr' (.eqRefl m) eq).eqSymm.eqTrans
        (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))))
      (.andI (coefficients_length _ _) (.andI (GaussianRationalPolynomialDegree.nonzero_of_flag_one _ _ fflag)
        (.andI (RationalBivariateGaussianEmbedding.embedded_row_shape G m a)
          (RationalPolynomialWeightedDegreeGaussianEmbedding.nonzero_rows_to_gaussian G m a gnz))))))

private theorem last_argument_congr (F : PTm 4) (G m a u v : PTm n) (h : Γ ⊢[PRAAx] u ≐ v) :
    Γ ⊢[PRAAx] Syn.subst ![G,m,a,u] F ≐ Syn.subst ![G,m,a,v] F :=
  Prf.eqCongr F (σ := ![G,m,a,u]) (σ' := ![G,m,a,v]) (fun i => by
    fin_cases i
    · exact .eqRefl G
    · exact .eqRefl m
    · exact .eqRefl a
    · exact h)

theorem index_embedding (f G m a c : PTm n) : Γ ⊢[PRAAx]
    k f G m a c ≐ GaussianSuperellipticCyclicLeading.k (coefficients f (succ c)) (embedded G m a) m a c := by
  let f' := coefficients f (succ c)
  let G' := embedded G m a
  have g : Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.index G' m a (d f c) ≐
      GaussianPolynomialWeightedDegree.index G' m a (GaussianSuperellipticCyclicLeading.d f' c) := by
    simpa only [GaussianPolynomialWeightedDegree.subst_index,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      last_argument_congr (GaussianPolynomialWeightedDegree.index (var 0) (var 1) (var 2) (var 3))
        G' m a (d f c) (GaussianSuperellipticCyclicLeading.d f' c) (f_degree_embedding f c)
  exact (RationalPolynomialWeightedDegreeGaussianEmbedding.index_conjugacy G m a (d f c)).eqTrans g

theorem weighted_degree_embedding (f G m a c : PTm n) : Γ ⊢[PRAAx]
    weightedDegree G m a (d f c) ≐
      GaussianPolynomialWeightedDegree.weightedDegree (embedded G m a) m a
        (GaussianRationalPolynomialDegree.degree (coefficients f (succ c)) c) := by
  let f' := coefficients f (succ c)
  let G' := embedded G m a
  have g : Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.weightedDegree G' m a (d f c) ≐
      GaussianPolynomialWeightedDegree.weightedDegree G' m a (GaussianRationalPolynomialDegree.degree f' c) := by
    simpa only [GaussianPolynomialWeightedDegree.subst_weightedDegree,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      last_argument_congr (GaussianPolynomialWeightedDegree.weightedDegree (var 0) (var 1) (var 2) (var 3))
        G' m a (d f c) (GaussianRationalPolynomialDegree.degree f' c) (f_degree_embedding f c)
  exact (RationalPolynomialWeightedDegreeGaussianEmbedding.weighted_degree_conjugacy G m a (d f c)).eqTrans g

private theorem original_relabel (F F' G m a c : PTm n) (h : Γ ⊢[PRAAx] F ≐ F') : Γ ⊢[PRAAx]
    sourceOriginal F G m a c ≐ sourceOriginal F' G m a c := by
  simpa only [GaussianNormFiberDivisibility.subst_sourceOriginal,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (sourceOriginal (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![F,G,m,a,c]) (σ' := ![F',G,m,a,c])
    (fun i => by
      fin_cases i
      · exact h
      · exact .eqRefl G
      · exact .eqRefl m
      · exact .eqRefl a
      · exact .eqRefl c)

theorem norm_embedding (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    embeddedEntries (norm f G m a c)
      (GaussianSuperellipticNormDegree.originalNorm (coefficients f (succ c)) (embedded G m a) m a c)
      (succ (degreeBound m a c)) := by
  have hn := monic_input f G m a c h
  have hf := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  let T := RationalRowSpanGaussianEmbedding.matrix (tailRows f m c) m (succ c)
  let T' := GaussianSuperellipticTail.tailRows (coefficients f (succ c)) m c
  let G' := embedded G m a
  have ht : Γ ⊢[PRAAx] T ≐ T' := table_embedding f m c (Prf.andE₁ hn) hf
  have he : Γ ⊢[PRAAx] sourceOriginal T G' m a c ≐ sourceOriginal T' G' m a c :=
    original_relabel T T' G' m a c ht
  have hn' : Γ ⊢[PRAAx] embeddedEntries (norm f G m a c) (sourceOriginal T G' m a c)
      (succ (degreeBound m a c)) := RationalPolynomialMonicNorm.norm_entries (tailRows f m c) G m a c hn
  exact RationalPolynomialMonicCompanionGaussianEmbedding.embedded_congr (.eqRefl (norm f G m a c)) he hn'

theorem source_leading_embedding (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) : Γ ⊢[PRAAx]
    embed (sourceLeading f G m a c) ≐ GaussianSuperellipticNormDegree.sourceLeading (coefficients f (succ c)) (embedded G m a) m a c := by
  let f' := coefficients f (succ c)
  let G' := embedded G m a
  let i := k f G m a c
  let j := GaussianSuperellipticCyclicLeading.k f' G' m a c
  let source := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))
  have fm := Prf.andE₁ (Prf.andE₂ source)
  have gm := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ source))
  have mpos : Γ ⊢[PRAAx] le one m := le_trans (le_succ_self one) (Prf.andE₁ h)
  have hi : Γ ⊢[PRAAx] lt i m := RationalPolynomialWeightedDegreeGaussianEmbedding.index_bound G m a (d f c) mpos
  have kij : Γ ⊢[PRAAx] i ≐ j := index_embedding f G m a c
  have row_eq : Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.row G' m i ≐ GaussianPolynomialWeightedDegree.row G' m j :=
    entry_congr (.eqRefl G') (congrMonus (.eqRefl m) (congrSucc kij))
  have selFlag : Γ ⊢[PRAAx] RationalPolynomialDegreeGaussianEmbedding.flag (row G m i) a ≐ one :=
    (RationalPolynomialWeightedDegreeGaussianEmbedding.row_flag_conjugacy G m a i hi).eqTrans
      ((GaussianPolynomialDeterminantTermDegree.flag_congr row_eq (.eqRefl a)).eqTrans
        (GaussianPolynomialWeightedDegree.selected_flag_one G' m a (GaussianSuperellipticCyclicLeading.d f' c) mpos
          (RationalPolynomialWeightedDegreeGaussianEmbedding.nonzero_rows_to_gaussian G m a gm)))
  have el : Γ ⊢[PRAAx] embed (leading (row G m i) a) ≐ GaussianSuperellipticCyclicLeading.rowLeading f' G' m a c :=
    (leading_embedding _ _ _ (RationalBivariateGaussianEmbedding.row_embedding G m (succ a) (slot m i) (slot_range _ _ hi)) selFlag).eqTrans
      (GaussianPolynomialDeterminantTermDegree.leading_congr row_eq (.eqRefl a))
  have ef : Γ ⊢[PRAAx] embed (leading f c) ≐ GaussianSuperellipticCyclicLeading.fLeading f' c :=
    leading_embedding _ _ _ (coefficient_list_embedding _ _) (flag_of_nonzero _ _ fm)
  have rot : Γ ⊢[PRAAx] rotation f G m a c ≐ GaussianSuperellipticCyclicLeading.rotation f' G' m a c := by
    ipra_congr (Foundations.RuntimeCyclicPermutation.rotationCode (var 0) (var 1) : PTm 2) with
      [.eqRefl m, kij] using [rotation, GaussianSuperellipticCyclicLeading.rotation]
  have sign : Γ ⊢[PRAAx] embed (RationalScalarDeterminantGaussianEmbedding.sign m (rotation f G m a c)) ≐
      GaussianPolynomialDeterminantTerms.signPoint m (GaussianSuperellipticCyclicLeading.rotation f' G' m a c) := by
    refine (RationalScalarDeterminantGaussianEmbedding.sign_embedding _ _).eqTrans ?_
    ipra_congr (GaussianPolynomialDeterminantTerms.signPoint (var 0) (var 1) : PTm 2) with [.eqRefl m, rot]
  exact (RationalGaussianEmbedding.embed_multiply _ _).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr sign ((RationalGaussianEmbedding.embed_multiply _ _).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr
        ((power_embedding _ _).eqTrans (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl m) el))
        ((power_embedding _ _).eqTrans (congrAp2 GaussianRationalReciprocal.powerF kij ef)))))

theorem exact_norm_degree (f G m a c : PTm n) (h : Γ ⊢[PRAAx] input f G m a c) :
    Γ ⊢[PRAAx] certificate f G m a c := by
  have ge := norm_embedding f G m a c h
  have cert := GaussianSuperellipticNormDegree.original_norm_degree (coefficients f (succ c)) (embedded G m a) m a c
    (gaussian_input f G m a c h)
  have flag : Γ ⊢[PRAAx] RationalPolynomialDegreeGaussianEmbedding.flag (norm f G m a c) (degreeBound m a c) ≐ one :=
    (RationalPolynomialDegreeGaussianEmbedding.flag_conjugacy _ _ _ ge).eqTrans (Prf.andE₁ cert)
  have deg := (RationalPolynomialDegreeGaussianEmbedding.degree_conjugacy _ _ _ ge).eqTrans
    ((Prf.andE₁ (Prf.andE₂ cert)).eqTrans (weighted_degree_embedding f G m a c).eqSymm)
  have lead := (leading_embedding _ _ _ ge flag).eqTrans
    ((Prf.andE₂ (Prf.andE₂ cert)).eqTrans (source_leading_embedding f G m a c h).eqSymm)
  exact .andI flag (.andI deg (RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _
    (RationalPolynomialLeadingGaussianEmbedding.leading_canonical _ _) (RationalArithmetic.multiply_guard _ _) lead))

theorem curve_equation (f m c x y : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hf : Γ ⊢[PRAAx] length f ≐ succ c) :
    Γ ⊢[PRAAx] Fm.iff
      (RationalArgmin.rationalEq (RationalBivariateGaussianEmbedding.monic (tailRows f m c) m x y) scalarZero)
      (RationalArgmin.rationalEq (power y m) (RationalPolynomialGaussianEmbedding.evaluate f x)) := by
  let T := RationalRowSpanGaussianEmbedding.matrix (tailRows f m c) m (succ c)
  let f' := coefficients f (succ c)
  let T' := GaussianSuperellipticTail.tailRows f' m c
  have tv : Γ ⊢[PRAAx] GaussianPolynomialMonicCompanion.monicValues T m (embed x) ≐
      GaussianPolynomialMonicCompanion.monicValues T' m (embed x) := by
    ipra_congr (GaussianPolynomialMonicCompanion.monicValues (var 0) (var 1) (var 2) : PTm 3) with
      [table_embedding f m c hm hf, .eqRefl m, .eqRefl (embed x)]
  have gv := GaussianRationalMonicReduction.evaluate_congr tv (.eqRefl (embed y))
  have hv := RationalPolynomialBuffersGaussianEmbedding.evaluation_transport f f' (succ c) x hf
    (coefficients_length _ _) (coefficient_list_embedding _ _)
  have rational := RationalBivariateGaussianEmbedding.monic_zero_iff (tailRows f m c) m c x y (tail_shape f m c hf)
  have gaussian := GaussianSuperellipticTail.curve_equality f' m c (embed x) (embed y) hm
  have powers := RationalScalarPowerGaussianEmbedding.power_equality (Γ := Γ) y m (RationalPolynomialGaussianEmbedding.evaluate f x)
  refine .andI (.impI ?_) (.impI ?_)
  · exact powers.wk.iffMpr ((gaussian.wk.iffMp (gv.wk.eqSymm.eqTrans (rational.wk.iffMp Prf.hyp0))).eqTrans hv.wk.eqSymm)
  · exact rational.wk.iffMpr (gv.wk.eqTrans (gaussian.wk.iffMpr ((powers.wk.iffMp Prf.hyp0).eqTrans hv.wk)))

def pointPowers (f m L : PTm n) : Fm PTm n := .all (lt (var 0) (length (Syn.shift L)) ⟶
  RationalArgmin.rationalEq (power (ordinate (Syn.shift L) (var 0)) (Syn.shift m))
    (RationalPolynomialGaussianEmbedding.evaluate (Syn.shift f) (abscissa (Syn.shift L) (var 0))))
def pointInput (f G m L : PTm n) : Fm PTm n := RationalCurvePointsGaussianEmbedding.distinct L ⋏
  (pointPowers f m L ⋏ RationalCurvePointsGaussianEmbedding.functionZeros G m L)

@[simp] theorem subst_pointPowers {l : ℕ} (σ : Fin n → PTm l) (f m L : PTm n) :
    (pointPowers f m L).subst σ = pointPowers (Syn.subst σ f) (Syn.subst σ m) (Syn.subst σ L) := by
  simp [pointPowers,Syn.subst_shift,Syn.shift_subst]

theorem point_power_at (f m L i : PTm n) (h : Γ ⊢[PRAAx] pointPowers f m L) (hi : Γ ⊢[PRAAx] lt i (length L)) :
    Γ ⊢[PRAAx] RationalArgmin.rationalEq (power (ordinate L i) m)
      (RationalPolynomialGaussianEmbedding.evaluate f (abscissa L i)) := by
  have here : Γ ⊢[PRAAx] lt i (length L) ⟶ RationalArgmin.rationalEq (power (ordinate L i) m)
      (RationalPolynomialGaussianEmbedding.evaluate f (abscissa L i)) := by simpa [pointPowers] using h.allE i
  exact .impE here hi

theorem curve_points (f m c L : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hf : Γ ⊢[PRAAx] length f ≐ succ c)
    (h : Γ ⊢[PRAAx] pointPowers f m L) : Γ ⊢[PRAAx] RationalCurvePointsGaussianEmbedding.curveZeros (tailRows f m c) m L := by
  refine .allI (.impI ?_)
  have hm' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift,one] using hm.shift
  have hf' : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift f) ≐ succ (Syn.shift c) := by simpa [Fm.shift,Syn.shift] using hf.shift
  have h' : Γ.map Fm.shift ⊢[PRAAx] pointPowers (Syn.shift f) (Syn.shift m) (Syn.shift L) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa [Syn.shift] using (curve_equation (Syn.shift f) (Syn.shift m) (Syn.shift c) (abscissa (Syn.shift L) (var 0))
    (ordinate (Syn.shift L) (var 0)) hm'.wk hf'.wk).iffMpr (point_power_at (Syn.shift f) (Syn.shift m) (Syn.shift L) (var 0) h'.wk Prf.hyp0)

theorem weighted_zero_bound (f G m a c L : PTm n) (h : Γ ⊢[PRAAx] input f G m a c)
    (hp : Γ ⊢[PRAAx] pointInput f G m L) : Γ ⊢[PRAAx] le (length L) (weightedDegree G m a (d f c)) := by
  have hn := monic_input f G m a c h
  have hf := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have hcurve := curve_points f m c L (Prf.andE₁ hn) hf (Prf.andE₁ (Prf.andE₂ hp))
  have cert := exact_norm_degree f G m a c h
  have count := RationalPolynomialMonicNorm.finite_zero_bound (tailRows f m c) G m a c L
    (.andI hn (.andI (.andI (.andE₁ hp) (.andI hcurve (.andE₂ (.andE₂ hp)))) (.andE₁ cert)))
  exact le_congr (.eqRefl _) (.andE₁ (.andE₂ cert)) count

def normF : PR 5 := PTm.toPR (norm (var 0) (var 1) (var 2) (var 3) (var 4))
theorem norm_at (f G m a c : PTm n) : Γ ⊢[PRAAx] PTm.app normF ![f,G,m,a,c] ≐ norm f G m a c := by
  simpa [normF] using toPR_eq (Γ := Γ) (norm (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![f,G,m,a,c]

theorem actual_rational_superelliptic_norm_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ certificate (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (exact_norm_degree _ _ _ _ _ Prf.hyp0))

theorem actual_rational_superelliptic_curve_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ length (var 0) ≐ succ (var 2) ⟶ Fm.iff
      (RationalArgmin.rationalEq (RationalBivariateGaussianEmbedding.monic (tailRows (var 0) (var 1) (var 2))
        (var 1) (var 3) (var 4)) scalarZero)
      (RationalArgmin.rationalEq (power (var 4) (var 1)) (RationalPolynomialGaussianEmbedding.evaluate (var 0) (var 3)))) :=
  closeUniv 5 (.impI (.impI (curve_equation _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_rational_superelliptic_weighted_zero_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ pointInput (var 0) (var 1) (var 2) (var 5) ⟶
      le (length (var 5)) (weightedDegree (var 1) (var 2) (var 3) (d (var 0) (var 4)))) :=
  closeUniv 6 (.impI (.impI (weighted_zero_bound _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_rational_superelliptic_norm_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (PTm.app normF ![var 0,var 1,var 2,var 3,var 4] ≐ norm (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (norm_at _ _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalSuperellipticNormDegree
