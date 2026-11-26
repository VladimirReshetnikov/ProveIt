import IPRADerivations.Analysis.Trigonometry.Hyperbolic.GaussianSineProductImaginaryLogDerivativeTail
import IPRADerivations.Analysis.Names.GaussianNameConjugation

/-!
# Exact denominator rescaling of the imaginary sine product and slope

Multiplying A and B by a positive integer preserves the literal product,
its logarithmic-derivative sum, and every observation of both cofinal
names. This permits dyadic increments at a fixed rational base point.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryScaling

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (eval_im_code eval_re_code)
open GaussianGammaEulerReflectionHead (body)
open GaussianNameConjugation (equal_samples_cross pointwiseEqual)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalFiniteProduct (product_zero)
open GaussianRationalHorner
  (canonical_unique ofGaussian_canonical ofGaussian_represents positive_product represents_congr)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr rescale_to)
open GaussianRootAlgebra (equal_of_values im_scale re_scale)
open GaussianSineProductImaginaryLogDerivative
  (axisNumerator factor factor_value logarithmRow logarithmSum logarithm_sum_succ product rationalReal realNumerator
    squareDenominator)
open GaussianSineProductName (sine_product_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem real_congr {a b E D : PTm n} (ha : Γ ⊢[PRAAx] a ≐ b) (hd : Γ ⊢[PRAAx] E ≐ D) :
    Γ ⊢[PRAAx] rationalReal a E ≐ rationalReal b D := by
  simpa only [GaussianSineProductImaginaryLogDerivative.subst_rationalReal,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rationalReal (var 0) (var 1) : PTm 2)
        (σ := ![a,E]) (σ' := ![b,D]) (fun i => by fin_cases i; exact ha; exact hd)

theorem rational_real_rescale (a B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] rationalReal (k*a) (k*B) ≐ rationalReal a B := by
  have scaled := rescale_to (rationalReal a B) (realNumerator a) B k (k*B)
    (ofGaussian_represents (Γ := Γ) _ _ hB) (mul_comm _ _)
  have positive := positive_product k B hk hB
  apply canonical_unique _ _ _ (k*B) (ofGaussian_canonical _ _ positive) (ofGaussian_canonical _ _ hB) positive
    (ofGaussian_represents _ _ positive) ?_
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := scaled)
  apply equal_of_values
  · simp only [re_scale, realNumerator, eval_re_code, ZT.toZ_ofNat]
    ipra_simps
  · simp [im_scale, realNumerator, eval_im_code, ZT.toZ_ofNat]

private theorem denominator_positive (i B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (squareDenominator i B) :=
  positive_product _ _ (positive_product _ _ hB (zero_lt_succ _))
    (positive_product _ _ hB (zero_lt_succ _))

theorem factor_rescale (i A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] factor i (k*A) (k*B) ≐ factor i A B := by
  have hk2 := positive_product _ _ hk hk
  have hE := denominator_positive i B hB
  have e : Γ ⊢[PRAAx] squareDenominator i (k*B) ≐ (k*k)*squareDenominator i B := by
    unfold squareDenominator
    ipra_ring
  have s : Γ ⊢[PRAAx] squareDenominator i (k*B)+(k*A)*(k*A) ≐ (k*k)*(squareDenominator i B+A*A) := by
    unfold squareDenominator
    ipra_ring
  exact (factor_value i (k*A) (k*B) (positive_product _ _ hk hB)).eqTrans
    ((real_congr s e).eqTrans ((rational_real_rescale _ _ _ hE hk2).eqTrans (factor_value i A B hB).eqSymm))

theorem row_rescale (i A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] logarithmRow i (k*A) (k*B) ≐ logarithmRow i A B := by
  let E := squareDenominator i B+A*A
  have hE : Γ ⊢[PRAAx] le one E := le_trans (denominator_positive i B hB) (le_add_right _ _)
  have e : Γ ⊢[PRAAx] squareDenominator i (k*B)+(k*A)*(k*A) ≐ (k*k)*E := by
    unfold E squareDenominator
    ipra_ring
  have s : Γ ⊢[PRAAx] two*(k*A)*(k*B) ≐ (k*k)*(two*A*B) := by ipra_ring
  exact (real_congr s e).eqTrans (rational_real_rescale _ _ _ hE (positive_product _ _ hk hk))

def invariance (A B k N : PTm n) : Fm PTm n :=
  (product (k*A) (k*B) N ≐ product A B N) ⋏ (logarithmSum (k*A) (k*B) N ≐ logarithmSum A B N)

ipra_subst invariance

theorem finite_rescale (A B k N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] invariance A B k N := by
  let Δ := Γ.map Fm.shift
  let s (t : PTm n) := Syn.shift t
  have hBs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hB.shift
  have hks : Δ ⊢[PRAAx] le one (s k) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hk.shift
  have base : Γ ⊢[PRAAx] invariance A B k zero := by
    have p (a d : PTm n) : Γ ⊢[PRAAx] product a d zero ≐ GaussianRationalSyntheticDivision.qone :=
      product_zero body (pairT (axisNumerator a) d)
    have q (a d : PTm n) : Γ ⊢[PRAAx] logarithmSum a d zero ≐ GaussianRationalHorner.qzero :=
      GaussianRationalFiniteSum.sum_zero _ _
    exact .andI ((p _ _).eqTrans (p _ _).eqSymm) ((q _ _).eqTrans (q _ _).eqSymm)
  have all : Γ ⊢[PRAAx] .all (invariance (s A) (s B) (s k) (var 0)) := by
    refine PRA.qfInd _ (by constructor <;> trivial) ?_ ?_
    · simpa only [subst_invariance, s, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using base
    · simp only [subst_invariance, s, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let a := s A
      let b := s B
      let m := s k
      let i : PTm (n+1) := var 0
      have h : (invariance a b m i :: Δ) ⊢[PRAAx] invariance a b m i := Prf.hyp0
      have p : (invariance a b m i :: Δ) ⊢[PRAAx] product (m*a) (m*b) (succ i) ≐ product a b (succ i) :=
        (sine_product_succ (axisNumerator (m*a)) (m*b) i).eqTrans
          ((qmul_congr h.andE₁ (factor_rescale i a b m hBs.wk hks.wk)).eqTrans
            (sine_product_succ (axisNumerator a) b i).eqSymm)
      have q : (invariance a b m i :: Δ) ⊢[PRAAx] logarithmSum (m*a) (m*b) (succ i) ≐ logarithmSum a b (succ i) :=
        (logarithm_sum_succ (m*a) (m*b) i).eqTrans
          ((qadd_congr h.andE₂ (row_rescale i a b m hBs.wk hks.wk)).eqTrans (logarithm_sum_succ a b i).eqSymm)
      exact .andI p q
  simpa only [subst_invariance, s, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using all.allE N

private abbrev sineF := GaussianSineProductName.nameF
private abbrev rowF := GaussianSineProductImaginaryLogDerivativeTail.nameF
def sineData (A B R : PTm n) : PTm n := GaussianSineProductName.data (axisNumerator A) R B
local notation "rowData" => GaussianSineProductImaginaryLogDerivativeTail.data

ipra_subst sineData [GaussianSineProductName.data]

theorem product_sample_rescale (A B k R p : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] ap2 sineF p (sineData (k*A) (k*B) R) ≐ ap2 sineF p (sineData A B R) :=
  (GaussianSineProductName.sample_at (axisNumerator (k*A)) R (k*B) p).eqTrans
    ((finite_rescale A B k (GaussianSineProductName.cutoff R p) hB hk).andE₁.eqTrans
      (GaussianSineProductName.sample_at (axisNumerator A) R B p).eqSymm)

theorem row_sample_rescale (A B k R p : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] ap2 rowF p (rowData (k*A) (k*B) R) ≐ ap2 rowF p (rowData A B R) :=
  (GaussianSineProductImaginaryLogDerivativeTail.sample_at (k*A) (k*B) R p).eqTrans
    ((finite_rescale A B k (GaussianSineProductImaginaryLogDerivativeTail.cutoff R p) hB hk).andE₂.eqTrans
      (GaussianSineProductImaginaryLogDerivativeTail.sample_at A B R p).eqSymm)

theorem cofinal_rescale (A B k R : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k)
    (hA : Γ ⊢[PRAAx] le A (R*B)) : Γ ⊢[PRAAx]
    crossEquivalent sineF sineF (sineData (k*A) (k*B) R) (sineData A B R) ⋏
      crossEquivalent rowF rowF (rowData (k*A) (k*B) R) (rowData A B R) := by
  let Δ := Γ.map Fm.shift
  let s (t : PTm n) := Syn.shift t
  have hb : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hB.shift
  have hks : Δ ⊢[PRAAx] le one (s k) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hk.shift
  have scaledB := positive_product _ _ hk hB
  have scaledA : Γ ⊢[PRAAx] le (k*A) (R*(k*B)) :=
    le_congr (mul_comm _ _) (by ipra_ring) (mul_le_mul_right k hA)
  have disk (a b : PTm n) (h : Γ ⊢[PRAAx] le a (R*b)) :
      Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (axisNumerator a) (R*b) :=
    le_congr (GaussianSineProductImaginaryLogDerivativeTail.axis_norm a).eqSymm (.eqRefl _) (le_mul_mono h h)
  refine .andI (equal_samples_cross _ _ _ _
    (GaussianSineProductName.name_regular _ _ _ scaledB (disk _ _ scaledA))
    (GaussianSineProductName.name_regular _ _ _ hB (disk _ _ hA)) (.allI ?_))
    (equal_samples_cross _ _ _ _
      (GaussianSineProductImaginaryLogDerivativeTail.regular _ _ _ scaledB scaledA)
      (GaussianSineProductImaginaryLogDerivativeTail.regular _ _ _ hB hA) (.allI ?_))
  · simpa only [pointwiseEqual, Syn.shift, s, Δ, subst_sineData, PTm.subst_mul] using
      product_sample_rescale (s A) (s B) (s k) (s R) (var 0) hb hks
  · simpa only [pointwiseEqual, Syn.shift, s, Δ, GaussianSineProductImaginaryLogDerivativeTail.subst_data, PTm.subst_mul]
      using row_sample_rescale (s A) (s B) (s k) (s R) (var 0) hb hks

theorem actual_imaginary_sine_product_finite_rescale_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 1) ⋏ le one (var 2)) ⟶ invariance (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (finite_rescale _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryScaling
