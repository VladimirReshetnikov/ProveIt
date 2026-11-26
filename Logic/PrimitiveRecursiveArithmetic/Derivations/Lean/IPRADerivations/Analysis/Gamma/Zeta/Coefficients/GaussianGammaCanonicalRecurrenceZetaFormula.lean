import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalCoefficientRecurrence

/-!
# The literal original gamma plus signed-zeta recurrence formula

The actual finite sum on the right of named C42 is rewritten into its
original displayed terms: gamma times c_(s+1), plus the finite signed
zeta sum over c_1 through c_s. All coefficients and scalar gamma/zeta
samples are the SAME original programs. This is an exact finite code
identity at each actual query, and therefore also binds the retimed
right name to the displayed source formula. No recurrence premise is
used in this rearrangement.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalRecurrenceZetaFormula

open_ipra
open GaussianRationalHorner (qmul qadd qzero)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open GaussianRationalEulerCoefficients (parityPoint)
open RationalGaussianEmbedding (embed)
open GaussianGammaHigherCoefficientName (sample)
open GaussianGammaCanonicalRecurrenceTerms (canonicalTerm canonicalSum data body)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def zetaTerm (p e j : PTm n) : PTm n :=
  qmul (qmul (parityPoint (pred (monus e j)))
    (embed (RationalReciprocalPowerName.zetaSample p (monus e j)))) (sample p j)
def zetaBody : PTm 2 := zetaTerm (fstT (var 1)) (sndT (var 1)) (var 0)
def formula (p s : PTm n) : PTm n :=
  qadd (qmul (embed (GammaEulerConstantName.gammaSample p zero)) (sample p (succ s)))
    (GaussianRationalFiniteSum.sum (shiftBody zetaBody) s (data p (succ (succ s))))
ipra_subst zetaTerm
ipra_subst formula

theorem zeta_term_congr {p q e f j k : PTm n} (hp : Γ ⊢[PRAAx] p ≐ q)
    (he : Γ ⊢[PRAAx] e ≐ f) (hj : Γ ⊢[PRAAx] j ≐ k) : Γ ⊢[PRAAx] zetaTerm p e j ≐ zetaTerm q f k := by
  ipra_congr (zetaTerm (var 0) (var 1) (var 2) : PTm 3) with [hp, he, hj]

theorem zeta_term_at (p e j : PTm n) : Γ ⊢[PRAAx] inst2 zetaBody j (data p e) ≐ zetaTerm p e j := by
  simp only [zetaBody,inst2,subst_zetaTerm,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact zeta_term_congr (fst_pair _ _) (snd_pair _ _) (.eqRefl _)

theorem index_high (s j : PTm n) (hj : Γ ⊢[PRAAx] lt j s) : Γ ⊢[PRAAx] le two (monus (succ s) j) := by
  have form : Γ ⊢[PRAAx] monus (succ s) j ≐ succ (succ (monus s (succ j))) :=
    (congrMonus (congrSucc (AnalyticNumberTheory.Totatives.split_lt hj)) (.eqRefl _)).eqTrans
      ((congrMonus (by ipra_ring) (.eqRefl _)).eqTrans (add_monus _ _))
  exact le_congr (.eqRefl _) form.eqSymm
    ((succ_monus_succ _ _).eqTrans ((succ_monus_succ _ _).eqTrans (zero_le _)))

theorem original_high_term (p s j : PTm n) (hj : Γ ⊢[PRAAx] lt j s) : Γ ⊢[PRAAx]
    canonicalTerm p (succ s) j ≐ zetaTerm p (succ s) j :=
  qmul_congr (GaussianGammaRecurrenceWeightCompatibility.original_full_high_weight _ _ (index_high s j hj)) (.eqRefl _)

theorem original_gamma_last_term (p s : PTm n) : Γ ⊢[PRAAx]
    canonicalTerm p (succ s) s ≐ qmul (embed (GammaEulerConstantName.gammaSample p zero)) (sample p s) :=
  qmul_congr ((GaussianGammaRecurrenceWeights.weight_congr (.eqRefl _) (.eqRefl _)
    ((congrMonus (by ipra_ring) (.eqRefl _)).eqTrans (add_monus _ _))).eqTrans
      (GaussianGammaRecurrenceWeights.weight_one _ _)) (.eqRefl _)

theorem original_high_prefix (p s : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum body s (data p (succ s)) ≐
      GaussianRationalFiniteSum.sum zetaBody s (data p (succ s)) := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have h := (GaussianGammaCanonicalRecurrenceTerms.canonical_term_at (Γ := lt (var 0) (Syn.shift s) :: Γ.map Fm.shift)
    (Syn.shift p) (succ (Syn.shift s)) (var 0)).eqTrans
      ((original_high_term _ _ _ Prf.hyp0).eqTrans (zeta_term_at _ _ _).eqSymm)
  simpa only [GaussianRationalFiniteSum.termsEqual,GaussianGammaCanonicalRecurrenceTerms.subst_data,
    PTm.subst_succ,Syn.shift] using h

theorem original_zeta_zero_term (p e : PTm n) : Γ ⊢[PRAAx] zetaTerm p e zero ≐ qzero :=
  (qmul_congr (.eqRefl _) (GaussianGammaCanonicalCoefficientRecurrence.canonical_zero p)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _)

theorem original_zeta_prefix_without_zero (p s e : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum zetaBody (succ s) (data p e) ≐
      GaussianRationalFiniteSum.sum (shiftBody zetaBody) s (data p e) :=
  (GaussianRationalFiniteSum.sum_shift_first _ _ _).eqTrans
    ((qadd_congr ((zeta_term_at _ _ _).eqTrans (original_zeta_zero_term _ _)) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalFiniteSum.sum_canonical _ _ _)))

theorem original_literal_C42_formula (p s : PTm n) : Γ ⊢[PRAAx]
    canonicalSum p (succ (succ s)) ≐ formula p s :=
  (GaussianRationalFiniteSum.sum_succ body (succ s) (data p (succ (succ s)))).eqTrans
    ((qadd_congr ((original_high_prefix p (succ s)).eqTrans (original_zeta_prefix_without_zero _ _ _))
      ((GaussianGammaCanonicalRecurrenceTerms.canonical_term_at _ _ _).eqTrans (original_gamma_last_term _ _))).eqTrans
        (GaussianRationalLinearProduct.qadd_commutative _ _))

theorem original_named_sample_formula (p s : PTm n) : Γ ⊢[PRAAx]
    GaussianGammaCanonicalRecurrenceName.sumSample p (succ s) ≐
      formula (GaussianGammaCanonicalRecurrenceName.clock p (succ s)) s :=
  (GaussianGammaCanonicalRecurrenceName.sample_at _ _).eqTrans (original_literal_C42_formula _ _)

theorem original_named_C42_formula (p q s : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded
      (GaussianGammaCanonicalCoefficientRecurrence.leftSample p (succ s))
      (formula (GaussianGammaCanonicalRecurrenceName.clock q (succ s)) s)
      (GaussianCoefficientNameBounds.unit p+GaussianCoefficientNameBounds.unit q)
      (GaussianCoefficientNameBounds.unit p*GaussianCoefficientNameBounds.unit q) :=
  GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (original_named_sample_formula q s) (.eqRefl _) (.eqRefl _)
    (GaussianGammaCanonicalCoefficientRecurrence.original_named_observation p q (succ s))

theorem original_Gamma_C42_literal_gamma_signed_zeta_formula_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (canonicalSum (var 0) (succ (succ (var 1))) ≐ formula (var 0) (var 1)) :=
  closeUniv 2 (original_literal_C42_formula _ _)

theorem original_Gamma_C42_actual_named_sample_literal_formula_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianGammaCanonicalRecurrenceName.sumSample (var 0) (succ (var 1)) ≐
      formula (GaussianGammaCanonicalRecurrenceName.clock (var 0) (succ (var 1))) (var 1)) :=
  closeUniv 2 (original_named_sample_formula _ _)

theorem original_Gamma_C42_independent_named_observations_literal_formula_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (GaussianRationalMetric.distanceBounded
        (GaussianGammaCanonicalCoefficientRecurrence.leftSample (var 0) (succ (var 2)))
        (formula (GaussianGammaCanonicalRecurrenceName.clock (var 1) (succ (var 2))) (var 2))
        (GaussianCoefficientNameBounds.unit (var 0)+GaussianCoefficientNameBounds.unit (var 1))
        (GaussianCoefficientNameBounds.unit (var 0)*GaussianCoefficientNameBounds.unit (var 1))) :=
  closeUniv 3 (original_named_C42_formula _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalRecurrenceZetaFormula
