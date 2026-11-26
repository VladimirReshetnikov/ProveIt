import IPRADerivations.Analysis.Polynomials.GaussianRationalPolynomialDegree
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRationalMonicReconstruction
import IPRADerivations.Core.LinearCombination

/-!
# Actual convolution, leading coefficient and computed product degree

The same runtime product and bounded coefficient scan are used throughout.
All lists, degrees, prefix lengths and convolution indices are numerical.
Zero factors are treated separately from the nonzero degree-additivity case.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProductDegree

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qadd_congr qmul_congr qzero_canonical qmul_zero_left qmul_zero_right canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant
  (recode recode_congr recode_canonical recode_eq zeroPrefix zero_prefix_at)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticCoefficientValues (qmul_recode_left qmul_recode_right)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProduct
  (product coefficient contribution contribution_inside contribution_outside contribution_body_at
    coefficient_canonical product_length product_lookup product_canonical constant_zero_sum)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree
  (first flag degree nonzeroCoefficients allZero first_zero_prefix first_nonzero
    first_from_witness flag_one_of_nonzero found_of_flag_one success_index degree_le)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReconstruction
  (spike spikeBody spikeData spikeSum spike_hit spike_miss spike_sum active_on spike_body_at
    different_of_lt different_of_gt)
open LeanProofs.IPRA.Analysis.GaussianRationalLinearProduct (padded padded_inside padded_outside)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def leading (C N : PTm n) : PTm n := recode (entry C (first C N))
@[simp] theorem subst_leading {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (leading C N) = leading (Syn.subst σ C) (Syn.subst σ N) := by simp [leading]

theorem raw_zero_left (a b : PTm n) (h : Γ ⊢[PRAAx] recode a ≐ qzero) : Γ ⊢[PRAAx] qmul a b ≐ qzero :=
  (qmul_recode_left _ _).eqSymm.eqTrans ((qmul_congr h (.eqRefl _)).eqTrans (qmul_zero_left _))
theorem raw_zero_right (a b : PTm n) (h : Γ ⊢[PRAAx] recode b ≐ qzero) : Γ ⊢[PRAAx] qmul a b ≐ qzero :=
  (qmul_recode_right _ _).eqSymm.eqTrans ((qmul_congr (.eqRefl _) h).eqTrans (qmul_zero_right _))
theorem product_recodes (a b : PTm n) : Γ ⊢[PRAAx] qmul a b ≐ qmul (recode a) (recode b) :=
  (qmul_recode_left _ _).eqSymm.eqTrans (qmul_recode_right (recode a) b).eqSymm

theorem difference_before (e f k i : PTm n) (hk : Γ ⊢[PRAAx] lt k (e+f))
    (hei : Γ ⊢[PRAAx] le e i) (hik : Γ ⊢[PRAAx] le i k) : Γ ⊢[PRAAx] lt (monus k i) f := by
  apply le_of_eq_add (d := monus i e+monus (e+f) (succ k))
  ipra_lc natEq (eq_add_of_le hk)+natEq (eq_add_of_le hei)+natEq (eq_add_of_le hik)

theorem difference_at (e f i : PTm n) (hei : Γ ⊢[PRAAx] lt e i)
    (hik : Γ ⊢[PRAAx] le i (e+f)) : Γ ⊢[PRAAx] lt (monus (e+f) i) f := by
  apply le_of_eq_add (d := monus i (succ e))
  ipra_lc natEq (eq_add_of_le hei)+natEq (eq_add_of_le hik)

theorem prefix_contribution_zero (P Q M e f k i : PTm n)
    (hP : Γ ⊢[PRAAx] zeroPrefix P e) (hQ : Γ ⊢[PRAAx] zeroPrefix Q f)
    (hk : Γ ⊢[PRAAx] lt k (e+f)) : Γ ⊢[PRAAx] contribution P Q M k i ≐ qzero := by
  refine .orE (lt_or_le k i) (contribution_outside _ _ _ _ _ Prf.hyp0) ?_
  refine .orE (lt_or_le i e) ?_ ?_
  · exact (contribution_inside _ _ _ _ _ Prf.hyp1).eqTrans
      (raw_zero_left _ _ (zero_prefix_at _ _ _ hP.wk.wk Prf.hyp0))
  · have less := difference_before e f k i hk.wk.wk Prf.hyp0 Prf.hyp1
    refine (contribution_inside _ _ _ _ _ Prf.hyp1).eqTrans ?_
    refine .orE (lt_or_le (monus k i) (succ M)) ?_ ?_
    · exact (qmul_congr (.eqRefl _) (padded_inside _ _ _ Prf.hyp0)).eqTrans
        (raw_zero_right _ _ (zero_prefix_at _ _ _ hQ.wk.wk.wk less.wk))
    · exact (qmul_congr (.eqRefl _) (padded_outside _ _ _ Prf.hyp0)).eqTrans (qmul_zero_right _)

/-- Bounded entry equality is transported through the genuine QF finite
sum kernel; no global convolution-zero law is assumed by its consumers. -/
def zeroTerms (P Q M t k : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift t) ⟶
  contribution (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift k) (var 0) ≐ qzero)
@[simp] theorem subst_zeroTerms {l : ℕ} (σ : Fin n → PTm l) (P Q M t k : PTm n) :
    (zeroTerms P Q M t k).subst σ = zeroTerms (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ M)
      (Syn.subst σ t) (Syn.subst σ k) := by simp [zeroTerms,Syn.subst_shift,Syn.shift_subst]
theorem zero_terms_at (P Q M t k i : PTm n) (h : Γ ⊢[PRAAx] zeroTerms P Q M t k)
    (hi : Γ ⊢[PRAAx] lt i t) : Γ ⊢[PRAAx] contribution P Q M k i ≐ qzero := by
  have e : Γ ⊢[PRAAx] lt i t ⟶ contribution P Q M k i ≐ qzero := by
    simpa only [zeroTerms,Fm.subst_imp,Fm.subst_eq,GaussianRationalPolynomialProduct.subst_contribution,
      GaussianRationalHorner.subst_qzero,subst_lt,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE e hi
theorem coefficient_zero_of_contributions (P Q M t k : PTm n)
    (h : Γ ⊢[PRAAx] zeroTerms P Q M t k) : Γ ⊢[PRAAx]
    coefficient P Q M t k ≐ qzero := by
  have eqs : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual GaussianRationalPolynomialProduct.contributionBody
      (qzero : PTm 2) t (GaussianRationalPolynomialProduct.data P Q M k) zero := by
    refine .allI (.impI ?_)
    have hs : Γ.map Fm.shift ⊢[PRAAx] zeroTerms (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift t) (Syn.shift k) := by
      simpa only [Fm.shift,subst_zeroTerms,Syn.shift] using h.shift
    simpa only [Syn.shift,GaussianRationalPolynomialProduct.subst_data,inst2,GaussianRationalHorner.subst_qzero] using
      (contribution_body_at (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift k) (var 0)).eqTrans
        (zero_terms_at _ _ _ _ _ _ hs.wk Prf.hyp0)
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ eqs).eqTrans (constant_zero_sum _ _)

theorem prefix_coefficient_zero (P Q M t e f k : PTm n)
    (hP : Γ ⊢[PRAAx] zeroPrefix P e) (hQ : Γ ⊢[PRAAx] zeroPrefix Q f)
    (hk : Γ ⊢[PRAAx] lt k (e+f)) : Γ ⊢[PRAAx] coefficient P Q M t k ≐ qzero := by
  apply coefficient_zero_of_contributions
  refine .allI (.impI ?_)
  have ps : Γ.map Fm.shift ⊢[PRAAx] zeroPrefix (Syn.shift P) (Syn.shift e) := by
    simpa only [Fm.shift,GaussianTranslatedNonconstant.subst_zeroPrefix,Syn.shift] using hP.shift
  have qs : Γ.map Fm.shift ⊢[PRAAx] zeroPrefix (Syn.shift Q) (Syn.shift f) := by
    simpa only [Fm.shift,GaussianTranslatedNonconstant.subst_zeroPrefix,Syn.shift] using hQ.shift
  have ks : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift k) (Syn.shift e+Syn.shift f) := by
    simpa only [Fm.shift,subst_lt,PTm.subst_add,Syn.shift] using hk.shift
  exact prefix_contribution_zero _ _ _ _ _ _ _ ps.wk qs.wk ks.wk

theorem contribution_zero_left (P Q M k i : PTm n)
    (h : Γ ⊢[PRAAx] recode (entry P i) ≐ qzero) : Γ ⊢[PRAAx] contribution P Q M k i ≐ qzero := by
  refine .orE (lt_or_le k i) (contribution_outside _ _ _ _ _ Prf.hyp0) ?_
  exact (contribution_inside _ _ _ _ _ Prf.hyp0).eqTrans (raw_zero_left _ _ h.wk)

theorem padded_prefix_zero (Q M f u : PTm n) (hQ : Γ ⊢[PRAAx] zeroPrefix Q f)
    (hu : Γ ⊢[PRAAx] lt u f) : Γ ⊢[PRAAx] recode (padded Q (succ M) u) ≐ qzero := by
  refine .orE (lt_or_le u (succ M)) ?_ ?_
  · exact (recode_congr (padded_inside _ _ _ Prf.hyp0)).eqTrans (zero_prefix_at _ _ _ hQ.wk hu.wk)
  · exact (recode_congr (padded_outside _ _ _ Prf.hyp0)).eqTrans (recode_eq _ qzero_canonical)

theorem contribution_at_sum (P Q M e f : PTm n) (hf : Γ ⊢[PRAAx] le f M) : Γ ⊢[PRAAx]
    contribution P Q M (e+f) e ≐ qmul (recode (entry P e)) (recode (entry Q f)) :=
  (contribution_inside _ _ _ _ _ (le_add_right e f)).eqTrans
    ((qmul_congr (.eqRefl _) ((GaussianRationalLinearProduct.padded_congr (.eqRefl _) (.eqRefl _) (add_monus' f e)).eqTrans
      (padded_inside _ _ _ ((succ_monus_succ _ _).eqTrans hf)))).eqTrans (product_recodes _ _))

theorem leading_contribution (P Q M e f i : PTm n)
    (hP : Γ ⊢[PRAAx] zeroPrefix P e) (hQ : Γ ⊢[PRAAx] zeroPrefix Q f) (hf : Γ ⊢[PRAAx] le f M) : Γ ⊢[PRAAx]
    contribution P Q M (e+f) i ≐ spike e (qmul (recode (entry P e)) (recode (entry Q f))) i := by
  refine .orE (lt_or_le i e) ?_ ?_
  · exact (contribution_zero_left _ _ _ _ _ (zero_prefix_at _ _ _ hP.wk Prf.hyp0)).eqTrans
      (spike_miss _ _ _ (different_of_lt Prf.hyp0)).eqSymm
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · have miss := spike_miss (Γ := (lt e i) :: (le e i) :: Γ) e
        (qmul (recode (entry P e)) (recode (entry Q f))) i (different_of_gt Prf.hyp0)
      refine .orE (lt_or_le (e+f) i) ?_ ?_
      · exact (contribution_outside _ _ _ _ _ Prf.hyp0).eqTrans miss.wk.eqSymm
      · exact (contribution_inside _ _ _ _ _ Prf.hyp0).eqTrans
          ((raw_zero_right _ _ (padded_prefix_zero _ _ _ _ hQ.wk.wk.wk (difference_at e f i Prf.hyp1 Prf.hyp0))).eqTrans miss.wk.eqSymm)
    · exact (GaussianRationalPolynomialProduct.contribution_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm).eqTrans
        ((contribution_at_sum _ _ _ _ _ hf.wk.wk).eqTrans (spike_hit _ _ _ Prf.hyp0.eqSymm).eqSymm)

theorem leading_coefficient (P Q N M e f : PTm n)
    (hP : Γ ⊢[PRAAx] zeroPrefix P e) (hQ : Γ ⊢[PRAAx] zeroPrefix Q f)
    (he : Γ ⊢[PRAAx] le e N) (hf : Γ ⊢[PRAAx] le f M) : Γ ⊢[PRAAx]
    coefficient P Q M (succ N) (e+f) ≐ qmul (recode (entry P e)) (recode (entry Q f)) := by
  have ps : Γ.map Fm.shift ⊢[PRAAx] zeroPrefix (Syn.shift P) (Syn.shift e) := by
    simpa only [Fm.shift,GaussianTranslatedNonconstant.subst_zeroPrefix,Syn.shift] using hP.shift
  have qs : Γ.map Fm.shift ⊢[PRAAx] zeroPrefix (Syn.shift Q) (Syn.shift f) := by
    simpa only [Fm.shift,GaussianTranslatedNonconstant.subst_zeroPrefix,Syn.shift] using hQ.shift
  have fs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift f) (Syn.shift M) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hf.shift
  have eqs : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual GaussianRationalPolynomialProduct.contributionBody spikeBody (succ N)
      (GaussianRationalPolynomialProduct.data P Q M (e+f)) (spikeData e (qmul (recode (entry P e)) (recode (entry Q f)))) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift
    have eq : Δ ⊢[PRAAx]
        inst2 GaussianRationalPolynomialProduct.contributionBody (var 0)
          (GaussianRationalPolynomialProduct.data (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift e+Syn.shift f)) ≐
        inst2 spikeBody (var 0) (spikeData (Syn.shift e) (qmul (recode (entry (Syn.shift P) (Syn.shift e))) (recode (entry (Syn.shift Q) (Syn.shift f))))) :=
      (contribution_body_at (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift e+Syn.shift f) (var 0)).eqTrans
      ((leading_contribution _ _ _ _ _ _ ps.wk qs.wk fs.wk).eqTrans (spike_body_at _ _ _).eqSymm)
    simpa only [Δ,Syn.shift,GaussianRationalPolynomialProduct.subst_data,PTm.subst_add,ConciseIPRA.PTm.subst_succ,GaussianRationalMonicReconstruction.subst_spikeData,
      GaussianRationalHorner.subst_qmul,GaussianTranslatedNonconstant.subst_recode,subst_entry] using eq
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ eqs).eqTrans
    ((spike_sum _ _ _ (GaussianRationalHorner.qmul_canonical _ _)).eqTrans
      (active_on _ _ _ ((succ_monus_succ _ _).eqTrans he)))

theorem sum_bound (e f N M : PTm n) (he : Γ ⊢[PRAAx] le e N) (hf : Γ ⊢[PRAAx] le f M) : Γ ⊢[PRAAx]
    le (e+f) (N+M) := le_trans (add_le_add_right f he)
      (le_congr (add_comm f N) (add_comm M N) (add_le_add_right N hf))

theorem product_zero_prefix (P Q N M e f : PTm n)
    (hP : Γ ⊢[PRAAx] zeroPrefix P e) (hQ : Γ ⊢[PRAAx] zeroPrefix Q f)
    (he : Γ ⊢[PRAAx] le e N) (hf : Γ ⊢[PRAAx] le f M) : Γ ⊢[PRAAx]
    zeroPrefix (product P Q N M) (e+f) := by
  have ps : Γ.map Fm.shift ⊢[PRAAx] zeroPrefix (Syn.shift P) (Syn.shift e) := by
    simpa only [Fm.shift,GaussianTranslatedNonconstant.subst_zeroPrefix,Syn.shift] using hP.shift
  have qs : Γ.map Fm.shift ⊢[PRAAx] zeroPrefix (Syn.shift Q) (Syn.shift f) := by
    simpa only [Fm.shift,GaussianTranslatedNonconstant.subst_zeroPrefix,Syn.shift] using hQ.shift
  have bound : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e+Syn.shift f) (Syn.shift N+Syn.shift M) := by
    simpa only [Fm.shift,subst_le,PTm.subst_add,Syn.shift] using (sum_bound e f N M he hf).shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift (e+f)) :: Γ.map Fm.shift
  have below : Δ ⊢[PRAAx] lt (var 0) (Syn.shift e+Syn.shift f) := by
    simpa only [Δ,Syn.shift,PTm.subst_add] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (e+f)))
  have eq : Δ ⊢[PRAAx] recode (entry (product (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M)) (var 0)) ≐ qzero :=
    (recode_congr (product_lookup _ _ _ _ _ (le_trans (le_of_lt below) bound.wk))).eqTrans
      ((recode_congr (prefix_coefficient_zero _ _ _ _ _ _ _ ps.wk qs.wk below)).eqTrans (recode_eq _ qzero_canonical))
  simpa only [Δ,Syn.shift,GaussianRationalPolynomialProduct.subst_product] using eq

theorem product_entry_at (P Q N M e f : PTm n)
    (hP : Γ ⊢[PRAAx] zeroPrefix P e) (hQ : Γ ⊢[PRAAx] zeroPrefix Q f)
    (he : Γ ⊢[PRAAx] le e N) (hf : Γ ⊢[PRAAx] le f M) : Γ ⊢[PRAAx]
    entry (product P Q N M) (e+f) ≐ qmul (recode (entry P e)) (recode (entry Q f)) :=
  (product_lookup _ _ _ _ _ (sum_bound e f N M he hf)).eqTrans (leading_coefficient _ _ _ _ _ _ hP hQ he hf)

theorem leading_canonical (C N : PTm n) : Γ ⊢[PRAAx] canonical (leading C N) := recode_canonical _
theorem leading_nonzero (C N : PTm n) (h : Γ ⊢[PRAAx] nonzeroCoefficients C N) : Γ ⊢[PRAAx]
    neg (leading C N ≐ qzero) := first_nonzero C N (found_of_flag_one C N (flag_one_of_nonzero C N h))
theorem multiply_nonzero (a b : PTm n) (ha : Γ ⊢[PRAAx] canonical a) (hb : Γ ⊢[PRAAx] canonical b)
    (hna : Γ ⊢[PRAAx] neg (a ≐ qzero)) (hnb : Γ ⊢[PRAAx] neg (b ≐ qzero)) : Γ ⊢[PRAAx]
    neg (qmul a b ≐ qzero) :=
  .impI (.impE hnb.wk (GaussianRationalFiniteRoots.product_zero_reflect a b ha.wk hb.wk hna.wk Prf.hyp0))

theorem first_exact (C N e : PTm n) (he : Γ ⊢[PRAAx] le e N)
    (hPrefix : Γ ⊢[PRAAx] zeroPrefix C e) (hNonzero : Γ ⊢[PRAAx] neg (recode (entry C e) ≐ qzero)) : Γ ⊢[PRAAx]
    first C N ≐ e := by
  have found := first_from_witness C N e ((succ_monus_succ _ _).eqTrans he) hNonzero
  refine .orE (lt_or_eq_of_le (.andE₂ found)) ?_ Prf.hyp0
  exact .botE _ (.impE (first_nonzero C N (.andE₁ found)).wk (zero_prefix_at _ _ _ hPrefix.wk Prf.hyp0))

theorem product_first (P Q N M : PTm n) (hP : Γ ⊢[PRAAx] nonzeroCoefficients P N)
    (hQ : Γ ⊢[PRAAx] nonzeroCoefficients Q M) : Γ ⊢[PRAAx]
    first (product P Q N M) (N+M) ≐ first P N+first Q M := by
  have ep := success_index P N (flag_one_of_nonzero _ _ hP)
  have fq := success_index Q M (flag_one_of_nonzero _ _ hQ)
  have value : Γ ⊢[PRAAx] recode (entry (product P Q N M) (first P N+first Q M)) ≐ qmul (leading P N) (leading Q M) :=
    (recode_congr (product_entry_at P Q N M (first P N) (first Q M) (first_zero_prefix _ _) (first_zero_prefix _ _) ep fq)).eqTrans
      (recode_eq _ (GaussianRationalHorner.qmul_canonical _ _))
  have nonzero := multiply_nonzero (leading P N) (leading Q M) (leading_canonical _ _) (leading_canonical _ _)
    (leading_nonzero _ _ hP) (leading_nonzero _ _ hQ)
  exact first_exact _ _ _ (sum_bound _ _ _ _ ep fq)
    (product_zero_prefix _ _ _ _ _ _ (first_zero_prefix _ _) (first_zero_prefix _ _) ep fq)
    (.impI (.impE nonzero.wk (value.wk.eqSymm.eqTrans Prf.hyp0)))

theorem product_success (P Q N M : PTm n) (hP : Γ ⊢[PRAAx] nonzeroCoefficients P N)
    (hQ : Γ ⊢[PRAAx] nonzeroCoefficients Q M) : Γ ⊢[PRAAx] flag (product P Q N M) (N+M) ≐ one := by
  apply GaussianRationalPolynomialDegree.flag_one_of_found
  exact lt_congr (product_first P Q N M hP hQ).eqSymm (.eqRefl _)
    ((succ_monus_succ _ _).eqTrans (sum_bound _ _ _ _ (success_index _ _ (flag_one_of_nonzero _ _ hP))
      (success_index _ _ (flag_one_of_nonzero _ _ hQ))))

theorem product_leading (P Q N M : PTm n) (hP : Γ ⊢[PRAAx] nonzeroCoefficients P N)
    (hQ : Γ ⊢[PRAAx] nonzeroCoefficients Q M) : Γ ⊢[PRAAx]
    leading (product P Q N M) (N+M) ≐ qmul (leading P N) (leading Q M) :=
  (recode_congr (entry_congr (.eqRefl _) (product_first _ _ _ _ hP hQ))).eqTrans
    ((recode_congr (product_entry_at _ _ _ _ _ _ (first_zero_prefix _ _) (first_zero_prefix _ _)
      (success_index _ _ (flag_one_of_nonzero _ _ hP)) (success_index _ _ (flag_one_of_nonzero _ _ hQ)))).eqTrans
      (recode_eq _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem degree_difference (N M e f : PTm n) (he : Γ ⊢[PRAAx] le e N) (hf : Γ ⊢[PRAAx] le f M) : Γ ⊢[PRAAx]
    monus (N+M) (e+f) ≐ monus N e+monus M f := by
  ipra_lc natEq (eq_add_of_le he)+natEq (eq_add_of_le hf)-natEq (eq_add_of_le (sum_bound e f N M he hf))

theorem product_degree (P Q N M : PTm n) (hP : Γ ⊢[PRAAx] nonzeroCoefficients P N)
    (hQ : Γ ⊢[PRAAx] nonzeroCoefficients Q M) : Γ ⊢[PRAAx]
    degree (product P Q N M) (N+M) ≐ degree P N+degree Q M :=
  (congrMonus (.eqRefl _) (product_first _ _ _ _ hP hQ)).eqTrans
    (degree_difference _ _ _ _ (success_index _ _ (flag_one_of_nonzero _ _ hP))
      (success_index _ _ (flag_one_of_nonzero _ _ hQ)))

theorem left_zero_coefficient (P Q N M k : PTm n) (hP : Γ ⊢[PRAAx] allZero P N) : Γ ⊢[PRAAx]
    coefficient P Q M (succ N) k ≐ qzero := by
  have ps : Γ.map Fm.shift ⊢[PRAAx] allZero (Syn.shift P) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianRationalPolynomialDegree.subst_allZero,Syn.shift] using hP.shift
  apply coefficient_zero_of_contributions
  refine .allI (.impI ?_)
  simpa only [Syn.shift,ConciseIPRA.PTm.subst_succ] using
    contribution_zero_left (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift k) (var 0)
      (zero_prefix_at _ _ _ ps.wk Prf.hyp0)

theorem padded_all_zero (Q M u : PTm n) (hQ : Γ ⊢[PRAAx] allZero Q M) : Γ ⊢[PRAAx]
    recode (padded Q (succ M) u) ≐ qzero := by
  refine .orE (lt_or_le u (succ M)) (padded_prefix_zero _ _ _ _ hQ.wk Prf.hyp0) ?_
  exact (recode_congr (padded_outside _ _ _ Prf.hyp0)).eqTrans (recode_eq _ qzero_canonical)

theorem right_zero_coefficient (P Q N M k : PTm n) (hQ : Γ ⊢[PRAAx] allZero Q M) : Γ ⊢[PRAAx]
    coefficient P Q M (succ N) k ≐ qzero := by
  have qs : Γ.map Fm.shift ⊢[PRAAx] allZero (Syn.shift Q) (Syn.shift M) := by
    simpa only [Fm.shift,GaussianRationalPolynomialDegree.subst_allZero,Syn.shift] using hQ.shift
  apply coefficient_zero_of_contributions
  refine .allI (.impI ?_)
  refine .orE (lt_or_le (Syn.shift k) (var 0)) (contribution_outside _ _ _ _ _ Prf.hyp0) ?_
  exact (contribution_inside _ _ _ _ _ Prf.hyp0).eqTrans
    (raw_zero_right _ _ (padded_all_zero _ _ _ qs.wk.wk))

theorem product_all_zero_left (P Q N M : PTm n) (hP : Γ ⊢[PRAAx] allZero P N) : Γ ⊢[PRAAx]
    allZero (product P Q N M) (N+M) := by
  have ps : Γ.map Fm.shift ⊢[PRAAx] allZero (Syn.shift P) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianRationalPolynomialDegree.subst_allZero,Syn.shift] using hP.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift (N+M))) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift N+Syn.shift M) := by
    have h : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift N+Syn.shift M)) := by
      simpa only [Δ,Syn.shift,PTm.subst_add] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift (N+M))))
    exact (succ_monus_succ _ _).eqSymm.eqTrans h
  have eq : Δ ⊢[PRAAx] recode (entry (product (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M)) (var 0)) ≐ qzero :=
    (recode_congr (product_lookup _ _ _ _ _ bound)).eqTrans
      ((recode_congr (left_zero_coefficient _ _ _ _ _ ps.wk)).eqTrans (recode_eq _ qzero_canonical))
  simpa only [Δ,Syn.shift,GaussianRationalPolynomialProduct.subst_product,ConciseIPRA.PTm.subst_succ] using eq

theorem product_all_zero_right (P Q N M : PTm n) (hQ : Γ ⊢[PRAAx] allZero Q M) : Γ ⊢[PRAAx]
    allZero (product P Q N M) (N+M) := by
  have qs : Γ.map Fm.shift ⊢[PRAAx] allZero (Syn.shift Q) (Syn.shift M) := by
    simpa only [Fm.shift,GaussianRationalPolynomialDegree.subst_allZero,Syn.shift] using hQ.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift (N+M))) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift N+Syn.shift M) := by
    have h : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift N+Syn.shift M)) := by
      simpa only [Δ,Syn.shift,PTm.subst_add] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift (N+M))))
    exact (succ_monus_succ _ _).eqSymm.eqTrans h
  have eq : Δ ⊢[PRAAx] recode (entry (product (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M)) (var 0)) ≐ qzero :=
    (recode_congr (product_lookup _ _ _ _ _ bound)).eqTrans
      ((recode_congr (right_zero_coefficient _ _ _ _ _ qs.wk)).eqTrans (recode_eq _ qzero_canonical))
  simpa only [Δ,Syn.shift,GaussianRationalPolynomialProduct.subst_product,ConciseIPRA.PTm.subst_succ] using eq

theorem product_failure_left (P Q N M : PTm n) (h : Γ ⊢[PRAAx] flag P N ≐ zero) : Γ ⊢[PRAAx]
    flag (product P Q N M) (N+M) ≐ zero :=
  GaussianRationalPolynomialDegree.flag_zero_of_all_zero _ _ (product_all_zero_left _ _ _ _
    (GaussianRationalPolynomialDegree.all_zero_of_flag_zero _ _ h))
theorem product_failure_right (P Q N M : PTm n) (h : Γ ⊢[PRAAx] flag Q M ≐ zero) : Γ ⊢[PRAAx]
    flag (product P Q N M) (N+M) ≐ zero :=
  GaussianRationalPolynomialDegree.flag_zero_of_all_zero _ _ (product_all_zero_right _ _ _ _
    (GaussianRationalPolynomialDegree.all_zero_of_flag_zero _ _ h))

theorem product_leading_nonzero (P Q N M : PTm n) (hP : Γ ⊢[PRAAx] nonzeroCoefficients P N)
    (hQ : Γ ⊢[PRAAx] nonzeroCoefficients Q M) : Γ ⊢[PRAAx] neg (leading (product P Q N M) (N+M) ≐ qzero) :=
  .impI (.impE (multiply_nonzero _ _ (leading_canonical _ _) (leading_canonical _ _)
    (leading_nonzero _ _ hP) (leading_nonzero _ _ hQ)).wk
      ((product_leading _ _ _ _ hP hQ).wk.eqSymm.eqTrans Prf.hyp0))

def input (P Q N M : PTm n) : Fm PTm n :=
  ((length P ≐ succ N) ⋏ (length Q ≐ succ M)) ⋏ (nonzeroCoefficients P N ⋏ nonzeroCoefficients Q M)
def certificate (P Q N M : PTm n) : Fm PTm n :=
  (flag (product P Q N M) (N+M) ≐ one) ⋏
    ((first (product P Q N M) (N+M) ≐ first P N+first Q M) ⋏
      ((leading (product P Q N M) (N+M) ≐ qmul (leading P N) (leading Q M)) ⋏
        (neg (leading (product P Q N M) (N+M) ≐ qzero) ⋏
          (degree (product P Q N M) (N+M) ≐ degree P N+degree Q M))))
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (P Q N M : PTm n) :
    (input P Q N M).subst σ = input (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ N) (Syn.subst σ M) := by simp [input]
@[simp] theorem subst_certificate {l : ℕ} (σ : Fin n → PTm l) (P Q N M : PTm n) :
    (certificate P Q N M).subst σ = certificate (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ N) (Syn.subst σ M) := by simp [certificate]

theorem product_correct (P Q N M : PTm n) (h : Γ ⊢[PRAAx] input P Q N M) : Γ ⊢[PRAAx] certificate P Q N M := by
  have hp := Prf.andE₁ (Prf.andE₂ h)
  have hq := Prf.andE₂ (Prf.andE₂ h)
  exact .andI (product_success _ _ _ _ hp hq) (.andI (product_first _ _ _ _ hp hq)
    (.andI (product_leading _ _ _ _ hp hq) (.andI (product_leading_nonzero _ _ _ _ hp hq) (product_degree _ _ _ _ hp hq))))

/-! The PR4 output retains the actual product and its computed tag, first
index, degree and canonical leading coefficient. No query point is an input. -/
def output (P Q N M : PTm n) : PTm n := pairT (product P Q N M)
  (pairT (flag (product P Q N M) (N+M)) (pairT (first (product P Q N M) (N+M))
    (pairT (degree (product P Q N M) (N+M)) (leading (product P Q N M) (N+M)))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (P Q N M : PTm n) : PTm n := PTm.app outputF ![P,Q,N,M]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (P Q N M : PTm n) :
    Syn.subst σ (output P Q N M) = output (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ N) (Syn.subst σ M) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (P Q N M : PTm n) :
    Syn.subst σ (run P Q N M) = run (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ N) (Syn.subst σ M) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (P Q N M : PTm n) : Γ ⊢[PRAAx] run P Q N M ≐ output P Q N M := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![P,Q,N,M]
theorem returned_product (P Q N M : PTm n) : Γ ⊢[PRAAx] fstT (run P Q N M) ≐ product P Q N M :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_flag (P Q N M : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run P Q N M)) ≐ flag (product P Q N M) (N+M) :=
  (congrFst ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_first (P Q N M : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run P Q N M))) ≐ first (product P Q N M) (N+M) :=
  (congrFst ((congrSnd ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_degree (P Q N M : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run P Q N M)))) ≐ degree (product P Q N M) (N+M) :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_leading (P Q N M : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run P Q N M)))) ≐ leading (product P Q N M) (N+M) :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_product_length (P Q N M : PTm n) : Γ ⊢[PRAAx]
    length (fstT (run P Q N M)) ≐ succ (N+M) :=
  (congrFst (returned_product _ _ _ _)).eqTrans (product_length _ _ _ _)
theorem returned_product_canonical (P Q N M : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (fstT (run P Q N M)) :=
  GaussianRationalMonicReduction.canonical_coefficients_congr (returned_product _ _ _ _) (product_canonical _ _ _ _)
theorem returned_success (P Q N M : PTm n) (hP : Γ ⊢[PRAAx] nonzeroCoefficients P N)
    (hQ : Γ ⊢[PRAAx] nonzeroCoefficients Q M) : Γ ⊢[PRAAx] fstT (sndT (run P Q N M)) ≐ one :=
  (returned_flag _ _ _ _).eqTrans (product_success _ _ _ _ hP hQ)
theorem returned_first_sum (P Q N M : PTm n) (hP : Γ ⊢[PRAAx] nonzeroCoefficients P N)
    (hQ : Γ ⊢[PRAAx] nonzeroCoefficients Q M) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run P Q N M))) ≐ first P N+first Q M :=
  (returned_first _ _ _ _).eqTrans (product_first _ _ _ _ hP hQ)
theorem returned_degree_sum (P Q N M : PTm n) (hP : Γ ⊢[PRAAx] nonzeroCoefficients P N)
    (hQ : Γ ⊢[PRAAx] nonzeroCoefficients Q M) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run P Q N M)))) ≐ degree P N+degree Q M :=
  (returned_degree _ _ _ _).eqTrans (product_degree _ _ _ _ hP hQ)
theorem returned_leading_product (P Q N M : PTm n) (hP : Γ ⊢[PRAAx] nonzeroCoefficients P N)
    (hQ : Γ ⊢[PRAAx] nonzeroCoefficients Q M) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run P Q N M)))) ≐ qmul (leading P N) (leading Q M) :=
  (returned_leading _ _ _ _).eqTrans (product_leading _ _ _ _ hP hQ)

/-! Every list, degree and scan index is bound inside the ordinary closed
object statement. The zero-factor statements deliberately omit additivity. -/
theorem actual_prefix_convolution_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (zeroPrefix (var 0) (var 4) ⟶ zeroPrefix (var 1) (var 5) ⟶ le (var 4) (var 2) ⟶ le (var 5) (var 3) ⟶
      zeroPrefix (product (var 0) (var 1) (var 2) (var 3)) (var 4+var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (product_zero_prefix _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_leading_convolution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (zeroPrefix (var 0) (var 4) ⟶ zeroPrefix (var 1) (var 5) ⟶ le (var 4) (var 2) ⟶ le (var 5) (var 3) ⟶
      entry (product (var 0) (var 1) (var 2) (var 3)) (var 4+var 5) ≐
        qmul (recode (entry (var 0) (var 4))) (recode (entry (var 1) (var 5)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (product_entry_at _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem computed_product_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ certificate (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (product_correct _ _ _ _ Prf.hyp0))
theorem zero_left_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (flag (var 0) (var 2) ≐ zero ⟶ flag (product (var 0) (var 1) (var 2) (var 3)) (var 2+var 3) ≐ zero) :=
  closeUniv 4 (.impI (product_failure_left _ _ _ _ Prf.hyp0))
theorem zero_right_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (flag (var 1) (var 3) ≐ zero ⟶ flag (product (var 0) (var 1) (var 2) (var 3)) (var 2+var 3) ≐ zero) :=
  closeUniv 4 (.impI (product_failure_right _ _ _ _ Prf.hyp0))
theorem actual_product_degree_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem returned_product_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (fstT (run (var 0) (var 1) (var 2) (var 3))) ≐ succ (var 2+var 3)) ⋏
      canonicalCoefficients (fstT (run (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.andI (returned_product_length _ _ _ _) (returned_product_canonical _ _ _ _))
theorem returned_product_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (nonzeroCoefficients (var 0) (var 2) ⟶ nonzeroCoefficients (var 1) (var 3) ⟶
      ((fstT (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ one) ⋏
        ((fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ first (var 0) (var 2)+first (var 1) (var 3)) ⋏
          (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) ≐ degree (var 0) (var 2)+degree (var 1) (var 3))))) :=
  closeUniv 4 (.impI (.impI (.andI (returned_success _ _ _ _ Prf.hyp1 Prf.hyp0)
    (.andI (returned_first_sum _ _ _ _ Prf.hyp1 Prf.hyp0) (returned_degree_sum _ _ _ _ Prf.hyp1 Prf.hyp0)))))
theorem returned_product_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (nonzeroCoefficients (var 0) (var 2) ⟶ nonzeroCoefficients (var 1) (var 3) ⟶
      sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) ≐
        qmul (leading (var 0) (var 2)) (leading (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (returned_leading_product _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProductDegree
