import IPRADerivations.Analysis.Logarithm.GaussianFiniteLogarithmPolynomial
import IPRADerivations.Analysis.RationalArithmetic.GaussianIntegerFractionPowers
import IPRADerivations.Analysis.Logarithm.ComplexLogarithmName

/-!
# The literal finite logarithm equals the original cleared sampler

The actual stored H_d polynomial is compared with the ORIGINAL
`ComplexLogarithmName.finiteNumerator/finiteDenominator` at degree L+2.
The original numerical divisor N>=1 is the only guard. Native signed
numerator recurrences, actual normalized term representations, and a true
QF finite-sum invariant derive this comparison. No disk, sampler equality,
evaluation identity, or logarithm/exponential law is supplied as a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmSampler

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (ofGaussian represents qadd canonical canonical_unique represents_congr positive_product)
open GaussianRationalSyntheticDivision (rescale_to qadd_congr)
open GaussianRootAlgebra (equal equal_of_values equal_of_code equal_re equal_im equal_refl)
open GaussianFiniteLogarithmPolynomial (coefficient sourceTerm polynomial value signNumerator kernelNumerator)
open ComplexLogarithmRemainder (re im add mul scale oneCode power)
open ComplexLogarithmName (finiteNumerator finiteDenominator baseNumerator baseDenominator)
open LogarithmRemainder (denominator denominator_positive three)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def termNumerator (z k : PTm n) : PTm n := ComplexLogarithmRemainder.neg (scale (fact k) (power (ComplexLogarithmRemainder.neg z) (succ k)))
def termDenominator (N k : PTm n) : PTm n := fact (succ k)*pw N (succ k)
def sample (z N L : PTm n) : PTm n := ofGaussian (finiteNumerator z N L) (finiteDenominator N L)
@[simp] theorem subst_termNumerator {m : ℕ} (σ : Fin n → PTm m) (z k : PTm n) :
    Syn.subst σ (termNumerator z k) = termNumerator (Syn.subst σ z) (Syn.subst σ k) := by simp [termNumerator,fact]
@[simp] theorem subst_termDenominator {m : ℕ} (σ : Fin n → PTm m) (N k : PTm n) :
    Syn.subst σ (termDenominator N k) = termDenominator (Syn.subst σ N) (Syn.subst σ k) := by simp [termDenominator,fact]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (z N L : PTm n) :
    Syn.subst σ (sample z N L) = sample (Syn.subst σ z) (Syn.subst σ N) (Syn.subst σ L) := by
  simp [sample,finiteNumerator,finiteDenominator,baseNumerator,baseDenominator,denominator,fact]

theorem kernel_native (k : PTm n) : Γ ⊢[PRAAx] equal (kernelNumerator k)
    (scale (fact k) (GaussianIntegerFractionPowers.parityScalar k)) := by
  have hp := natEq (.andE₁ (LogarithmExponentialCoefficients.kernel_parity (Γ := Γ) k))
  have hn := natEq (.andE₂ (LogarithmExponentialCoefficients.kernel_parity (Γ := Γ) k))
  apply equal_of_values
  · rw [kernelNumerator,ComplexLogarithmRemainder.eval_re_code,
      GaussianRootAlgebra.re_scale,GaussianIntegerFractionPowers.parity_scalar_re]
    change 𝔞((LogarithmExponentialCoefficients.kernel k).pos)-𝔞((LogarithmExponentialCoefficients.kernel k).neg) = _
    rw [hp,hn,Q.mk_mul,map_mul,Q.mk_mul,map_mul]; ring
  · rw [kernelNumerator,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat,
      GaussianRootAlgebra.im_scale,GaussianIntegerFractionPowers.parity_scalar_im,Q.mk_zero,map_zero]
    ring

theorem signed_term_numerator (z k : PTm n) : Γ ⊢[PRAAx]
    equal (mul (kernelNumerator k) (power z (succ k))) (termNumerator z k) := by
  have hr := equal_re (kernel_native (Γ := Γ) k)
  have hi := equal_im (kernel_native (Γ := Γ) k)
  have hx : Γ ⊢[PRAAx] equal (mul (kernelNumerator k) (power z (succ k)))
      (scale (fact k) (mul (GaussianIntegerFractionPowers.parityScalar k) (power z (succ k)))) := by
    apply equal_of_values
    · simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.re_scale]
      rw [hr,hi,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale]; ring
    · simp only [GaussianRootAlgebra.im_mul,GaussianRootAlgebra.im_scale]
      rw [hr,hi,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale]; ring
  exact GaussianRootAlgebra.equal_trans hx (GaussianIntegerFractionPowers.factorial_alternating_power z k)

theorem source_term_represents (z N k : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    represents (inst2 sourceTerm k (ofGaussian z N)) (termNumerator z k) (termDenominator N k) := by
  have hf := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) (succ k)
  have hC : Γ ⊢[PRAAx] represents (coefficient k) (kernelNumerator k) (fact (succ k)) :=
    represents_congr (GaussianFiniteLogarithmPolynomial.coefficient_kernel k).eqSymm (equal_refl _) (.eqRefl _)
      (GaussianRationalHorner.ofGaussian_represents _ _ hf)
  rw [GaussianFiniteLogarithmPolynomial.source_term_at]
  exact represents_congr (.eqRefl _) (signed_term_numerator z k) (.eqRefl _)
    (GaussianRationalHorner.qmul_represents _ _ _ _ _ _ hf (ComplexLogarithmCauchy.power_positive _ _ hN)
      hC (GaussianIntegerFractionPowers.power_represents z N (succ k) hN))

theorem finite_denominator_succ (N L : PTm n) : Γ ⊢[PRAAx]
    finiteDenominator N (succ L) ≐ finiteDenominator N L*((L+three)*N) := by
  have hd := natEq (LogarithmRemainder.denominator_succ (Γ := Γ) N L)
  unfold finiteDenominator
  apply deriveNat
  ipra_simps
  rw [hd]
  ring

theorem finite_numerator_succ (z N L : PTm n) : Γ ⊢[PRAAx] equal
    (finiteNumerator z N (succ L))
    (add (scale ((L+three)*N) (finiteNumerator z N L)) (scale (baseDenominator N) (termNumerator z (L+two)))) := by
  have hd := natEq (LogarithmRemainder.denominator_succ (Γ := Γ) N L)
  have hs := GaussianRootAlgebra.values_of_code (ComplexLogarithmRemainder.series_succ (Γ := Γ) z N L)
  have hk : Γ ⊢[PRAAx] succ (L+two) ≐ L+three := by ipra_ring
  have hpCode : Γ ⊢[PRAAx] power (ComplexLogarithmRemainder.neg z) (succ (L+two)) ≐
      power (ComplexLogarithmRemainder.neg z) (L+three) :=
    congrAp2 ComplexLogarithmRemainder.powerF hk (.eqRefl (ComplexLogarithmRemainder.neg z))
  have hp := GaussianRootAlgebra.values_of_code hpCode
  apply equal_of_values
  · simp only [finiteNumerator,termNumerator,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_neg]
    rw [hd,hs.1,hp.1]
    simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_neg,Q.mk_mul,map_mul]
    ring
  · simp only [finiteNumerator,termNumerator,GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_neg]
    rw [hd,hs.2,hp.2]
    simp only [GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_neg,Q.mk_mul,map_mul]
    ring

theorem factorial_one : Γ ⊢[PRAAx] fact (one : PTm n) ≐ one :=
  (fact_succ zero zero).eqTrans ((congrMul (fact_zero zero) (.eqRefl one)).eqTrans (one_mul one))
theorem term_denominator_zero (N : PTm n) : Γ ⊢[PRAAx] termDenominator N zero ≐ N :=
  (congrMul factorial_one (pw_one N)).eqTrans (one_mul N)
theorem term_denominator_one (N : PTm n) : Γ ⊢[PRAAx] termDenominator N one ≐ baseDenominator N := by
  have e : Γ ⊢[PRAAx] zero+two ≐ succ one := by ipra_ring
  have h : Γ ⊢[PRAAx] denominator N zero ≐ termDenominator N one :=
    congrMul (congrAp2 factF e (.eqRefl zero)) (congrAp2 powF e (.eqRefl N))
  exact h.eqSymm.eqTrans (LogarithmRemainder.denominator_zero N)

theorem native_power_one (z : PTm n) : Γ ⊢[PRAAx] equal (power z one) z := by
  have hs := GaussianRootAlgebra.values_of_code (ComplexLogarithmRemainder.power_succ (Γ := Γ) z zero)
  have hz := GaussianRootAlgebra.values_of_code (ComplexLogarithmRemainder.power_zero (Γ := Γ) z)
  apply equal_of_values
  · rw [hs.1,GaussianRootAlgebra.re_mul,hz.1,hz.2,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]; ring
  · rw [hs.2,GaussianRootAlgebra.im_mul,hz.1,hz.2,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]; ring
theorem native_power_two (z : PTm n) : Γ ⊢[PRAAx] equal (power z two) (mul z z) := by
  have hs := GaussianRootAlgebra.values_of_code (ComplexLogarithmRemainder.power_succ (Γ := Γ) z one)
  have hz := native_power_one (Γ := Γ) z
  apply equal_of_values
  · rw [hs.1,GaussianRootAlgebra.re_mul,equal_re hz,equal_im hz,GaussianRootAlgebra.re_mul]
  · rw [hs.2,GaussianRootAlgebra.im_mul,equal_re hz,equal_im hz,GaussianRootAlgebra.im_mul]

theorem term_numerator_zero (z : PTm n) : Γ ⊢[PRAAx] equal (termNumerator z zero) z := by
  have hr := equal_re (native_power_one (Γ := Γ) (ComplexLogarithmRemainder.neg z))
  have hi := equal_im (native_power_one (Γ := Γ) (ComplexLogarithmRemainder.neg z))
  have hf := natEq (fact_zero (Γ := Γ) (zero : PTm n))
  apply equal_of_values
  · rw [termNumerator,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.re_scale,hr,hf,Q.mk_one,map_one,
      GaussianRootAlgebra.re_neg]; ring
  · rw [termNumerator,GaussianRootAlgebra.im_neg,GaussianRootAlgebra.im_scale,hi,hf,Q.mk_one,map_one,
      GaussianRootAlgebra.im_neg]; ring
theorem term_numerator_one (z : PTm n) : Γ ⊢[PRAAx] equal (termNumerator z one) (ComplexLogarithmRemainder.neg (mul z z)) := by
  have hr := equal_re (native_power_two (Γ := Γ) (ComplexLogarithmRemainder.neg z))
  have hi := equal_im (native_power_two (Γ := Γ) (ComplexLogarithmRemainder.neg z))
  have hf := natEq (factorial_one (Γ := Γ) (n := n))
  apply equal_of_values
  · rw [termNumerator,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.re_scale,hr,hf,Q.mk_one,map_one]
    simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg]; ring
  · rw [termNumerator,GaussianRootAlgebra.im_neg,GaussianRootAlgebra.im_scale,hi,hf,Q.mk_one,map_one]
    simp only [GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg]; ring

theorem value_two (w : PTm n) : Γ ⊢[PRAAx] value two w ≐
    qadd (inst2 sourceTerm zero w) (inst2 sourceTerm one w) := by
  have hs : Γ ⊢[PRAAx] GaussianRationalFiniteSum.sum sourceTerm one w ≐ inst2 sourceTerm zero w :=
    (GaussianRationalFiniteSum.sum_succ sourceTerm zero w).eqTrans
      ((qadd_congr (GaussianRationalFiniteSum.sum_zero sourceTerm w) (.eqRefl _)).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add _ (by
          rw [GaussianFiniteLogarithmPolynomial.source_term_at]
          exact GaussianRationalHorner.qmul_canonical _ _)))
  exact (GaussianRationalFiniteSum.sum_succ sourceTerm one w).eqTrans (qadd_congr hs (.eqRefl _))

theorem base_represents (z N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    represents (value two (ofGaussian z N)) (baseNumerator z N) (baseDenominator N) := by
  have hB := ComplexLogarithmName.base_positive N hN
  have h0 : Γ ⊢[PRAAx] represents (inst2 sourceTerm zero (ofGaussian z N)) z N :=
    represents_congr (.eqRefl _) (term_numerator_zero z) (term_denominator_zero N)
      (source_term_represents z N zero hN)
  have h0' := rescale_to _ _ _ (two*N) (baseDenominator N) h0 (by unfold baseDenominator; ipra_ring)
  have h1 : Γ ⊢[PRAAx] represents (inst2 sourceTerm one (ofGaussian z N))
      (ComplexLogarithmRemainder.neg (mul z z)) (baseDenominator N) :=
    represents_congr (.eqRefl _) (term_numerator_one z) (term_denominator_one N)
      (source_term_represents z N one hN)
  exact represents_congr (value_two (ofGaussian z N)).eqSymm (equal_refl _) (.eqRefl _)
    (GaussianRationalHorner.qadd_represents _ _ _ _ _ hB h0' h1)

def sampleLaw (z N L : PTm n) : Fm PTm n :=
  represents (value (L+two) (ofGaussian z N)) (finiteNumerator z N L) (finiteDenominator N L)
@[simp] theorem subst_sampleLaw {m : ℕ} (σ : Fin n → PTm m) (z N L : PTm n) :
    (sampleLaw z N L).subst σ = sampleLaw (Syn.subst σ z) (Syn.subst σ N) (Syn.subst σ L) := by
  simp [sampleLaw,finiteNumerator,finiteDenominator,baseNumerator,baseDenominator,denominator,fact]

theorem sample_zero (z N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] sampleLaw z N zero := by
  have hs := GaussianRationalHorner.represents_rescale _ _ _ (denominator N zero) (base_represents z N hN)
  have hz := GaussianRootAlgebra.values_of_code (ComplexLogarithmRemainder.series_zero (Γ := Γ) z N)
  have he : Γ ⊢[PRAAx] equal (scale (denominator N zero) (baseNumerator z N)) (finiteNumerator z N zero) := by
    apply equal_of_values
    · simp only [finiteNumerator,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale]
      rw [hz.1,GaussianRootAlgebra.re_zero]; ring
    · simp only [finiteNumerator,GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_scale]
      rw [hz.2,GaussianRootAlgebra.im_zero]; ring
  exact represents_congr (GaussianRationalFiniteSum.sum_index_congr sourceTerm (zero_add two).eqSymm (.eqRefl _))
    he (.eqRefl _) hs

theorem sample_step (z N L : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (ih : Γ ⊢[PRAAx] sampleLaw z N L) : Γ ⊢[PRAAx] sampleLaw z N (succ L) := by
  have hD := ComplexLogarithmName.finite_positive N (succ L) hN
  have he : Γ ⊢[PRAAx] termDenominator N (L+two) ≐ denominator N (succ L) := by
    have e : Γ ⊢[PRAAx] succ (L+two) ≐ succ L+two := by ipra_ring
    exact congrMul (congrAp2 factF e (.eqRefl zero)) (congrAp2 powF e (.eqRefl N))
  have hPrev : Γ ⊢[PRAAx] represents (value (L+two) (ofGaussian z N))
      (scale ((L+three)*N) (finiteNumerator z N L)) (finiteDenominator N (succ L)) :=
    rescale_to _ _ _ _ _ ih (finite_denominator_succ N L).eqSymm
  have hTerm : Γ ⊢[PRAAx] represents (inst2 sourceTerm (L+two) (ofGaussian z N))
      (scale (baseDenominator N) (termNumerator z (L+two))) (finiteDenominator N (succ L)) :=
    rescale_to _ _ _ _ _ (source_term_represents z N (L+two) hN)
      ((congrMul he (.eqRefl _)).eqTrans (mul_comm _ _))
  have hs := GaussianRationalHorner.qadd_represents _ _ _ _ _ hD hPrev hTerm
  have hValue : Γ ⊢[PRAAx] value (succ L+two) (ofGaussian z N) ≐
      qadd (value (L+two) (ofGaussian z N)) (inst2 sourceTerm (L+two) (ofGaussian z N)) :=
    (GaussianRationalFiniteSum.sum_index_congr sourceTerm (by ipra_ring) (.eqRefl _)).eqTrans
      (GaussianRationalFiniteSum.sum_succ sourceTerm (L+two) (ofGaussian z N))
  exact represents_congr hValue.eqSymm (GaussianRootAlgebra.equal_symm (finite_numerator_succ z N L)) (.eqRefl _) hs

theorem finite_sample_represents (z N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] sampleLaw z N L := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
    simpa only [Fm.shift,Syn.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hN.shift
  have all : Γ ⊢[PRAAx] .all (sampleLaw (Syn.shift z) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simp only [subst_sampleLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact sample_zero z N hN
    · simp only [subst_sampleLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact sample_step _ _ _ hs.wk Prf.hyp0
  simpa only [subst_sampleLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE L

theorem value_eq_original_sample (z N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    value (L+two) (ofGaussian z N) ≐ sample z N L := by
  have hp := ComplexLogarithmName.finite_positive N L hN
  exact canonical_unique _ _ (finiteNumerator z N L) (finiteDenominator N L)
    (GaussianRationalFiniteSum.sum_canonical sourceTerm (L+two) (ofGaussian z N))
    (GaussianRationalHorner.ofGaussian_canonical _ _ hp) hp (finite_sample_represents z N L hN)
    (GaussianRationalHorner.ofGaussian_represents _ _ hp)
theorem polynomial_eq_original_sample (z N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (polynomial (L+two)) (ofGaussian z N) ≐ sample z N L :=
  (GaussianFiniteLogarithmPolynomial.polynomial_evaluation (L+two) (ofGaussian z N)).eqTrans
    (value_eq_original_sample z N L hN)

/-- Literal finite exponential composition of the ORIGINAL cleared sampler. -/
theorem composition_eq_original_sample (z N L K : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (GaussianFiniteLogarithmPolynomial.composition (L+two) K) (ofGaussian z N) ≐
      GaussianRationalPolynomialExponential.scalarSum (sample z N L) K :=
  (GaussianFiniteLogarithmPolynomial.composition_evaluation (L+two) K (ofGaussian z N)).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody
      (.eqRefl (succ K)) (value_eq_original_sample z N L hN))

def output (z N L K : PTm n) : PTm n := pairT (polynomial (L+two))
  (pairT (GaussianFiniteLogarithmPolynomial.composition (L+two) K) (sample z N L))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (z N L K : PTm n) : PTm n := PTm.app outputF ![z,N,L,K]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (z N L K : PTm n) :
    Syn.subst σ (output z N L K) = output (Syn.subst σ z) (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ K) := by
  simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (z N L K : PTm n) :
    Syn.subst σ (run z N L K) = run (Syn.subst σ z) (Syn.subst σ N) (Syn.subst σ L) (Syn.subst σ K) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (z N L K : PTm n) : Γ ⊢[PRAAx] run z N L K ≐ output z N L K := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![z,N,L,K]
theorem returned_polynomial (z N L K : PTm n) : Γ ⊢[PRAAx] fstT (run z N L K) ≐ polynomial (L+two) :=
  (congrFst (program_at z N L K)).eqTrans (fst_pair _ _)
theorem returned_composition (z N L K : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run z N L K)) ≐ GaussianFiniteLogarithmPolynomial.composition (L+two) K :=
  (congrFst ((congrSnd (program_at z N L K)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_sample (z N L K : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run z N L K)) ≐ sample z N L :=
  (congrSnd ((congrSnd (program_at z N L K)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_polynomial_evaluation (z N L K : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (fstT (run z N L K)) (ofGaussian z N) ≐ sndT (sndT (run z N L K)) :=
  (GaussianRationalMonicReduction.evaluate_congr (returned_polynomial z N L K) (.eqRefl _)).eqTrans
    ((polynomial_eq_original_sample z N L hN).eqTrans (returned_sample z N L K).eqSymm)
theorem returned_composition_evaluation (z N L K : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (fstT (sndT (run z N L K))) (ofGaussian z N) ≐
      ap2 GaussianRationalPolynomialExponential.scalarF (sndT (sndT (run z N L K))) K := by
  have hC := GaussianRationalMonicReduction.evaluate_congr (Γ := Γ) (returned_composition z N L K) (.eqRefl (ofGaussian z N))
  have hS : Γ ⊢[PRAAx] GaussianRationalPolynomialExponential.scalarSum (sample z N L) K ≐
      GaussianRationalPolynomialExponential.scalarSum (sndT (sndT (run z N L K))) K :=
    GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody
      (.eqRefl (succ K)) (returned_sample z N L K).eqSymm
  exact hC.eqTrans ((composition_eq_original_sample z N L K hN).eqTrans
    (hS.eqTrans (GaussianRationalPolynomialExponential.scalar_program_at (sndT (sndT (run z N L K))) K).eqSymm))

theorem actual_source_term_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ represents (inst2 sourceTerm (var 2) (ofGaussian (var 0) (var 1)))
      (termNumerator (var 0) (var 2)) (termDenominator (var 1) (var 2))) :=
  closeUniv 3 (.impI (source_term_represents _ _ _ Prf.hyp0))
theorem actual_original_sample_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ sampleLaw (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (finite_sample_represents _ _ _ Prf.hyp0))
theorem literal_sum_equals_original_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ value (var 2+two) (ofGaussian (var 0) (var 1)) ≐ sample (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (value_eq_original_sample _ _ _ Prf.hyp0))
theorem actual_logarithm_polynomial_old_sampler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ GaussianRationalHorner.evaluate (polynomial (var 2+two)) (ofGaussian (var 0) (var 1)) ≐
      sample (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (polynomial_eq_original_sample _ _ _ Prf.hyp0))
theorem literal_finite_composition_old_sampler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ GaussianRationalHorner.evaluate
      (GaussianFiniteLogarithmPolynomial.composition (var 2+two) (var 3)) (ofGaussian (var 0) (var 1)) ≐
        GaussianRationalPolynomialExponential.scalarSum (sample (var 0) (var 1) (var 2)) (var 3)) :=
  closeUniv 4 (.impI (composition_eq_original_sample _ _ _ _ Prf.hyp0))
theorem actual_original_sample_composition_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem returned_original_sample_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ GaussianRationalHorner.evaluate
      (fstT (run (var 0) (var 1) (var 2) (var 3))) (ofGaussian (var 0) (var 1)) ≐
        sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (returned_polynomial_evaluation _ _ _ _ Prf.hyp0))
theorem returned_literal_old_sample_composition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ GaussianRationalHorner.evaluate
      (fstT (sndT (run (var 0) (var 1) (var 2) (var 3)))) (ofGaussian (var 0) (var 1)) ≐
        ap2 GaussianRationalPolynomialExponential.scalarF
          (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) (var 3)) :=
  closeUniv 4 (.impI (returned_composition_evaluation _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmSampler
