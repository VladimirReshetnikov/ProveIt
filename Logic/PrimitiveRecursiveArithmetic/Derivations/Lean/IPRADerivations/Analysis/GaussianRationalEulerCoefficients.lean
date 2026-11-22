import IPRADerivations.Analysis.GaussianRationalWeightedCoefficientConvolution
import IPRADerivations.Analysis.GaussianFiniteLogarithmPolynomial

/-!
# Actual Euler-weighted coefficient buffers

The real finite sequence at declared degree N stores (N-i)*C_i. Its
polynomial is x times the formal derivative, padded to the SAME degree
bound N. Genuine numeric coefficient rules derive the low-exponent
Leibniz identity for the ORIGINAL product, with both resulting products
and their added buffer constructed explicitly. No derivative/output law
is a premise. The original H_d coefficients give exact signed unit Euler
coefficients. Power/exponential Bell identification remains separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalEulerCoefficients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qadd qmul canonical ofGaussian represents canonical_unique)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr canonicalCoefficients)
open GaussianRationalNaturalScale (natScale natScale_congr)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside cauchySum termBody data)
open GaussianRationalWeightedCoefficientConvolution (leftSum rightSum leftBody rightBody)
open GaussianRationalPolynomialProduct (product product_length)
open GaussianRationalPolynomialBuffers (added added_lookup)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowBody : PTm 2 := natScale (monus (sndT (var 1)) (var 0)) (entry (fstT (var 1)) (var 0))
def euler (C N : PTm n) : PTm n := sequence rowBody (succ N) (pairT C N)
@[simp] theorem subst_euler {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (euler C N) = euler (Syn.subst σ C) (Syn.subst σ N) := by simp [euler]
theorem euler_length (C N : PTm n) : Γ ⊢[PRAAx] length (euler C N) ≐ succ N := sequence_length _ _ _
theorem row_at (C N i : PTm n) : Γ ⊢[PRAAx] inst2 rowBody i (pairT C N) ≐ natScale (monus N i) (entry C i) := by
  simp only [rowBody,inst2,GaussianRationalNaturalScale.subst_natScale,PTm.subst_monus,
    Foundations.MasterCertificate.subst_entry,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact natScale_congr (congrMonus (snd_pair _ _) (.eqRefl _)) (entry_congr (fst_pair _ _) (.eqRefl _))
theorem euler_lookup (C N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (euler C N) i ≐ natScale (monus N i) (entry C i) :=
  (sequence_decode rowBody (x := pairT C N) ((succ_monus_succ _ _).eqTrans hi)).eqTrans (row_at C N i)
theorem euler_canonical (C N : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (euler C N) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (euler C N))) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (lt_congr (.eqRefl _) (euler_length (Syn.shift C) (Syn.shift N))
      (by simpa only [Δ,Syn.shift,subst_euler] using (Prf.hyp0 (Ax := PRAAx))))
  simpa only [Δ,Syn.shift,subst_euler] using GaussianRationalHorner.canonical_congr
    (euler_lookup (Syn.shift C) (Syn.shift N) (var 0) hi) (GaussianRationalNaturalScale.natScale_canonical _ _)

theorem euler_entry_exponent (C N e : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    entry (euler C N) (monus N e) ≐ natScale e (entry C (monus N e)) :=
  (euler_lookup C N (monus N e) (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
    (natScale_congr (GaussianRationalMonicReconstruction.complement N e he) (.eqRefl _))
theorem euler_exponent (C N e : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    exponentCoefficient (euler C N) N e ≐ natScale e (exponentCoefficient C N e) :=
  (exponent_inside (euler C N) N e he).eqTrans ((euler_entry_exponent C N e he).eqTrans
    (natScale_congr (.eqRefl _) (exponent_inside C N e he).eqSymm))
theorem euler_constant (C N : PTm n) : Γ ⊢[PRAAx] entry (euler C N) N ≐ qzero :=
  (euler_lookup C N N (le_refl _)).eqTrans
    ((natScale_congr (monus_self N) (.eqRefl _)).eqTrans (GaussianRationalNaturalScale.natScale_zero _))

theorem left_cauchy (P Q N M e : PTm n) (hN : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    cauchySum (euler P N) Q N M e ≐ leftSum P Q N M e := by
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hN.shift
  refine GaussianRationalFiniteSum.sum_congr_bounded termBody leftBody (succ e)
    (data (euler P N) Q N M e) (data P Q N M e) (.allI (.impI ?_))
  let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) :=
    le_trans ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) hn.wk
  have h := (GaussianRationalLowCoefficientConvolution.term_at (Γ := Δ) (euler (Syn.shift P) (Syn.shift N))
      (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift e) (var 0)).eqTrans
    ((qmul_congr (euler_entry_exponent (Syn.shift P) (Syn.shift N) (var 0) hi) (.eqRefl _)).eqTrans
      (GaussianRationalWeightedCoefficientConvolution.left_at (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift e) (var 0)).eqSymm)
  simpa only [Δ,Syn.shift,ConciseIPRA.PTm.subst_succ,GaussianRationalLowCoefficientConvolution.subst_data,subst_euler] using h

theorem right_cauchy (P Q N M e : PTm n) (hM : Γ ⊢[PRAAx] le e M) : Γ ⊢[PRAAx]
    cauchySum P (euler Q M) N M e ≐ rightSum P Q N M e := by
  have hm : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift M) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hM.shift
  refine GaussianRationalFiniteSum.sum_congr_bounded termBody rightBody (succ e)
    (data P (euler Q M) N M e) (data P Q N M e) (.allI (.impI ?_))
  let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (monus (Syn.shift e) (var 0)) (Syn.shift M) :=
    le_trans (GaussianRationalMonicReconstruction.monus_le_left _ _) hm.wk
  have h := (GaussianRationalLowCoefficientConvolution.term_at (Γ := Δ) (Syn.shift P) (euler (Syn.shift Q) (Syn.shift M))
      (Syn.shift N) (Syn.shift M) (Syn.shift e) (var 0)).eqTrans
    ((qmul_congr (.eqRefl _) (euler_entry_exponent (Syn.shift Q) (Syn.shift M) (monus (Syn.shift e) (var 0)) hi)).eqTrans
      (GaussianRationalWeightedCoefficientConvolution.right_at (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift e) (var 0)).eqSymm)
  simpa only [Δ,Syn.shift,ConciseIPRA.PTm.subst_succ,GaussianRationalLowCoefficientConvolution.subst_data,subst_euler] using h

def leibniz (P Q N M : PTm n) : PTm n := added
  (product (euler P N) Q N M) (product P (euler Q M) N M) (succ (N+M))
@[simp] theorem subst_leibniz {l : ℕ} (σ : Fin n → PTm l) (P Q N M : PTm n) :
    Syn.subst σ (leibniz P Q N M) = leibniz (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ N) (Syn.subst σ M) := by
  simp [leibniz]

theorem product_leibniz (P Q N M e : PTm n) (hN : Γ ⊢[PRAAx] le e N)
    (hM : Γ ⊢[PRAAx] le e M) : Γ ⊢[PRAAx]
    entry (euler (product P Q N M) (N+M)) (monus (N+M) e) ≐ entry (leibniz P Q N M) (monus (N+M) e) := by
  have he := le_trans hN (le_add_right N M)
  have hL : Γ ⊢[PRAAx] leftSum P Q N M e ≐ entry (product (euler P N) Q N M) (monus (N+M) e) :=
    (left_cauchy P Q N M e hN).eqSymm.eqTrans
      (GaussianRationalLowCoefficientConvolution.coefficient_cauchy (euler P N) Q N M e hN hM).eqSymm
  have hR : Γ ⊢[PRAAx] rightSum P Q N M e ≐ entry (product P (euler Q M) N M) (monus (N+M) e) :=
    (right_cauchy P Q N M e hM).eqSymm.eqTrans
      (GaussianRationalLowCoefficientConvolution.coefficient_cauchy P (euler Q M) N M e hN hM).eqSymm
  exact (euler_entry_exponent _ _ _ he).eqTrans
    ((natScale_congr (.eqRefl _) (exponent_inside (product P Q N M) (N+M) e he).eqSymm).eqTrans
      ((GaussianRationalWeightedCoefficientConvolution.weighted_cauchy P Q N M e hN hM).eqTrans
        ((qadd_congr hL hR).eqTrans
          (added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _))).eqSymm)))

def parityPoint (k : PTm n) : PTm n := ofGaussian (GaussianFiniteLogarithmPolynomial.signNumerator k) one
@[simp] theorem subst_parityPoint {l : ℕ} (σ : Fin n → PTm l) (k : PTm n) :
    Syn.subst σ (parityPoint k) = parityPoint (Syn.subst σ k) := by simp [parityPoint]
theorem logarithm_weight_cancel (k : PTm n) : Γ ⊢[PRAAx]
    natScale (succ k) (GaussianFiniteLogarithmPolynomial.coefficient k) ≐ parityPoint k := by
  have hs := zero_lt_succ (Γ := Γ) k
  have hc := GaussianRationalNaturalScale.natScale_represents (Γ := Γ) (succ k)
    (GaussianFiniteLogarithmPolynomial.coefficient k) (GaussianFiniteLogarithmPolynomial.signNumerator k) (succ k)
    hs (GaussianFiniteLogarithmPolynomial.coefficient_represents k)
  have hp : Γ ⊢[PRAAx] represents (parityPoint k)
      (ComplexLogarithmRemainder.scale (succ k) (GaussianFiniteLogarithmPolynomial.signNumerator k)) (succ k) :=
    GaussianRationalSyntheticDivision.rescale_to _ _ one (succ k) (succ k)
      (GaussianRationalHorner.ofGaussian_represents _ one (le_refl one)) (one_mul _)
  exact canonical_unique _ _ _ _ (GaussianRationalNaturalScale.natScale_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) hs hc hp

theorem logarithm_euler_positive (d k : PTm n) (hk : Γ ⊢[PRAAx] lt k d) : Γ ⊢[PRAAx]
    entry (euler (GaussianFiniteLogarithmPolynomial.polynomial d) d) (monus d (succ k)) ≐ parityPoint k :=
  (euler_entry_exponent _ _ _ hk).eqTrans
    ((natScale_congr (.eqRefl _) (GaussianFiniteLogarithmPolynomial.polynomial_positive_coefficient d k hk)).eqTrans
      (logarithm_weight_cancel k))

def eulerF : PR 2 := PTm.toPR (euler (var 0) (var 1))
def output (P Q N M : PTm n) : PTm n := pairT (euler (product P Q N M) (N+M)) (leibniz P Q N M)
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

theorem euler_program_at (C N : PTm n) : Γ ⊢[PRAAx] ap2 eulerF C N ≐ euler C N := by
  simpa [eulerF,ap2] using toPR_eq (Γ := Γ) (euler (var 0) (var 1) : PTm 2) ![C,N]
theorem program_at (P Q N M : PTm n) : Γ ⊢[PRAAx] run P Q N M ≐ output P Q N M := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![P,Q,N,M]
theorem returned_euler (P Q N M : PTm n) : Γ ⊢[PRAAx] fstT (run P Q N M) ≐ euler (product P Q N M) (N+M) :=
  (congrFst (program_at P Q N M)).eqTrans (fst_pair _ _)
theorem returned_leibniz (P Q N M : PTm n) : Γ ⊢[PRAAx] sndT (run P Q N M) ≐ leibniz P Q N M :=
  (congrSnd (program_at P Q N M)).eqTrans (snd_pair _ _)
theorem returned_product_rule (P Q N M e : PTm n) (hN : Γ ⊢[PRAAx] le e N)
    (hM : Γ ⊢[PRAAx] le e M) : Γ ⊢[PRAAx]
    entry (fstT (run P Q N M)) (monus (N+M) e) ≐ entry (sndT (run P Q N M)) (monus (N+M) e) :=
  (entry_congr (returned_euler P Q N M) (.eqRefl _)).eqTrans
    ((product_leibniz P Q N M e hN hM).eqTrans (entry_congr (returned_leibniz P Q N M).eqSymm (.eqRefl _)))

theorem actual_euler_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (euler (var 0) (var 1)) ≐ succ (var 1) ⋏ canonicalCoefficients (euler (var 0) (var 1))) :=
  closeUniv 2 (.andI (euler_length _ _) (euler_canonical _ _))
theorem actual_euler_exponent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 1) ⟶ exponentCoefficient (euler (var 0) (var 1)) (var 1) (var 2) ≐
      natScale (var 2) (exponentCoefficient (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (euler_exponent _ _ _ Prf.hyp0))
theorem actual_euler_zero_constant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (entry (euler (var 0) (var 1)) (var 1) ≐ qzero) := closeUniv 2 (euler_constant _ _)
theorem actual_low_product_euler_rule_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 2) ⟶ le (var 4) (var 3) ⟶
      entry (euler (product (var 0) (var 1) (var 2) (var 3)) (var 2+var 3)) (monus (var 2+var 3) (var 4)) ≐
        entry (leibniz (var 0) (var 1) (var 2) (var 3)) (monus (var 2+var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (product_leibniz _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_logarithm_euler_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (var 0) ⟶ entry (euler (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0))
      (monus (var 0) (succ (var 1))) ≐ parityPoint (var 1)) :=
  closeUniv 2 (.impI (logarithm_euler_positive _ _ Prf.hyp0))
theorem actual_euler_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 eulerF (var 0) (var 1) ≐ euler (var 0) (var 1)) := closeUniv 2 (euler_program_at _ _)
theorem actual_euler_product_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_euler_product_rule_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 2) ⟶ le (var 4) (var 3) ⟶
      entry (fstT (run (var 0) (var 1) (var 2) (var 3))) (monus (var 2+var 3) (var 4)) ≐
        entry (sndT (run (var 0) (var 1) (var 2) (var 3))) (monus (var 2+var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (returned_product_rule _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalEulerCoefficients
