import IPRADerivations.Analysis.Polynomials.Products.Powers.GaussianRationalPolynomialPowerSupport

/-!
# Actual finite exponential coefficients stabilize at their exponent

For an original zero constant coefficient, the SAME finite factorial
exponential buffer has its exponent-e coefficient fixed after its first
e powers, for e<=N and e<=K. Genuine power support kills each later
contribution; the original padded coefficient recurrence then proves a
true numerical QF stability invariant. The fixed original power cap K
is retained throughout. This does not yet identify the coefficient with
the old Bell history or supply the analytic C4 tail.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponentialStability

open_ipra
open GaussianRationalHorner (qzero)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_right canonical_coefficient_at)
open GaussianRationalPolynomialExponential (stage stage_congr stage_length stage_canonical stage_coefficient_succ inverseFactorial)
open GaussianRationalPolynomialPowers (powerPrefix)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside index_decompose)
open GaussianRationalPolynomialPowerSupport (min_product low_power_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (C N K j e : PTm n) : PTm n := exponentCoefficient (stage C N K j) (j*N) e
ipra_subst coefficient

theorem exponent_congr {C D N M e f : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D)
    (hN : Γ ⊢[PRAAx] N ≐ M) (he : Γ ⊢[PRAAx] e ≐ f) : Γ ⊢[PRAAx]
    exponentCoefficient C N e ≐ exponentCoefficient D M f := by
  ipra_congr (exponentCoefficient (var 0) (var 1) (var 2) : PTm 3) with [hC, hN, he]
theorem coefficient_index_congr (C N K e : PTm n) {j l : PTm n} (hj : Γ ⊢[PRAAx] j ≐ l) : Γ ⊢[PRAAx]
    coefficient C N K j e ≐ coefficient C N K l e :=
  exponent_congr (stage_congr (.eqRefl C) (.eqRefl N) (.eqRefl K) hj) (congrMul hj (.eqRefl N)) (.eqRefl e)

theorem pad_index (N j e : PTm n) (he : Γ ⊢[PRAAx] le e (j*N)) : Γ ⊢[PRAAx]
    monus (succ j*N) e ≐ N+monus (j*N) e :=
  (congrMonus (by ipra_ring) (.eqRefl e)).eqTrans (index_decompose N (j*N) e he)

theorem padded_coefficient (C N K j e : PTm n) (he : Γ ⊢[PRAAx] le e (j*N)) : Γ ⊢[PRAAx]
    GaussianRationalPolynomialBuffers.padCoefficient (stage C N K j) N (monus (succ j*N) e) ≐
      entry (stage C N K j) (monus (j*N) e) := by
  have hidx := pad_index (Γ := Γ) N j e he
  have hN : Γ ⊢[PRAAx] le N (monus (succ j*N) e) :=
    le_congr (.eqRefl _) hidx.eqSymm (le_add_right N _)
  exact (GaussianRationalPolynomialBuffers.pad_coefficient_after _ _ _ hN).eqTrans
    (entry_congr (.eqRefl _) ((congrMonus hidx (.eqRefl N)).eqTrans (add_monus' _ _)))

theorem coefficient_successor (C N K j e : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) (hej : Γ ⊢[PRAAx] le e j) (hj : Γ ⊢[PRAAx] lt j K) : Γ ⊢[PRAAx]
    coefficient C N K (succ j) e ≐ coefficient C N K j e := by
  have hp := min_product e j N he hej
  have hnext := le_trans hp (mul_le_mul_right N (le_succ_self j))
  have hZero : Γ ⊢[PRAAx] entry (powerPrefix C N K (succ j)) (monus (succ j*N) e) ≐ qzero :=
    (exponent_inside _ _ _ hnext).eqSymm.eqTrans
      (low_power_zero C N K (succ j) e hC hj he ((succ_monus_succ _ _).eqTrans hej))
  have hPower : Γ ⊢[PRAAx] GaussianRationalHorner.qmul (inverseFactorial (succ j))
      (entry (powerPrefix C N K (succ j)) (monus (succ j*N) e)) ≐ qzero :=
    (qmul_congr (.eqRefl _) hZero).eqTrans (qmul_zero_right _)
  have hEntry : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (entry (stage C N K j) (monus (j*N) e)) :=
    canonical_coefficient_at _ _ (stage_canonical C N K j)
      (lt_congr (.eqRefl _) (stage_length C N K j).eqSymm
        ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _)))
  exact (exponent_inside _ _ _ hnext).eqTrans
    ((stage_coefficient_succ C N K j (monus (succ j*N) e) (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
      ((qadd_congr (padded_coefficient C N K j e hp) hPower).eqTrans
        ((GaussianReciprocalHorner.qadd_zero_right _ hEntry).eqTrans (exponent_inside _ _ _ hp).eqSymm)))

def stabilityLaw (C N K e r : PTm n) : Fm PTm n := le (e+r) K ⟶
  coefficient C N K (e+r) e ≐ coefficient C N K e e
ipra_subst stabilityLaw

theorem stability_zero (C N K e : PTm n) : Γ ⊢[PRAAx] stabilityLaw C N K e zero :=
  .impI (coefficient_index_congr C N K e (add_zero e))
theorem stability_step (C N K e r : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) (ih : Γ ⊢[PRAAx] stabilityLaw C N K e r) : Γ ⊢[PRAAx]
    stabilityLaw C N K e (succ r) := by
  refine .impI ?_
  have hs : (le (e+succ r) K :: Γ) ⊢[PRAAx] e+succ r ≐ succ (e+r) := by ipra_ring
  have hj : (le (e+succ r) K :: Γ) ⊢[PRAAx] lt (e+r) K := le_congr hs (.eqRefl _) Prf.hyp0
  have hprev : (le (e+succ r) K :: Γ) ⊢[PRAAx] le (e+r) K := le_trans (le_succ_self _) hj
  exact (coefficient_index_congr C N K e hs).eqTrans
    ((coefficient_successor C N K (e+r) e hC.wk he.wk (le_add_right _ _) hj).eqTrans (.impE ih.wk hprev))

theorem coefficient_stability (C N K e r : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) (hr : Γ ⊢[PRAAx] le (e+r) K) : Γ ⊢[PRAAx]
    coefficient C N K (e+r) e ≐ coefficient C N K e e := by
  have hc : Γ.map Fm.shift ⊢[PRAAx] entry (Syn.shift C) (Syn.shift N) ≐ qzero := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.MasterCertificate.subst_entry,GaussianRationalHorner.subst_qzero,Syn.shift] using hC.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using he.shift
  have all : Γ ⊢[PRAAx] .all (stabilityLaw (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift e) (var 0)) := by
    ipra_qfind (by trivial) [subst_stabilityLaw]
    · exact stability_zero C N K e
    · exact stability_step _ _ _ _ _ hc.wk hn.wk Prf.hyp0
  have gate : Γ ⊢[PRAAx] stabilityLaw C N K e r := by
    simpa only [subst_stabilityLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE gate hr

theorem finite_exponential_cutoff (C N K e : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    exponentCoefficient (GaussianRationalPolynomialExponential.polynomial C N K) (K*N) e ≐ coefficient C N K e e := by
  have hsum := (eq_add_of_le hK).eqSymm
  have hr : Γ ⊢[PRAAx] le (e+monus K e) K := le_congr hsum.eqSymm (.eqRefl _) (le_refl K)
  exact (coefficient_index_congr C N K e hsum).eqSymm.eqTrans
    (coefficient_stability C N K e (monus K e) hC he hr)
theorem logarithm_exponential_cutoff (d K e : PTm n) (he : Γ ⊢[PRAAx] le e d)
    (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    exponentCoefficient (GaussianFiniteLogarithmPolynomial.composition d K) (K*d) e ≐
      coefficient (GaussianFiniteLogarithmPolynomial.polynomial d) d K e e :=
  finite_exponential_cutoff _ _ _ _ (GaussianFiniteLogarithmPolynomial.polynomial_constant d) he hK

def output (C N K e : PTm n) : PTm n := pairT (coefficient C N K K e) (coefficient C N K e e)
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (C N K e : PTm n) : PTm n := PTm.app outputF ![C,N,K,e]
ipra_subst output
ipra_subst run

theorem program_at (C N K e : PTm n) : Γ ⊢[PRAAx] run C N K e ≐ output C N K e := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,K,e]
theorem returned_final (C N K e : PTm n) : Γ ⊢[PRAAx] fstT (run C N K e) ≐ coefficient C N K K e :=
  (program_at C N K e).fstE
theorem returned_initial (C N K e : PTm n) : Γ ⊢[PRAAx] sndT (run C N K e) ≐ coefficient C N K e e :=
  (program_at C N K e).sndE
theorem returned_agreement (C N K e : PTm n) (hC : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (he : Γ ⊢[PRAAx] le e N) (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    fstT (run C N K e) ≐ sndT (run C N K e) :=
  (returned_final C N K e).eqTrans ((finite_exponential_cutoff C N K e hC he hK).eqTrans (returned_initial C N K e).eqSymm)
theorem returned_logarithm_agreement (d K e : PTm n) (he : Γ ⊢[PRAAx] le e d)
    (hK : Γ ⊢[PRAAx] le e K) : Γ ⊢[PRAAx]
    fstT (run (GaussianFiniteLogarithmPolynomial.polynomial d) d K e) ≐
      sndT (run (GaussianFiniteLogarithmPolynomial.polynomial d) d K e) :=
  returned_agreement _ _ _ _ (GaussianFiniteLogarithmPolynomial.polynomial_constant d) he hK

theorem actual_later_power_coefficient_stability_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (entry (var 0) (var 1) ≐ qzero ⟶ le (var 4) (var 1) ⟶ le (var 4) (var 3) ⟶ lt (var 3) (var 2) ⟶
      coefficient (var 0) (var 1) (var 2) (succ (var 3)) (var 4) ≐ coefficient (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (coefficient_successor _ _ _ _ _ Prf.hyp0.wk.wk.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_finite_exponential_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (entry (var 0) (var 1) ≐ qzero ⟶ le (var 3) (var 1) ⟶ le (var 3) (var 2) ⟶
      exponentCoefficient (GaussianRationalPolynomialExponential.polynomial (var 0) (var 1) (var 2)) (var 2*var 1) (var 3) ≐
        coefficient (var 0) (var 1) (var 2) (var 3) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (finite_exponential_cutoff _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem original_logarithm_composition_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶
      exponentCoefficient (GaussianFiniteLogarithmPolynomial.composition (var 0) (var 1)) (var 1*var 0) (var 2) ≐
        coefficient (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0) (var 1) (var 2) (var 2)) :=
  closeUniv 3 (.impI (.impI (logarithm_exponential_cutoff _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_finite_coefficient_cutoff_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_finite_cutoff_agreement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (entry (var 0) (var 1) ≐ qzero ⟶ le (var 3) (var 1) ⟶ le (var 3) (var 2) ⟶
      fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ sndT (run (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (returned_agreement _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem original_returned_logarithm_cutoff_agreement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶ le (var 2) (var 1) ⟶
      fstT (run (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0) (var 1) (var 2)) ≐
        sndT (run (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (returned_logarithm_agreement _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponentialStability
