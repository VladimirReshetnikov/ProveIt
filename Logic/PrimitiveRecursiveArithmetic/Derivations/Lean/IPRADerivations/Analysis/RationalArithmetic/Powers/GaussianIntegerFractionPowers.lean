import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRationalReciprocal
import IPRADerivations.Analysis.Polynomials.Division.GaussianRationalSyntheticDivision
import IPRADerivations.Analysis.Logarithm.FiniteSeries.Remainders.ComplexLogarithmCauchy
import IPRADerivations.Analysis.Exponential.Polynomials.LogarithmExponentialCoefficients

/-!
# Actual fractions of the original Gaussian integer powers

The normalized Gaussian-rational power of `z/N` equals the actual signed
Gaussian-integer power divided by `N^k`. The original numerical positive
divisor is the only guard; all signed numerator codes and exponents are
internal. Both powers are the existing actual recursors.

The actual even/odd program also signs the native power of `-z`. These
finite identities are suppliers for comparing the literal logarithm
polynomial with the older factorial-cleared logarithm sampler. They do
not assume that comparison or any analytic logarithm/exponential law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianIntegerFractionPowers

open_ipra
open GaussianRationalHorner (ofGaussian represents canonical canonical_unique represents_congr positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRootAlgebra (equal equal_of_values equal_re equal_im equal_of_code equal_refl)
open ComplexLogarithmRemainder (oneCode mul re im)
open LogarithmExponentialCoefficients (evenBit oddBit)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem fraction_congr {a b A B : PTm n} (ha : Γ ⊢[PRAAx] a ≐ b)
    (hA : Γ ⊢[PRAAx] A ≐ B) : Γ ⊢[PRAAx] ofGaussian a A ≐ ofGaussian b B := by
  ipra_congr (ofGaussian (var 0) (var 1) : PTm 2) with [ha, hA]

theorem fraction_multiply (a b A B : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    GaussianRationalHorner.qmul (ofGaussian a A) (ofGaussian b B) ≐ ofGaussian (mul a b) (A*B) := by
  have hp := positive_product A B hA hB
  exact canonical_unique _ _ (mul a b) (A*B)
    (GaussianRationalHorner.qmul_canonical _ _) (GaussianRationalHorner.ofGaussian_canonical _ _ hp) hp
    (GaussianRationalHorner.qmul_represents _ _ _ _ _ _ hA hB
      (GaussianRationalHorner.ofGaussian_represents a A hA) (GaussianRationalHorner.ofGaussian_represents b B hB))
    (GaussianRationalHorner.ofGaussian_represents _ _ hp)

def powerLaw (z N k : PTm n) : Fm PTm n :=
  GaussianRationalReciprocal.power (ofGaussian z N) k ≐
    ofGaussian (ComplexLogarithmRemainder.power z k) (pw N k)
ipra_subst powerLaw

theorem fraction_power (z N k : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalReciprocal.power (ofGaussian z N) k ≐
      ofGaussian (ComplexLogarithmRemainder.power z k) (pw N k) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
    simpa only [Fm.shift,Syn.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hN.shift
  have all : Γ ⊢[PRAAx] .all (powerLaw (Syn.shift z) (Syn.shift N) (var 0)) := by
    ipra_qfind [subst_powerLaw]
    · exact (GaussianRationalReciprocal.power_zero _).eqTrans
        (fraction_congr (ComplexLogarithmRemainder.power_zero z) (pw_zero N)).eqSymm
    · exact (GaussianRationalReciprocal.power_succ _ _).eqTrans
        ((qmul_congr Prf.hyp0 (.eqRefl _)).eqTrans
          ((fraction_multiply _ _ _ _ (ComplexLogarithmCauchy.power_positive _ _ hs.wk) hs.wk).eqTrans
            (fraction_congr (ComplexLogarithmRemainder.power_succ _ _).eqSymm (pw_succ _ _).eqSymm)))
  change Γ ⊢[PRAAx] powerLaw z N k
  simpa only [subst_powerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem power_represents (z N k : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    represents (GaussianRationalReciprocal.power (ofGaussian z N) k)
      (ComplexLogarithmRemainder.power z k) (pw N k) :=
  represents_congr (fraction_power z N k hN).eqSymm (equal_refl _) (.eqRefl _)
    (GaussianRationalHorner.ofGaussian_represents _ _ (ComplexLogarithmCauchy.power_positive _ _ hN))

def parityScalar (k : PTm n) : PTm n :=
  ComplexLogarithmRemainder.code (⟨evenBit k,oddBit k⟩ : ZT n) (ZT.ofNat zero)
ipra_subst parityScalar [ZT.subst, ZT.ofNat]

theorem parity_scalar_re (k : PTm n) : ZT.toZ Γ (re (parityScalar k)) = 𝔞(evenBit k)-𝔞(oddBit k) := by
  rw [parityScalar,ComplexLogarithmRemainder.eval_re_code]
  rfl
theorem parity_scalar_im (k : PTm n) : ZT.toZ Γ (im (parityScalar k)) = 0 := by
  rw [parityScalar,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat,Q.mk_zero,map_zero]

theorem parity_scalar_zero : Γ ⊢[PRAAx] equal (parityScalar (zero : PTm n)) oneCode := by
  have he := natEq (LogarithmExponentialCoefficients.evenBit_zero (Γ := Γ) (n := n))
  have ho := natEq (LogarithmExponentialCoefficients.oddBit_zero (Γ := Γ) (n := n))
  apply equal_of_values
  · rw [parity_scalar_re,GaussianRootAlgebra.re_one,he,ho,Q.mk_one,Q.mk_zero,map_one,map_zero]; ring
  · rw [parity_scalar_im,GaussianRootAlgebra.im_one]

theorem parity_scalar_succ (k : PTm n) : Γ ⊢[PRAAx]
    equal (parityScalar (succ k)) (ComplexLogarithmRemainder.neg (parityScalar k)) := by
  have ep : Γ ⊢[PRAAx] evenBit (succ k) ≐ oddBit k := Prf.andE₁ (AnalyticNumberTheory.Mobius.par_succ k)
  have op : Γ ⊢[PRAAx] oddBit (succ k) ≐ evenBit k := Prf.andE₂ (AnalyticNumberTheory.Mobius.par_succ k)
  apply equal_of_values
  · rw [parity_scalar_re,GaussianRootAlgebra.re_neg,parity_scalar_re,natEq ep,natEq op]; ring
  · rw [parity_scalar_im,GaussianRootAlgebra.im_neg,parity_scalar_im]; ring

def negativePowerLaw (z k : PTm n) : Fm PTm n :=
  equal (ComplexLogarithmRemainder.power (ComplexLogarithmRemainder.neg z) k)
    (mul (parityScalar k) (ComplexLogarithmRemainder.power z k))
ipra_subst negativePowerLaw

theorem negative_power_step (z k : PTm n) (ih : Γ ⊢[PRAAx] negativePowerLaw z k) :
    Γ ⊢[PRAAx] negativePowerLaw z (succ k) := by
  have hp := GaussianRootAlgebra.values_of_code (ComplexLogarithmRemainder.power_succ (Γ := Γ) (ComplexLogarithmRemainder.neg z) k)
  have hq := GaussianRootAlgebra.values_of_code (ComplexLogarithmRemainder.power_succ (Γ := Γ) z k)
  have he := equal_re (parity_scalar_succ (Γ := Γ) k)
  have hi := equal_im (parity_scalar_succ (Γ := Γ) k)
  have ir := equal_re ih
  have ii := equal_im ih
  change Γ ⊢[PRAAx] equal _ _
  apply equal_of_values
  · rw [hp.1,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,
      ir,ii,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul]
    rw [GaussianRootAlgebra.re_mul,he,hi,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,hq.1,hq.2,
      GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul]
    ring
  · rw [hp.2,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,
      ir,ii,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul]
    rw [GaussianRootAlgebra.im_mul,he,hi,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,hq.1,hq.2,
      GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul]
    ring

theorem negative_power (z k : PTm n) : Γ ⊢[PRAAx] negativePowerLaw z k := by
  have all : Γ ⊢[PRAAx] .all (negativePowerLaw (Syn.shift z) (var 0)) := by
    ipra_qfind (⟨trivial,trivial⟩) [subst_negativePowerLaw]
    · change Γ ⊢[PRAAx] equal _ _
      have hp := GaussianRootAlgebra.values_of_code (ComplexLogarithmRemainder.power_zero (Γ := Γ) (ComplexLogarithmRemainder.neg z))
      have hq := GaussianRootAlgebra.values_of_code (ComplexLogarithmRemainder.power_zero (Γ := Γ) z)
      apply equal_of_values
      · rw [hp.1,GaussianRootAlgebra.re_mul,equal_re parity_scalar_zero,equal_im parity_scalar_zero,hq.1,hq.2,
          GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]; ring
      · rw [hp.2,GaussianRootAlgebra.im_mul,equal_re parity_scalar_zero,equal_im parity_scalar_zero,hq.1,hq.2,
          GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]; ring
    · exact negative_power_step _ _ Prf.hyp0
  simpa only [subst_negativePowerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

/-- The precise signed numerator occurring in the original old cubic-tail
update. This is a derived native identity, not a supplied alternating law. -/
theorem factorial_alternating_power (z k : PTm n) : Γ ⊢[PRAAx] equal
    (ComplexLogarithmRemainder.scale (Products.fact k) (mul (parityScalar k) (ComplexLogarithmRemainder.power z (succ k))))
    (ComplexLogarithmRemainder.neg (ComplexLogarithmRemainder.scale (Products.fact k)
      (ComplexLogarithmRemainder.power (ComplexLogarithmRemainder.neg z) (succ k)))) := by
  have hn := negative_power (Γ := Γ) z (succ k)
  have hr := equal_re hn
  have hi := equal_im hn
  have hs := equal_re (parity_scalar_succ (Γ := Γ) k)
  have ht := equal_im (parity_scalar_succ (Γ := Γ) k)
  apply equal_of_values
  · simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_neg]
    rw [hr]
    simp only [GaussianRootAlgebra.re_mul]
    rw [hs,ht,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg]
    ring
  · simp only [GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_neg]
    rw [hi]
    simp only [GaussianRootAlgebra.im_mul]
    rw [hs,ht,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg]
    ring

def output (z N k : PTm n) : PTm n :=
  pairT (GaussianRationalReciprocal.power (ofGaussian z N) k)
    (pairT (ComplexLogarithmRemainder.power z k) (pw N k))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (z N k : PTm n) : PTm n := ap3 outputF z N k
ipra_subst output
ipra_subst run
theorem program_at (z N k : PTm n) : Γ ⊢[PRAAx] run z N k ≐ output z N k := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![z,N,k]
theorem returned_power (z N k : PTm n) : Γ ⊢[PRAAx]
    fstT (run z N k) ≐ GaussianRationalReciprocal.power (ofGaussian z N) k :=
  (program_at z N k).fstE
theorem returned_numerator (z N k : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run z N k)) ≐ ComplexLogarithmRemainder.power z k :=
  (program_at z N k).sndE.fstE
theorem returned_denominator (z N k : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run z N k)) ≐ pw N k :=
  (program_at z N k).sndE.sndE
theorem returned_representation (z N k : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    represents (fstT (run z N k)) (fstT (sndT (run z N k))) (sndT (sndT (run z N k))) :=
  represents_congr (returned_power z N k).eqSymm (equal_of_code (returned_numerator z N k).eqSymm)
    (returned_denominator z N k).eqSymm (power_represents z N k hN)

theorem actual_fraction_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le one (var 3) ⟶
      GaussianRationalHorner.qmul (ofGaussian (var 0) (var 2)) (ofGaussian (var 1) (var 3)) ≐
        ofGaussian (mul (var 0) (var 1)) (var 2*var 3)) :=
  closeUniv 4 (.impI (.impI (fraction_multiply _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_fraction_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ GaussianRationalReciprocal.power (ofGaussian (var 0) (var 1)) (var 2) ≐
      ofGaussian (ComplexLogarithmRemainder.power (var 0) (var 2)) (pw (var 1) (var 2))) :=
  closeUniv 3 (.impI (fraction_power _ _ _ Prf.hyp0))
theorem actual_power_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ represents (GaussianRationalReciprocal.power (ofGaussian (var 0) (var 1)) (var 2))
      (ComplexLogarithmRemainder.power (var 0) (var 2)) (pw (var 1) (var 2))) :=
  closeUniv 3 (.impI (power_represents _ _ _ Prf.hyp0))
theorem actual_native_negative_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (negativePowerLaw (var 0) (var 1)) := closeUniv 2 (negative_power _ _)
theorem actual_factorial_signed_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (equal (ComplexLogarithmRemainder.scale (Products.fact (var 1))
      (mul (parityScalar (var 1)) (ComplexLogarithmRemainder.power (var 0) (succ (var 1)))))
      (ComplexLogarithmRemainder.neg (ComplexLogarithmRemainder.scale (Products.fact (var 1))
        (ComplexLogarithmRemainder.power (ComplexLogarithmRemainder.neg (var 0)) (succ (var 1)))))) :=
  closeUniv 2 (factorial_alternating_power _ _)
theorem actual_fraction_power_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_power_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ represents (fstT (run (var 0) (var 1) (var 2)))
      (fstT (sndT (run (var 0) (var 1) (var 2)))) (sndT (sndT (run (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (returned_representation _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianIntegerFractionPowers
