import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelUnitBound
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerTransformedPower
import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelGridComparison

/-!
# Original lower-time beta rows at transformed rational times

At t=(a/b)^A, a positive and a<=b, every actual beta replacement row
is bounded by (b/a)^(A-1)+2^-p. The original power sample is retained
at its genuine argument-dependent replacement clock. The literal kernel
is bounded by one on this entire interval for every positive degree N.
Only native monotonicity of the original dyadic clock is needed to keep
the requested observation error; no auxiliary limit or output law is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelLowerTransformedPower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLowerPowerOrder (source)
open GaussianEulerCompactProductComparison (clock)
open GaussianBetaKernelGridComparison (row)
open GaussianBetaKernelExponential (kernel)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (p A a b : PTm n) : PTm n := GaussianEulerLowerTransformedPower.numerator p A a b
def denominator (p A a : PTm n) : PTm n := GaussianEulerLowerTransformedPower.denominator p A a
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p A a b : PTm n) :
    Syn.subst σ (numerator p A a b) = numerator (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [numerator,GaussianEulerLowerTransformedPower.numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (p A a : PTm n) :
    Syn.subst σ (denominator p A a) = denominator (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ a) := by
  simp [denominator,GaussianEulerLowerTransformedPower.denominator]

theorem kernel_source (z R B A a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] GaussianBetaKernelRefinement.source (pw a A) (pw b A) N := by
  have hb := RationalNonnegativePowers.denominator_positive b A h.andE₂.andE₁.andE₂
  have first := pw_le_pw A h.andE₂.andE₂
  have larger : Γ ⊢[PRAAx] le (pw b A) (pw b A*N) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (pw b A) hN)
  exact .andI hb (.andI hN (le_trans first larger))

/-- The SAME literal beta row, with its original power observation clock,
has the sharp transformed lower-time majorant, independently of N. -/
theorem original_transformed_beta_row (p z R B A a b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (row p z B (pw a A) (pw b A) N) (numerator p A a b) (denominator p A a) := by
  let k := clock p z B (pw a A) (pw b A)
  let X := pw b (pred A)
  let Y := pw a (pred A)
  let P := unit p
  let Q := unit k
  have hq : Γ ⊢[PRAAx] le one Q := unit_positive k
  have hp : Γ ⊢[PRAAx] le one P := unit_positive p
  have hy := RationalNonnegativePowers.denominator_positive a (pred A) h.andE₂.andE₁.andE₁
  have hd := positive_product Y Q hy hq
  have targetDen := positive_product Y P hy hp
  have old := GaussianEulerLowerTransformedPower.original_power_bound k z R B A a b h
  have product := bounded_product _ _ _ _ one one hd (le_refl one) old
    (GaussianBetaKernelUnitBound.kernel_bound _ _ N (kernel_source z R B A a b N h hN))
  have raw : Γ ⊢[PRAAx] bounded (row p z B (pw a A) (pw b A) N) (X*Q+Y) (Y*Q) :=
    bound_congr (.eqRefl _) (by dsimp only [X,Y,Q,k]; ipra_ring) (by dsimp only [X,Y,Q,k]; ipra_ring) product
  have later : Γ ⊢[PRAAx] le P Q := GaussianExponentialReference.unit_monotone
    (GaussianEulerCompactProductComparison.clock_later p z B (pw a A) (pw b A))
  have compare : Γ ⊢[PRAAx] le ((X*Q+Y)*(Y*P)) ((X*P+Y)*(Y*Q)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (X*Q*Y*P) (mul_le_mul_right (Y*Y) later))
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hd targetDen compare raw

def output (p z B A a b N : PTm n) : PTm n := pairT (row p z B (pw a A) (pw b A) N)
  (pairT (numerator p A a b) (denominator p A a))
def outputF : PR 7 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (p z B A a b N : PTm n) : PTm n := PTm.app outputF ![p,z,B,A,a,b,N]
theorem program_at (p z B A a b N : PTm n) : Γ ⊢[PRAAx] run p z B A a b N ≐ output p z B A a b N := by
  simpa [run,outputF,output] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![p,z,B,A,a,b,N]

theorem original_beta_transformed_lower_time_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⋏ le one (var 7)) ⟶
      bounded (row (var 0) (var 1) (var 3) (pw (var 5) (var 4)) (pw (var 6) (var 4)) (var 7))
        (numerator (var 0) (var 4) (var 5) (var 6)) (denominator (var 0) (var 4) (var 5))) :=
  closeUniv 8 (.impI (original_transformed_beta_row _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_transformed_beta_kernel_support_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⋏ le one (var 6)) ⟶
      GaussianBetaKernelRefinement.source (pw (var 4) (var 3)) (pw (var 5) (var 3)) (var 6)) :=
  closeUniv 7 (.impI (kernel_source _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_transformed_lower_beta_row_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianBetaKernelLowerTransformedPower
