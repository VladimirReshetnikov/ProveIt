import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelRefinement

/-!
# The original beta kernel is dominated by the original decay

On the full nonnegative interval a<=bN the actual kernel is positive.
Its exact dyadic refinement is compared with the unchanged original
Euler decay observation at arbitrarily fine finite cutoffs. The already
proved half-interval approximation controls those later cutoffs. One
actual scalar integer-gap query removes only the auxiliary refinement
error and keeps the requested ordinary decay observation error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelDomination

open_ipra
open GaussianBetaKernelRefinement (source cutoff cutoff_succ cutoff_ge refined_source)
open GaussianBetaKernelExponential (kernel)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianNamedRealOrderTransport (upperSlack)
open RationalValueBounds (upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cost (a : PTm n) : PTm n := GaussianBetaKernelExponential.coefficient a*a*a
ipra_subst cost

theorem later_half_source (a b N j : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    GaussianBetaKernelLogarithm.source a b (cutoff N (succ j)) := by
  have refined := refined_source a b N (succ j) h
  have first := mul_le_mul_right two h.andE₂.andE₂
  have later := AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (two*b)) (cutoff_ge (Γ := Γ) N j)
  have e : Γ ⊢[PRAAx] (two*b)*cutoff N j ≐ b*cutoff N (succ j) :=
    (by ipra_ring : Γ ⊢[PRAAx] (two*b)*cutoff N j ≐ b*(two*cutoff N j)).eqTrans
      (congrMul (.eqRefl _) (cutoff_succ N j).eqSymm)
  exact .andI h.andE₁ (.andI refined.andE₂.andE₁
    (le_trans (le_congr (mul_comm _ _) (by ipra_ring) first) (le_congr (.eqRefl _) e later)))

theorem auxiliary_denominator (a b N j : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    le (unit j) (b*b*cutoff N (succ j)) := by
  have later := GaussianExponentialReference.unit_monotone (le_succ_self (Γ := Γ) j)
  have mesh : Γ ⊢[PRAAx] le (unit (succ j)) (cutoff N (succ j)) :=
    le_congr (one_mul _) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono h.andE₂.andE₁ (le_refl _))
  have b2 := positive_product (Γ := Γ) _ _ h.andE₁ h.andE₁
  have gain : Γ ⊢[PRAAx] le (cutoff N (succ j)) (b*b*cutoff N (succ j)) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (cutoff N (succ j)) b2)
  exact le_trans later (le_trans mesh gain)

/-- The sole auxiliary error is cost(a)*eps_j. The exact original
observation at p, and its ordinary eps_p, stay fixed throughout. -/
theorem cofinal_upper_slack (p j a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    upperSlack (fstT (kernel a b N)) (fstT (ap2 decayF p (decayData a b))) one (unit p) (cost a) j := by
  let K := cutoff N (succ j)
  have half := later_half_source a b N j h
  have time : Γ ⊢[PRAAx] le a (a*b) :=
    le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl a) h.andE₁)
  have approximate := GaussianBetaKernelExponential.original_decay_sample_bound p a b K a half time
  have d := positive_product (Γ := Γ) _ _ (positive_product _ _ (positive_product _ _ h.andE₁ h.andE₁) half.andE₂.andE₁) (unit_positive p)
  have scalar := RationalValueBounds.upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ d approximate)
  have inherited := RationalValueBounds.upper_order_left _ _ _ _ _
    (GaussianBetaKernelRefinement.kernel_refinement_order a b N (succ j) h) scalar
  have raw := mul_le_mul_right (cost a*unit p*unit p) (auxiliary_denominator a b N j h)
  have full := add_le_add_right (b*b*K*unit p*unit j) raw
  exact RationalValueBounds.upper_mono _ _ _ _ _ _ d inherited
    (le_congr (by dsimp only [GaussianBetaKernelExponential.errorNumerator,GaussianBetaKernelExponential.errorDenominator,
        GaussianBetaKernelExponential.constantBound,K,cost]; ipra_ring)
      (by dsimp only [GaussianBetaKernelExponential.errorNumerator,GaussianBetaKernelExponential.errorDenominator,
        GaussianBetaKernelExponential.constantBound,K,cost]; ipra_ring) full)

/-- Complete full-interval beta domination at every requested ORIGINAL
decay observation, including the zero-base endpoint a=bN. -/
theorem original_kernel_upper (p a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    upper (fstT (kernel a b N)) (fstT (ap2 decayF p (decayData a b))) one (unit p) :=
  GaussianNamedRealOrderTransport.remove_upper_slack _ _ one (unit p) (cost a)
    (cofinal_upper_slack p (GaussianNamedRealOrderTransport.precision (fstT (kernel a b N))
      (fstT (ap2 decayF p (decayData a b))) (unit p) (cost a)) a b N h)

theorem original_kernel_domination (p a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE RationalGaussianEmbedding.scalarZero (fstT (kernel a b N)) ⋏
      upper (fstT (kernel a b N)) (fstT (ap2 decayF p (decayData a b))) one (unit p) :=
  .andI (GaussianBetaKernelRefinement.kernel_nonnegative a b N h) (original_kernel_upper p a b N h)

def output (p a b N : PTm n) : PTm n := pairT (kernel a b N)
  (pairT (ap2 decayF p (decayData a b)) (pairT one (unit p)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (p a b N : PTm n) : PTm n := PTm.app outputF ![p,a,b,N]
ipra_subst output
theorem program_at (p a b N : PTm n) : Γ ⊢[PRAAx] run p a b N ≐ output p a b N := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![p,a,b,N]
theorem returned_kernel (p a b N : PTm n) : Γ ⊢[PRAAx] fstT (run p a b N) ≐ kernel a b N :=
  (program_at p a b N).fstE
theorem returned_tail (p a b N : PTm n) : Γ ⊢[PRAAx] sndT (run p a b N) ≐ pairT (ap2 decayF p (decayData a b)) (pairT one (unit p)) :=
  (program_at p a b N).sndE
theorem returned_decay (p a b N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p a b N)) ≐ ap2 decayF p (decayData a b) :=
  (returned_tail p a b N).fstE
theorem returned_last (p a b N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run p a b N)) ≐ pairT one (unit p) :=
  (returned_tail p a b N).sndE
theorem returned_numerator (p a b N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run p a b N))) ≐ one :=
  (returned_last p a b N).fstE
theorem returned_denominator (p a b N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run p a b N))) ≐ unit p :=
  (returned_last p a b N).sndE
theorem returned_upper (p a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    upper (fstT (fstT (run p a b N))) (fstT (fstT (sndT (run p a b N))))
      (fstT (sndT (sndT (run p a b N)))) (sndT (sndT (sndT (run p a b N)))) :=
  RationalValueBounds.upper_congr (congrFst (returned_kernel p a b N)).eqSymm (congrFst (returned_decay p a b N)).eqSymm
    (returned_numerator p a b N).eqSymm (returned_denominator p a b N).eqSymm (original_kernel_upper p a b N h)

theorem actual_beta_cofinal_domination_slack_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 2) (var 3) (var 4) ⟶ upperSlack (fstT (kernel (var 2) (var 3) (var 4)))
      (fstT (ap2 decayF (var 0) (decayData (var 2) (var 3)))) one (unit (var 0)) (cost (var 2)) (var 1)) :=
  closeUniv 5 (.impI (cofinal_upper_slack _ _ _ _ _ Prf.hyp0))
theorem original_full_interval_beta_kernel_upper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ upper (fstT (kernel (var 1) (var 2) (var 3)))
      (fstT (ap2 decayF (var 0) (decayData (var 1) (var 2)))) one (unit (var 0))) :=
  closeUniv 4 (.impI (original_kernel_upper _ _ _ _ Prf.hyp0))
theorem original_full_interval_beta_kernel_domination_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶
      (RationalArgmin.rationalLE RationalGaussianEmbedding.scalarZero (fstT (kernel (var 1) (var 2) (var 3))) ⋏
        upper (fstT (kernel (var 1) (var 2) (var 3))) (fstT (ap2 decayF (var 0) (decayData (var 1) (var 2)))) one (unit (var 0)))) :=
  closeUniv 4 (.impI (original_kernel_domination _ _ _ _ Prf.hyp0))
theorem actual_full_interval_beta_kernel_domination_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_full_interval_beta_kernel_upper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ upper
      (fstT (fstT (run (var 0) (var 1) (var 2) (var 3)))) (fstT (fstT (sndT (run (var 0) (var 1) (var 2) (var 3)))))
      (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))))) :=
  closeUniv 4 (.impI (returned_upper _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelDomination
