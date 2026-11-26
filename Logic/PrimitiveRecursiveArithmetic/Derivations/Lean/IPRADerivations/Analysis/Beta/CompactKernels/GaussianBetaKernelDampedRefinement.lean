import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelDampedDoubling
import IPRADerivations.Core.CertificateTactics

/-!
# Actual finite dyadic telescope of the beta relative error

Every value is the original kernel at cutoff N*2^j. The invariant
retains the exact finite geometric factor (2^j-1)/2^j and the later
kernel as multiplier. Its induction is a native atomic inequality,
not an induction on a name or a supplied approximation predicate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelDampedRefinement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaKernelDampedDoubling (smaller larger commonDenominator)
open GaussianBetaKernelRefinement (cutoff cutoff_zero cutoff_succ cutoff_ge)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def numerator (a b N : PTm n) : PTm n := pw (monus (b*N) a) N
def denominator (b N : PTm n) : PTm n := pw (b*N) N
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (numerator a b N) = numerator (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (b N : PTm n) :
    Syn.subst σ (denominator b N) = denominator (Syn.subst σ b) (Syn.subst σ N) := by simp [denominator]

theorem numerator_congr {a a' b b' N N' : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') (hN : Γ ⊢[PRAAx] N ≐ N') : Γ ⊢[PRAAx]
    numerator a b N ≐ numerator a' b' N' :=
  congrAp2 powF hN (congrMonus (congrMul hb hN) ha)
theorem denominator_congr {b b' N N' : PTm n}
    (hb : Γ ⊢[PRAAx] b ≐ b') (hN : Γ ⊢[PRAAx] N ≐ N') : Γ ⊢[PRAAx]
    denominator b N ≐ denominator b' N' := congrAp2 powF hN (congrMul hb hN)

theorem next_numerator (a b N : PTm n) : Γ ⊢[PRAAx]
    numerator a b (two*N) ≐ pw (larger a (b*N)) N :=
  (congrAp2 powF (.eqRefl (two*N)) (congrMonus (by ipra_ring : Γ ⊢[PRAAx] b*(two*N) ≐ two*(b*N)) (.eqRefl a))).eqTrans
    (AnalyticNumberTheory.RSA.pw_mul (monus (two*(b*N)) a) two N).eqSymm

theorem next_denominator (b N : PTm n) : Γ ⊢[PRAAx]
    denominator b (two*N) ≐ commonDenominator (b*N) N := congrAp2 powF (.eqRefl _) (by ipra_ring)

theorem current_common_numerator (a b N : PTm n) : Γ ⊢[PRAAx]
    pw (smaller a (b*N)) N ≐ numerator a b N*pw (num 4*(b*N)) N :=
  AnalyticNumberTheory.LocalFactor.pw_mul_base _ _ _

/-- One actual step, cleared only at the two actual kernel denominators. -/
theorem native_step (a b N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    le ((two*b*b*N)*numerator a b (two*N)*denominator b N)
      ((two*b*b*N)*numerator a b N*denominator b (two*N)+a*a*numerator a b (two*N)*denominator b N) := by
  have raw : Γ ⊢[PRAAx] le
      ((two*b*b*N)*pw (larger a (b*N)) N)
      ((two*b*b*N)*pw (smaller a (b*N)) N+a*a*pw (larger a (b*N)) N) :=
    RationalValueBounds.positive_cancel h.andE₂.andE₁
      (le_congr (by ipra_ring) (by ipra_ring)
        (GaussianBetaKernelDampedDoubling.doubling_relative_cleared a (b*N) N h.andE₂.andE₂))
  have np := natEq (next_numerator (Γ := Γ) a b N)
  have nd := natEq (next_denominator (Γ := Γ) b N)
  have cp := natEq (current_common_numerator (Γ := Γ) a b N)
  have cd := natEq (show Γ ⊢[PRAAx] commonDenominator (b*N) N ≐ pw (num 4*(b*N)) N*denominator b N from
    GaussianBetaKernelRefinement.doubling_denominator (b*N) N)
  apply le_congr ?_ ?_ (mul_le_mul_right (denominator b N) raw)
  · apply deriveNat; ipra_simps; rw [np]
  · apply deriveNat; ipra_simps; rw [np,nd,cp,cd]; ring

theorem native_monotone (a b N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    le (numerator a b N*denominator b (two*N)) (numerator a b (two*N)*denominator b N) := by
  have small : Γ ⊢[PRAAx] le a (b*N) := le_trans (le_of_eq_add (d := a) (by ipra_ring)) h.andE₂.andE₂
  have baseEq : Γ ⊢[PRAAx] b*(two*N) ≐ two*(b*N) := by ipra_ring
  have denEq := congrAp2 powF (.eqRefl (two*N)) baseEq
  have numEq := congrAp2 powF (.eqRefl (two*N)) (congrMonus baseEq (.eqRefl a))
  exact le_congr (congrMul (.eqRefl _) denEq.eqSymm) (congrMul numEq.eqSymm (.eqRefl _))
    (GaussianBetaKernelRefinement.doubling_cleared a (b*N) N small)

def relation (D A W P Q P0 Q0 : PTm n) : Fm PTm n :=
  le (D*W*P*Q0) (D*W*P0*Q+A*monus W one*P*Q0)

/-- The finite telescoping step uses the actual relative error and
actual monotonicity, with no sign or regularity law supplied. -/
theorem telescope_step (D A W P Q PN QN P0 Q0 : PTm n)
    (hW : Γ ⊢[PRAAx] le one W) (hQ : Γ ⊢[PRAAx] le one Q)
    (ih : Γ ⊢[PRAAx] relation D A W P Q P0 Q0)
    (step : Γ ⊢[PRAAx] le (D*(two*W)*PN*Q) (D*(two*W)*P*QN+A*PN*Q))
    (mono : Γ ⊢[PRAAx] le (P*QN) (PN*Q)) : Γ ⊢[PRAAx]
    relation D A (two*W) PN QN P0 Q0 := by
  have budget : Γ ⊢[PRAAx]
      le (Q*(D*(two*W)*PN*Q0))
        (Q*(D*(two*W)*P0*QN+A*(two*monus W one+one)*PN*Q0)) := by
    ipra_le (𝔞 Q0)*sl step+(𝔞 (two*QN))*sl ih+(𝔞 (two*A*monus W one*Q0))*sl mono
  have cancelled := RationalValueBounds.positive_cancel hQ budget
  have h2 : Γ ⊢[PRAAx] le one (two*W) := le_trans hW (le_of_eq_add (d := W) (by ipra_ring))
  have gap : Γ ⊢[PRAAx] two*monus W one+one ≐ monus (two*W) one := by
    ipra_lc -2*natEq (eq_add_of_le hW)+natEq (eq_add_of_le h2)
  exact le_congr (.eqRefl _) (congrAdd (.eqRefl _) (congrMul (congrMul (congrMul (.eqRefl A) gap) (.eqRefl PN)) (.eqRefl Q0))) cancelled

def refinementLaw (a b N j : PTm n) : Fm PTm n := relation (b*b*N) (a*a) (unit j)
  (numerator a b (cutoff N j)) (denominator b (cutoff N j)) (numerator a b N) (denominator b N)
@[simp] theorem subst_refinementLaw {m : ℕ} (σ : Fin n → PTm m) (a b N j : PTm n) :
    (refinementLaw a b N j).subst σ = refinementLaw (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) (Syn.subst σ j) := by
  simp [refinementLaw,relation]

theorem refinement_zero (a b N : PTm n) : Γ ⊢[PRAAx] refinementLaw a b N zero := by
  have u := natEq (show Γ ⊢[PRAAx] unit zero ≐ one from pw_zero two)
  have ep := natEq (numerator_congr (Γ := Γ) (.eqRefl a) (.eqRefl b) (cutoff_zero N))
  have eq := natEq (denominator_congr (Γ := Γ) (.eqRefl b) (cutoff_zero N))
  have gap := natEq (show Γ ⊢[PRAAx] monus (unit zero) one ≐ zero from
    (congrMonus (pw_zero two) (.eqRefl one)).eqTrans (monus_self one))
  apply le_of_eq_add (d := zero)
  apply deriveNat
  ipra_simps
  rw [ep,eq,u,gap]; ring

theorem later_source (a b N j : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    GaussianBetaKernelLogarithm.source a b (cutoff N j) :=
  .andI h.andE₁ (.andI (le_trans h.andE₂.andE₁ (cutoff_ge N j))
    (le_trans h.andE₂.andE₂ (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl b) (cutoff_ge N j))))

theorem refinement_step (a b N j : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N)
    (ih : Γ ⊢[PRAAx] refinementLaw a b N j) : Γ ⊢[PRAAx] refinementLaw a b N (succ j) := by
  let K := cutoff N j
  have hs := later_source a b N j h
  have rawStep := native_step a b K hs
  have alignedStep : Γ ⊢[PRAAx]
      le ((b*b*N)*(two*unit j)*numerator a b (two*K)*denominator b K)
        ((b*b*N)*(two*unit j)*numerator a b K*denominator b (two*K)+a*a*numerator a b (two*K)*denominator b K) :=
    le_congr (by dsimp only [K,cutoff]; ipra_ring) (by dsimp only [K,cutoff]; ipra_ring) rawStep
  have raw := telescope_step (b*b*N) (a*a) (unit j) _ _ _ _ _ _ (unit_positive j)
    (RationalNonnegativePowers.denominator_positive _ _ (positive_product _ _ h.andE₁ hs.andE₂.andE₁)) ih alignedStep (native_monotone a b K hs)
  have eqU : Γ ⊢[PRAAx] unit (succ j) ≐ two*unit j := (pw_succ two j).eqTrans (mul_comm _ _)
  have eqK := cutoff_succ (Γ := Γ) N j
  have eqP := numerator_congr (.eqRefl a) (.eqRefl b) eqK
  have eqQ := denominator_congr (.eqRefl b) eqK
  apply le_congr ?_ ?_ raw
  · apply deriveNat
    have eu := natEq eqU
    have ep := natEq eqP
    ipra_simps
    rw [eu,ep]
  · apply deriveNat
    have eu := natEq eqU
    have ep := natEq eqP
    have eq := natEq eqQ
    have em := natEq (congrMonus eqU (.eqRefl one))
    ipra_simps
    rw [eu,ep,eq,em]

theorem actual_dyadic_telescope (a b N j : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    refinementLaw a b N j := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianBetaKernelLogarithm.source (Syn.shift a) (Syn.shift b) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (refinementLaw (Syn.shift a) (Syn.shift b) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_refinementLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact refinement_zero a b N
    · simp only [subst_refinementLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact refinement_step _ _ _ _ hs.wk Prf.hyp0
  simpa only [subst_refinementLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

def geometricNumerator (a b N j : PTm n) : PTm n :=
  a*a*monus (unit j) one*numerator a b (cutoff N j)
def geometricDenominator (b N j : PTm n) : PTm n :=
  b*b*N*unit j*denominator b (cutoff N j)
def relativeNumerator (a b N j : PTm n) : PTm n := a*a*numerator a b (cutoff N j)
def relativeDenominator (b N j : PTm n) : PTm n := b*b*N*denominator b (cutoff N j)

theorem denominator_positive (b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le one (denominator b N) := RationalNonnegativePowers.denominator_positive _ _ (positive_product b N hb hN)

theorem original_finite_geometric_error (a b N j : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (GaussianBetaKernelRefinement.value a b (cutoff N j)) (GaussianBetaKernelRefinement.value a b N)
      (geometricNumerator a b N j) (geometricDenominator b N j) := by
  let P := numerator a b (cutoff N j)
  let Q := denominator b (cutoff N j)
  let P0 := numerator a b N
  let Q0 := denominator b N
  let D := b*b*N
  let W := unit j
  let G := monus W one
  have hs := later_source a b N j h
  have q := denominator_positive (Γ := Γ) b (cutoff N j) h.andE₁ hs.andE₂.andE₁
  have q0 := denominator_positive (Γ := Γ) b N h.andE₁ h.andE₂.andE₁
  have raw := actual_dyadic_telescope a b N j h
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ (ZT.ofNat P) (ZT.ofNat P0) Q Q0
    (geometricNumerator a b N j) (geometricDenominator b N j) q q0
    (RationalNonnegativePowers.power_represents _ _ _ (positive_product b (cutoff N j) h.andE₁ hs.andE₂.andE₁))
    (RationalNonnegativePowers.power_represents _ _ _ (positive_product b N h.andE₁ h.andE₂.andE₁))
  apply zle_of_toZ (Q*monus (D*W*P0*Q+a*a*G*P*Q0) (D*W*P*Q0))
  have e := natEq (eq_add_of_le raw)
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
  dsimp only [geometricNumerator,geometricDenominator,P,Q,P0,Q0,D,W,G] at e ⊢
  ipra_simps
  linear_combination -𝔞(denominator b (cutoff N j))*e

/-- The exact later beta value remains as the error multiplier. -/
theorem original_finite_relative_error (a b N j : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (GaussianBetaKernelRefinement.value a b (cutoff N j)) (GaussianBetaKernelRefinement.value a b N)
      (relativeNumerator a b N j) (relativeDenominator b N j) := by
  have hs := later_source a b N j h
  have den := positive_product (Γ := Γ) _ _
    (positive_product _ _ (positive_product _ _ (positive_product b b h.andE₁ h.andE₁) h.andE₂.andE₁) (unit_positive j))
    (denominator_positive b (cutoff N j) h.andE₁ hs.andE₂.andE₁)
  apply RationalValueBounds.upper_mono _ _ _ _ _ _ den (original_finite_geometric_error a b N j h)
  exact le_congr (by dsimp only [geometricNumerator,relativeDenominator]; ipra_ring)
    (by dsimp only [geometricDenominator,relativeNumerator]; ipra_ring)
    (mul_le_mul_right (a*a*numerator a b (cutoff N j)*(b*b*N*denominator b (cutoff N j))) (GaussianRationalMonicReconstruction.monus_le_left (unit j) one))

theorem original_beta_dyadic_relative_telescope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianBetaKernelLogarithm.source (var 0) (var 1) (var 2) ⟶ refinementLaw (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (actual_dyadic_telescope _ _ _ _ Prf.hyp0))
theorem original_beta_finite_geometric_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianBetaKernelLogarithm.source (var 0) (var 1) (var 2) ⟶
      RationalValueBounds.upper
        (GaussianBetaKernelRefinement.value (var 0) (var 1) (cutoff (var 2) (var 3)))
        (GaussianBetaKernelRefinement.value (var 0) (var 1) (var 2))
        (geometricNumerator (var 0) (var 1) (var 2) (var 3)) (geometricDenominator (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_finite_geometric_error _ _ _ _ Prf.hyp0))

theorem original_kernel_finite_relative_error (a b N j : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (GaussianBetaKernelExponential.kernel a b (cutoff N j)))
      (fstT (GaussianBetaKernelExponential.kernel a b N)) (relativeNumerator a b N j) (relativeDenominator b N j) := by
  have hs := later_source a b N j h
  have old : Γ ⊢[PRAAx] GaussianBetaKernelRefinement.source a b N :=
    .andI h.andE₁ (.andI h.andE₂.andE₁ (le_trans (le_of_eq_add (d := a) (by ipra_ring)) h.andE₂.andE₂))
  have later : Γ ⊢[PRAAx] GaussianBetaKernelRefinement.source a b (cutoff N j) :=
    .andI hs.andE₁ (.andI hs.andE₂.andE₁ (le_trans (le_of_eq_add (d := a) (by ipra_ring)) hs.andE₂.andE₂))
  exact RationalValueBounds.upper_congr (GaussianBetaKernelRefinement.kernel_real_part _ _ _ later).eqSymm
    (GaussianBetaKernelRefinement.kernel_real_part _ _ _ old).eqSymm (.eqRefl _) (.eqRefl _)
    (original_finite_relative_error a b N j h)

theorem original_actual_kernels_finite_relative_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianBetaKernelLogarithm.source (var 0) (var 1) (var 2) ⟶
      RationalValueBounds.upper
        (fstT (GaussianBetaKernelExponential.kernel (var 0) (var 1) (cutoff (var 2) (var 3))))
        (fstT (GaussianBetaKernelExponential.kernel (var 0) (var 1) (var 2)))
        (relativeNumerator (var 0) (var 1) (var 2) (var 3)) (relativeDenominator (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_kernel_finite_relative_error _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelDampedRefinement
