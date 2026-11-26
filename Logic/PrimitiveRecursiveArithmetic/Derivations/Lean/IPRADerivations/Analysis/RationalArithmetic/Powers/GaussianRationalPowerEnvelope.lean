import IPRADerivations.Algebra.PowerDifference
import IPRADerivations.Analysis.Polynomials.GaussianRationalHornerLipschitz
import IPRADerivations.Core.LinearCombination

/-!
# Exact finite envelopes for rationally enlarged Gaussian disks

All numerical radii, denominators and exponents are object variables.  The
power error is the actual natural program K(Z,r)=r (Z+1)^(r-1), with K(Z,0)=0.
A genuine finite power-difference proof yields the O(1/H) envelope at Z+1/H.
The weighted numerator uses denominator H^N, including the empty sum.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPowerEnvelope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Algebra.PowerDifference (gd gd_zero gd_le power_diff)
open LeanProofs.IPRA.Analysis.GaussianProductStability (power_product)
open LeanProofs.IPRA.Analysis.GaussianRationalHornerPerturbation (weighted_power)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def error (Z r : PTm n) : PTm n := r*pw (Z+one) (pred r)

@[simp] theorem subst_error {m : ℕ} (σ : Fin n → PTm m) (Z r : PTm n) :
    Syn.subst σ (error Z r) = error (Syn.subst σ Z) (Syn.subst σ r) := by simp [error]

theorem error_zero (Z : PTm n) : Γ ⊢[PRAAx] error Z zero ≐ zero := by unfold error; ipra_ring

theorem error_succ (Z r : PTm n) : Γ ⊢[PRAAx] error Z (succ r) ≐ succ r*pw (Z+one) r :=
  congrMul (.eqRefl _) (congrAp2 powF (pred_succ r) (.eqRefl _))

/-- The previously derived finite geometric sum is bounded uniformly,
including exponent zero. No power-difference bound is a premise. -/
theorem geometric_bound (x y R r : PTm n)
    (hx : Γ ⊢[PRAAx] le x R) (hy : Γ ⊢[PRAAx] le y R) :
    Γ ⊢[PRAAx] le (gd x y r) (r*pw R (pred r)) := by
  refine .orE (zero_or_succ r) ?_ ?_
  · have e := natEq (Prf.hyp0 : (r ≐ zero)::Γ ⊢[PRAAx] r ≐ zero)
    have g := natEq ((congrAp2 Algebra.PowerDifference.gdF
      (Prf.hyp0 : (r ≐ zero)::Γ ⊢[PRAAx] r ≐ zero) (.eqRefl _)).eqTrans (gd_zero x y))
    refine le_of_eq_add (d := zero) ?_
    apply deriveNat
    ipra_simps
    rw [e,g]
    ring
  · have h : (r ≐ succ (pred r))::Γ ⊢[PRAAx]
        le (gd x y (succ (pred r))) (succ (pred r)*pw R (pred r)) := gd_le _ hx.wk hy.wk
    have e : (r ≐ succ (pred r))::Γ ⊢[PRAAx] r ≐ succ (pred r) := Prf.hyp0
    exact le_congr (congrAp2 Algebra.PowerDifference.gdF e (.eqRefl _)).eqSymm
      (congrMul e (.eqRefl _)).eqSymm h

/-- Exact finite difference when the natural bases differ by one. -/
theorem adjacent_power (y r : PTm n) : Γ ⊢[PRAAx]
    pw (y+one) r ≐ pw y r+gd (y+one) y r := by
  ipra_lc natEq (power_diff (Γ := Γ) (y+one) y r)

/-- Actual natural numerator envelope, valid also at exponent zero and Z=0. -/
theorem power_envelope (Z H r : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    le (pw (Z*H+one) r) (pw Z r*pw H r+error Z r*pw H (pred r)) := by
  have upper : Γ ⊢[PRAAx] le (Z*H+one) ((Z+one)*H) :=
    le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ (le_refl (Z*H)) hH)
  have lower : Γ ⊢[PRAAx] le (Z*H) ((Z+one)*H) :=
    le_trans (le_add_right (Z*H) one) upper
  have bound := geometric_bound (Z*H+one) (Z*H) ((Z+one)*H) r upper lower
  have right : Γ ⊢[PRAAx] r*pw ((Z+one)*H) (pred r) ≐ error Z r*pw H (pred r) :=
    (congrMul (.eqRefl _) (power_product (Z+one) H (pred r))).eqTrans (by unfold error; ipra_ring)
  exact le_congr (adjacent_power (Z*H) r).eqSymm
    (congrAdd (power_product Z H r) right)
    (add_le_add₂ (le_refl (pw (Z*H) r)) bound)

/-- Rational form: (Z+1/H)^r <= Z^r+K/H, after positive clearing. -/
theorem power_envelope_cross (Z H r : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    le (H*pw (Z*H+one) r) ((pw Z r*H+error Z r)*pw H r) := by
  have scaled := le_mul_mono (le_refl H) (power_envelope Z H r hH)
  have weighted := natEq (weighted_power (Γ := Γ) H r)
  have rearrange : Γ ⊢[PRAAx]
      H*(pw Z r*pw H r+error Z r*pw H (pred r)) ≐ (pw Z r*H+error Z r)*pw H r := by
    apply deriveNat
    unfold error
    ipra_simps
    linear_combination Groth.ι (IPRA.Q.mk Γ (pw (Z+one) (pred r)))*weighted
  exact le_congr (.eqRefl _) rearrange scaled

/-! The uniform-denominator weighted finite sum. -/
def weightedStep : PTm 3 := sndT (var 2)*var 1+succ (var 0)*pw (fstT (var 2)) (var 0)*sndT (var 2)
def weightedF : PR 2 := rec2 zero weightedStep
def weighted (U H N : PTm n) : PTm n := ap2 weightedF N (pairT U H)

@[simp] theorem subst_weighted {m : ℕ} (σ : Fin n → PTm m) (U H N : PTm n) :
    Syn.subst σ (weighted U H N) = weighted (Syn.subst σ U) (Syn.subst σ H) (Syn.subst σ N) := by
  simp only [weighted,subst_ap2,subst_pairT]

theorem weighted_zero (U H : PTm n) : Γ ⊢[PRAAx] weighted U H zero ≐ zero := by
  simpa only [weighted,weightedF,ConciseIPRA.PTm.subst_zero] using rec2_zero (Γ := Γ) zero weightedStep (pairT U H)

theorem weighted_succ (U H N : PTm n) : Γ ⊢[PRAAx]
    weighted U H (succ N) ≐ H*weighted U H N+succ N*pw U N*H := by
  have h := rec2_succ (Γ := Γ) zero weightedStep N (pairT U H)
  change Γ ⊢[PRAAx] weighted U H (succ N) ≐ Syn.subst ![N,weighted U H N,pairT U H] weightedStep at h
  have shape : Syn.subst ![N,weighted U H N,pairT U H] weightedStep =
      sndT (pairT U H)*weighted U H N+succ N*pw (fstT (pairT U H)) N*sndT (pairT U H) := by simp [weightedStep]
  rw [shape] at h
  exact h.eqTrans (congrAdd (congrMul (snd_pair U H) (.eqRefl _))
    (congrMul (congrMul (.eqRefl _) (congrAp2 powF (.eqRefl _) (fst_pair U H))) (snd_pair U H)))

def weightedErrorBody : PTm 2 := succ (var 0)*error (var 1) (var 0)
def weightedError (Z N : PTm n) : PTm n := ap2 (sumF weightedErrorBody) N Z

@[simp] theorem subst_weightedError {m : ℕ} (σ : Fin n → PTm m) (Z N : PTm n) :
    Syn.subst σ (weightedError Z N) = weightedError (Syn.subst σ Z) (Syn.subst σ N) := by
  simp only [weightedError,subst_ap2]

theorem weighted_error_body_at (Z i : PTm n) : inst2 weightedErrorBody i Z = succ i*error Z i := by
  simp [weightedErrorBody,inst2]
theorem weighted_error_zero (Z : PTm n) : Γ ⊢[PRAAx] weightedError Z zero ≐ zero := sum_zero _ _
theorem weighted_error_succ (Z N : PTm n) : Γ ⊢[PRAAx]
    weightedError Z (succ N) ≐ weightedError Z N+succ N*error Z N := by
  simpa only [weightedError,weighted_error_body_at] using sum_succ' (Γ := Γ) weightedErrorBody N Z

def weightedLaw (Z H N : PTm n) : Fm PTm n :=
  le (H*weighted (Z*H+one) H N)
    ((GaussianRationalHornerLipschitz.weighted Z N*H+weightedError Z N)*pw H N)
@[simp] theorem subst_weightedLaw {m : ℕ} (σ : Fin n → PTm m) (Z H N : PTm n) :
    (weightedLaw Z H N).subst σ = weightedLaw (Syn.subst σ Z) (Syn.subst σ H) (Syn.subst σ N) := by
  simp [weightedLaw]

theorem weighted_envelope_zero (Z H : PTm n) : Γ ⊢[PRAAx] weightedLaw Z H zero := by
  refine le_of_eq_add (d := zero) ?_
  have w := natEq (weighted_zero (Γ := Γ) (Z*H+one) H)
  have z := natEq (GaussianRationalHornerLipschitz.weighted_zero (Γ := Γ) Z)
  have e := natEq (weighted_error_zero (Γ := Γ) Z)
  change Γ ⊢[PRAAx] _ ≐ _
  apply deriveNat
  ipra_simps
  rw [w,z,e]
  ring

theorem weighted_envelope_step (Z H N : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (ih : Γ ⊢[PRAAx] weightedLaw Z H N) : Γ ⊢[PRAAx] weightedLaw Z H (succ N) := by
  have old := le_mul_mono (le_refl H) ih
  have next := le_mul_mono (le_refl (succ N*H)) (power_envelope_cross Z H N hH)
  have combined := add_le_add₂ old next
  have ws := natEq (weighted_succ (Γ := Γ) (Z*H+one) H N)
  have zs := natEq (GaussianRationalHornerLipschitz.weighted_succ (Γ := Γ) Z N)
  have es := natEq (weighted_error_succ (Γ := Γ) Z N)
  have ps := natEq (pw_succ (Γ := Γ) H N)
  have left : Γ ⊢[PRAAx]
      H*(H*weighted (Z*H+one) H N)+(succ N*H)*(H*pw (Z*H+one) N) ≐
        H*weighted (Z*H+one) H (succ N) := by
    apply deriveNat
    ipra_simps
    rw [ws]
    ring
  have right : Γ ⊢[PRAAx]
      H*((GaussianRationalHornerLipschitz.weighted Z N*H+weightedError Z N)*pw H N)+
        (succ N*H)*((pw Z N*H+error Z N)*pw H N) ≐
      (GaussianRationalHornerLipschitz.weighted Z (succ N)*H+weightedError Z (succ N))*pw H (succ N) := by
    apply deriveNat
    ipra_simps
    rw [zs,es,ps]
    ring
  exact le_congr left right combined

/-- Exact weighted rational envelope, with an actual finite error sum.
Multiplying both sides by A gives the source M_Z constant envelope. -/
theorem weighted_envelope (Z H N : PTm n) (hH : Γ ⊢[PRAAx] le one H) :
    Γ ⊢[PRAAx] weightedLaw Z H N := by
  have positive : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift H) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hH.shift
  have all : Γ ⊢[PRAAx] .all (weightedLaw (Syn.shift Z) (Syn.shift H) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_weightedLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact weighted_envelope_zero Z H
    · simp only [subst_weightedLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact weighted_envelope_step _ _ _ positive.wk Prf.hyp0
  simpa only [subst_weightedLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem constant_envelope (Z H N A : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    le (H*(A*weighted (Z*H+one) H N))
      ((GaussianRationalHornerLipschitz.constant N Z A*H+A*weightedError Z N)*pw H N) := by
  have h := le_mul_mono (le_refl A) (weighted_envelope Z H N hH)
  exact le_congr (by ipra_ring) (by unfold GaussianRationalHornerLipschitz.constant; ipra_ring) h

/-! Literal finite-sum meaning of the runtime numerator program. -/
def sourceBody : PTm 2 := succ (var 0)*pw (fstT (var 1)) (var 0)*
  pw (fstT (sndT (var 1))) (monus (sndT (sndT (var 1))) (var 0))
def sourcePrefix (U H N k : PTm n) : PTm n := ap2 (sumF sourceBody) k (pairT U (pairT H N))

@[simp] theorem subst_sourcePrefix {m : ℕ} (σ : Fin n → PTm m) (U H N k : PTm n) :
    Syn.subst σ (sourcePrefix U H N k) = sourcePrefix (Syn.subst σ U) (Syn.subst σ H)
      (Syn.subst σ N) (Syn.subst σ k) := by simp [sourcePrefix]

theorem source_body_at (U H N i : PTm n) : Γ ⊢[PRAAx]
    inst2 sourceBody i (pairT U (pairT H N)) ≐ succ i*pw U i*pw H (monus N i) := by
  have hU := fst_pair (Γ := Γ) U (pairT H N)
  have hH := (congrFst (snd_pair (Γ := Γ) U (pairT H N))).eqTrans (fst_pair H N)
  have hN := (congrSnd (snd_pair (Γ := Γ) U (pairT H N))).eqTrans (snd_pair H N)
  simp only [sourceBody,inst2,PTm.subst_mul,subst_ap2,subst_fstT,subst_sndT,PTm.subst_monus,
    ConciseIPRA.PTm.subst_succ,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrMul (congrMul (.eqRefl _) (congrAp2 powF (.eqRefl _) hU))
    (congrAp2 powF (congrMonus hN (.eqRefl _)) hH)

theorem source_prefix_zero (U H N : PTm n) : Γ ⊢[PRAAx] sourcePrefix U H N zero ≐ zero := sum_zero _ _
theorem source_prefix_succ (U H N k : PTm n) : Γ ⊢[PRAAx]
    sourcePrefix U H N (succ k) ≐ sourcePrefix U H N k+succ k*pw U k*pw H (monus N k) :=
  (sum_succ' sourceBody k (pairT U (pairT H N))).eqTrans (congrAdd (.eqRefl _) (source_body_at U H N k))

def sourceLaw (U H N k : PTm n) : Fm PTm n := le k N ⟶
  sourcePrefix U H N k ≐ weighted U H k*pw H (monus N k)
@[simp] theorem subst_sourceLaw {m : ℕ} (σ : Fin n → PTm m) (U H N k : PTm n) :
    (sourceLaw U H N k).subst σ = sourceLaw (Syn.subst σ U) (Syn.subst σ H)
      (Syn.subst σ N) (Syn.subst σ k) := by simp [sourceLaw]

theorem source_prefix_step (U H N k : PTm n) (hk : Γ ⊢[PRAAx] le (succ k) N)
    (ih : Γ ⊢[PRAAx] sourcePrefix U H N k ≐ weighted U H k*pw H (monus N k)) : Γ ⊢[PRAAx]
    sourcePrefix U H N (succ k) ≐ weighted U H (succ k)*pw H (monus N (succ k)) := by
  have shape : Γ ⊢[PRAAx] N ≐ k+succ (monus N (succ k)) :=
    (eq_add_of_le hk).eqTrans (by ipra_ring)
  have remaining : Γ ⊢[PRAAx] monus N k ≐ succ (monus N (succ k)) :=
    (congrMonus shape (.eqRefl _)).eqTrans (add_monus' _ _)
  have power := natEq ((congrAp2 powF remaining (.eqRefl H)).eqTrans (pw_succ H (monus N (succ k))))
  have s := natEq (source_prefix_succ (Γ := Γ) U H N k)
  have w := natEq (weighted_succ (Γ := Γ) U H k)
  have e := natEq ih
  apply deriveNat
  ipra_simps
  rw [s,e,w,power]
  ring

/-- Full finite-sum identity, proved by QF induction on an arbitrary prefix.
It is valid even for H=0; the rational interpretation uses H>=1 separately. -/
theorem source_prefix (U H N k : PTm n) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    sourcePrefix U H N k ≐ weighted U H k*pw H (monus N k) := by
  have all : Γ ⊢[PRAAx] .all (sourceLaw (Syn.shift U) (Syn.shift H) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_sourceLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      refine .impI ?_
      exact (source_prefix_zero U H N).wk.eqTrans
        ((congrMul (weighted_zero U H) (.eqRefl _)).eqTrans (zero_mul _)).eqSymm.wk
    · simp only [subst_sourceLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact source_prefix_step _ _ _ _ Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] sourceLaw U H N k := by
    simpa only [subst_sourceLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

/-- W(U,H,N)=sum_(i<N) (i+1)U^i H^(N-i), with literal internal summation. -/
theorem weighted_source_sum (U H N : PTm n) : Γ ⊢[PRAAx]
    weighted U H N ≐ sourcePrefix U H N N := by
  have right : Γ ⊢[PRAAx] weighted U H N*pw H (monus N N) ≐ weighted U H N :=
    (congrMul (.eqRefl _) ((congrAp2 powF (monus_self N) (.eqRefl H)).eqTrans (pw_zero H))).eqTrans (by ipra_ring)
  exact ((source_prefix U H N N (le_refl _)).eqTrans right).eqSymm

/-- Coarse disk envelope used only for the vanishing remainder term. -/
theorem coarse_power_envelope (Z H r : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    le (pw (Z*H+one) r) (pw (Z+one) r*pw H r) := by
  have upper : Γ ⊢[PRAAx] le (Z*H+one) ((Z+one)*H) :=
    le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ (le_refl (Z*H)) hH)
  exact le_congr (.eqRefl _) (power_product (Z+one) H r) (pw_le_pw r upper)

theorem denominator_positive (H N : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    le one (pw H N) := GaussianFactorBudget.power_positive H N hH

/-! Actual primitive recursive computed constants and numerator metadata. -/
def output (Z H r N : PTm n) : PTm n :=
  pairT (error Z r) (pairT (weightedError Z N) (pairT (weighted (Z*H+one) H N) (pw H N)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (Z H r N : PTm n) : PTm n := PTm.app outputF ![Z,H,r,N]

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (Z H r N : PTm n) :
    Syn.subst σ (output Z H r N) = output (Syn.subst σ Z) (Syn.subst σ H)
      (Syn.subst σ r) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (Z H r N : PTm n) :
    Syn.subst σ (run Z H r N) = run (Syn.subst σ Z) (Syn.subst σ H)
      (Syn.subst σ r) (Syn.subst σ N) := by
  simp only [run,PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem envelope_program (Z H r N : PTm n) : Γ ⊢[PRAAx] run Z H r N ≐ output Z H r N := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![Z,H,r,N]

theorem power_envelope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶
      (le (pw (var 0*var 1+one) (var 2))
        (pw (var 0) (var 2)*pw (var 1) (var 2)+error (var 0) (var 2)*pw (var 1) (pred (var 2))) ⋏
       le (var 1*pw (var 0*var 1+one) (var 2))
        ((pw (var 0) (var 2)*var 1+error (var 0) (var 2))*pw (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.andI (power_envelope _ _ _ Prf.hyp0) (power_envelope_cross _ _ _ Prf.hyp0)))

theorem coarse_power_envelope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le (pw (var 0*var 1+one) (var 2))
      (pw (var 0+one) (var 2)*pw (var 1) (var 2))) :=
  closeUniv 3 (.impI (coarse_power_envelope _ _ _ Prf.hyp0))

theorem weighted_envelope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ (le one (pw (var 1) (var 2)) ⋏ weightedLaw (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.andI (denominator_positive _ _ Prf.hyp0) (weighted_envelope _ _ _ Prf.hyp0)))

theorem constant_envelope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le (var 1*(var 3*weighted (var 0*var 1+one) (var 1) (var 2)))
      ((GaussianRationalHornerLipschitz.constant (var 2) (var 0) (var 3)*var 1+
          var 3*weightedError (var 0) (var 2))*pw (var 1) (var 2))) :=
  closeUniv 4 (.impI (constant_envelope _ _ _ _ Prf.hyp0))

theorem weighted_source_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (weighted (var 0) (var 1) (var 2) ≐ sourcePrefix (var 0) (var 1) (var 2) (var 2)) :=
  closeUniv 3 (weighted_source_sum _ _ _)

theorem envelope_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (envelope_program _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalPowerEnvelope
