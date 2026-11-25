import IPRADerivations.Analysis.FiniteExponential
import IPRADerivations.Core.LinearCombination

/-!
# Literal finite logarithm polynomial and its differential residual

Gamma (C4), finite algebra only. For internal cutoff `N`, numerator code `x`
and denominator `D`, `logarithm` evaluates the literal polynomial
`N! D^N ∑_{j=1}^N (-1)^(j-1)(x/D)^j/j`.
`derivative` independently evaluates its termwise formal derivative. Every
sum, coefficient, signed power and cutoff is an actual PR program. The
coefficient interpretation and the exact geometric derivative residual are
derived, rather than assumed.

This does not yet identify the coefficients of the literal composition
`exp(log(1+w))` with Bell history, or establish the analytic name identity.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.FiniteLogarithm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.LogarithmExponentialCoefficients
  (value code eval_value_code eval_value_congr kernel kernelCode kernel_differential kernel_zero)
open LeanProofs.IPRA.Analysis.FiniteExponential
  (power powerF powerCode power_succ power_zero scalar dscalar scalar_congr scalar_self scalar_step
    weight weight_exact data component)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Numerator of the `j=k+1` logarithmic monomial, or its derivative's
monomial before multiplication by `k+1`. -/
def monomial (differentiate : Bool) (x k : PTm n) : ZT n :=
  kernel k*power x (if differentiate then k else succ k)

@[simp] theorem subst_monomial {m : ℕ} (σ : Fin n → PTm m) (d : Bool) (x k : PTm n) :
    (monomial d x k).subst σ = monomial d (Syn.subst σ x) (Syn.subst σ k) := by
  cases d <;> simp [monomial]

def monomialF (d : Bool) : PR 2 := PTm.toPR (code (monomial d (var 0) (var 1)))
def monomialCode (d : Bool) (x k : PTm n) : PTm n := ap2 (monomialF d) x k

@[simp] theorem subst_monomialCode {m : ℕ} (σ : Fin n → PTm m) (d : Bool) (x k : PTm n) :
    Syn.subst σ (monomialCode d x k) = monomialCode d (Syn.subst σ x) (Syn.subst σ k) := by simp [monomialCode]

theorem monomial_at (d : Bool) (x k : PTm n) :
    Γ ⊢[PRAAx] monomialCode d x k ≐ code (monomial d x k) := by
  simpa [monomialCode,monomialF,ap2] using
    toPR_eq (Γ := Γ) (code (monomial d (var 0) (var 1)) : PTm 2) ![x,k]

theorem monomial_value (d : Bool) (x k : PTm n) :
    ZT.toZ Γ (value (monomialCode d x k)) = ZT.toZ Γ (monomial d x k) :=
  (eval_value_congr (monomial_at d x k)).trans (eval_value_code _)

def coefficient (d : Bool) (N k D : PTm n) : PTm n :=
  if d then dscalar N k D else scalar N (succ k) D

@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (d : Bool) (N k D : PTm n) :
    Syn.subst σ (coefficient d N k D) = coefficient d (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ D) := by
  cases d <;> simp [coefficient]

def body (d p : Bool) : PTm 2 :=
  coefficient d (fstT (var 1)) (var 0) (sndT (sndT (var 1)))*
    component p (value (monomialCode d (fstT (sndT (var 1))) (var 0)))
def sum (d p : Bool) (r N x D : PTm n) : PTm n := ap2 (sumF (body d p)) r (data N x D)
def logarithm (x D N : PTm n) : ZT n := ⟨sum false true N N x D,sum false false N N x D⟩
def derivative (x D N : PTm n) : ZT n := ⟨sum true true N N x D,sum true false N N x D⟩

@[simp] theorem subst_sum {m : ℕ} (σ : Fin n → PTm m) (d p : Bool) (r N x D : PTm n) :
    Syn.subst σ (sum d p r N x D) = sum d p (Syn.subst σ r) (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ D) := by simp [sum]
@[simp] theorem subst_logarithm {m : ℕ} (σ : Fin n → PTm m) (x D N : PTm n) :
    (logarithm x D N).subst σ = logarithm (Syn.subst σ x) (Syn.subst σ D) (Syn.subst σ N) := by simp [logarithm,ZT.subst]
@[simp] theorem subst_derivative {m : ℕ} (σ : Fin n → PTm m) (x D N : PTm n) :
    (derivative x D N).subst σ = derivative (Syn.subst σ x) (Syn.subst σ D) (Syn.subst σ N) := by simp [derivative,ZT.subst]

theorem coefficient_congr (d : Bool) {N N' k k' D D' : PTm n}
    (hN : Γ ⊢[PRAAx] N ≐ N') (hk : Γ ⊢[PRAAx] k ≐ k') (hD : Γ ⊢[PRAAx] D ≐ D') :
    Γ ⊢[PRAAx] coefficient d N k D ≐ coefficient d N' k' D' := by
  cases d
  · exact scalar_congr hN (congrSucc hk) hD
  · exact congrMul (congrSucc hk) (scalar_congr hN (congrSucc hk) hD)

theorem body_at (d p : Bool) (k N x D : PTm n) :
    Γ ⊢[PRAAx] inst2 (body d p) k (data N x D) ≐
      coefficient d N k D*component p (value (monomialCode d x k)) := by
  have hn : Γ ⊢[PRAAx] fstT (data N x D) ≐ N := fst_pair _ _
  have hx : Γ ⊢[PRAAx] fstT (sndT (data N x D)) ≐ x :=
    (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have hd : Γ ⊢[PRAAx] sndT (sndT (data N x D)) ≐ D :=
    (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  have a : inst2 (body d p) k (data N x D) =
      coefficient d (fstT (data N x D)) k (sndT (sndT (data N x D)))*
        component p (value (monomialCode d (fstT (sndT (data N x D))) k)) := by
    cases p <;> simp [body,component,inst2,value]
  rw [a]
  apply congrMul (coefficient_congr d hn (.eqRefl _) hd)
  cases p
  · exact congrSnd (congrAp2 (monomialF d) hx (.eqRefl _))
  · exact congrFst (congrAp2 (monomialF d) hx (.eqRefl _))

theorem coefficient_step (d : Bool) (N k D : PTm n) (hk : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] coefficient d (succ N) k D ≐ (succ N*D)*coefficient d N k D := by
  cases d
  · exact scalar_step N (succ k) D hk
  · exact (congrMul (.eqRefl _) (scalar_step N (succ k) D hk)).eqTrans (by simp only [coefficient,if_true,dscalar]; ipra_ring)

theorem prefix_step (d p : Bool) (N x D : PTm n) :
    Γ ⊢[PRAAx] sum d p N (succ N) x D ≐ (succ N*D)*sum d p N N x D := by
  apply sum_scale
  refine .allI (.impI ?_)
  rw [show Syn.shift (data (succ N) x D) = data (succ (Syn.shift N)) (Syn.shift x) (Syn.shift D) by simp [Syn.shift]]
  rw [show Syn.shift (data N x D) = data (Syn.shift N) (Syn.shift x) (Syn.shift D) by simp [Syn.shift]]
  simp only [Syn.shift,PTm.subst_mul,ConciseIPRA.PTm.subst_succ]
  let Δ : List (Fm PTm (n+1)) := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  change Δ ⊢[PRAAx] inst2 (body d p) (var 0) (data (succ (Syn.shift N)) (Syn.shift x) (Syn.shift D)) ≐
    (succ (Syn.shift N)*Syn.shift D)*inst2 (body d p) (var 0) (data (Syn.shift N) (Syn.shift x) (Syn.shift D))
  ipra_lc natEq (body_at (Γ := Δ) d p (var 0) (succ (Syn.shift N)) (Syn.shift x) (Syn.shift D))-
    (𝔞(Syn.shift N)+1)*𝔞(Syn.shift D)*natEq (body_at (Γ := Δ) d p (var 0) (Syn.shift N) (Syn.shift x) (Syn.shift D))+ 𝔞(component p (value (monomialCode d (Syn.shift x) (var 0))))*natEq (coefficient_step (Γ := Δ) d (Syn.shift N) (var 0) (Syn.shift D) Prf.hyp0)

theorem coefficient_endpoint (d : Bool) (N D : PTm n) :
    Γ ⊢[PRAAx] coefficient d (succ N) N D ≐ (if d then succ N else one) := by
  cases d
  · exact scalar_self _ _
  · exact (congrMul (.eqRefl _) (scalar_self (succ N) D)).eqTrans (by simp only [if_true]; ipra_ring)

theorem component_recurrence (d p : Bool) (N x D : PTm n) :
    Γ ⊢[PRAAx] sum d p (succ N) (succ N) x D ≐
      (succ N*D)*sum d p N N x D+(if d then succ N else one)*component p (value (monomialCode d x N)) :=
  (sum_succ' (body d p) N (data (succ N) x D)).eqTrans
    (congrAdd (prefix_step d p N x D)
      ((body_at d p N (succ N) x D).eqTrans (congrMul (coefficient_endpoint d N D) (.eqRefl _))))

theorem logarithm_recurrence (x D N : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (logarithm x D (succ N))
      (ZT.ofNat (succ N*D)*logarithm x D N+kernel N*power x (succ N)) := by
  have p := natEq (component_recurrence (Γ := Γ) false true N x D)
  have q := natEq (component_recurrence (Γ := Γ) false false N x D)
  have m := monomial_value (Γ := Γ) false x N
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [logarithm,ZT.toZ]
  simp only [component,Bool.false_eq_true,if_false,if_true] at p q
  simp only [monomial,Bool.false_eq_true,if_false] at m
  rw [ZT.toZ_mul] at m
  simp only [value,ZT.toZ] at m
  simp only [value] at p q ⊢
  ipra_simps
  linear_combination p-q+m

theorem derivative_recurrence (x D N : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (derivative x D (succ N))
      (ZT.ofNat (succ N*D)*derivative x D N+ZT.ofNat (succ N)*kernel N*power x N) := by
  have p := natEq (component_recurrence (Γ := Γ) true true N x D)
  have q := natEq (component_recurrence (Γ := Γ) true false N x D)
  have m := monomial_value (Γ := Γ) true x N
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [derivative,ZT.toZ]
  simp only [component,Bool.false_eq_true,if_false,if_true] at p q
  simp only [monomial,if_true] at m
  rw [ZT.toZ_mul] at m
  simp only [value,ZT.toZ] at m
  simp only [value] at p q ⊢
  ipra_simps
  linear_combination p-q+(𝔞(N)+1)*m

theorem zero_sum (d : Bool) (x D : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (⟨sum d true zero zero x D,sum d false zero zero x D⟩ : ZT n) (ZT.natLit 0) := by
  have p := natEq (sum_zero (Γ := Γ) (body d true) (data zero x D))
  have q := natEq (sum_zero (Γ := Γ) (body d false) (data zero x D))
  apply ZT.derive
  rw [ZT.toZ_natLit]
  simp only [ZT.toZ,sum]
  linear_combination p-q

theorem logarithm_zero (x D : PTm n) : Γ ⊢[PRAAx] ZT.eq (logarithm x D zero) (ZT.natLit 0) := zero_sum false x D
theorem derivative_zero (x D : PTm n) : Γ ⊢[PRAAx] ZT.eq (derivative x D zero) (ZT.natLit 0) := zero_sum true x D

/-- Exact original logarithmic coefficient `(-1)^k/(k+1)`, with both
the common polynomial denominator and the input denominator cleared. -/
theorem logarithmic_coefficient (N k D : PTm n) (hk : Γ ⊢[PRAAx] lt k N) : Γ ⊢[PRAAx]
    ZT.eq (ZT.ofNat (succ k*pw D (succ k)*coefficient false N k D)*kernel k)
      (ZT.ofNat (FiniteExponential.denominator D N)*
        (⟨LogarithmExponentialCoefficients.evenBit k,LogarithmExponentialCoefficients.oddBit k⟩ : ZT n)) := by
  ipra_lc [coefficient, Bool.false_eq_true, if_false] 𝔞(pw D (succ k))*𝔞(scalar N (succ k) D)*ZT.toZ_eq (LogarithmExponentialCoefficients.logarithmic_coefficient (Γ := Γ) k)+ ZT.toZ Γ (⟨LogarithmExponentialCoefficients.evenBit k,LogarithmExponentialCoefficients.oddBit k⟩ : ZT n)*natEq (FiniteExponential.coefficient_clearing (Γ := Γ) N (succ k) D hk)

theorem denominator_recurrence (D N : PTm n) : Γ ⊢[PRAAx]
    FiniteExponential.denominator D (succ N) ≐ (succ N*D)*FiniteExponential.denominator D N := by
  have f := natEq (fact_succ (Γ := Γ) N zero)
  have p := natEq (pw_succ (Γ := Γ) D N)
  apply deriveNat
  unfold FiniteExponential.denominator
  ipra_simps
  rw [f,p]; ring

def differentialFormula (x D N : PTm n) : Fm PTm n :=
  ZT.eq ((ZT.ofNat D+value x)*derivative x D N+kernel N*power x N)
    (ZT.ofNat (FiniteExponential.denominator D N))

@[simp] theorem subst_differentialFormula {m : ℕ} (σ : Fin n → PTm m) (x D N : PTm n) :
    (differentialFormula x D N).subst σ =
      differentialFormula (Syn.subst σ x) (Syn.subst σ D) (Syn.subst σ N) := by simp [differentialFormula]

/-- Exact finite geometric derivative identity `(D+x) H'_N = N!D^N−g_N x^N`.
The correction is the actual next logarithmic derivative coefficient. -/
theorem differential_residual (x D N : PTm n) : Γ ⊢[PRAAx] differentialFormula x D N := by
  have all : Γ ⊢[PRAAx] .all (differentialFormula (Syn.shift x) (Syn.shift D) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_differentialFormula,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      have d := ZT.toZ_eq (derivative_zero (Γ := Γ) x D)
      have p := ZT.toZ_eq (power_zero (Γ := Γ) x)
      have k := (eval_value_congr (kernel_zero (Γ := Γ) (n := n))).trans (eval_value_code (Γ := Γ) (ZT.natLit 1))
      have f := natEq (fact_zero (Γ := Γ) (zero : PTm n))
      have z := natEq (pw_zero (Γ := Γ) D)
      apply ZT.derive
      simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
      simp only [FiniteExponential.denominator,Q.mk_mul,map_mul]
      change ZT.toZ Γ (kernel zero) = ZT.toZ Γ (ZT.natLit 1) at k
      simp only [ZT.toZ_natLit] at d p k
      change 𝔞(fact zero) = 1 at f
      change 𝔞(pw D zero) = 1 at z
      rw [d,p,k,f,z]; ring
    · simp only [subst_differentialFormula,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let Δ : List (Fm PTm (n+1)) :=
        differentialFormula (Syn.shift x) (Syn.shift D) (var 0) :: Γ.map Fm.shift
      change Δ ⊢[PRAAx] differentialFormula (Syn.shift x) (Syn.shift D) (succ (var 0))
      have ih := ZT.toZ_eq (Γ := Δ) (Prf.hyp0 : Δ ⊢[PRAAx] differentialFormula (Syn.shift x) (Syn.shift D) (var 0))
      have d := ZT.toZ_eq (derivative_recurrence (Γ := Δ) (Syn.shift x) (Syn.shift D) (var 0))
      have k := ZT.toZ_eq (kernel_differential (Γ := Δ) (var 0))
      have p := ZT.toZ_eq (power_succ (Γ := Δ) (Syn.shift x) (var 0))
      have f := natEq (denominator_recurrence (Γ := Δ) (Syn.shift D) (var 0))
      apply ZT.derive
      simp only [differentialFormula,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_natLit] at ih d k p ⊢
      ipra_simps
      linear_combination (𝔞(Syn.shift D)+ZT.toZ Δ (value (Syn.shift x)))*d+
        (𝔞(var 0)+1)*𝔞(Syn.shift D)*ih+ZT.toZ Δ (power (Syn.shift x) (succ (var 0)))*k-
        (𝔞(var 0)+1)*ZT.toZ Δ (kernel (var 0))*p-f
  simpa only [subst_differentialFormula,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE N all

/-! ## Actual output metadata and closed source-linked identities -/

def program (x D N : PTm n) : PTm n :=
  pairT (code (logarithm x D N)) (pairT (code (derivative x D N)) (FiniteExponential.denominator D N))
def programF : PR 3 := PTm.toPR (program (var 0) (var 1) (var 2))

@[simp] theorem subst_program {m : ℕ} (σ : Fin n → PTm m) (x D N : PTm n) :
    Syn.subst σ (program x D N) = program (Syn.subst σ x) (Syn.subst σ D) (Syn.subst σ N) := by simp [program]

theorem program_at (x D N : PTm n) :
    Γ ⊢[PRAAx] ap3 programF x D N ≐ program x D N := by
  simpa [programF,ap3] using toPR_eq (Γ := Γ) (program (var 0) (var 1) (var 2) : PTm 3) ![x,D,N]

theorem logarithmic_coefficient_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (lt (var 1) (var 0) ⟶
        ZT.eq (ZT.ofNat (succ (var 1)*pw (var 2) (succ (var 1))*coefficient false (var 0) (var 1) (var 2))*kernel (var 1))
          (ZT.ofNat (FiniteExponential.denominator (var 2) (var 0))*
            (⟨LogarithmExponentialCoefficients.evenBit (var 1),LogarithmExponentialCoefficients.oddBit (var 1)⟩ : ZT 3))) :=
  closeUniv 3 (.impI (logarithmic_coefficient _ _ _ Prf.hyp0))

theorem logarithmic_recurrences_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ZT.eq (logarithm (var 0) (var 1) (succ (var 2)))
        (ZT.ofNat (succ (var 2)*var 1)*logarithm (var 0) (var 1) (var 2)+kernel (var 2)*power (var 0) (succ (var 2))) ⋏
       ZT.eq (derivative (var 0) (var 1) (succ (var 2)))
        (ZT.ofNat (succ (var 2)*var 1)*derivative (var 0) (var 1) (var 2)+ZT.ofNat (succ (var 2))*kernel (var 2)*power (var 0) (var 2))) :=
  closeUniv 3 (.andI (logarithm_recurrence _ _ _) (derivative_recurrence _ _ _))

theorem logarithmic_differential_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (differentialFormula (var 0) (var 1) (var 2)) :=
  closeUniv 3 (differential_residual _ _ _)

theorem logarithmic_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((ap3 programF (var 0) (var 1) (var 2) ≐ program (var 0) (var 1) (var 2)) ⋏
        ((fstT (program (var 0) (var 1) (var 2)) ≐ code (logarithm (var 0) (var 1) (var 2))) ⋏
          ((fstT (sndT (program (var 0) (var 1) (var 2))) ≐ code (derivative (var 0) (var 1) (var 2))) ⋏
            ((sndT (sndT (program (var 0) (var 1) (var 2))) ≐ FiniteExponential.denominator (var 1) (var 2)) ⋏
              (le one (var 1) ⟶ le one (FiniteExponential.denominator (var 1) (var 2))))))) :=
  closeUniv 3 (.andI (program_at _ _ _) (.andI (fst_pair _ _)
    (.andI ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
      (.andI ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
        (.impI (FiniteExponential.denominator_positive _ _ Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.FiniteLogarithm
