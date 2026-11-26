import IPRADerivations.Analysis.Exponential.Polynomials.LogarithmExponentialCoefficients
import IPRADerivations.Core.LinearCombination

/-!
# Literal finite exponential polynomials and their differential residual

Finite algebra for Gamma (C4). `exponential x D N` is the actually evaluated
polynomial `N! D^N ∑_{k≤N} (x/D)^k/k!`. Its coefficients are computed from
binomial coefficients and factorials, and their exact denominator-clearing
identity is derived. `derivative` evaluates the literal termwise formal
derivative, independently of `exponential`.

All cutoffs and signed input coordinates are internal. The exact polynomial
identity `D E'_N = E_N - x^N` is proved from the two literal sums. No recurrence
or derivative identity is a premise. The coefficient/Bell identification,
complex evaluation, analytic tails and the completed C4 name identity remain
separate obligations.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.FiniteExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.LogarithmExponentialCoefficients (value code eval_value_code eval_value_congr monus_succ_le)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.Combinatorics.Binomial (binom pos_mul quo_of_eq)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Actual signed powers -/

def powerStep : PTm 3 := code (value (var 1)*value (var 2))
def powerF : PR 2 := rec2 (pairT one zero) powerStep
def powerCode (x k : PTm n) : PTm n := ap2 powerF k x
def power (x k : PTm n) : ZT n := value (powerCode x k)

@[simp] theorem subst_powerCode {m : ℕ} (σ : Fin n → PTm m) (x k : PTm n) :
    Syn.subst σ (powerCode x k) = powerCode (Syn.subst σ x) (Syn.subst σ k) := by simp [powerCode]
@[simp] theorem subst_power {m : ℕ} (σ : Fin n → PTm m) (x k : PTm n) :
    (power x k).subst σ = power (Syn.subst σ x) (Syn.subst σ k) := by simp [power]

theorem powerCode_zero (x : PTm n) : Γ ⊢[PRAAx] powerCode x zero ≐ pairT one zero := by
  simpa [powerCode,powerF] using rec2_zero (Γ := Γ) (pairT one zero) powerStep x

theorem powerCode_succ (x k : PTm n) :
    Γ ⊢[PRAAx] powerCode x (succ k) ≐ code (power x k*value x) := by
  simpa [powerCode,powerF,powerStep,power] using rec2_succ (Γ := Γ) (pairT one zero) powerStep k x

theorem power_zero (x : PTm n) : Γ ⊢[PRAAx] ZT.eq (power x zero) (ZT.natLit 1) := by
  apply ZT.derive
  exact (eval_value_congr (powerCode_zero x)).trans (eval_value_code (ZT.natLit 1))

theorem power_succ (x k : PTm n) : Γ ⊢[PRAAx] ZT.eq (power x (succ k)) (power x k*value x) := by
  apply ZT.derive
  exact (eval_value_congr (powerCode_succ x k)).trans (eval_value_code _)

/-! ## The actual factorial quotient weight -/

/-- `N!/k!`, computed without a partial quotient. -/
def weight (N k : PTm n) : PTm n := binom N k*fact (monus N k)

@[simp] theorem subst_weight {m : ℕ} (σ : Fin n → PTm m) (N k : PTm n) :
    Syn.subst σ (weight N k) = weight (Syn.subst σ N) (Syn.subst σ k) := by simp [weight,fact,binom]

theorem weight_exact (N k : PTm n) (hk : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] fact k*weight N k ≐ fact N := by
  have e : Γ ⊢[PRAAx] fact k*weight N k ≐ (fact k*fact (monus N k))*binom N k := by unfold weight; ipra_ring
  exact e.eqTrans (binom_eq hk).eqSymm

theorem weight_self (N : PTm n) : Γ ⊢[PRAAx] weight N N ≐ one := by
  refine mul_cancel (fact_pos N) ?_
  exact (weight_exact N N (le_refl N)).eqTrans (by ipra_ring)

theorem weight_step (N k : PTm n) (hk : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] weight (succ N) k ≐ succ N*weight N k := by
  refine mul_cancel (fact_pos k) ?_
  ipra_lc natEq (weight_exact (succ N) k (le_trans hk (le_succ_self N)))+natEq (fact_succ (Γ := Γ) N zero)-
    (𝔞(N)+1)*natEq (weight_exact N k hk)

theorem weight_quotient (N k : PTm n) (hk : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] quo (fact N) (fact k) ≐ weight N k :=
  quo_of_eq (fact_pos k) (weight_exact N k hk).eqSymm

/-! ## Literal value and termwise derivative sums -/

def scalar (N k D : PTm n) : PTm n := weight N k*pw D (monus N k)
def dscalar (N k D : PTm n) : PTm n := succ k*scalar N (succ k) D

@[simp] theorem subst_scalar {m : ℕ} (σ : Fin n → PTm m) (N k D : PTm n) :
    Syn.subst σ (scalar N k D) = scalar (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ D) := by simp [scalar]
@[simp] theorem subst_dscalar {m : ℕ} (σ : Fin n → PTm m) (N k D : PTm n) :
    Syn.subst σ (dscalar N k D) = dscalar (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ D) := by simp [dscalar]

/-- Packed persistent data: `(N,(x,D))`. -/
def pBody : PTm 2 := scalar (fstT (var 1)) (var 0) (sndT (sndT (var 1)))*
  (power (fstT (sndT (var 1))) (var 0)).pos
def mBody : PTm 2 := scalar (fstT (var 1)) (var 0) (sndT (sndT (var 1)))*
  (power (fstT (sndT (var 1))) (var 0)).neg
def dpBody : PTm 2 := dscalar (fstT (var 1)) (var 0) (sndT (sndT (var 1)))*
  (power (fstT (sndT (var 1))) (var 0)).pos
def dmBody : PTm 2 := dscalar (fstT (var 1)) (var 0) (sndT (sndT (var 1)))*
  (power (fstT (sndT (var 1))) (var 0)).neg
def data (N x D : PTm n) : PTm n := pairT N (pairT x D)
def sum (b : PTm 2) (r N x D : PTm n) : PTm n := ap2 (sumF b) r (data N x D)
def exponential (x D N : PTm n) : ZT n := ⟨sum pBody (succ N) N x D,sum mBody (succ N) N x D⟩
def derivative (x D N : PTm n) : ZT n := ⟨sum dpBody N N x D,sum dmBody N N x D⟩

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (N x D : PTm n) :
    Syn.subst σ (data N x D) = data (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ D) := by simp [data]
@[simp] theorem subst_sum {m : ℕ} (σ : Fin n → PTm m) (b : PTm 2) (r N x D : PTm n) :
    Syn.subst σ (sum b r N x D) = sum b (Syn.subst σ r) (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ D) := by simp [sum]
@[simp] theorem subst_exponential {m : ℕ} (σ : Fin n → PTm m) (x D N : PTm n) :
    (exponential x D N).subst σ = exponential (Syn.subst σ x) (Syn.subst σ D) (Syn.subst σ N) := by simp [exponential,ZT.subst]
@[simp] theorem subst_derivative {m : ℕ} (σ : Fin n → PTm m) (x D N : PTm n) :
    (derivative x D N).subst σ = derivative (Syn.subst σ x) (Syn.subst σ D) (Syn.subst σ N) := by simp [derivative,ZT.subst]

theorem scalar_self (N D : PTm n) : Γ ⊢[PRAAx] scalar N N D ≐ one :=
  (congrMul (weight_self N) ((congrAp2 powF (monus_self N) (.eqRefl D)).eqTrans (pw_zero D))).eqTrans (one_mul one)

theorem scalar_step (N k D : PTm n) (hk : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] scalar (succ N) k D ≐ (succ N*D)*scalar N k D := by
  have w := natEq (weight_step N k hk)
  have p := natEq ((congrAp2 powF (monus_succ_le hk) (.eqRefl D)).eqTrans (pw_succ D (monus N k)))
  apply deriveNat; unfold scalar; ipra_simps
  rw [w,p]; ring

theorem scalar_congr {N N' k k' D D' : PTm n}
    (hN : Γ ⊢[PRAAx] N ≐ N') (hk : Γ ⊢[PRAAx] k ≐ k') (hD : Γ ⊢[PRAAx] D ≐ D') :
    Γ ⊢[PRAAx] scalar N k D ≐ scalar N' k' D' := by
  have h := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (scalar (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![N,k,D]) (σ' := ![N',k',D']) (fun i => by fin_cases i <;> assumption)
  simpa using h

theorem body_at (k N x D : PTm n) :
    Γ ⊢[PRAAx] (inst2 pBody k (data N x D) ≐ scalar N k D*(power x k).pos) ⋏
      (inst2 mBody k (data N x D) ≐ scalar N k D*(power x k).neg) := by
  have hn : Γ ⊢[PRAAx] fstT (data N x D) ≐ N := fst_pair _ _
  have hx : Γ ⊢[PRAAx] fstT (sndT (data N x D)) ≐ x :=
    (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have hd : Γ ⊢[PRAAx] sndT (sndT (data N x D)) ≐ D :=
    (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  have p : inst2 pBody k (data N x D) =
      scalar (fstT (data N x D)) k (sndT (sndT (data N x D)))*
        (power (fstT (sndT (data N x D))) k).pos := by simp [inst2,pBody,power,value]
  have q : inst2 mBody k (data N x D) =
      scalar (fstT (data N x D)) k (sndT (sndT (data N x D)))*
        (power (fstT (sndT (data N x D))) k).neg := by simp [inst2,mBody,power,value]
  rw [p,q]
  exact .andI (congrMul (scalar_congr hn (.eqRefl _) hd) (congrFst (congrAp2 powerF (.eqRefl _) hx)))
    (congrMul (scalar_congr hn (.eqRefl _) hd) (congrSnd (congrAp2 powerF (.eqRefl _) hx)))

def component (positive : Bool) (a : ZT n) : PTm n := if positive then a.pos else a.neg
def body (differentiate positive : Bool) : PTm 2 :=
  if differentiate then (if positive then dpBody else dmBody) else (if positive then pBody else mBody)

theorem dbody_at (k N x D : PTm n) :
    Γ ⊢[PRAAx] (inst2 dpBody k (data N x D) ≐ dscalar N k D*(power x k).pos) ⋏
      (inst2 dmBody k (data N x D) ≐ dscalar N k D*(power x k).neg) := by
  have hn : Γ ⊢[PRAAx] fstT (data N x D) ≐ N := fst_pair _ _
  have hx : Γ ⊢[PRAAx] fstT (sndT (data N x D)) ≐ x :=
    (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have hd : Γ ⊢[PRAAx] sndT (sndT (data N x D)) ≐ D :=
    (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  have p : inst2 dpBody k (data N x D) =
      dscalar (fstT (data N x D)) k (sndT (sndT (data N x D)))*
        (power (fstT (sndT (data N x D))) k).pos := by simp [inst2,dpBody,power,value]
  have q : inst2 dmBody k (data N x D) =
      dscalar (fstT (data N x D)) k (sndT (sndT (data N x D)))*
        (power (fstT (sndT (data N x D))) k).neg := by simp [inst2,dmBody,power,value]
  rw [p,q]
  have ds : Γ ⊢[PRAAx] dscalar (fstT (data N x D)) k (sndT (sndT (data N x D))) ≐ dscalar N k D :=
    congrMul (.eqRefl _) (scalar_congr hn (.eqRefl _) hd)
  exact .andI (congrMul ds (congrFst (congrAp2 powerF (.eqRefl _) hx)))
    (congrMul ds (congrSnd (congrAp2 powerF (.eqRefl _) hx)))

theorem body_at_component (d p : Bool) (k N x D : PTm n) :
    Γ ⊢[PRAAx] inst2 (body d p) k (data N x D) ≐
      (if d then dscalar N k D else scalar N k D)*component p (power x k) := by
  cases d <;> cases p
  · exact Prf.andE₂ (body_at k N x D)
  · exact Prf.andE₁ (body_at k N x D)
  · exact Prf.andE₂ (dbody_at k N x D)
  · exact Prf.andE₁ (dbody_at k N x D)

theorem body_step (d p : Bool) (k N x D : PTm n)
    (hk : Γ ⊢[PRAAx] le (if d then succ k else k) N) :
    Γ ⊢[PRAAx] inst2 (body d p) k (data (succ N) x D) ≐
      (succ N*D)*inst2 (body d p) k (data N x D) := by
  have a := natEq (body_at_component (Γ := Γ) d p k (succ N) x D)
  have b := natEq (body_at_component (Γ := Γ) d p k N x D)
  cases d
  · have w := natEq (scalar_step N k D hk)
    apply deriveNat
    simp only [Bool.false_eq_true,if_false] at a b
    ipra_simps
    linear_combination a-(𝔞(N)+1)*𝔞(D)*b+𝔞(component p (power x k))*w
  · have w := natEq (scalar_step N (succ k) D hk)
    apply deriveNat
    simp only [if_true,dscalar,Q.mk_mul,map_mul,Q.mk_succ] at a b
    ipra_simps
    linear_combination a-(𝔞(N)+1)*𝔞(D)*b+(𝔞(k)+1)*𝔞(component p (power x k))*w

theorem prefix_step (d p : Bool) (N x D : PTm n) :
    Γ ⊢[PRAAx] sum (body d p) (if d then N else succ N) (succ N) x D ≐
      (succ N*D)*sum (body d p) (if d then N else succ N) N x D := by
  apply sum_scale
  refine .allI (.impI ?_)
  rw [show Syn.shift (data (succ N) x D) =
    data (succ (Syn.shift N)) (Syn.shift x) (Syn.shift D) by simp [Syn.shift]]
  rw [show Syn.shift (data N x D) = data (Syn.shift N) (Syn.shift x) (Syn.shift D) by simp [Syn.shift]]
  simp only [Syn.shift,PTm.subst_mul,ConciseIPRA.PTm.subst_succ]
  apply body_step
  cases d
  · exact (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  · exact Prf.hyp0

theorem endpoint (d p : Bool) (N x D : PTm n) :
    Γ ⊢[PRAAx] inst2 (body d p) (if d then N else succ N) (data (succ N) x D) ≐
      (if d then succ N else one)*component p (power x (if d then N else succ N)) := by
  have a := body_at_component (Γ := Γ) d p (if d then N else succ N) (succ N) x D
  cases d
  · exact a.eqTrans (congrMul (scalar_self (succ N) D) (.eqRefl _))
  · exact a.eqTrans (congrMul (congrMul (.eqRefl _) (scalar_self (succ N) D)) (.eqRefl _))
      |>.eqTrans (by simp only [if_true]; ipra_ring)

theorem component_recurrence (d p : Bool) (N x D : PTm n) :
    Γ ⊢[PRAAx] sum (body d p) (succ (if d then N else succ N)) (succ N) x D ≐
      (succ N*D)*sum (body d p) (if d then N else succ N) N x D +
        (if d then succ N else one)*component p (power x (if d then N else succ N)) :=
  (sum_succ' (body d p) _ (data (succ N) x D)).eqTrans
    (congrAdd (prefix_step d p N x D) (endpoint d p N x D))

theorem exponential_recurrence (x D N : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (exponential x D (succ N))
      (ZT.ofNat (succ N*D)*exponential x D N+power x (succ N)) := by
  have p := natEq (component_recurrence (Γ := Γ) false true N x D)
  have q := natEq (component_recurrence (Γ := Γ) false false N x D)
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [exponential,ZT.toZ]
  simp only [body,component,Bool.false_eq_true,if_false,if_true] at p q
  ipra_simps
  linear_combination p-q

theorem derivative_recurrence (x D N : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (derivative x D (succ N))
      (ZT.ofNat (succ N*D)*derivative x D N+ZT.ofNat (succ N)*power x N) := by
  have p := natEq (component_recurrence (Γ := Γ) true true N x D)
  have q := natEq (component_recurrence (Γ := Γ) true false N x D)
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [derivative,ZT.toZ]
  simp only [body,component,Bool.false_eq_true,if_false,if_true] at p q
  ipra_simps
  linear_combination p-q

theorem exponential_zero (x D : PTm n) : Γ ⊢[PRAAx] ZT.eq (exponential x D zero) (ZT.natLit 1) := by
  have p := natEq (sum_succ' (Γ := Γ) pBody zero (data zero x D))
  have q := natEq (sum_succ' (Γ := Γ) mBody zero (data zero x D))
  have zp := natEq (sum_zero (Γ := Γ) pBody (data zero x D))
  have zq := natEq (sum_zero (Γ := Γ) mBody (data zero x D))
  have ep := natEq (Prf.andE₁ (body_at (Γ := Γ) zero zero x D))
  have eq := natEq (Prf.andE₂ (body_at (Γ := Γ) zero zero x D))
  have w := natEq (scalar_self (Γ := Γ) zero D)
  have i := ZT.toZ_eq (power_zero (Γ := Γ) x)
  apply ZT.derive
  simp only [exponential,ZT.toZ_natLit,ZT.toZ,sum] at i ⊢
  ipra_simps
  rw [p,q,zp,zq,ep,eq,w]
  linear_combination i

theorem derivative_zero (x D : PTm n) : Γ ⊢[PRAAx] ZT.eq (derivative x D zero) (ZT.natLit 0) := by
  have p := natEq (sum_zero (Γ := Γ) dpBody (data zero x D))
  have q := natEq (sum_zero (Γ := Γ) dmBody (data zero x D))
  apply ZT.derive
  rw [ZT.toZ_natLit]
  simp only [derivative,ZT.toZ,sum]
  ipra_simps
  linear_combination p-q

def differentialFormula (x D N : PTm n) : Fm PTm n :=
  ZT.eq (ZT.ofNat D*derivative x D N+power x N) (exponential x D N)

@[simp] theorem subst_differentialFormula {m : ℕ} (σ : Fin n → PTm m) (x D N : PTm n) :
    (differentialFormula x D N).subst σ =
      differentialFormula (Syn.subst σ x) (Syn.subst σ D) (Syn.subst σ N) := by
  simp [differentialFormula]

/-- The literal finite exponential's derivative differs from itself by
exactly its last homogeneous term. This holds even at the totalized `D=0`. -/
theorem differential_residual (x D N : PTm n) : Γ ⊢[PRAAx] differentialFormula x D N := by
  have all : Γ ⊢[PRAAx] .all (differentialFormula (Syn.shift x) (Syn.shift D) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_differentialFormula,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      have a := ZT.toZ_eq (exponential_zero (Γ := Γ) x D)
      have b := ZT.toZ_eq (derivative_zero (Γ := Γ) x D)
      have c := ZT.toZ_eq (power_zero (Γ := Γ) x)
      apply ZT.derive
      simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
      simp only [ZT.toZ_natLit] at a b c
      linear_combination 𝔞(D)*b+c-a
    · simp only [subst_differentialFormula,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let Δ : List (Fm PTm (n+1)) :=
        differentialFormula (Syn.shift x) (Syn.shift D) (var 0) :: Γ.map Fm.shift
      change Δ ⊢[PRAAx] differentialFormula (Syn.shift x) (Syn.shift D) (succ (var 0))
      have ih := ZT.toZ_eq (Γ := Δ) (Prf.hyp0 : Δ ⊢[PRAAx] differentialFormula (Syn.shift x) (Syn.shift D) (var 0))
      have a := ZT.toZ_eq (exponential_recurrence (Γ := Δ) (Syn.shift x) (Syn.shift D) (var 0))
      have b := ZT.toZ_eq (derivative_recurrence (Γ := Δ) (Syn.shift x) (Syn.shift D) (var 0))
      apply ZT.derive
      simp only [differentialFormula,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat] at ih a b ⊢
      ipra_simps
      linear_combination 𝔞(Syn.shift D)*b-a+(𝔞(var 0)+1)*𝔞(Syn.shift D)*ih
  simpa only [subst_differentialFormula,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE N all

/-! ## Exact rational term interpretation and executable certificate -/

def denominator (D N : PTm n) : PTm n := fact N*pw D N

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (D N : PTm n) :
    Syn.subst σ (denominator D N) = denominator (Syn.subst σ D) (Syn.subst σ N) := by simp [denominator,fact]

/-- Each actual summand, divided by `N!D^N`, has exactly coefficient
`1/(k!D^k)`. This is the literal exponential finite sum, not a definition
through a differential recurrence. -/
theorem coefficient_clearing (N k D : PTm n) (hk : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] (fact k*pw D k)*scalar N k D ≐ denominator D N := by
  have w := natEq (weight_exact N k hk)
  have p := natEq ((congrAp2 powF (eq_add_of_le hk) (.eqRefl D)).eqTrans
    (pw_add D k (monus N k)))
  apply deriveNat
  unfold scalar denominator
  ipra_simps
  linear_combination 𝔞(pw D k)*𝔞(pw D (monus N k))*w-𝔞(fact N)*p

theorem denominator_positive (D N : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le one (denominator D N) := by
  have d : Γ ⊢[PRAAx] D ≐ succ (pred D) :=
    LeanProofs.IPRA.AnalyticNumberTheory.Primes.eq_succ_pred ((eq_add_of_le hD).eqTrans (by ipra_ring))
  have p := pos_mul (fact_pos N) (LeanProofs.IPRA.AnalyticNumberTheory.Valuation.pw_pos' d N)
  change Γ ⊢[PRAAx] denominator D N ≐ succ (pred (denominator D N)) at p
  exact le_of_eq_add (d := pred (denominator D N)) (p.eqTrans (by ipra_ring))

/-- Actual output: `(signed numerator,(signed formal derivative,positive denominator))`. -/
def program (x D N : PTm n) : PTm n :=
  pairT (code (exponential x D N)) (pairT (code (derivative x D N)) (denominator D N))
def programF : PR 3 := PTm.toPR (program (var 0) (var 1) (var 2))

@[simp] theorem subst_program {m : ℕ} (σ : Fin n → PTm m) (x D N : PTm n) :
    Syn.subst σ (program x D N) = program (Syn.subst σ x) (Syn.subst σ D) (Syn.subst σ N) := by simp [program]

theorem program_at (x D N : PTm n) :
    Γ ⊢[PRAAx] ap3 programF x D N ≐ program x D N := by
  simpa [programF,ap3] using toPR_eq (Γ := Γ) (program (var 0) (var 1) (var 2) : PTm 3) ![x,D,N]

theorem power_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (ZT.eq (power (var 0) zero) (ZT.natLit 1) ⋏
        ZT.eq (power (var 0) (succ (var 1))) (power (var 0) (var 1)*value (var 0))) :=
  closeUniv 2 (.andI (power_zero _) (power_succ _ _))

theorem literal_coefficient_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le (var 1) (var 0) ⟶
        ((fact (var 1)*weight (var 0) (var 1) ≐ fact (var 0)) ⋏
          ((quo (fact (var 0)) (fact (var 1)) ≐ weight (var 0) (var 1)) ⋏
            ((fact (var 1)*pw (var 2) (var 1))*scalar (var 0) (var 1) (var 2) ≐ denominator (var 2) (var 0))))) :=
  closeUniv 3 (.impI (.andI (weight_exact _ _ Prf.hyp0)
    (.andI (weight_quotient _ _ Prf.hyp0) (coefficient_clearing _ _ _ Prf.hyp0))))

theorem literal_recurrences_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ZT.eq (exponential (var 0) (var 1) (succ (var 2)))
        (ZT.ofNat (succ (var 2)*var 1)*exponential (var 0) (var 1) (var 2)+power (var 0) (succ (var 2))) ⋏
      ZT.eq (derivative (var 0) (var 1) (succ (var 2)))
        (ZT.ofNat (succ (var 2)*var 1)*derivative (var 0) (var 1) (var 2)+ZT.ofNat (succ (var 2))*power (var 0) (var 2))) :=
  closeUniv 3 (.andI (exponential_recurrence _ _ _) (derivative_recurrence _ _ _))

theorem literal_differential_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (differentialFormula (var 0) (var 1) (var 2)) :=
  closeUniv 3 (differential_residual _ _ _)

theorem literal_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((ap3 programF (var 0) (var 1) (var 2) ≐ program (var 0) (var 1) (var 2)) ⋏
        ((fstT (program (var 0) (var 1) (var 2)) ≐ code (exponential (var 0) (var 1) (var 2))) ⋏
          ((fstT (sndT (program (var 0) (var 1) (var 2))) ≐ code (derivative (var 0) (var 1) (var 2))) ⋏
            ((sndT (sndT (program (var 0) (var 1) (var 2))) ≐ denominator (var 1) (var 2)) ⋏
              (le one (var 1) ⟶ le one (denominator (var 1) (var 2))))))) :=
  closeUniv 3 (.andI (program_at _ _ _) (.andI (fst_pair _ _)
    (.andI ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
      (.andI ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
        (.impI (denominator_positive _ _ Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.FiniteExponential
