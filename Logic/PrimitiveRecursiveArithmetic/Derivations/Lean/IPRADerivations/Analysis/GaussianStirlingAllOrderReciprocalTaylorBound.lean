import IPRADerivations.Analysis.GaussianStirlingAllOrderReciprocalTaylor
import IPRADerivations.Analysis.GaussianStirlingAllOrderCentralTaylorBound

/-!
# Explicit integer bounds for the cleared reciprocal-power defect

All monomials left after the fourth-order factor have degree 2e-2.
The unscaled step is at most the central denominator, so their
absolute coefficient sums give a certified internal signed bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderReciprocalTaylorBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderReciprocalTaylor
  (outerFourth innerFourth secondCoefficient clearedDefect exact_fourth_order)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Finset Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def mass (e : ℕ) : ℕ := ∑ k ∈ range (e+1), e.choose k
def size (e : ℕ) : ℕ := 2*mass e+2*mass e+secondCoefficient e*(e+mass e)
def width (e : ℕ) : ℕ := 2*e-2

private theorem power_nonnegative (u : PTm n) (a : ℕ) : Nonneg Γ ((𝔞 u)^a) := by
  simpa only [AnalyticNumberTheory.RobinThreePos.pw_lit] using nn_term (Γ := Γ) (pw u (num a))

private theorem monomial_slack (x h : PTm n) (a b c : ℕ) (e : a+b=c) (hh : Γ ⊢[PRAAx] le h x) :
    Nonneg Γ ((𝔞 x)^c-(𝔞 x)^a*(𝔞 h)^b) := by
  have e' : Γ ⊢[PRAAx] pw x (num a)*pw x (num b) ≐ pw x (num c) := by
    refine (pw_add x _ _).eqSymm.eqTrans (congrAp2 powF ?_ (.eqRefl x))
    apply deriveNat
    ipra_simps
    simpa only [Nat.cast_add] using congrArg (fun t : ℕ => (t : Groth (IPRA.Q Γ))) e
  have hh' := le_congr (.eqRefl _) e' (le_mul_mono (le_refl (pw x (num a))) (pw_le_pw (num b) hh))
  simpa only [sl_def,IPRA.Q.mk_mul,map_mul,AnalyticNumberTheory.RobinThreePos.pw_lit] using nn_sl hh'

private theorem outer_estimate (e : ℕ) (x h : PTm n) (hh : Γ ⊢[PRAAx] le h x) :
    Nonneg Γ (((2*mass e : ℕ):Groth (IPRA.Q Γ))*(𝔞 x)^(width e) -
      (𝔞 x)*(𝔞 x)*(𝔞 x)^e*outerFourth e (𝔞 x) (𝔞 h)) ∧
    Nonneg Γ ((𝔞 x)*(𝔞 x)*(𝔞 x)^e*outerFourth e (𝔞 x) (𝔞 h)) := by
  let R := (𝔞 x)^(width e)
  let X := (𝔞 x)*(𝔞 x)*(𝔞 x)^e
  let term (k : ℕ) : Groth (IPRA.Q Γ) :=
    if 4≤k ∧ Even k then ((2*e.choose k : ℕ):Groth (IPRA.Q Γ))*(𝔞 x)^(e-k)*(𝔞 h)^(k-4) else 0
  have nn (k : ℕ) :
      Nonneg Γ (((2*e.choose k : ℕ):Groth (IPRA.Q Γ))*R-X*term k) ∧ Nonneg Γ (X*term k) := by
    by_cases hk : 4≤k ∧ Even k
    · have xpos := nn_mul (nn_mul (nn_term (Γ := Γ) x) (nn_term x)) (power_nonnegative x e)
      have b := nn_mul (nn_mul (nn_natCast (Γ := Γ) (2*e.choose k)) (power_nonnegative x (e-k)))
        (power_nonnegative h (k-4))
      have positive : Nonneg Γ (X*term k) := by simpa only [term,if_pos hk,X] using nn_mul xpos b
      by_cases hke : k≤e
      · have d : (e+2+(e-k))+(k-4)=width e := by unfold width; omega
        have r := nn_mul (nn_natCast (Γ := Γ) (2*e.choose k)) (monomial_slack x h _ _ _ d hh)
        refine ⟨?_,positive⟩
        convert r using 1
        simp only [term,if_pos hk,R,X,pow_add]
        ring
      · have hz : e.choose k=0 := Nat.choose_eq_zero_of_lt (by omega)
        refine ⟨?_,positive⟩
        simp [term,hz,nn_zero]
    · refine ⟨?_,?_⟩
      · simpa only [term,if_neg hk,MulZeroClass.mul_zero,_root_.sub_zero,R] using
          nn_mul (nn_natCast (Γ := Γ) (2*e.choose k)) (power_nonnegative x (width e))
      · simpa only [term,if_neg hk,MulZeroClass.mul_zero] using (nn_zero (Γ := Γ))
  constructor
  · unfold mass outerFourth
    push_cast
    simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
    exact nn_sum _ _ (fun k _ => by simpa [R,X,term,Nat.cast_mul] using (nn k).1)
  · unfold outerFourth
    rw [Finset.mul_sum]
    exact nn_sum _ _ (fun k _ => (nn k).2)

private theorem inner_estimate (e α β : ℕ) (x h : PTm n) (hαβ : α+β=2)
    (hh : Γ ⊢[PRAAx] le h x) :
    let X := (𝔞 x)^α*(𝔞 h)^β
    let T := innerFourth e (𝔞 x) (𝔞 h)
    let R := (𝔞 x)^(width e)
    Nonneg Γ ((mass e : Groth (IPRA.Q Γ))*R-X*T) ∧ Nonneg Γ ((mass e : Groth (IPRA.Q Γ))*R+X*T) := by
  let X := (𝔞 x)^α*(𝔞 h)^β
  let R := (𝔞 x)^(width e)
  let term (k : ℕ) : Groth (IPRA.Q Γ) :=
    if 2≤k then (e.choose k : Groth (IPRA.Q Γ))*((𝔞 x)*(𝔞 x))^(e-k)*(-1)^k*((𝔞 h)*(𝔞 h))^(k-2) else 0
  have nn (k : ℕ) :
      Nonneg Γ ((e.choose k : Groth (IPRA.Q Γ))*R-X*term k) ∧
      Nonneg Γ ((e.choose k : Groth (IPRA.Q Γ))*R+X*term k) := by
    by_cases hk : 2≤k ∧ k≤e
    · let a := α+2*(e-k)
      let b := β+2*(k-2)
      have d : a+b=width e := by unfold a b width; omega
      have low := nn_mul (nn_natCast (Γ := Γ) (e.choose k)) (monomial_slack x h a b _ d hh)
      have high := nn_mul (nn_natCast (Γ := Γ) (e.choose k))
        (nn_add (power_nonnegative x (width e)) (nn_mul (power_nonnegative x a) (power_nonnegative h b)))
      have et : X*term k =
          (e.choose k : Groth (IPRA.Q Γ))*(-1)^k*(𝔞 x)^a*(𝔞 h)^b := by
        dsimp only [term,X,a,b]
        rw [if_pos hk.1,pow_add,pow_add,pow_mul,pow_mul]
        simp only [pow_two]
        ring
      rw [et]
      rcases Nat.even_or_odd k with ev | od
      · rw [ev.neg_one_pow]
        constructor
        · convert low using 1
          unfold R
          ring
        · convert high using 1
          unfold R
          ring
      · rw [od.neg_one_pow]
        constructor
        · convert high using 1
          unfold R
          ring
        · convert low using 1
          unfold R
          ring
    · have z : term k=0 := by
        unfold term
        by_cases h₂ : 2≤k
        · have hz : e.choose k=0 := Nat.choose_eq_zero_of_lt (by omega)
          simp [h₂,hz]
        · simp [h₂]
      simp only [z,MulZeroClass.mul_zero,_root_.sub_zero,_root_.add_zero]
      have m := nn_mul (nn_natCast (Γ := Γ) (e.choose k)) (power_nonnegative x (width e))
      exact ⟨m,m⟩
  change Nonneg Γ ((mass e : Groth (IPRA.Q Γ))*R-X*innerFourth e (𝔞 x) (𝔞 h)) ∧
    Nonneg Γ ((mass e : Groth (IPRA.Q Γ))*R+X*innerFourth e (𝔞 x) (𝔞 h))
  unfold mass innerFourth
  push_cast
  simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  exact ⟨nn_sum _ _ (fun k _ => (nn k).1),nn_sum _ _ (fun k _ => (nn k).2)⟩

def integerDefect (e : ℕ) (x h : PTm n) : ZT n :=
  ZT.ofNat (x*x*pw x (num e)*(pw (x+h) (num e)+pw (monus x h) (num e))) -
    ZT.ofNat ((two*(x*x)+num (secondCoefficient e)*(h*h))*pw ((x+h)*monus x h) (num e))

def integerBound (e : ℕ) (x h : PTm n) : PTm n := num (size e)*pw h (num 4)*pw x (num (width e))

theorem integer_defect_at (e : ℕ) (x h : PTm n) (hh : Γ ⊢[PRAAx] le h x) :
    ZT.toZ Γ (integerDefect e x h) = clearedDefect e (𝔞 x) (𝔞 h) := by
  have hx := natEq (eq_add_of_le hh)
  ipra_simps
  have ex : 𝔞(monus x h) = 𝔞 x-𝔞 h := by linear_combination -hx
  have powEq : ((𝔞 x+𝔞 h)*(𝔞 x-𝔞 h))^e = ((𝔞 x)*(𝔞 x)-(𝔞 h)*(𝔞 h))^e := by
    congr 1
    ring
  dsimp only [integerDefect,clearedDefect]
  ipra_simps
  simp only [AnalyticNumberTheory.RobinThreePos.pw_lit]
  ipra_simps
  rw [ex,powEq]
  ring

theorem integer_error (e : ℕ) (he : 2≤e) (x h : PTm n) (hh : Γ ⊢[PRAAx] le h x) :
    (Γ ⊢[PRAAx] zle (integerDefect e x h) (ZT.ofNat (integerBound e x h))) ∧
      (Γ ⊢[PRAAx] zle (-ZT.ofNat (integerBound e x h)) (integerDefect e x h)) := by
  let X := 𝔞 x
  let H := 𝔞 h
  let O := X*X*X^e*outerFourth e X H
  let T := innerFourth e X H
  let R := X^(width e)
  let K : Groth (IPRA.Q Γ) := (secondCoefficient e : ℕ)
  let C : Groth (IPRA.Q Γ) := (mass e : ℕ)
  let V := (size e : Groth (IPRA.Q Γ))*R
  let E := O-2*(X*X*T)+K*((e : Groth (IPRA.Q Γ))*R-H*H*T)
  have hO₀ := (outer_estimate e x h hh).1
  have hO₁ := (outer_estimate e x h hh).2
  have xi := inner_estimate e 2 0 x h (by decide) hh
  have hi := inner_estimate e 0 2 x h (by decide) hh
  have x0 : Nonneg Γ (C*R-X*X*T) := by simpa only [X,H,T,C,R,pow_zero,_root_.mul_one,pow_two] using xi.1
  have x1 : Nonneg Γ (C*R+X*X*T) := by simpa only [X,H,T,C,R,pow_zero,_root_.mul_one,pow_two] using xi.2
  have h0 : Nonneg Γ (C*R-H*H*T) := by simpa only [X,H,T,C,R,pow_zero,_root_.one_mul,pow_two] using hi.1
  have h1 : Nonneg Γ (C*R+H*H*T) := by simpa only [X,H,T,C,R,pow_zero,_root_.one_mul,pow_two] using hi.2
  have hK : Nonneg Γ K := nn_natCast _
  have h2 : Nonneg Γ (2:Groth (IPRA.Q Γ)) := by exact nn_natCast 2
  have hR := power_nonnegative (Γ := Γ) x (width e)
  have up : Nonneg Γ (V-E) := by
    have j := nn_add hO₀ (nn_add (nn_mul h2 x1) (nn_mul hK h1))
    convert j using 1
    unfold V E size C K O T R
    push_cast
    ring
  have lows : Nonneg Γ (V+E) := by
    have j := nn_add (nn_mul (nn_natCast (Γ := Γ) (2*mass e)) hR) (nn_add hO₁ (nn_add
      (nn_mul h2 x0) (nn_mul hK (nn_add h0 (nn_mul (nn_natCast (Γ := Γ) (2*e)) hR)))))
    convert j using 1
    unfold V E size C K O T R
    push_cast
    ring
  have he' : clearedDefect e X H = H^4*E := by
    rw [exact_fourth_order e he]
    have ep : (X*X)^(e-1)=R := by
      unfold R width
      rw [show X*X = X^2 by ring,←pow_mul,show 2*(e-1)=2*e-2 by omega]
    rw [ep]
    unfold E O T K
    ring
  constructor
  · apply zle_of_comb (H^4*(V-E))
    · rw [integer_defect_at e x h hh]
      change _ - clearedDefect e X H = H^4*(V-E)
      rw [he']
      simp only [integerBound,ZT.toZ_ofNat]
      ipra_simps
      simp only [AnalyticNumberTheory.RobinThreePos.pw_lit]
      unfold V R H X
      ring
    · exact nn_mul (power_nonnegative h 4) up
  · apply zle_of_comb (H^4*(V+E))
    · rw [integer_defect_at e x h hh]
      change clearedDefect e X H - _ = H^4*(V+E)
      rw [he']
      simp only [integerBound,ZT.toZ_neg,ZT.toZ_ofNat]
      ipra_simps
      simp only [AnalyticNumberTheory.RobinThreePos.pw_lit]
      unfold V R H X
      ring
    · exact nn_mul (power_nonnegative h 4) lows

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderReciprocalTaylorBound
