import IPRADerivations.Probability.Expectation
import IPRADerivations.Analysis.WeightedAMGM
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.Core.ProdLemmas
import IPRADerivations.DiophantineNumberTheory.SuperellipticFamily
import IPRADerivations.Geometry.HypercubeSplit
import IPRADerivations.Core.CertificateTactics

/-!
# Finite Hölder and Lyapunov inequalities with rational exponents

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/06_inequalities.tex`, `thm:holder` ("Finite
Hölder with effective rational exponents") and `cor:lyapunov`. The packet states the finite object-language core:
"rational upper bounds `A, B > 0` satisfying `A^p ≥ E|X|^p` and `B^q ≥ E|Y|^q` … imply `E|XY| ≤ AB`". Its proof
runs through Young's inequality, and "for fixed integer powers it can instead be reduced to a polynomial
factorization after clearing denominators".

Every rational conjugate pair is `p = k/i`, `q = k/j` with `i + j = k` (`1/p + 1/q = 1`). Write `U = X^i` and
`V = Y^j` for natural values `X, Y`, so `U^p = X^k` and `V^q = Y^k`. In the cleared form with a finite weighted law
(weights `w`, total `W`, `Ew(Z) = Σ_m w_m Z_m`), for every fixed `i = a + 1 ≥ 1` and `j = b ≥ 0`:

* `young`: `k X^i Y^j ≤ i X^k + j Y^k`, from the weighted AM–GM inequality `WeightedAMGM.mult_convex`;
* `young_pt`: the same inequality at `X β`, `Y α`, multiplied by the weight;
* `lin3_le`: a reusable weighted-sum lemma: `c₀ f_m ≤ c₁ g_m + c₂ h_m` for `m < N` gives
  `c₀ Σ f ≤ c₁ Σ g + c₂ Σ h` with constants `c₀, c₁, c₂`;
* `holder` (`thm:holder`): if `Ew(X^k) ≤ α^k W` and `Ew(Y^k) ≤ β^k W` with `α, β > 0`, then
  `Ew(X^i Y^j) ≤ α^i β^j W`, i.e. `E[UV] ≤ A B` whenever `A^p ≥ E[U^p]` and `B^q ≥ E[V^q]` (`A = α^i`, `B = β^j`);
* `lyapunov` (`cor:lyapunov`): if `Ew(X^k) ≤ α^k W` with `α > 0`, then `Ew(X^i) ≤ α^i W` for every `i ≤ k`, i.e.
  every certified upper bound for `E[X^k]^{1/k}` bounds `E[X^i]^{1/i}`.

Exponents are fixed metatheoretic naturals, as in the packet ("fixed positive rational exponents"); each instance is
a separate iPRA theorem schema. The bounds `α, β` are arbitrary positive terms.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.FiniteHolder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' le_zero_of)
open LeanProofs.IPRA.Analysis.WeightedAMGM (mult_convex)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.DiophantineNumberTheory.Hurwitz (add_le_add)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Weighted sums of a linear inequality -/

/-- The invariant `c₀ Σ_{m<N} f ≤ c₁ Σ_{m<N} g + c₂ Σ_{m<N} h`. -/
abbrev LinF (f g h : PTm 2) (c₀ c₁ c₂ N x : PTm n) : Fm PTm n :=
  le (c₀ * ap2 (sumF f) N x) (c₁ * ap2 (sumF g) N x + c₂ * ap2 (sumF h) N x)

theorem lin_base (f g h : PTm 2) (c₀ c₁ c₂ x : PTm n) : Γ ⊢[PRAAx] LinF f g h c₀ c₁ c₂ zero x :=
  le_zero_of ((congrMul (.eqRefl _) (sum_zero f x)).eqTrans (mul_zero _))

theorem lin_step {f g h : PTm 2} {c₀ c₁ c₂ N x : PTm n}
    (hN : Γ ⊢[PRAAx] le (c₀ * inst2 f N x) (c₁ * inst2 g N x + c₂ * inst2 h N x))
    (ih : Γ ⊢[PRAAx] LinF f g h c₀ c₁ c₂ N x) : Γ ⊢[PRAAx] LinF f g h c₀ c₁ c₂ (succ N) x := by
  refine le_congr ?_ ?_ (add_le_add ih hN)
  · ipra_lc (-𝔞 c₀) * natEq (sum_succ' (Γ := Γ) f N x)
  · ipra_lc (-𝔞 c₁) * natEq (sum_succ' (Γ := Γ) g N x) - 𝔞 c₂ * natEq (sum_succ' (Γ := Γ) h N x)

/-- `c₀ f_m ≤ c₁ g_m + c₂ h_m` for `m < N` gives `c₀ Σ_{m<N} f ≤ c₁ Σ_{m<N} g + c₂ Σ_{m<N} h`. -/
theorem lin3_le {f g h : PTm 2} {c₀ c₁ c₂ N x : PTm n}
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift c₀ * inst2 f (var 0) (Syn.shift x))
        (Syn.shift c₁ * inst2 g (var 0) (Syn.shift x) + Syn.shift c₂ * inst2 h (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] LinF f g h c₀ c₁ c₂ N x := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      LinF f g h (Syn.shift c₀) (Syn.shift c₁) (Syn.shift c₂) (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (lin_base f g h c₀ c₁ c₂ x)
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (lin_step (Prf.impE hb.allOpen.wk.wk Prf.hyp0)
        (Prf.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have h := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact .impE h (le_refl N)

/-! ## Young's inequality for conjugate exponents `k/i`, `k/j` -/

/-- The exponent `i = a + 1`. -/
abbrev eI {m : ℕ} (a : ℕ) : PTm m := succ (num a)
/-- The exponent `j = b`. -/
abbrev eJ {m : ℕ} (b : ℕ) : PTm m := num b
/-- The exponent `k = i + j`. -/
abbrev eK {m : ℕ} (a b : ℕ) : PTm m := succ (num a + num b)

section Young

variable (a b : ℕ)

theorem pw_comm_exp (u e d : PTm n) : Γ ⊢[PRAAx] pw (pw u e) d ≐ pw (pw u d) e :=
  (pw_mul u e d).eqTrans ((congrAp2 powF (show Γ ⊢[PRAAx] e * d ≐ d * e by ipra_ring)
    (.eqRefl u)).eqTrans (pw_mul u d e).eqSymm)

/-- Young's inequality `k X^i Y^j ≤ i X^k + j Y^k`, `k = i + j`, `i ≥ 1`. -/
theorem young (u v : PTm n) :
    Γ ⊢[PRAAx] le (eK a b * (pw u (eI a) * pw v (eJ b))) (eI a * pw u (eK a b) + eJ b * pw v (eK a b)) := by
  refine mult_convex (a₀ := num a) (b := num b) ?_
  have e := (pw_mul_base (Γ := Γ) (pw u (eI a)) (pw v (eJ b)) (eK a b)).eqTrans
    (congrMul (pw_comm_exp u (eI a) (eK a b)) (pw_comm_exp v (eJ b) (eK a b)))
  exact le_congr (.eqRefl _) e (le_refl _)

/-- `k (β^i α^j) · w (X^i Y^j) ≤ i β^k · w X^k + j α^k · w Y^k`: Young at `X β`, `Y α`, weighted. -/
theorem young_pt (u v α β ω : PTm n) :
    Γ ⊢[PRAAx] le (eK a b * (pw β (eI a) * pw α (eJ b)) * (ω * (pw u (eI a) * pw v (eJ b))))
      (eI a * pw β (eK a b) * (ω * pw u (eK a b)) + eJ b * pw α (eK a b) * (ω * pw v (eK a b))) := by
  have y := le_mul_mono (le_refl ω) (young (Γ := Γ) a b (u * β) (v * α))
  have e1 := pw_mul_base (Γ := Γ) u β (eI a)
  have e2 := pw_mul_base (Γ := Γ) v α (eJ b)
  have e3 := pw_mul_base (Γ := Γ) u β (eK a b)
  have e4 := pw_mul_base (Γ := Γ) v α (eK a b)
  refine le_congr ((congrMul (.eqRefl ω) (congrMul (.eqRefl _) (congrMul e1 e2))).eqTrans ?_)
    ((congrMul (.eqRefl ω) (congrAdd (congrMul (.eqRefl _) e3) (congrMul (.eqRefl _) e4))).eqTrans ?_) y
  · ipra_ring
  · ipra_ring

end Young

/-! ## Hölder and Lyapunov -/

section Holder

variable (a b : ℕ) (w X Y : PTm 2)

/-- `thm:holder`: `Ew(X^k) ≤ α^k W` and `Ew(Y^k) ≤ β^k W` (`α, β > 0`) give `Ew(X^i Y^j) ≤ α^i β^j W`. -/
theorem holder {α β N x : PTm n} (hα : Γ ⊢[PRAAx] α ≐ succ (pred α)) (hβ : Γ ⊢[PRAAx] β ≐ succ (pred β))
    (hX : Γ ⊢[PRAAx] le (Ew w (pw X (eK a b)) N x) (pw α (eK a b) * Wt w N x))
    (hY : Γ ⊢[PRAAx] le (Ew w (pw Y (eK a b)) N x) (pw β (eK a b) * Wt w N x)) :
    Γ ⊢[PRAAx] le (Ew w (pw X (eI a) * pw Y (eJ b)) N x) (pw α (eI a) * pw β (eJ b) * Wt w N x) := by
  -- the weighted Young inequality summed over the outcomes
  have L : Γ ⊢[PRAAx] LinF (w * (pw X (eI a) * pw Y (eJ b))) (w * pw X (eK a b)) (w * pw Y (eK a b))
      (eK a b * (pw β (eI a) * pw α (eJ b))) (eI a * pw β (eK a b)) (eJ b * pw α (eK a b)) N x := by
    refine lin3_le (.allI (.impI ?_))
    have p := young_pt (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) a b (inst2 X (var 0) (Syn.shift x))
      (inst2 Y (var 0) (Syn.shift x)) (Syn.shift α) (Syn.shift β) (inst2 w (var 0) (Syn.shift x))
    simpa [Syn.shift, inst2] using p
  -- the moment bounds
  have R : Γ ⊢[PRAAx] le (eI a * pw β (eK a b) * Ew w (pw X (eK a b)) N x + eJ b * pw α (eK a b) * Ew w (pw Y (eK a b)) N x)
      (eI a * pw β (eK a b) * (pw α (eK a b) * Wt w N x) + eJ b * pw α (eK a b) * (pw β (eK a b) * Wt w N x)) :=
    add_le_add (le_mul_mono (le_refl _) hX) (le_mul_mono (le_refl _) hY)
  -- `α^k β^k = (β^i α^j)(α^i β^j)` and `k = i + j`
  have ek : Γ ⊢[PRAAx] (eK a b : PTm n) ≐ eI a + eJ b := by ipra_ring
  have qa : Γ ⊢[PRAAx] pw α (eK a b) ≐ pw α (eI a) * pw α (eJ b) :=
    (congrAp2 powF ek (.eqRefl α)).eqTrans (pw_add α (eI a) (eJ b))
  have qb : Γ ⊢[PRAAx] pw β (eK a b) ≐ pw β (eI a) * pw β (eJ b) :=
    (congrAp2 powF ek (.eqRefl β)).eqTrans (pw_add β (eI a) (eJ b))
  have T := le_trans L R
  have hc : Γ ⊢[PRAAx] eK a b * (pw β (eI a) * pw α (eJ b)) ≐ succ (pred (eK a b * (pw β (eI a) * pw α (eJ b)))) :=
    pos_mul' (AnalyticNumberTheory.Primes.eq_succ_pred (.eqRefl _)) (pos_mul' (pw_pos' hβ _) (pw_pos' hα _))
  refine le_cancel_pos hc (le_congr (.eqRefl _) ((congrAdd (congrMul (congrMul (.eqRefl _) qb) (congrMul qa (.eqRefl _)))
    (congrMul (congrMul (.eqRefl _) qa) (congrMul qb (.eqRefl _)))).eqTrans ?_) T)
  ipra_ring

/-- `cor:lyapunov`: `Ew(X^k) ≤ α^k W` (`α > 0`) gives `Ew(X^i) ≤ α^i W` for `i ≤ k`. -/
theorem lyapunov {α N x : PTm n} (hα : Γ ⊢[PRAAx] α ≐ succ (pred α))
    (hX : Γ ⊢[PRAAx] le (Ew w (pw X (eK a b)) N x) (pw α (eK a b) * Wt w N x)) :
    Γ ⊢[PRAAx] le (Ew w (pw X (eI a)) N x) (pw α (eI a) * Wt w N x) := by
  -- `Y = 1`, `β = 1`
  have one_pos : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm
  have p1 : ∀ e : PTm n, Γ ⊢[PRAAx] pw one e ≐ one := fun e => DiophantineNumberTheory.SuperellipticFamily.one_pw e
  have hY : Γ ⊢[PRAAx] le (Ew w (pw (one : PTm 2) (eK a b)) N x) (pw one (eK a b) * Wt w N x) := by
    have s : Γ ⊢[PRAAx] Ew w (pw (one : PTm 2) (eK a b)) N x ≐ Wt w N x := by
      refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
      have q : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
          inst2 w (var 0) (Syn.shift x) * pw one (eK a b) ≐ inst2 w (var 0) (Syn.shift x) :=
        (congrMul (.eqRefl _) (DiophantineNumberTheory.SuperellipticFamily.one_pw _)).eqTrans (Expectation.mul_one' _)
      simpa [inst2] using q
    exact le_congr s.eqSymm ((congrMul (p1 _) (.eqRefl _)).eqTrans (one_mul _)).eqSymm (le_refl _)
  have h := holder a b w X (one : PTm 2) hα one_pos hX hY
  have s : Γ ⊢[PRAAx] Ew w (pw X (eI a) * pw (one : PTm 2) (eJ b)) N x ≐ Ew w (pw X (eI a)) N x := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    have q : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
        inst2 w (var 0) (Syn.shift x) * (pw (inst2 X (var 0) (Syn.shift x)) (eI a) * pw one (eJ b)) ≐
          inst2 w (var 0) (Syn.shift x) * pw (inst2 X (var 0) (Syn.shift x)) (eI a) :=
      congrMul (.eqRefl _) ((congrMul (.eqRefl _) (DiophantineNumberTheory.SuperellipticFamily.one_pw _)).eqTrans (Expectation.mul_one' _))
    simpa [inst2] using q
  exact le_congr s ((congrMul (congrMul (.eqRefl _) (p1 _)) (.eqRefl _)).eqTrans
    (congrMul (Expectation.mul_one' _) (.eqRefl _))) h

end Holder

end LeanProofs.IPRA.Probability.FiniteHolder
