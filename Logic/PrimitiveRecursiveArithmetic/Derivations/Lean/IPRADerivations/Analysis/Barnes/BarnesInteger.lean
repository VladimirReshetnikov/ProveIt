import IPRADerivations.Analysis.FiniteOperations.FiniteProducts.Products
import IPRADerivations.AnalyticNumberTheory.LocalFactor
import IPRADerivations.Combinatorics.Binomial
import IPRADerivations.AnalyticNumberTheory.Euler
import IPRADerivations.Core.ProdLemmas
import IPRADerivations.Core.CongruenceTactic

/-!
# The Barnes G-function at positive integers

Packet: `analysis/barnes_g_ipra_2026-11-16` (Section 4: `thm:integer-ipra`, the superfactorial
identity `eq:superfactorial` and the hyperfactorial identity `eq:hyper-cross`). At positive
integers `G(n + 1) = ∏_{j<n} j!`; this product is `barnes n`, the sequence `g_n` of the packet.

* `barnes_zero`, `barnes_succ` (`thm:integer-ipra`): `g_0 = 1`, `g_{n+1} = n! g_n`;
* `barnes_one` … `barnes_four`: `G(2) = 1`, `G(3) = 1`, `G(4) = 2`, `G(5) = 12`;
* `hyp_zero`, `hyp_succ`: the hyperfactorial `H(m) = ∏_{j=1}^{m} j^j`;
* `hyper_cross` (`eq:hyper-cross`): `G(m + 1) H(m) = (m!)^m`;
* `barnes_pos`, `hyp_pos`: both are positive;
* `barnes_quotient` (`eq:G-over-H`): `G(m + 1) = (m!)^m / H(m)`, with the quotient exact;
* `barnes_power_form`: `G(m + 2) = ∏_{i<m} (i + 1)^{m−i}`, the product behind
  `log G(n + 1) = ∑_{j} (n − j) log j` in the packet's lower bound.

The superfactorial identity `G(n + 2) = ∏_{j≤n} j!` is the definition of `barnes (n + 1)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BarnesInteger

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples (pw_pos)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul quo_of_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (prod_mul1)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The sequences -/

/-- `j ↦ j!`. -/
abbrev facB : PTm 2 := fact (var 0)
/-- `j ↦ (j + 1)^{j+1}`. -/
abbrev hypB : PTm 2 := pw (succ (var 0)) (succ (var 0))

/-- `g_m = ∏_{j<m} j! = G(m + 1)`. -/
abbrev barnes (m : PTm n) : PTm n := ap2 (prodF facB) m zero
/-- The hyperfactorial `H(m) = ∏_{j<m} (j + 1)^{j+1}`. -/
abbrev hyp (m : PTm n) : PTm n := ap2 (prodF hypB) m zero

theorem barnes_zero : Γ ⊢[PRAAx] barnes (zero : PTm n) ≐ one := prod_zero _ _

theorem barnes_succ (m : PTm n) : Γ ⊢[PRAAx] barnes (succ m) ≐ barnes m * fact m := by
  have h := prod_succ (Γ := Γ) facB m zero
  have e : Syn.subst ![m, zero] facB = fact m := by simp
  rw [e] at h
  exact h

theorem hyp_zero : Γ ⊢[PRAAx] hyp (zero : PTm n) ≐ one := prod_zero _ _

theorem hyp_succ (m : PTm n) : Γ ⊢[PRAAx] hyp (succ m) ≐ hyp m * pw (succ m) (succ m) := by
  have h := prod_succ (Γ := Γ) hypB m zero
  have e : Syn.subst ![m, zero] hypB = pw (succ m) (succ m) := by simp
  rw [e] at h
  exact h

/-! ## The first values -/

theorem fact_one : Γ ⊢[PRAAx] fact (one : PTm n) ≐ one :=
  (fact_succ zero zero).eqTrans ((congrMul (fact_zero zero) (.eqRefl _)).eqTrans (one_mul _))

theorem fact_two : Γ ⊢[PRAAx] fact (two : PTm n) ≐ two :=
  (fact_succ one zero).eqTrans ((congrMul fact_one (.eqRefl _)).eqTrans (one_mul _))

theorem fact_three : Γ ⊢[PRAAx] fact (succ two : PTm n) ≐ two * succ two :=
  (fact_succ two zero).eqTrans (congrMul fact_two (.eqRefl _))

/-- `G(2) = 1`. -/
theorem barnes_one : Γ ⊢[PRAAx] barnes (one : PTm n) ≐ one :=
  (barnes_succ zero).eqTrans ((congrMul barnes_zero (fact_zero zero)).eqTrans (one_mul _))

/-- `G(3) = 1`. -/
theorem barnes_two : Γ ⊢[PRAAx] barnes (two : PTm n) ≐ one :=
  (barnes_succ one).eqTrans ((congrMul barnes_one fact_one).eqTrans (one_mul _))

/-- `G(4) = 2`. -/
theorem barnes_three : Γ ⊢[PRAAx] barnes (succ two : PTm n) ≐ two :=
  (barnes_succ two).eqTrans ((congrMul barnes_two fact_two).eqTrans (one_mul _))

/-- `G(5) = 12`. -/
theorem barnes_four : Γ ⊢[PRAAx] barnes (succ (succ two) : PTm n) ≐ two * (two * succ two) :=
  (barnes_succ (succ two)).eqTrans (congrMul barnes_three fact_three)

/-! ## The hyperfactorial identity -/

theorem hc_base : Γ ⊢[PRAAx] barnes (zero : PTm n) * hyp zero ≐ pw (fact zero) zero := by
  ipra_lc 𝔞(hyp zero) * natEq (barnes_zero (Γ := Γ)) + natEq (hyp_zero (Γ := Γ)) -
    natEq (pw_zero (Γ := Γ) (fact (zero : PTm n)))

theorem hc_step {m : PTm n} (ih : Γ ⊢[PRAAx] barnes m * hyp m ≐ pw (fact m) m) :
    Γ ⊢[PRAAx] barnes (succ m) * hyp (succ m) ≐ pw (fact (succ m)) (succ m) := by
  have eR : Γ ⊢[PRAAx] pw (fact (succ m)) (succ m) ≐ (pw (fact m) m * fact m) * pw (succ m) (succ m) :=
    (congrAp2 powF (.eqRefl _) (fact_succ m zero)).eqTrans
      ((pw_mul_base _ _ _).eqTrans (congrMul (pw_succ _ _) (.eqRefl _)))
  ipra_lc 𝔞(hyp (succ m)) * natEq (barnes_succ (Γ := Γ) m) + 𝔞(barnes m) * 𝔞(fact m) * natEq (hyp_succ (Γ := Γ) m) +
    𝔞(fact m) * 𝔞(pw (succ m) (succ m)) * natEq ih - natEq eR

/-- Variables: `0 = m`. -/
private abbrev hcF : Fm PTm 1 := barnes (var 0) * hyp (var 0) ≐ pw (fact (var 0)) (var 0)

private theorem hc₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] hcF := by
  ipra_ind [subst_ap2]
  · exact hc_base
  · exact hc_step Prf.hyp0

/-- `eq:hyper-cross`: `G(m + 1) H(m) = (m!)^m`. -/
theorem hyper_cross (m : PTm n) : Γ ⊢[PRAAx] barnes m * hyp m ≐ pw (fact m) m := by
  have h := inst (Γ := Γ) hc₀ (![m] : Fin 1 → PTm n)
  simpa using h

/-! ## Positivity and the quotient form -/

alias one_pos := Common.one_pos

/-- Variables: `0 = m`. -/
private abbrev bposF : Fm PTm 1 := barnes (var 0) ≐ succ (pred (barnes (var 0)))
private abbrev hposF : Fm PTm 1 := hyp (var 0) ≐ succ (pred (hyp (var 0)))

theorem pos_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] a ≐ succ (pred a) := by
  have e : Γ ⊢[PRAAx] pred a ≐ pred b := by
    ipra_congr (pred (var 0) : PTm 1) with [h]
  exact h.eqTrans (hb.eqTrans (congrSucc e.eqSymm))

private theorem bpos₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] bposF := by
  ipra_ind [subst_ap2]
  · exact pos_congr barnes_zero one_pos
  · exact pos_congr (barnes_succ _) (pos_mul Prf.hyp0 (fact_pos _))

private theorem hpos₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] hposF := by
  ipra_ind [subst_ap2]
  · exact pos_congr hyp_zero one_pos
  · exact pos_congr (hyp_succ _) (pos_mul Prf.hyp0 (pw_pos _ _))

/-- `G(m + 1) > 0`. -/
theorem barnes_pos (m : PTm n) : Γ ⊢[PRAAx] barnes m ≐ succ (pred (barnes m)) := by
  have h := inst (Γ := Γ) bpos₀ (![m] : Fin 1 → PTm n)
  simpa using h

/-- `H(m) > 0`. -/
theorem hyp_pos (m : PTm n) : Γ ⊢[PRAAx] hyp m ≐ succ (pred (hyp m)) := by
  have h := inst (Γ := Γ) hpos₀ (![m] : Fin 1 → PTm n)
  simpa using h

/-- `eq:G-over-H`: `G(m + 1) = (m!)^m / H(m)`, the quotient being exact. -/
theorem barnes_quotient (m : PTm n) : Γ ⊢[PRAAx] quo (pw (fact m) m) (hyp m) ≐ barnes m :=
  quo_of_eq (hyp_pos m) ((hyper_cross m).eqSymm.eqTrans (mul_comm _ _))

/-! ## The power form -/

/-- `(i + 1)^{m ∸ i}`, with `m` the parameter. -/
abbrev epB : PTm 2 := pw (succ (var 0)) (monus (var 1) (var 0))
/-- `i + 1`: the body of the factorial. -/
abbrev succB : PTm 2 := succ (var 0)

theorem inst2_ep (i m : PTm n) : inst2 epB i m = pw (succ i) (monus m i) := by simp [inst2]

theorem inst2_ep_mul (i m : PTm n) : inst2 (epB * succB) i m = pw (succ i) (monus m i) * succ i := by
  simp [inst2]

/-- `(i + 1)^{(m + 1) ∸ i} = (i + 1)^{m ∸ i} · (i + 1)` for `i < m`. -/
theorem ep_shift_pt {i m : PTm n} (h : Γ ⊢[PRAAx] lt i m) :
    Γ ⊢[PRAAx] inst2 epB i (succ m) ≐ inst2 (epB * succB) i m := by
  rw [inst2_ep, inst2_ep_mul]
  have e : Γ ⊢[PRAAx] succ m ≐ i + succ (monus m i) :=
    (congrSucc (eq_add_of_le (le_of_lt h))).eqTrans (add_succ _ _).eqSymm
  exact (congrAp2 powF ((congrMonus e (.eqRefl _)).eqTrans (add_monus' _ _)) (.eqRefl _)).eqTrans (pw_succ _ _)

/-- `∏_{i<m} (i + 1) = m!`. -/
theorem prod_succ_fact (m x : PTm n) : Γ ⊢[PRAAx] ap2 (prodF succB) m x ≐ fact m := by
  refine prod_congr_bounded succB (succ (var 0)) x zero m (.allI (.impI ?_))
  exact .eqRefl _

/-- `∏_{i<m} (i + 1)^{m+1−i} = (∏_{i<m} (i + 1)^{m−i}) · m!`. -/
theorem ep_shift (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF epB) m (succ m) ≐ ap2 (prodF epB) m m * fact m := by
  refine (prod_congr_bounded epB (epB * succB) (succ m) m m (.allI (.impI ?_))).eqTrans
    ((prod_mul1 epB succB m m).eqTrans (congrMul (.eqRefl _) (prod_succ_fact m m)))
  have es : Syn.shift (succ m) = succ (Syn.shift m) := by simp [Syn.shift]
  rw [es]
  exact ep_shift_pt Prf.hyp0

theorem pf_step {m : PTm n} (ih : Γ ⊢[PRAAx] ap2 (prodF epB) m m ≐ barnes (succ m)) :
    Γ ⊢[PRAAx] ap2 (prodF epB) (succ m) (succ m) ≐ barnes (succ (succ m)) := by
  have e₁ := prod_succ (Γ := Γ) epB m (succ m)
  have ee : Syn.subst ![m, succ m] epB = pw (succ m) (monus (succ m) m) := inst2_ep m (succ m)
  rw [ee] at e₁
  have p₁ : Γ ⊢[PRAAx] pw (succ m) (monus (succ m) m) ≐ succ m := by
    have e : Γ ⊢[PRAAx] succ m ≐ m + succ zero := by ipra_ring
    exact (congrAp2 powF ((congrMonus e (.eqRefl _)).eqTrans (add_monus' _ _)) (.eqRefl _)).eqTrans
      ((pw_succ _ _).eqTrans ((congrMul (pw_zero _) (.eqRefl _)).eqTrans (one_mul _)))
  ipra_lc natEq e₁ - natEq (barnes_succ (Γ := Γ) (succ m)) +
    𝔞(pw (succ m) (monus (succ m) m)) * natEq (ep_shift (Γ := Γ) m) + 𝔞(ap2 (prodF epB) m m) * 𝔞(fact m) * natEq p₁ +
    𝔞(fact m) * (𝔞(m) + 1) * natEq ih - 𝔞(barnes (succ m)) * natEq (fact_succ (Γ := Γ) m zero)

/-- Variables: `0 = m`. -/
private abbrev pfF : Fm PTm 1 := ap2 (prodF epB) (var 0) (var 0) ≐ barnes (succ (var 0))

private theorem pf₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] pfF := by
  ipra_ind [subst_ap2]
  · exact (prod_zero _ _).eqTrans barnes_one.eqSymm
  · exact pf_step Prf.hyp0

/-- `G(m + 2) = ∏_{i<m} (i + 1)^{m−i}`. -/
theorem barnes_power_form (m : PTm n) : Γ ⊢[PRAAx] ap2 (prodF epB) m m ≐ barnes (succ m) := by
  have h := inst (Γ := Γ) pf₀ (![m] : Fin 1 → PTm n)
  simpa using h

end LeanProofs.IPRA.Analysis.BarnesInteger
