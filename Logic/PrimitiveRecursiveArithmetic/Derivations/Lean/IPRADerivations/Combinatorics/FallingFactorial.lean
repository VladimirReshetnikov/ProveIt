import IPRADerivations.Combinatorics.StirlingPowers
import IPRADerivations.Combinatorics.BinomialIdentities

/-!
# The falling factorial

Packet: `combinatorics/bell_numbers_ipra` (the proof of `lem:finite-shift`: `(X)_k (X − k)_j =
(X)_{k+j}`). For natural `X`, `(X)_k = ∏_{j<k} (X ∸ j)` (`Combinatorics/StirlingPowers`).

* `monus_monus_add`: `(X ∸ k) ∸ j = X ∸ (k + j)`;
* `ff_add`: `(X)_{k+j} = (X)_k (X ∸ k)_j`, the shift identity of the proof;
* `ff_self`: `(X)_X = X!`;
* `ff_fact`: `(X)_k (X ∸ k)! = X!` for `k ≤ X`;
* `ff_binom`: `(X)_k = k! C(X, k)` for `k ≤ X`, which connects the falling factorial with the
  exact binomial coefficients of `Combinatorics/Binomial`.

The umbral functional `𝓛` and the identities derived from it are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.FallingFactorial

open_ipra
open LeanProofs.IPRA.Combinatorics.StirlingPowers (ffB ff ff_zero ff_succ congrFF)
open LeanProofs.IPRA.Combinatorics.Binomial (binom bden)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Iterated truncated subtraction -/

/-- Variables: `0 = j` (induction), `1 = X`, `2 = k`. -/
private abbrev mmF : Fm PTm 3 := monus (monus (var 1) (var 2)) (var 0) ≐ monus (var 1) (var 2 + var 0)

private theorem mm₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] mmF := by
  ipra_ind
  · exact (monus_zero _).eqTrans (congrMonus (.eqRefl _) (add_zero _)).eqSymm
  · refine (monus_succ _ _).eqTrans ((congrPred Prf.hyp0).eqTrans ?_)
    exact (monus_succ _ _).eqSymm.eqTrans (congrMonus (.eqRefl _) (add_succ _ _).eqSymm)

/-- `(X ∸ k) ∸ j = X ∸ (k + j)`. -/
theorem monus_monus_add (X k j : PTm n) : Γ ⊢[PRAAx] monus (monus X k) j ≐ monus X (k + j) := by
  have h := inst (Γ := Γ) mm₀ (![j, X, k] : Fin 3 → PTm n)
  simpa using h

/-! ## The shift identity -/

theorem ff_add_base (X k : PTm n) : Γ ⊢[PRAAx] ff X (k + zero) ≐ ff X k * ff (monus X k) zero := by
  ipra_lc natEq (congrFF (Γ := Γ) (.eqRefl X) (add_zero k)) - 𝔞(ff X k) * natEq (ff_zero (Γ := Γ) (monus X k))

theorem ff_add_step {X k j : PTm n} (ih : Γ ⊢[PRAAx] ff X (k + j) ≐ ff X k * ff (monus X k) j) :
    Γ ⊢[PRAAx] ff X (k + succ j) ≐ ff X k * ff (monus X k) (succ j) := by
  ipra_lc natEq ((congrFF (.eqRefl X) (add_succ k j)).eqTrans (ff_succ (Γ := Γ) X (k + j))) +
    𝔞(monus X (k + j)) * natEq ih - 𝔞(ff X k) * natEq (ff_succ (Γ := Γ) (monus X k) j) -
    𝔞(ff X k) * 𝔞(ff (monus X k) j) * natEq (monus_monus_add (Γ := Γ) X k j)

/-- Variables: `0 = j` (induction), `1 = X`, `2 = k`. -/
private abbrev faF : Fm PTm 3 := ff (var 1) (var 2 + var 0) ≐ ff (var 1) (var 2) * ff (monus (var 1) (var 2)) (var 0)

private theorem fa₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] faF := by
  ipra_ind [subst_ap2]
  · exact ff_add_base _ _
  · exact ff_add_step Prf.hyp0

/-- `(X)_{k+j} = (X)_k (X ∸ k)_j`. -/
theorem ff_add (X k j : PTm n) : Γ ⊢[PRAAx] ff X (k + j) ≐ ff X k * ff (monus X k) j := by
  have h := inst (Γ := Γ) fa₀ (![j, X, k] : Fin 3 → PTm n)
  simpa using h

/-! ## Factorials and binomial coefficients -/

theorem ff_one (X : PTm n) : Γ ⊢[PRAAx] ff X one ≐ X :=
  (ff_succ X zero).eqTrans ((congrMul (ff_zero X) (monus_zero X)).eqTrans (one_mul X))

theorem ff_self_step {X : PTm n} (ih : Γ ⊢[PRAAx] ff X X ≐ fact X) :
    Γ ⊢[PRAAx] ff (succ X) (succ X) ≐ fact (succ X) := by
  have e : Γ ⊢[PRAAx] succ X ≐ one + X := by ipra_ring
  ipra_lc natEq ((congrFF (.eqRefl (succ X)) e).eqTrans (ff_add (Γ := Γ) (succ X) one X)) +
    𝔞(ff (monus (succ X) one) X) * natEq (ff_one (Γ := Γ) (succ X)) +
    (𝔞(X) + 1) * natEq (congrFF (Γ := Γ) ((succ_monus_succ X zero).eqTrans (monus_zero X)) (.eqRefl X)) +
    (𝔞(X) + 1) * natEq ih - natEq (fact_succ (Γ := Γ) X zero)

/-- Variable: `0 = X`. -/
private abbrev fsF : Fm PTm 1 := ff (var 0) (var 0) ≐ fact (var 0)

private theorem fs₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] fsF := by
  ipra_ind [subst_ap2]
  · exact (ff_zero _).eqTrans (fact_zero _).eqSymm
  · exact ff_self_step Prf.hyp0

/-- `(X)_X = X!`. -/
theorem ff_self (X : PTm n) : Γ ⊢[PRAAx] ff X X ≐ fact X := by
  have h := inst (Γ := Γ) fs₀ (![X] : Fin 1 → PTm n)
  simpa using h

/-- `(X)_k (X ∸ k)! = X!` for `k ≤ X`. -/
theorem ff_fact {k X : PTm n} (h : Γ ⊢[PRAAx] le k X) : Γ ⊢[PRAAx] ff X k * fact (monus X k) ≐ fact X := by
  have e := eq_add_of_le h
  refine (congrMul (.eqRefl _) (ff_self _).eqSymm).eqTrans ((ff_add X k (monus X k)).eqSymm.eqTrans ?_)
  exact (congrFF (.eqRefl _) e.eqSymm).eqTrans (ff_self X)

/-- `(X)_k = k! C(X, k)` for `k ≤ X`. -/
theorem ff_binom {k X : PTm n} (h : Γ ⊢[PRAAx] le k X) : Γ ⊢[PRAAx] ff X k ≐ fact k * binom X k := by
  refine mul_cancel (fact_pos (monus X k)) ?_
  ipra_lc natEq (ff_fact h) + natEq (binom_eq h)

end LeanProofs.IPRA.Combinatorics.FallingFactorial
