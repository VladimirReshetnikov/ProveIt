import IPRADerivations.DiophantineNumberTheory.HurwitzLoop
import IPRADerivations.Core.BoundedSums

/-!
# Precision independence of the continued-fraction prefix (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `hurwitz.tex`, §"Why the continued-fraction prefix
can be obtained primitively recursively": the digits are read off a primitive recursive Cauchy name, and the
extraction "is the promised path to a quantifier-free induction proof" only if the prefix does not depend on the
working precision.

Two approximations `Y/W` and `Z/V` run the loop of `HurwitzLoop` from the same start `s₀`:

* `nxt_of_dig`: at a common state the next states agree once the digits agree (the state's other components do
  not depend on the approximation);
* `dig_agree₁`, `dig_agree₂`: at a common state with both approximations in the same sign region, the name-level
  certificates of `HurwitzExtraction.digit_from_name` (separation `σ`, the bound `E`, a Cauchy bound `C`) give
  equal digits: `digit_stable`/`digit_stable₂` place `A` between `⌊A'/Dn'⌋ Dn` and `(⌊A'/Dn'⌋ + 1) Dn`, and the
  division uniqueness `div_mod_unique` turns this into `⌊A/Dn⌋ = ⌊A'/Dn'⌋`;
* `loop_agree`: digit agreement at every state `j < N` gives the same state `N` — one quantifier-free induction.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.HurwitzPrefix

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.HurwitzExtraction (adist digit_from_name digit_stable₂
  close_from_cauchy sep_transfer)
open LeanProofs.IPRA.DiophantineNumberTheory.HurwitzLoop

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- At a common state, equal digits give equal next states. -/
theorem nxt_of_dig {s Y W Z V : PTm n} (h : Γ ⊢[PRAAx] dig s Y W ≐ dig s Z V) :
    Γ ⊢[PRAAx] nxt s Y W ≐ nxt s Z V :=
  congrPairT (congrAdd (congrMul h (.eqRefl _)) (.eqRefl _))
    (congrPairT (congrAdd (congrMul h (.eqRefl _)) (.eqRefl _)) (.eqRefl _))

/-- `q Dn ≤ A < (q + 1) Dn` with `Dn ≥ 1` gives `⌊A/Dn⌋ = q`. -/
theorem quo_of_between {A Dn q : PTm n} (hD : Γ ⊢[PRAAx] Dn ≐ succ (pred Dn))
    (h : Γ ⊢[PRAAx] le (q * Dn) A ⋏ lt A (succ q * Dn)) : Γ ⊢[PRAAx] quo A Dn ≐ q :=
  le_antisymm
    (Order.le_of_lt_succ (Division.quo_lt_of_lt_mul hD (lt_congr (.eqRefl _) (mul_comm _ _) (Prf.andE₂ h))))
    (Division.le_quo_of_mul_le hD (le_congr (mul_comm _ _) (.eqRefl _) (Prf.andE₁ h)))

/-- `Dn ≐ succ (pred Dn)` gives `1 ≤ Dn`. -/
alias one_le_of_succ := Common.one_le_of_pos

/-- Digit agreement in region 1 from the name-level certificates of `digit_from_name`. -/
theorem dig_agree₁ {s Y W Z V σn σd E C : PTm n} (hR : Γ ⊢[PRAAx] R1 s Y W) (hR' : Γ ⊢[PRAAx] R1 s Z V)
    (hdet : Γ ⊢[PRAAx] detP s ⋎ detM s)
    (hDn : Γ ⊢[PRAAx] Dn s Y W ≐ succ (pred (Dn s Y W))) (hDn' : Γ ⊢[PRAAx] Dn s Z V ≐ succ (pred (Dn s Z V)))
    (hσ : Γ ⊢[PRAAx] le one σn) (hE : Γ ⊢[PRAAx] le (Dn s Y W) (E * W))
    (hc : Γ ⊢[PRAAx] le (adist (W * Z) (V * Y)) C)
    (h6 : Γ ⊢[PRAAx] le (num 6 * (σd * E) * C) (σn * (Dn s Y W * Dn s Z V)))
    (hs0 : Γ ⊢[PRAAx] le (σn * W)
      (σd * adist ((sP' s + dig s Z V * sP s) * W) ((sQ' s + dig s Z V * sQ s) * Y)))
    (hs1 : Γ ⊢[PRAAx] le (σn * W)
      (σd * adist ((sP' s + succ (dig s Z V) * sP s) * W) ((sQ' s + succ (dig s Z V) * sQ s) * Y))) :
    Γ ⊢[PRAAx] dig s Y W ≐ dig s Z V := by
  have hD1 : Γ ⊢[PRAAx] sQ s * Y ≐ sP s * W + Dn s Y W := add_adist (Prf.andE₁ hR)
  have hA1 : Γ ⊢[PRAAx] sP' s * W ≐ sQ' s * Y + An s Y W := add_adist (Prf.andE₂ hR)
  have hD1' : Γ ⊢[PRAAx] sQ s * Z ≐ sP s * V + Dn s Z V := add_adist (Prf.andE₁ hR')
  have hA1' : Γ ⊢[PRAAx] sP' s * V ≐ sQ' s * Z + An s Z V := add_adist (Prf.andE₂ hR')
  exact quo_of_between hDn
    (digit_from_name hdet hA1 hD1 hA1' hD1' (one_le_of_succ hDn) hDn' hσ hE hc h6 hs0 hs1)

/-- Digit agreement in region 2 (`digit_stable₂` with the name-level certificates). -/
theorem dig_agree₂ {s Y W Z V σn σd E C : PTm n} (hR : Γ ⊢[PRAAx] R2 s Y W) (hR' : Γ ⊢[PRAAx] R2 s Z V)
    (hdet : Γ ⊢[PRAAx] detP s ⋎ detM s)
    (hDn : Γ ⊢[PRAAx] Dn s Y W ≐ succ (pred (Dn s Y W))) (hDn' : Γ ⊢[PRAAx] Dn s Z V ≐ succ (pred (Dn s Z V)))
    (hσ : Γ ⊢[PRAAx] le one σn) (hE : Γ ⊢[PRAAx] le (Dn s Y W) (E * Y))
    (hc : Γ ⊢[PRAAx] le (adist (Y * V) (Z * W)) C)
    (h6 : Γ ⊢[PRAAx] le (num 6 * (σd * E) * C) (σn * (Dn s Y W * Dn s Z V)))
    (hs0 : Γ ⊢[PRAAx] le (σn * Y)
      (σd * adist ((sQ' s + dig s Z V * sQ s) * Y) ((sP' s + dig s Z V * sP s) * W)))
    (hs1 : Γ ⊢[PRAAx] le (σn * Y)
      (σd * adist ((sQ' s + succ (dig s Z V) * sQ s) * Y) ((sP' s + succ (dig s Z V) * sP s) * W))) :
    Γ ⊢[PRAAx] dig s Y W ≐ dig s Z V := by
  have hD2 : Γ ⊢[PRAAx] sP s * W ≐ sQ s * Y + Dn s Y W := add_adist' (Prf.andE₁ hR)
  have hA2 : Γ ⊢[PRAAx] sQ' s * Y ≐ sP' s * W + An s Y W := add_adist' (Prf.andE₂ hR)
  have hD2' : Γ ⊢[PRAAx] sP s * V ≐ sQ s * Z + Dn s Z V := add_adist' (Prf.andE₁ hR')
  have hA2' : Γ ⊢[PRAAx] sQ' s * Z ≐ sP' s * V + An s Z V := add_adist' (Prf.andE₂ hR')
  exact quo_of_between hDn
    (digit_stable₂ (Ld := σd * E) hdet hA2 hD2 hA2' hD2' (one_le_of_succ hDn) hDn' hσ
      (close_from_cauchy hc h6) (sep_transfer hs0 hE) (sep_transfer hs1 hE))

/-- Precision independence: digit agreement at every state `j < N` gives the same state `N` for both
approximations. -/
theorem loop_agree (s0 Y W Z V N : PTm n)
    (hdig : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      dig (state (var 0) (Syn.shift s0) (Syn.shift Y) (Syn.shift W)) (Syn.shift Y) (Syn.shift W) ≐
        dig (state (var 0) (Syn.shift s0) (Syn.shift Y) (Syn.shift W)) (Syn.shift Z) (Syn.shift V))) :
    Γ ⊢[PRAAx] state N s0 Y W ≐ state N s0 Z V := by
  let P : Fm PTm (n + 1) := state (var 0) (Syn.shift s0) (Syn.shift Y) (Syn.shift W) ≐
    state (var 0) (Syn.shift s0) (Syn.shift Z) (Syn.shift V)
  have atEnd : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N trivial ?_ ?_
    · ipra_ind_simp [P, subst_state, Syn.subst_inst_shift]
      exact (state_zero _ _ _).eqTrans (state_zero _ _ _).eqSymm
    · ipra_ind_simp [P, subst_state, subst_repl_shift]
      refine .impI ?_
      let Θ := lt (var 0) (Syn.shift N) :: P :: Γ.map Fm.shift
      have hd : Θ ⊢[PRAAx]
          dig (state (var 0) (Syn.shift s0) (Syn.shift Y) (Syn.shift W)) (Syn.shift Y) (Syn.shift W) ≐
            dig (state (var 0) (Syn.shift s0) (Syn.shift Y) (Syn.shift W)) (Syn.shift Z) (Syn.shift V) :=
        .impE hdig.allOpen.wk.wk Prf.hyp0
      exact (state_succ _ _ _ _).eqTrans ((nxt_of_dig hd).eqTrans
        ((congrNxt Prf.hyp1 (.eqRefl _) (.eqRefl _)).eqTrans (state_succ _ _ _ _).eqSymm))
  simpa only [P, Fm.subst_eq, subst_state, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using atEnd

end LeanProofs.IPRA.DiophantineNumberTheory.HurwitzPrefix
