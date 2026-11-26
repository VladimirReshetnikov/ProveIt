import IPRADerivations.Foundations.RuntimePermutationWords
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.SubstCommand
import IPRADerivations.Core.Header

/-!
# Appending a numerical mixed-radix word digit

The actual little-endian append code is w+v*m^d. Original quotient and
remainder uniqueness proves its new digit and every earlier digit; the
interval bound is genuine mixed-radix arithmetic. All radix, length,
word, digit and position parameters are numerical. Positive radix is a
local guard, not a supplied decoding or word-expansion law. No Analysis
imports or variable-dimensional host tuples are used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RuntimeWordAppend

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def append (m d w v : PTm n) : PTm n := w+v*pw m d
ipra_subst append

theorem positive_form (D : PTm n) (h : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] D ≐ succ (pred D) := by
  refine .orE (zero_or_succ D) ?_ Prf.hyp0
  exact not_succ_le_self zero _ (le_congr (.eqRefl _) Prf.hyp0 h.wk)

theorem power_positive (m d : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx] le one (pw m d) := by
  have base := congrAp2 powF (.eqRefl d) (positive_form m hm)
  exact le_congr (.eqRefl _) (base.eqTrans (DiophantineNumberTheory.FLTMultiples.pw_pos (pred m) d)).eqSymm (zero_lt_succ _)

/-- The actual quotient/remainder equations at any genuinely positive divisor. -/
theorem divide_spec (D z : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    (z ≐ D*quo z D+rem z D) ⋏ lt (rem z D) D := by
  have pos := positive_form D hD
  have old := div_mod (Γ := Γ) z (pred D)
  have q := congrAp2 quoF (.eqRefl z) pos.eqSymm
  have r := congrAp2 remF (.eqRefl z) pos.eqSymm
  exact .andI ((Prf.andE₁ old).eqTrans (congrAdd (congrMul pos.eqSymm q) r))
    (lt_congr r pos.eqSymm (.andE₂ old))

theorem divide_unique (D z q r : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hz : Γ ⊢[PRAAx] z ≐ D*q+r) (hr : Γ ⊢[PRAAx] lt r D) : Γ ⊢[PRAAx]
    (quo z D ≐ q) ⋏ (rem z D ≐ r) := by
  have pos := positive_form D hD
  have actual := div_mod_unique (hz.eqTrans (congrAdd (congrMul pos (.eqRefl _)) (.eqRefl _)))
    (lt_congr (.eqRefl _) pos hr)
  exact .andI ((congrAp2 quoF (.eqRefl _) pos).eqTrans (.andE₁ actual))
    ((congrAp2 remF (.eqRefl _) pos).eqTrans (.andE₂ actual))

theorem remainder_small (m v : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hv : Γ ⊢[PRAAx] lt v m) : Γ ⊢[PRAAx]
    rem v m ≐ v := .andE₂ (divide_unique m v zero v hm (by ipra_ring) hv)

theorem append_bound (m d w v : PTm n) (hw : Γ ⊢[PRAAx] lt w (pw m d))
    (hv : Γ ⊢[PRAAx] lt v m) : Γ ⊢[PRAAx] lt (append m d w v) (pw m (succ d)) :=
  lt_congr (.eqRefl _) (pw_succ m d).eqSymm (MixedRadixExpansion.append_interval hw hv)

theorem append_quotient (m d w v : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hw : Γ ⊢[PRAAx] lt w (pw m d)) : Γ ⊢[PRAAx] quo (append m d w v) (pw m d) ≐ v :=
  .andE₁ (divide_unique (pw m d) (append m d w v) v w (power_positive m d hm) (by unfold append; ipra_ring) hw)

theorem digit_new (m d w v : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hw : Γ ⊢[PRAAx] lt w (pw m d)) (hv : Γ ⊢[PRAAx] lt v m) : Γ ⊢[PRAAx]
    RuntimePermutationWords.digit m (append m d w v) d ≐ v :=
  (congrAp2 remF (append_quotient _ _ _ _ hm hw) (.eqRefl _)).eqTrans (remainder_small m v hm hv)

/-- Every earlier place divides the appended high place by an extra radix factor. -/
theorem higher_place (m d i : PTm n) (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx]
    pw m d ≐ pw m i*m*pw m (monus d (succ i)) :=
  (congrAp2 powF (eq_add_of_le hi) (.eqRefl _)).eqTrans
    ((pw_add _ _ _).eqTrans (congrMul (pw_succ _ _) (.eqRefl _)))

/-- The low-digit statement needs no bound on the original high word or appended digit. -/
theorem digit_before (m d w v i : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx]
    RuntimePermutationWords.digit m (append m d w v) i ≐ RuntimePermutationWords.digit m w i := by
  let P := pw m i
  let T := pw m (monus d (succ i))
  have ws := divide_spec P w (power_positive m i hm)
  have place := higher_place m d i hi
  have e : Γ ⊢[PRAAx] append m d w v ≐ P*(quo w P+m*(v*T))+rem w P := by
    have we := natEq (Prf.andE₁ ws)
    have pe := natEq place
    unfold append
    apply deriveNat
    ipra_simps
    dsimp only [P,T] at we ⊢
    rw [pe]
    linear_combination we
  have q := Prf.andE₁ (divide_unique P (append m d w v) (quo w P+m*(v*T)) (rem w P) (power_positive m i hm) e (.andE₂ ws))
  have qs := divide_spec m (quo w P) hm
  have qe : Γ ⊢[PRAAx] quo w P+m*(v*T) ≐ m*(quo (quo w P) m+v*T)+rem (quo w P) m := by
    ipra_lc natEq (Prf.andE₁ qs)
  exact (congrAp2 remF q (.eqRefl _)).eqTrans
    (.andE₂ (divide_unique m _ (quo (quo w P) m+v*T) (rem (quo w P) m) hm qe (.andE₂ qs)))

def appendF : PR 4 := PTm.toPR (append (var 0) (var 1) (var 2) (var 3))
def run (m d w v : PTm n) : PTm n := app appendF ![m,d,w,v]
theorem program_at (m d w v : PTm n) : Γ ⊢[PRAAx] run m d w v ≐ append m d w v := by
  simpa [run,appendF] using toPR_eq (Γ := Γ) (append (var 0) (var 1) (var 2) (var 3) : PTm 4) ![m,d,w,v]

theorem actual_append_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (pw (var 0) (var 1)) ⟶ lt (var 3) (var 0) ⟶ lt (append (var 0) (var 1) (var 2) (var 3)) (pw (var 0) (succ (var 1)))) :=
  closeUniv 4 (.impI (.impI (append_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_appended_digit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ lt (var 2) (pw (var 0) (var 1)) ⟶ lt (var 3) (var 0) ⟶
      RuntimePermutationWords.digit (var 0) (append (var 0) (var 1) (var 2) (var 3)) (var 1) ≐ var 3) :=
  closeUniv 4 (.impI (.impI (.impI (digit_new _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_earlier_digit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ lt (var 4) (var 1) ⟶ RuntimePermutationWords.digit (var 0)
      (append (var 0) (var 1) (var 2) (var 3)) (var 4) ≐ RuntimePermutationWords.digit (var 0) (var 2) (var 4)) :=
  closeUniv 5 (.impI (.impI (digit_before _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_append_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ append (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)

end LeanProofs.IPRA.Foundations.RuntimeWordAppend
