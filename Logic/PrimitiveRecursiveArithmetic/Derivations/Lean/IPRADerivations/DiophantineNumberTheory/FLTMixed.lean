import IPRADerivations.DiophantineNumberTheory.FLTMultiples

/-!
# Mixed exponents from Fermat's quartic theorem

Packet: `diophantine-number-theory/flt_ipra`, Corollary `cor:mixed` (the parts reducing to
Fermat's stronger quartic theorem `thm:four`, `FermatQuartic.fermat_quartic`):

* `mixed_quartic`: `X, Y ≥ 1 → X^{4i} + Y^{4j} ≠ Z^{2k}` for all `i, j, k`;
* `mixed_four`: if `4` divides `a`, `b` and `c`, then `X, Y ≥ 1 → X^a + Y^b ≠ Z^c`.

`X^{4i} = (X^i)⁴` (`FLTMultiples.pw_lift`) with `X^i ≥ 1`, and `Z^{2k} = (Z^k)²` (`RSA.pw_mul`), so a
solution is a positive solution of `x⁴ + y⁴ = z²`. For `4 ∣ a, b, c` write `c = 2 (2 (c/4))`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.FLTMixed

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.Pythagoras (two_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (q4)
open LeanProofs.IPRA.DiophantineNumberTheory.FermatQuartic (fermat_quartic quarticFormula)
open LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples (pw_pos pw_lift)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `thm:four` at terms: `x, y ≥ 1 → x⁴ + y⁴ ≠ z²`. -/
theorem quartic_at (x' y' z : PTm n) : Γ ⊢[PRAAx] neg (q4 (succ x') + q4 (succ y') ≐ z * z) := by
  have h := inst (Γ := Γ) (Prf.allOpen (Prf.allOpen (Prf.allOpen
    (fermat_quartic : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 quarticFormula)))) (![x', y', z] : Fin 3 → PTm n)
  simpa using h

alias pw_two' := Common.pw_two

/-- `Z^{2k} = (Z^k)²`. -/
alias pw_double := Common.pw_double

/-- `cor:mixed`, second part: `X^{4i} + Y^{4j} ≠ Z^{2k}`. -/
theorem mixed_quartic (x' y' Z i j k : PTm n) :
    Γ ⊢[PRAAx] neg (pw (succ x') ((two * two) * i) + pw (succ y') ((two * two) * j) ≐ pw Z (two * k)) := by
  refine .impI (.impE (quartic_at (pred (pw (succ x') i)) (pred (pw (succ y') j)) (pw Z k)) ?_)
  have X := pw_pos (Γ := (pw (succ x') ((two * two) * i) + pw (succ y') ((two * two) * j) ≐ pw Z (two * k)) :: Γ) x' i
  have Y := pw_pos (Γ := (pw (succ x') ((two * two) * i) + pw (succ y') ((two * two) * j) ≐ pw Z (two * k)) :: Γ) y' j
  have qX := congrMul (congrMul X X) (congrMul X X)
  have qY := congrMul (congrMul Y Y) (congrMul Y Y)
  exact (congrAdd qX qY).eqSymm.eqTrans ((congrAdd (pw_lift (.eqRefl _)).eqSymm (pw_lift (.eqRefl _)).eqSymm).eqTrans
    (Prf.hyp0.eqTrans (pw_double _ _)))

/-- `cor:mixed`, the exponent-four case: `4 ∣ a, b, c → X^a + Y^b ≠ Z^c`. -/
theorem mixed_four {x' y' Z a b c : PTm n} (ha : Γ ⊢[PRAAx] dvd (two * two) a)
    (hb : Γ ⊢[PRAAx] dvd (two * two) b) (hc : Γ ⊢[PRAAx] dvd (two * two) c) :
    Γ ⊢[PRAAx] neg (pw (succ x') a + pw (succ y') b ≐ pw Z c) := by
  have h4 : Γ ⊢[PRAAx] (two * two : PTm n) ≐ succ (pred (two * two)) := pos_mul two_pos two_pos
  have ea := eq_of_dvd' h4 ha; have eb := eq_of_dvd' h4 hb; have ec := eq_of_dvd' h4 hc
  have ec' : Γ ⊢[PRAAx] c ≐ two * (two * quo c (two * two)) :=
    ec.eqTrans (by ipra_ring)
  refine .impI (.impE (mixed_quartic x' y' Z (quo a (two * two)) (quo b (two * two))
    (two * quo c (two * two))) ?_)
  exact (congrAdd (congrPw (.eqRefl _) ea.wk) (congrPw (.eqRefl _) eb.wk)).eqSymm.eqTrans
    (Prf.hyp0.eqTrans (congrPw (.eqRefl _) ec'.wk))

/-- Variables: `0 = X − 1`, `1 = Y − 1`, `2 = Z`, `3 = i`, `4 = j`, `5 = k`. -/
abbrev mixedQuarticFormula : Fm PTm 6 :=
  neg (pw (succ (var 0)) ((two * two) * var 3) + pw (succ (var 1)) ((two * two) * var 4) ≐ pw (var 2) (two * var 5))

theorem mixed_quartic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6 mixedQuarticFormula :=
  closeUniv 6 (mixed_quartic _ _ _ _ _ _)

/-- Variables: `0 = X − 1`, `1 = Y − 1`, `2 = Z`, `3 = a`, `4 = b`, `5 = c`. -/
abbrev mixedFourFormula : Fm PTm 6 :=
  dvd (two * two) (var 3) ⟶ dvd (two * two) (var 4) ⟶ dvd (two * two) (var 5) ⟶
    neg (pw (succ (var 0)) (var 3) + pw (succ (var 1)) (var 4) ≐ pw (var 2) (var 5))

theorem mixed_four_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6 mixedFourFormula :=
  closeUniv 6 (.impI (.impI (.impI (mixed_four Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.DiophantineNumberTheory.FLTMixed
