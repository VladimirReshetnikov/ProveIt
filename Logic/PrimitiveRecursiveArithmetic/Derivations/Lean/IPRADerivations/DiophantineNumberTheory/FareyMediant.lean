import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Farey separation and the mediant

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/diophantine.tex`, Theorem `dio:farey`:
if `a/b < c/d` with `b c − a d = 1`, then every fraction `p/q` strictly between them has `q ≥ b + d`; the mediant
`(a + c)/(b + d)` is reduced, lies strictly between them and attains the bound.

All numbers are natural, the determinant condition is `b c = a d + 1`, and the order of fractions is the order of
the cross products.

* **`farey_separation`**: `a q < b p` and `d p < c q` give `b + d ≤ q`, from
  `q = d (b p − a q) + b (c q − d p)`;
* **`mediant_between`**: `a (b + d) < b (a + c)` and `d (a + c) < c (b + d)`;
* **`mediant_reduced`**: a common divisor `g ≥ 1` of `a + c` and `b + d` is `1`, since it divides
  `b (a + c) − a (b + d) = 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.FareyMediant

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_mul' dvd_sub' eq_one_of_dvd_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- **Farey separation**: for `b c = a d + 1`, a fraction `p/q` with `a/b < p/q < c/d` has `q ≥ b + d`. -/
theorem farey_separation {a b c d p q : PTm n} (hdet : Γ ⊢[PRAAx] b * c ≐ a * d + one)
    (h1 : Γ ⊢[PRAAx] lt (a * q) (b * p)) (h2 : Γ ⊢[PRAAx] lt (d * p) (c * q)) :
    Γ ⊢[PRAAx] le (b + d) q := by
  refine le_of_eq_add (d := d * monus (b * p) (succ (a * q)) + b * monus (c * q) (succ (d * p))) ?_
  ipra_lc 𝔞 d * natEq (eq_add_of_le h1) + 𝔞 b * natEq (eq_add_of_le h2) - 𝔞 q * natEq hdet

/-- **The mediant lies strictly between**: `a/b < (a + c)/(b + d) < c/d`. -/
theorem mediant_between {a b c d : PTm n} (hdet : Γ ⊢[PRAAx] b * c ≐ a * d + one) :
    Γ ⊢[PRAAx] lt (a * (b + d)) (b * (a + c)) ⋏ lt (d * (a + c)) (c * (b + d)) := by
  refine .andI (le_of_eq_add (d := zero) ?_) (le_of_eq_add (d := zero) ?_)
  · ipra_lc natEq hdet
  · ipra_lc natEq hdet

theorem med_alg {a b c d : PTm n} (hdet : Γ ⊢[PRAAx] b * c ≐ a * d + one) :
    Γ ⊢[PRAAx] (a + c) * b ≐ one + (b + d) * a := by
  ipra_lc natEq hdet

/-- **The mediant is reduced**: a common divisor of `a + c` and `b + d` is `1`. -/
theorem mediant_reduced {a b c d g : PTm n} (hdet : Γ ⊢[PRAAx] b * c ≐ a * d + one)
    (hg : Γ ⊢[PRAAx] g ≐ succ (pred g)) (h1 : Γ ⊢[PRAAx] dvd g (a + c)) (h2 : Γ ⊢[PRAAx] dvd g (b + d)) :
    Γ ⊢[PRAAx] g ≐ one := by
  have d1 : Γ ⊢[PRAAx] dvd g ((a + c) * b) := dvd_mul' hg b h1
  have d2 : Γ ⊢[PRAAx] dvd g ((b + d) * a) := dvd_mul' hg a h2
  exact eq_one_of_dvd_one hg (dvd_sub' hg (dvd_congr (med_alg hdet) d1) d2)

end LeanProofs.IPRA.DiophantineNumberTheory.FareyMediant
