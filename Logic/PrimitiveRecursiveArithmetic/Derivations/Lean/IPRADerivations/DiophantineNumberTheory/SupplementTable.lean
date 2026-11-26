import IPRADerivations.DiophantineNumberTheory.SecondSupplement
import IPRADerivations.DiophantineNumberTheory.QuadraticSupplements
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Core.CertificateTactics
import IPRADerivations.Core.Header

/-!
# The supplementary signs by `p mod 8`

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex`, §"Supplementary laws
and witnesses", the table after `eq:two`: "The resulting signs can be read directly from `p`."

    p mod 8     1    3    5    7
    (−1/p)     +1   −1   +1   −1
    (2/p)      +1   −1   −1   +1

With `signBit p a` the bit of "`a` is not a square modulo `p`" (`0` for the sign `+1`, `1` for the sign `−1`), for
a prime `p`:

* `minus_of`, `two_of`: for `p = 2h + 1`, `signBit p (p − 1) = par h`, and `signBit p 2 = par X` whenever
  `h (h + 1) = 2 X` (the two laws `QuadraticSupplements.minus_one_law`, `SecondSupplement.two_law` with the
  half `⌊p/2⌋` replaced by the given `h`);
* **`table_one`**: `p = 8t + 1` gives the bits `0`, `0`;
* **`table_three`**: `p = 8t + 3` gives the bits `1`, `1`;
* **`table_five`**: `p = 8t + 5` gives the bits `0`, `1`;
* **`table_seven`**: `p = 8t + 7` gives the bits `1`, `0`.

In each case `h = 4t + r` and `h (h + 1)/2` is written as `2Y` or `2Y + 1` with an explicit polynomial `Y` in `t`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.SupplementTable

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble (two_pos')
open LeanProofs.IPRA.DiophantineNumberTheory.QuadraticReciprocityGoal (signBit)
open LeanProofs.IPRA.DiophantineNumberTheory.QuadraticSupplements (minus_one_law)
open LeanProofs.IPRA.DiophantineNumberTheory.SecondSupplement (two_law)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The laws at a given half -/

theorem half_alg {p H h : PTm n} (e : Γ ⊢[PRAAx] p ≐ two * H + one) (eh : Γ ⊢[PRAAx] p ≐ two * h + one) :
    Γ ⊢[PRAAx] two * H ≐ two * h := by
  ipra_lc natEq eh - natEq e

/-- `p = 2h + 1` is odd and `⌊p/2⌋ = h`. -/
theorem half_of {p h : PTm n} (eh : Γ ⊢[PRAAx] p ≐ two * h + one) :
    Γ ⊢[PRAAx] (par p ≐ one) ⋏ (half p ≐ h) := by
  have hodd : Γ ⊢[PRAAx] par p ≐ one := (congrAp1 parF eh).eqTrans (par_double_succ h)
  exact .andI hodd (Combinatorics.BinomialIdentities.mul_cancel two_pos' (half_alg (odd_of hodd) eh))

/-- `(−1/p)` at `p = 2h + 1`: the bit is `par h`. -/
theorem minus_of {p h : PTm n} (hp : Γ ⊢[PRAAx] prime p) (eh : Γ ⊢[PRAAx] p ≐ two * h + one) :
    Γ ⊢[PRAAx] signBit p (pred p) ≐ par h :=
  (minus_one_law hp (Prf.andE₁ (half_of eh))).eqTrans (congrAp1 parF (Prf.andE₂ (half_of eh)))

/-- `(2/p)` at `p = 2h + 1`: the bit is `par X` when `h (h + 1) = 2 X`. -/
theorem two_of {p h X : PTm n} (hp : Γ ⊢[PRAAx] prime p) (eh : Γ ⊢[PRAAx] p ≐ two * h + one)
    (eX : Γ ⊢[PRAAx] h * succ h ≐ two * X + zero) : Γ ⊢[PRAAx] signBit p two ≐ par X := by
  have hh := Prf.andE₂ (half_of eh)
  have q : Γ ⊢[PRAAx] quo (half p * succ (half p)) two ≐ X :=
    quo_eq two_pos' ((congrMul hh (congrSucc hh)).eqTrans eX) (zero_lt_succ _)
  exact (two_law hp (Prf.andE₁ (half_of eh))).eqTrans (congrAp1 parF q)

/-! ## The four residues -/

theorem h1 {p t : PTm n} (e : Γ ⊢[PRAAx] p ≐ num 8 * t + one) : Γ ⊢[PRAAx] p ≐ two * (two * (two * t)) + one := by
  ipra_lc natEq e

theorem x1 (t : PTm n) :
    Γ ⊢[PRAAx] (two * (two * t)) * succ (two * (two * t)) ≐ two * (two * (t * (num 4 * t + one))) + zero := by
  ipra_lc

/-- **`p ≡ 1 (mod 8)`**: `−1` and `2` are squares modulo `p`. -/
theorem table_one {p t : PTm n} (hp : Γ ⊢[PRAAx] prime p) (e : Γ ⊢[PRAAx] p ≐ num 8 * t + one) :
    Γ ⊢[PRAAx] (signBit p (pred p) ≐ zero) ⋏ (signBit p two ≐ zero) :=
  .andI ((minus_of hp (h1 e)).eqTrans (par_double _))
    ((two_of hp (h1 e) (x1 t)).eqTrans (par_double _))

theorem h3 {p t : PTm n} (e : Γ ⊢[PRAAx] p ≐ num 8 * t + num 3) :
    Γ ⊢[PRAAx] p ≐ two * (two * (two * t) + one) + one := by
  ipra_lc natEq e

theorem x3 (t : PTm n) :
    Γ ⊢[PRAAx] (two * (two * t) + one) * succ (two * (two * t) + one) ≐
      two * (two * (num 4 * (t * t) + num 3 * t) + one) + zero := by
  ipra_lc

/-- **`p ≡ 3 (mod 8)`**: neither `−1` nor `2` is a square modulo `p`. -/
theorem table_three {p t : PTm n} (hp : Γ ⊢[PRAAx] prime p) (e : Γ ⊢[PRAAx] p ≐ num 8 * t + num 3) :
    Γ ⊢[PRAAx] (signBit p (pred p) ≐ one) ⋏ (signBit p two ≐ one) :=
  .andI ((minus_of hp (h3 e)).eqTrans (par_double_succ _))
    ((two_of hp (h3 e) (x3 t)).eqTrans (par_double_succ _))

theorem h5 {p t : PTm n} (e : Γ ⊢[PRAAx] p ≐ num 8 * t + num 5) :
    Γ ⊢[PRAAx] p ≐ two * (two * (two * t + one)) + one := by
  ipra_lc natEq e

theorem x5 (t : PTm n) :
    Γ ⊢[PRAAx] (two * (two * t + one)) * succ (two * (two * t + one)) ≐
      two * (two * (num 4 * (t * t) + num 5 * t + one) + one) + zero := by
  ipra_lc

/-- **`p ≡ 5 (mod 8)`**: `−1` is a square modulo `p` and `2` is not. -/
theorem table_five {p t : PTm n} (hp : Γ ⊢[PRAAx] prime p) (e : Γ ⊢[PRAAx] p ≐ num 8 * t + num 5) :
    Γ ⊢[PRAAx] (signBit p (pred p) ≐ zero) ⋏ (signBit p two ≐ one) :=
  .andI ((minus_of hp (h5 e)).eqTrans (par_double _))
    ((two_of hp (h5 e) (x5 t)).eqTrans (par_double_succ _))

theorem h7 {p t : PTm n} (e : Γ ⊢[PRAAx] p ≐ num 8 * t + num 7) :
    Γ ⊢[PRAAx] p ≐ two * (two * (two * t + one) + one) + one := by
  ipra_lc natEq e

theorem x7 (t : PTm n) :
    Γ ⊢[PRAAx] (two * (two * t + one) + one) * succ (two * (two * t + one) + one) ≐
      two * (two * ((num 4 * t + num 3) * (t + one))) + zero := by
  ipra_lc

/-- **`p ≡ 7 (mod 8)`**: `2` is a square modulo `p` and `−1` is not. -/
theorem table_seven {p t : PTm n} (hp : Γ ⊢[PRAAx] prime p) (e : Γ ⊢[PRAAx] p ≐ num 8 * t + num 7) :
    Γ ⊢[PRAAx] (signBit p (pred p) ≐ one) ⋏ (signBit p two ≐ zero) :=
  .andI ((minus_of hp (h7 e)).eqTrans (par_double_succ _))
    ((two_of hp (h7 e) (x7 t)).eqTrans (par_double _))

end LeanProofs.IPRA.DiophantineNumberTheory.SupplementTable
