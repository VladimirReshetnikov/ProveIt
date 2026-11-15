/--
Bridge outline for the current ProveIt ConciseIPRA development.

STATUS: the generic transfer theorem below uses an existing proved theorem in
`ConciseIPRA.NativeBiInterpretation`.  The missing work is the construction of
the closed arithmetic formula `GE` and its derivation in `PRAAx`, as detailed
in FORMALIZATION.md and the paper.
-/

import ConciseIPRA.NativeBiInterpretation

namespace LeanProofs.ConciseIPRA.GoldbachEuler

open Syn
open scoped Fm

/-- Any closed theorem proved in the ordinary iPRA presentation transfers to
    the native scalar calculus used by ConciseIPRA. -/
theorem transfer_closed_to_native {φ : Fm PTm 0}
    (h : ([] : List (Fm PTm 0)) ⊢[PRAAx] φ) :
    NPrf [] (NFm.ofPRA φ) :=
  (pra_iff_native (Γ := []) (φ := φ)).mp h

/-!
Instantiation plan:

1. Build primitive-recursive symbols/terms for
   `pow`, bounded perfect-power search, prime valuation, gcd fold, canonical
   root/exponent, rational numerator/denominator accumulation, and
   `B(k) = 2^(2*(k+1)^2)`.

2. Let `GE : Fm PTm 0` be the universal closure of the natural-number formula

     B(k) <= N ->
       Num(N) <= Den(N) /\
       (2^k - 1) * Den(N) <= 2^k * Num(N).

   The second conjunct is exactly `S_N >= 1 - 2^-k`; the first is `S_N <= 1`.

3. Prove

     goldbachEuler_iPRA : ([] : List (Fm PTm 0)) ⊢[PRAAx] GE

   using only defining equations and quantifier-free induction.

4. Obtain the native theorem with

     exact transfer_closed_to_native goldbachEuler_iPRA

The current repository already proves `pra_iff_native`, so no new
bi-interpretation argument is required.
-/

end LeanProofs.ConciseIPRA.GoldbachEuler
