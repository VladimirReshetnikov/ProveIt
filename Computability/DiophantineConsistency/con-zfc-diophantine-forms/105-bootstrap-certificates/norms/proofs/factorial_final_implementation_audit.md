# Independent review of the final square-radius implementation

The final macro and caller were reviewed after the default radius was
changed to `F_H^2`. The final caller additionally exposes the already
proved `--radius linear` alternative, with radius `H^2 F_H`; its argument
parser allows exactly `square` or `linear`, defaulting to `square`. `FACTORIAL_IMPLEMENTATION_PINS.json` records the exact inspected
source and parent781 polynomial hashes. Paths there are relative to the
separate direct-certificate component. The arithmetic proof valid for
every n is in `factorial_square_radius.md`.

## Literal macro

`bootstrap_factorial.py` creates its first output F_H, stores the single
radius `self.square(out)`, and reuses that radius for every later factorial.
For an argument n and its output F, it requests

    C=binom(F_H^2+n,n), N=(F_H^2+1)^n

and creates the nonnegative rows

    N+C=C F+r+1, C=r+s+1.

The rows exactly assert `(F-1)C<N<=FC`, once the universal binomial/power
interfaces have supplied C,N. For the first call n=H,F=F_H, the proved
fixed-point lemma forces F_H=H!. Every later argument n<=H is then handled
by the common-radius bound. No additional precision-power certificate is
requested.

## Actual caller contract

The caller first requests H!, then t! through the inherited
`moduli_product(t,F_H)` method. The macro inventory and radius certificate
contain exactly these two calls, sharing one radius. It defines

    t=t0+1, m=m0+1,
    R0=2+t+x+y+m+M0,
    H=R0^(2^23).

All outer inputs are natural, so R0>=4 and H>=t>=1. In particular H>=5.
The first-argument dominance obligation is therefore discharged by the
actual caller; it is not silently assumed by a general-purpose factorial
routine.

## Positivity before applying the power theorem

The final source uses the inherited shared positive-power compiler. Its
base/exponent positivity conditions must be established before invoking
its semantic theorem.

The factorial numerator base F_H^2+1 is positive even if F_H were zero;
its exponent is H or t, both positive. All binomial upper and lower
arguments appearing as power exponents are positive in this caller. The
common binomial radix is a natural power output plus one, so both it and
its successor are positive independently of the intended output values.
The other fixed or carrier bases are positive sums.

There is one base that needs an equation rather than syntax:
`moduli_product(t,F_H)` requests `power(F_H,t)`. Its actual shared-base row
is

    2 A F_H = T_base+F_H^2+1,

where T_base is nonnegative. If F_H=0, the left side is zero and the right
side is at least one, a contradiction. Thus F_H>0 follows before either
power correctness or factorial correctness is used. This removes the
potential circular positivity premise.

The factorial binomial satisfies F_H^2+n>=n, so its exact semantic value
C is positive. The ceiling rows and N>0 would independently reject a
zero first output after arithmetic recovery.

## Why the shared frame creates no new cycle

For soundness, the shared power frame and radix-digit binomial certificate
have their inherited universal semantics on every satisfying tuple with
the just-established positive inputs. That semantics is applied first.
The fixed-point theorem then identifies F_H. One must not assume the
intended factorial value in order to prove either universal arithmetic
interface; the inspected code introduces no such assumption.

For completeness, start with a source/refutation witness and its outer
parameters. Compute H, F_H=H!, R=F_H^2, the other genuine factorials,
the ordinary finite modulus product, and then the canonical CRT data.
All semantic binomial arguments and values are now fixed. Deferred
binomials use

    q=2^(sum of distinct upper arguments)+1.

All upper arguments are already fixed at this point. Consequently q
strictly exceeds2^n for every encoded binomial with upper argument n.
Compute q and all associated power values. Choose a sufficiently large
shared Pell frame last. Power and binomial outputs are their ordinary
arithmetic values and do not depend on that final frame's size.

The numerical feedback R=F_H^2 is resolved by the proved fixed-point
lemma. The frame is an auxiliary certificate for already chosen arithmetic
values, not a definition of those values. No additional semantic cycle
was found.

## Scope of this approval

The local square-radius factorial theorem, exact ceiling rows, actual
argument order, shared-radius reuse, positivity obligations and semantic
construction order are approved by this independent ordinary mathematical
review. Exact diagnostics pass normally and with Python assertions disabled;
the proof does not depend on them.

This review does not independently certify the nine-column source
projection, affine contractions, integer guard elimination, expanded
quartic census or C222-to-ZFC-refutation bridge. Those remain the separately
identified proofs and checks of the direct-certificate component. This is
not an external human review, a Lean/Rocq certificate or an encoded
internal-ZFC derivation.

## Retained linear-radius alternative

The one conditional radius expression chooses `square(out)` in square
mode and `square(n)*out` in linear mode. The latter is precisely the
initially audited first-argument radius H^2 F_H; its full local proof is
retained in `factorial_bootstrap_audit.md`. The ceiling rows, common radius
reuse and caller order are unchanged. Both branches therefore have the
same factorial semantics. The conditional is a finite compile-time choice
between two literal polynomials; it is not an unencoded arithmetic branch
inside an equation. The square-mode parent781 literal remains the pinned
main object.
