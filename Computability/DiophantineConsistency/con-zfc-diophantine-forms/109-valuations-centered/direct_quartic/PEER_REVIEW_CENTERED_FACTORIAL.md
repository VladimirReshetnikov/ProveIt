# Independent review of the centered factorial replacement

## Verdict

No gap was found in the new centered-factorial theorem, its replacement of the
two factorial graphs, the odd-horizon completeness argument, or the dependency
order proving that the shared radix is large enough. The supplied exact
natural and integer polynomials pass a fresh complete reproduction and the
independent domain/projection/expansion checkers. This is an ordinary review
of the new arithmetic change composed with the named inherited C222,
simultaneous-power and CRT interfaces; it is not a reproof of those entire
inherited developments or a new Lean/internal-ZFC artifact.

The mathematical review read centered_factorial_proof.md and the actual new
builder and verifier. It also inspected the inherited moduli_product source,
shared-radix source, exact integer-domain checker, and integer projection
checker. The parent truth-padding statements were checked in report.tex and
its retained calibration notes.

## The factorial fixed point

The ratio identity is exact: pairing f+1,...,f+n around
m=f+(n+1)/2 produces

    R=n! / product_d(1−d²/m²).

The positive squared deviations sum to n(n²−1)/24 for both parities of n.
All factors are strictly positive even when f=0. Thus R>=n! is available
before the radius estimate and before claiming that f is a factorial. At a
fixed point this already forces f>=n!, which is the crucial noncircular step.
The induction n(n²−1)<=4n! and product lower bound then yield

    0<=R−n!<=n!/(6n!−1)<1.

The separate n=0 and n=1 cases are exactly1, including f=0. Therefore no false
small fixed point or zero-candidate branch remains. For odd n=2h+1 the powers
of2 cancel exactly, and the two remainder rows are precisely floor(V/C)=f
with C>0.

## Digits before factorial correctness

The lower-digit estimate binom(f+n,j)<=m^n is valid for every candidate f>=0
and every0<=j<=n, without assuming f=n!. Its separate j=0,1,2,3 cases cover
the places where the elementary2^j<=j! estimate fails. For n=j=3, the centered
product bound supplies the missing case directly. Hence the proposed factorial
output cannot create a carry that invalidates the fixed-point argument.

The larger odd horizon t=2t0+1 preserves existence by adding truth-padding
rows, whose state transition is the identity. The horizon is chosen before
the carrier and accumulator. H=2R^D+1 strictly exceeds the unchanged local
majorant R^D, so the changed parity introduces no new upper-bound obligation.
The actual builder applies these literal substitutions to both factorial
inputs and records their half-indices.

## Shared radix and the remaining binomial graphs

Using q=B(V_H+V_t+1) is essential and correct. The other candidate factorial
is not bounded by the first one before validation; the sum handles both.
The shared-power base row excludes q=0 over naturals, so B>=1 and q exceeds
both factorial numerators. The review confirms the proof order: recover
positive powers, then both factorial binomials, then T=H! and F=t!, then
the remaining product and range binomials.

The actual retained moduli_product rows give

    modulus+1=TQ,
    modulus=B+slack+1,

hence B<TQ before invoking the product formula. The aggregate source row is
8B=sum(A_j)+slack, giving each positive column A_j<=8B. These are literal
nonnegative-row consequences, not assumptions about the desired CRT product.
With the now-established T=H!, the estimates Q+t<=T^(2t+2) and
A_j<T^(2t+3) follow as written. R>=4 and t<=R imply
R(2R+3)<=R^4<=H. Consequently every still-uninterpreted lower digit is
bounded by T^H<V_H<q. The deferred radix cycle is therefore closed.
For completeness, the genuine arithmetic and CRT values are selected before
the common Pell frame, so no cofinal witness is selected prematurely.

## Integer domain restoration

The actual integer conversion guards159 of the663 natural source coordinates
by rows x=a²+b²+c(c+1). These imply x>=0 over all integers. Conversely every
nonnegative x has this representation: Legendre's three-square theorem applied
to4x+1 gives exactly one odd square and two even squares modulo4, and the
identity follows after reordering and dividing by4.

The independent domain checker verifies every unchanged source residual,
every guard's three fresh variables, and504 further nonnegativity deductions
from the actual source rows. It restores all663 source coordinates, rather
than only selected semantic ports. The287 subsequent monic eliminations are
exact substitutions over unrestricted integers and have polynomial reverse
restorations; no unproved sign condition is applied to those restorations.
All remaining residuals stay quadratic, so their sum of squares is quartic.

## Fresh finite evidence

A fresh full invocation of centered_verify.py completed successfully; its
unchanged receipt is PEER_REPLAY_CENTERED_FACTORIAL.json. It independently
checks the two factorial interfaces,21 positive-power graphs,15 seed
indices, one derived index, three binomial graphs and eight range-divisibility
graphs. It rejects all three supplied arithmetic mutations and reproduces all
14 defining files from a fresh temporary build.

The review separately counted the literal final JSON files:

| Domain | Variables | Quadratic residuals | Exact SOS degree | Terms | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Nonnegative integers |395|313|4|8292|83843425|
| Unrestricted integers |853|453|4|9747|2445790974704|

The finite factorial fixtures and graph checks corroborate the transcription.
They do not replace the general fixed-point proof, the unbounded shared-Pell
and CRT theorems, or the inherited C222/refutation calibration.
