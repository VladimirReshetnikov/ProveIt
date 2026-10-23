# Parent-quartic review: no certified reduction below 31 variables

## Outcome

The pinned 31-positive-variable parent remains a system of 22 quadratic
equations, with a degree-four sum of squares. This investigation does not
claim a 30-variable quartic, a new consistency equivalence, or any global
minimality result. The published 34/37 fifty-integer quartics reuse the
same packing-register elimination and leave this positive parent unchanged.

The exact symbolic audit enumerates all 23 substitutions obtained by solving
one existing residual for a variable with coefficient +1 or -1. Every such
direct substitution leaves at least one cubic or quartic residual. The
resulting direct SOS therefore has degree six or eight, not four. This is
only an obstruction to that explicitly enumerated rewriting method. It
does not exclude simultaneous substitutions, new identities, or a different
Pell encoding. The audit supplies a uniformly nonzero leading coefficient
for every listed degree claim, with the four compiler ports positive.

## A concrete but unresolved 30-variable route

Write q=beta J+1, C=q-F-alpha and retain L=q^2-1. In the shifted transport
convention, the parent has

    X=wq,
    (K0+w)C=F+z(q-1).

Multiplying the second equation by q and using the two retained identities
gives the quadratic equation

    (K0 q+X)C=qF+z(L+1-q).

Deleting w and X=wq would leave 30 coordinates and 21 quadratic equations.
The exact difference identity, verified by the script, is

    T_new-q T = (X-qw)C-z(L+1-q^2).

The reverse direction needs q|X in order to restore the integer w=X/q.
The new equation proves only q|XC. Cancelling C is unjustified without
gcd(C,q)=1 or an independently proved divisibility theorem. Also, before
q|X is available, the source proof's bound X>=q cannot simply be inherited;
an affine positive replacement X=q+x could enforce that bound without a
new coordinate, but would not solve the divisibility problem.

There is an elementary counterexample to the *cancellation step*, not to
the complete 30-variable candidate: q=4,C=2,X=6,F=1,alpha=1,z=2,K0=2,L=15
satisfies the new transport and L=q^2-1, although q does not divide X.
These are toy ports, not the authentic fixed compiler tuple, and this is
not a zero of the full Pell system. No full counterexample is asserted.

The authentic native decoder eventually proves C=1 modulo 4. Its low-bit
condition is (C-1) AND (MC J+1)=0 with MC=2 modulo 4. However, the reviewed
soundness proof reaches the native mask conditions only after recovering
X=2^R, using q|X to establish that q is a power of two, and then obtaining
q=B^N. Using that late C-odd conclusion to justify the earlier divisibility
would be circular. Merely forcing C odd would still not exclude odd prime
factors of q without an additional argument.

The exact open obligation is therefore: prove q|X for every solution of
the relaxed system using facts established before the native decoder, or
construct a comparably small interface that enforces the required coprimality.
No such proof was found in this investigation.

## Alternative norm lift

The identity Delta=(a+2)^2-1 allows replacing Delta and F2 by new products
u=(a+2)c and t=(a+2)f. The two norms become D^2=u^2-c^2+1 and
I^2=t^2-(a+2)^2-f^2+1. But u and t cost the same two coordinates that
Delta and F2 saved. C2 is still needed by I=i C2; replacing it by a new
product v=ic is again count-neutral. No variable saving follows from these
identities alone.

## Reproduction and source boundary

Run `python3 audit_eliminations.py` with SymPy installed. It reads the
pinned comparison circuit as inert JSON; no upstream program is executed.
Outputs are ELIMINATION_AUDIT.json and SOURCE_PINS.json. All fetched sources
have exact Git-blob SHA-1 and SHA-256 checks against repository commit
22e75dd6b87b1b199bb08c778d7cf075ae5aae08. The source transport convention is
explicitly the shifted one. The ordinary blank proof is inspected for the
ordering of X, q and native-mask recovery; computational tests do not replace
its unbounded Pell, compiler or K215 theorems.
