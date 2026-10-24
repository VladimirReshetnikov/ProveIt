# Initial audit: the superseded n^2 F radius

The final implementation uses F^2. See `factorial_square_radius.md` and
`factorial_final_implementation_audit.md` for the final theorem and code review.

Audited the proposed scalar theorem and the concrete files
`agent_alt/hybrid/bootstrap_factorial.py` and `bootstrap_builder.py`.
This is an independent mathematical review, not a proof-assistant check.

## Scalar theorem

For n,F nonnegative integers, set R=n^2 F, C=binom(R+n,n),
N=(R+1)^n. Then

    F=ceil(N/C) iff F=n!.

Here C,N are positive. F=0 is impossible. For n=0 or n=1 the quotient
N/C is exactly1, so the result is immediate.

For n>=2 and F>=1, put K=n! and

    f=N/C=K product_(j=1)^n (R+1)/(R+j).

Writing each factor as 1-a_j, where a_j=(j-1)/(R+j), gives

    0 <= K-f <= K sum a_j
               < K n(n-1)/(2R)
               < K/(2F).

The standard product estimate follows by induction for a_j in [0,1].
The strict bound is valid because R>0 and at least j=2 contributes a
positive numerator with denominator strictly larger than R.

Thus f>K/2. If F=ceil(f), then F>=f>K/2, and consequently
K-f<K/(2F)<1. Since f<=K and K is integral, ceil(f)=K. Conversely,
if F=K, the same defect is less than1/2, so ceil(f)=K. There is no
assumption that F already has a factorial-sized lower bound.

## Concrete polynomial rows

The actual builder introduces nonnegative r,s and imposes

    N+C = C F+r+1,
    C = r+s+1.

Since C>0, these are exactly

    (F-1)C < N <= F C.

They therefore encode F=ceil(N/C). In particular the zero-output branch
is rejected by these rows, not by a tacit positive-F convention. The use
of a ceiling instead of a floor and the two occurrences of +1 are correct.

## A common radius for smaller factorials

The actual first argument is H; the next is t, with H>=t>=1. The builder
sets R=H^2 F_H and first uses the above certificate for H. Soundness gives
F_H=H!. For every 0<=n<=H, the same radius gives

    0 <= n!-(R+1)^n/binom(R+n,n)
       < n! n(n-1)/(2H^2 H!) < 1/2

when n>=2. The cases n=0,1 are exact. Consequently every subsequent
ceiling output is n!. This requires the first argument to dominate all
later arguments; it is not a valid generic override without that caller
contract. The concrete caller supplies

    H=(2+t+x+y+m+M0)^(2^23), t>=1,

which proves the required order. In fact H>=2, so R+1 is strictly above
one in all satisfying assignments after the first scalar theorem.

## No semantic dependency cycle

The inspected implementation defers binomial certificates. Their common
radix is q=2^(sum of their upper arguments)+1, and binomial coefficients
are selected as base-q digits of (q+1)^n. This method does not call a
factorial macro. Power calls are also finalized after the semantic
arguments and outputs have been fixed.

For completeness, choose the outer/refutation and CRT data first, compute
H and its actual factorial H!, then R, all remaining factorial and
binomial values, the common binomial radix, and the resulting power
values. The shared Pell frame can be chosen last. The numerical outputs
of powers and binomials do not depend on the size of that final frame.
Thus the apparent feedback R=H^2 F_H is resolved by the proved scalar
fixed-point lemma; it is not circular use of a factorial theorem inside
the binomial or power certificates.

For soundness, the inherited binomial and power interfaces must retain
their universal meaning for every satisfying nonnegative input tuple.
That is the existing dependency boundary. The new scalar argument does
not infer their meaning from finite examples or from intended values.

## Scope

The audit approves the local bootstrap lemma, exact ceiling rows, the
shared-radius contract of the concrete caller, and the absence of a new
semantic cycle in the inspected macro architecture. It does not by
itself audit the unrelated nine-column source projection, integer guard
reduction, expanded quartic census, or inherited C222/refutation bridge.
