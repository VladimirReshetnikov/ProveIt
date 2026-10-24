# Actual-row integer companions of the frozen 667-natural source

Let P be the literal residual system at
`projected-factorial-radius/both_source/equation.json`: 667 natural
coordinates, 585 quadratic rows. Its ordinary source/refutation proof is
frozen and unchanged. This candidate changes only the domain conversion
and subsequent exact algebraic projections. Every final variable ranges
over the **unrestricted integers**.

## 1. The new sign certificate is a theorem of the actual rows

Recompute the sign derivation from P itself. A selected set of 161 seed
coordinates is initially assumed nonnegative. Each of the other 506
coordinates is justified, in a stored order, by an exact original row
`c*x=F` or its negative, with c a positive integer and x absent from F.
There are two accepted forms:

1. F has nonnegative coefficients. In every monomial, all coordinates
   having odd exponent have already been proved nonnegative. Every
   even power is nonnegative for an arbitrary integer input. Thus F>=0.
2. The entire F is the exact square of an affine integer polynomial.
   Its square identity is independently expanded, so F>=0 without any
   sign assumptions on its operands.

In either case `c*x=F>=0` implies x>=0. Induction along the certificate
therefore proves all 667 coordinates nonnegative from the seed signs
and the actual row equalities, for arbitrary integer assignments.

The independent checker compares each purported row identity to P,
expands every affine square and checks that each needed sign is already
available. It rejects missing, repeated and changed inferences. The seed
selection is freshly computed from the new 667 system; no old guard
index is transferred by name. Variable metadata may inform a producer
heuristic, but is never a sign premise in the checker. Neither 161 nor
the final variable counts are claimed optimal, even within a rule class.

This inference precedes all factorial, power, binomial and CRT source
interpretations. Those theorems are only applied after a genuine natural
assignment has been recovered. In particular there is no appeal to the
intended meaning of a candidate factorial to prove its input's sign.

## 2. Private quadratic guards are exact over the integers

For each seed x introduce three fresh integer coordinates a,b,c and retain

```
x=a^2+b^2+c(c+1).                                 (1)
```

Every integer c has c(c+1)>=0, so (1) forces x>=0. Conversely, for
every natural x, `4x+1` is positive and is not of the exceptional
three-square form `4^a(8b+7)`. By Legendre it is a sum of three integer
squares. Modulo four exactly one summand is odd. Write the three squares
as `(2c+1)^2,(2a)^2,(2b)^2`; subtracting one and dividing by four gives
(1). Hence every natural seed has such witnesses. Different seeds have
private auxiliaries, so all witnesses can be chosen simultaneously.

Retain every original row of P verbatim, append all 161 guards, and
declare all coordinates unrestricted integers. Call the result Q.
It has 1,150 coordinates and 746 quadratic rows. Any integer zero of Q
has nonnegative seed coordinates by (1), then all original coordinates
are natural by Section 1 and satisfy P. Conversely every natural zero
of P extends to an integer zero of Q by the preceding guard witnesses.
Thus zero existence is equivalent in both directions.

No substitution into an old residual is used in this conversion. Every
residual is still quadratic and its sum of squares is quartic, rather
than degree eight. Completeness uses no search bound on square witnesses.

## 3. Signed monic projection is applied only after the domain conversion

At a current stage a residual is exactly `v-f(z)` or its negative,
where f is an integer polynomial independent of v and in the remaining
coordinates. Then for every integer assignment to z it defines the
unique integer v=f(z). Substitute f into **every** other residual and
delete the defining row. The certificate permits the step only when
every resulting residual has degree at most two. It drops another row
only if its entire substituted polynomial is identically zero.

Every step is independently replayed as an exact polynomial identity.
The certificate saves its full restoring polynomial and elimination
order. Reversing that order restores later-deleted coordinates before
they are needed by an earlier definition. Since all restoring polynomials
have integer coefficients, there is no integrality or denominator
condition. They may have negative coefficients and may have negative
values; the domain at this stage is the unrestricted integers.

All four supplied certificates have `unconstrained_removed=[]`. Therefore
they give a bijection between the child zero set and the entire augmented
integer-parent zero set, not merely an existential projection with some
free coordinates silently discarded. All original guards undergo the
same substitutions as all other rows. A removed guard is either a monic
definition satisfied by restoration or an exact zero identity; it is
never omitted by a separate sign-handling path.

For soundness of a final child zero, first restore **all** of Q, with
integer values. Only then use Q's guard equations and the original
ordered sign certificate to recover a natural zero of P. Positivity is
not assumed during signed restoration. This order prevents an invalid
inference that a signed restoring polynomial preserves natural numbers.

## 4. Final equations and exact finite evidence

Each child equation is the sum of the squares of its complete listed
quadratic residuals. Over the integers such a sum is zero if and only if
every residual is zero. Independent full expansion checks every collected
integer coefficient, exact degree four and occurrence of every coordinate.

| Integer variables | Quadratic rows | Collected terms | Height |
|---:|---:|---:|---:|
| 862 | 458 | 11,245 | 2,445,790,974,704 |
| 863 | 459 | 9,909 | 2,445,790,974,704 |
| 865 | 461 | 9,814 | 2,445,790,974,704 |
| 891 | 487 | 6,797 | 63,905,891 |

The 863 point improves the accepted 888 point's coordinates, rows and
terms at the same height. The 891 point improves the accepted 917 point
in all four listed measures. The 862 and 865 points retain their genuine
coordinate/term tradeoffs. A support64 probe had 872 coordinates and
157,852 terms at the larger height, and is dominated; its literal output
is not retained. Support caps select candidate definitions, never truncate
any polynomial term. No global or worldwide simplicity claim follows.

The source engine is read from the immutable accepted 407 archive,
SHA256 `59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59`.
Only its inspected ordinary integer arithmetic files are used. The
independent checker imports the pinned row/sign, projection and polynomial
verifiers; it imports no sign selector, optimizer or producer. It also
restores three off-source signed assignments per child and compares every
surviving row and every deleted defining/zero row. These finite diagnostics
supplement the exact unbounded identities above; they do not decide
whether the equation has a zero.

All ordinary source/refutation semantics are inherited from P. No natural
parent, incoming archive or frozen projection is changed. No Lean, native
coefficient generator or historical H10 emitter is run. This work neither
proves consistency nor supplies a new internal object-ZFC derivation.
