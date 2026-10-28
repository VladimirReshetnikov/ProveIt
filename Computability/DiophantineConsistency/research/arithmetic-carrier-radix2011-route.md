# Recovering the actual binary radix after literal soundness

Read-only route, 27 October 2026. This follows the literal soundness pair
currently being implemented and the accepted internal power-recovery
theorem. It is not an implemented or compiled proof, and does not close
the native word/carry/tableau bridge.

For positive literal coordinates, compose the derived five additive
equations with `maintained_power` to get X=Exp.exp R with X=w*q and
q=beta*J+1. Current beta is exactly 2^94517-1. The next substantive scalar
endpoint should derive an internal positive N with

```
q = Exp.exp (94517*N)
94517*N <= R
w = Exp.exp (R-94517*N).
```

No binary radix, exponent divisibility, repunit or desired source rank
may be supplied as an extra premise of the concrete literal-zero client.

## Existing internal number theory suffices for radix recovery

Foundation already has `Pow2.of_dvd`, `exp_pow2`,
`exponential_of_pow2`, `exp_of_exponential`, `exp_add`, `exp_monotone`,
`exp_monotone_le` and `nat_cast_exp`. These concern arbitrary arithmetic
model values, rather than only standard naturals.

Since q divides X=Exp.exp R, `Pow2.of_dvd` gives Pow2 q. Hence u=log q
satisfies Exp.exp u=q. Positivity of w gives q<=X, so u<=R. The actual
addition identity for exponentials and the justified subtraction
u+(R-u)=R then give w=Exp.exp(R-u), by positive q cancellation.

For width d>=2, write beta=Exp.exp d-1 and retain beta+1=Exp.exp d.
Genuine Sigma1 successor induction supplies a natural quotient z with

```
Exp.exp (d*n) = 1+beta*z
```

for every internal n. At a successor multiply by beta+1; the new quotient
is 1+z+beta*z. This avoids introducing arbitrary-base internal powers.

Divide u by d: u=d*n+r, r<d. The preceding identity and exp_add imply
Exp.exp u has the same remainder modulo beta as Exp.exp r. But the actual
q=beta*J+1 has remainder 1, because beta>1. Also r<d gives
Exp.exp r<beta+1, hence Exp.exp r<=beta. Equality with beta would give
remainder 0, a contradiction. Therefore Exp.exp r<beta, so its remainder
is itself and it equals1. Exponential injectivity gives r=0.

J>0 gives q>=beta+1=Exp.exp d, hence d<=u and n>0. Specialize to the
actual fixed d=94517 using the existing natural-cast exponential identity,
with the standard finite equality 47*2011=94517. Keep the huge coefficient
opaque; do not expand its decimal or binary numeral in a tactic.

An optional repunit value `(Exp.exp(d*N)-1)/beta` can be bound to the
original J by exact cancellation. A separate primitive-recursive repunit
graph is needed only if subsequent word coding actually uses that graph.
Do not assume a complexity property of a choice-defined selector.

## Further internal obligations

This scalar result still precedes the actual binary-population and
fixed-mask word/carry interpretation. The external native proofs use
finite words, residue-indexed arrays and binomial valuation arguments.
Their arbitrary-length internal counterparts need represented words and
genuine definable induction; an externally finite `ZMod N` array cannot
simply be instantiated at a nonstandard internal N.

The converse must likewise construct internally encoded tableaux and
rank-forced scalar packings from an actual internal halting history, then
the simultaneous outer and auxiliary Pell witnesses. The newly derived
strong seed at R*ycoord(R,a) removes one divisibility search from that
construction, but does not discharge these population/word obligations.
They remain part of the polynomial connection in the HA ledger.
