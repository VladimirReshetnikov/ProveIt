# Internal radix exponent alignment

Proposed pair: `ArithmeticRadixAlignment` and Checks. The sole mathematical
inputs are arbitrary internal arithmetic values in an IΣ1 model. Imports
are exactly Foundation's existing Exponential.Log and Mathlib.Tactic.Ring;
no prerequisite refresh is proposed.

The generic endpoint takes d>=2, J>0 and

```
Exp.exp R = w*((Exp.exp d-1)*J+1).
```

It must derive an internal N>0 such that q=(Exp.exp d-1)*J+1 equals
Exp.exp(d*N), d*N<=R and w=Exp.exp(R-d*N). Positive w, a power-of-two
radix and divisibility of the exponent are conclusions, not extra premises.

First, genuine Sigma1 induction gives a nonnegative quotient z with
Exp.exp(d*n)=1+(Exp.exp d-1)*z. Divide an arbitrary exponent u by d;
exp_add and this quotient identify the residue of Exp.exp u modulo beta
with the residue of Exp.exp(u%d), where beta=Exp.exp d-1. If the former
is beta*J+1, this remainder is1. Since u%d<d, the remaining power is at
most beta; equality gives remainder0 and is impossible. It is therefore
1, giving u%d=0 by exponential injectivity. J>0 forces N>0.

For the factor endpoint, q divides Exp.exp R. Foundation's existing
Pow2.of_dvd and exponential_of_pow2 give q=Exp.exp(log q). Apply exponent
alignment, use positivity of the actual factorization to derive w>0 and
d*N<=R, then use exp_add and positive q cancellation to derive the exact
remaining exponential factor. No external prime-factorization theorem,
standard-index assumption, arbitrary-base internal power or desired
exponent-divisibility oracle is used.

The later concrete current-equation client must first derive the five norms
and X=Exp.exp R from its literal zero, then apply this result at d=94517
and the actual fixed beta. Those concrete premises are not proved by this
generic pair. Native population, fixed-mask word/carry/tableau soundness,
the simultaneous converse witnesses and final PA/HA assembly remain open.

The exact source/header/provider inventory is audited before compilation.
Both final inputs and the driver are read completely; both inputs are
snapshotted before the first command. Fresh capped regular outputs,
all attempts, reserve guards and a distinct peer replay are required.
