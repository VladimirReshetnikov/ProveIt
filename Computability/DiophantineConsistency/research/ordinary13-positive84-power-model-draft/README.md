# Proposed direct power recovery for the positive 84 graph

This is an **unelaborated** source proposal, not a proof that the 84 graph's
no-zero assertion is equivalent to consistency. It gives a conditional path
to `X=2^R` and then `q | X` without using 84→83 or assuming `q | X`. The
explicit `ExactPowerGraphCut` and the complete Lean/provider/axiom validation
remain open.

`ExactPowerFacts` specifies one natural graph rank R, first Pell index n,
actual oriented main root, and first-index quotient w for the same positive
84 valuation. Its hypotheses include the two coordinate equations at those
same indices, `2*n=R+1`, the graph rank formula, and the actual extra-term
carrier balance

```
k=R+1+4*X*Y²*w,
U*main+H*k=U*(X+a*c)+H*(U*gamma+X*Y*q+R+1),
Y=q³*s, U=Y*q², a=X*Y+Y, H=3+4*a.
```

The previous conditional source obtains `q | 3X` from that balance; it needs
neither `q | X` nor a coprimality assumption. Compact beta gives `q≥46`, so
`q | 3X` and `X>0` imply `X≥16`. The local growth proposal uses the same first
and main Pell coordinates and the existing `power_bound` to obtain `2^R<Y`.
It uses explicit model predecessor algebra rather than `omega` on an abstract
model. The existing q-balance source converts the extra-term carrier to

```
q*(main+H*W)=q*(X+a*c+H*gamma)+H*X,
W=4*X*q*s*w.
```

The sign-free oriented-power helper then proposes `X=2^R` using that balance
and the same x/y coordinates. Its theorem body is copied verbatim from the
pinned earlier source into a standalone module: this avoids importing the
other earlier growth lemmas, which contain abstract-model `omega` calls.
The copied proof, its tactics and all its actual providers are still
unelaborated. The compact Mersenne cancellation in the preceding divisibility
packet then proposes `q | X`. The final source theorem makes that result
conditional on `ExactPowerGraphCut`.

To discharge the cut from the actual 84 zero, the remaining graph work must
bind the first norm and signed carrier, extract its natural first Pell root
and early index, establish the compact rank window and represented signed
rank, bind and orient the **extra-term** main root, and supply the strong and
direct-auxiliary hypotheses for the exact-index theorem using the same
witnesses. Its main Pell x and y coordinates must both describe that same
oriented root. The prior 84→87 reverse-root proposal and 12-input original
literal chain are an alternative route with their own open obligations;
this proposal does not use either route, nor the no-extra-term eta-natural
power theorem that assumes an X quotient.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-positive84-power-model-draft/check.py
```

The checker pins the graph and source dependencies, checks exact graph rows
and the verbatim helper body, and runs bounded q-balance and lower-bound
controls. These checks do not elaborate Lean or establish a graph fact in all
models, provider provenance, or the physical PDF connection.
