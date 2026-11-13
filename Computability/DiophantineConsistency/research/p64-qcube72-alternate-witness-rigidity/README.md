# A constraint on changing witnesses in the 72-to-76Y direction

This is a source-based and standard-integer investigation, not a Lean theorem
for the 72-to-76Y implication. It gives a necessary condition on a proposed
witness transformation; it neither constructs a 76Y witness nor rules out
one with changed parameters.

## The main carrier is rigid at fixed scale

For a positive 72-graph zero, the checked
[`FreeMainGraphMainRoot.main_root`](../p64-qcube72-main-root-draft/FreeMainGraphMainRoot.lean)
extracts a positive-scale main equation and carrier

```
Y=q³s, U=Y², X=wq, a=(X+1)Y, H=4a+3, Delta=a²+H,
g²=1+Delta*c²,    U*g=U*(X+a*c)+H*h,
c=(eta+zeta)*Y+eta,    k=eta+zeta.
```

The checker for that theorem is described in the [main-root packet](../p64-qcube72-main-root-draft/README.md);
its direct-provider and ancestry qualifications apply here. Independently,
fix positive integer `q,X,Y,k,c` and consider two nonnegative values of `h`
whose free-main square residual vanishes. Their
`D(h)=U*(X+a*c)+H*h` are positive and have the same square
`U²*(1+Delta*c²)`. Thus they are equal, and `H>0` forces the two `h`
values equal. Also `eta=c−kY` and `zeta=k−eta` are fixed if they exist.
This argument uses only ordered integer arithmetic and does not require
classifying Pell solutions. A direct application to a 76Y witness additionally
needs the positive-root result on its own side, not merely equality of
squares; [`P64Root.main_root`](../../Lean/DiophantineConsistency/Compact44/P64Root.lean)
proves the needed sign and carrier after the P64 lift under its stated
positivity, transport and `q³ | Y` hypotheses.

Consequently, within any conversion that preserves `q,X,Y,k,c,R`, varying
only the independent auxiliary witnesses or replacing the free-carrier
coordinate cannot change the old-carrier criterion. The
[carrier-gap analysis](../p64-qcube72-fixed-compact-carrier-gap/README.md)
shows, **under its additional first-index residue, size and divisibility
hypotheses**, exactly when a positive old `gamma` exists. If its criterion
fails for those fixed values, an alternate 76Y witness must change at least
one of `q,X,Y,k,c,R`, rather than just those auxiliary coordinates. This is
conditional: no fixed-port actual zero failing the criterion has been shown.
Changing `F` or `alpha` can change `R`, and must not be overlooked.

## A conditional restriction on preserving q

The established old-graph arithmetic route proves `X=2^R`: see
[`P64Facts.facts_ports`](../../Lean/DiophantineConsistency/Compact44/P64Facts.lean),
which applies [`P72Power.power_of_mod`](../../Lean/DiophantineConsistency/Compact44/P72Power.lean)
after its listed first-index, carrier, positivity and compact-port facts.
The source-level witness transformations from 76Y back toward P64 preserve
`J` and `w`: the [76Y-to-77 map](../p64-qcube76-independent-y-lemmas-draft/IndependentYWitnessDraft.lean)
updates coordinate 12, the 77/78 and 78/79 maps preserve the valuation, and
the subsequent maps update only coordinates 9 and 7. The transformed P64
witness therefore has the same `q=beta*J+1` and `X=wq`.
This paragraph is a source inspection of the composition, not a newly
Lean-checked standalone theorem about the 76Y source.

For **standard positive integers**, these facts imply `q | 2^R`, and hence
`q=2^d` for some `d≥1`. At the fixed compact beta
`beta=2^B−1` with `B=590069`, the identity

```
beta*J+1 = 2^d
```

holds exactly when `d=B*t` for some positive integer `t`, in which case
`J=1+2^B+...+2^((t−1)B)`. Indeed `(2^B−1)|(2^d−1)` if and only if
`B|d`: reducing `d` modulo B leaves remainder `2^r−1`, with
`0≤r<B`. In particular `3 | q` is incompatible with retaining q in an
old-graph witness. This is a restriction on the proposed **same-q conversion**,
not evidence that a positive 72 zero with `3|q` exists. The reviewed
[modular families](../p64-qcube72-fixed-mask-all-moduli-controls/README.md)
are positive nonzero outputs, and their
[boundary zero](../p64-qcube72-fixed-mask-boundary-zero/README.md) has zero
coordinates. Neither is a 72 positive zero.

An existential conversion might change J and q; then its graph rank and
transport equation change too. The currently checked window `n<R<2n`
alone neither supplies an alternative witness nor establishes the exact
first-index equality required by the old power-recovery argument.

[`check.py`](check.py) uses isolated, unoptimized Python for bounded controls
on positive-square rigidity and the finite-beta repunit criterion; its
exit-0 [result](result.json) is not the proof of either general statement.
The checker SHA-256 is
`400547fa93fa3206050731eb5e97fc7e5b888ad67dcb022c6eb955c16c3a7e4f`;
the result SHA-256 is
`89fb9c08c0196ca8102e8bfd74c528b2a0693f6ae58cfbbe1ee00d65479238f3`.
