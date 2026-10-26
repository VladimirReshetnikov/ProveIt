# Checked rank and threshold for compact H2082

[`GapNineRatio66.lean`](Lean/DiophantineConsistency/GapNineRatio66.lean)
supplies the numerical outer ratio for the 443/450-operation candidate.
Its parameter `a` is **half** the coefficient-height exponent:

```
H=2^(2*a), B=4096*H*b^2
L=b*B^2200
N=2^(15*a+79)*B^1162
R=L*(S+T+1)-S-1
t=b*B^116.
```

The rank is defined as natural data without truncated subtraction, and its
displayed integer identity is proved for every positive `b`. All lower
rank, threshold and margin bounds required by the free-carrier finalizer
are proved before any source equation or code-range condition is assumed.
The threshold has no separate factor `b`; the radix exponent is even.

When `b=2^k`, put `nu=2*a+12+2*k`. For the actual low/high mask with
31 low positions and 22 high positions, Lean derives its population as
`139*nu-31*k-22`. The exact identity

```
k+2200*nu + (139*nu-31*k-22)
  = 2*(15*a+79+1162*nu)
```

therefore converts `N^2 | choose(2*R,R)` into the required no-carry test.
`binomial_iff` derives that identity from the actual mask rather than taking
an assumed population equation. It only needs `S<L` in addition to the
finite mask-position conditions. The result includes `k=0`, hence `b=1`.

`sound` first recovers a power-of-two `b`, the binomial divisibility and the
weak cap `g<4*b*B^116` from a positive finalizer zero. `complete` constructs
all positive finalizer witnesses from the stronger code cap, divisibility
and a power-of-two `b`. The old generic free-carrier theorem supplies the
arithmetic tail without a new native calibration premise.

The coherent compact54-sharp instance is `a=432007`, yielding the actual
candidate radix exponent 864026 and threshold exponent 6480184. Dedicated
checks verify that binding without expanding the huge powers. All eleven axiom
audits use only Lean's standard axioms.

The subsequent [source-word/carry contract](GAP_SOURCE_CONTRACT66.md) and
[unbounded source existence](GAP_SOURCE_NINE66.md) now pass Lean.
The literal counted DAG still needs identification with this recipe.
Authentic native semantics and the internal ZFC biconditional remain open.
