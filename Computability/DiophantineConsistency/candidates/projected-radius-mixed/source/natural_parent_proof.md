# Candidate-output factorial radii with the projected low-digit radix

All original coordinates are nonnegative integers. This new sibling keeps
the complete eight-column source, projected carrier, fixed majorants,
canonical index, aggregate CRT representative bound, low-digit divisibility
graphs, additive Pell-index compiler and natural contraction certificates
of the reviewed 407/888 archive. Its only semantic changes are:

* replace the H-factorial radius by `T*H^2`, or replace both factorial
  radii by `T*H^2` and `J*t^2`;
* in the latter case replace the common radix by `B*(V_H+V_t+1)`.

Here T,J are initially arbitrary proposed outputs. They are not assumed
positive or factorials. The earlier ordinary proof and source/calibration
pins are reviewed in `PROPOSAL_REVIEW_QUARTICS407888.md`; the complete
local factorial proof is in the frozen
`synchronized-factorial-radius/PROOF.md`. No frozen parent or incoming
file changes. Lean remains paused; no new internal-ZFC derivation is
claimed.

## 1. Exact local representation, including a zero candidate

For any naturals n,f put `rho=f*n^2`, `C=binom(rho+n,n)`,
`V=(rho+1)^n`. The natural equations

```
V+C=C*f+r+1,    C=r+s+1
```

are equivalent to `f=ceil(V/C)`. Since V,C>=1, they imply f>=1.
If n=0 they force f=1. If n>=1 and f>=1, write F=n! and

```
V/C=F product_(i=1)^n (rho+1)/(rho+i).
```

The factors are in (0,1], and their deficiencies have sum strictly
smaller than `1/(2f)`. The finite product inequality gives

```
F*(1-1/(2f)) < V/C <= F.
```

Thus `f=ceil(V/C)` implies f<=F and
`F<f+f/(2f-1)<=f+1`, hence F=f by integrality. Conversely f=F gives
`F-1<V/C<=F`, and the natural remainder witnesses are
`r=V+C-C*f-1`, `s=C-r-1`. This proves both directions for every
natural candidate, including zero. It uses no upper bound on f.

## 2. Shared powers remain pointwise correct before these meanings

The unchanged shared frame is

```
W=2+sum(distinct power bases, exponents and outputs),
Z=z0+1,    A^2-W^3(W+2)Z^2=1.
```

All power exponents and all factorial/binomial inputs are positive by
literal nonnegative arithmetic. Every requested base n has its actual
natural modulus row `2An=T_n+n^2+1`, excluding n=0 independently of
its intended meaning. Pell classification at W+1 gives a positive
index divisible by W, so `A>W^W>=n^k` and
`T_n>=2A-2>n^k,m`. The indexed-Pell tests and the oriented congruence
therefore identify all proposed outputs m=n^k simultaneously, at their
present arguments. These arguments do not use any factorial, binomial
or CRT-product interpretation.

There are 21 powers, 16 exponent atoms and 15 seed tests in the
both-radius sibling. Only t+1 is derived by the exact addition law.
The H-only sibling has 22 powers, 17 exponent atoms, 15 seeds and two
derived pairs. The original finite-unit/common-CRT construction supplies
the 15 seed witnesses simultaneously in either case. All power arguments
and results are allocated before the first private Pell coordinate, and
every raw defining gate is triangular. Consequently no private frame or
index coordinate enters an arithmetic argument.

Two details are explicit in the independent cut checker. First the raw
frame sum can reuse an already requested addition gate, such as `2+t`.
Its actual defining addition identity is expanded on both sides when
checking the full atom sum. Second the derived index pairs are checked
algebraically from their earlier seed pair and the literal pair at 1 or
2; they are not assumed to satisfy a deleted auxiliary norm test.

## 3. Both radii: validate both factorial binomials without a sign cycle

Write

```
rho_H=T*H^2,    V_H=(rho_H+1)^H,
rho_t=J*t^2,    V_t=(rho_t+1)^t,
q=B*(V_H+V_t+1).
```

The outer source has `t>=1`, `R=2+t+x+y+M0>=4` and
`H=R^(2^23)>=R^4`. Its endpoint and fixed-power definitions are unchanged.
The requested power with base q excludes q=0, hence B>=1. The requested
power `T^t` separately excludes T=0. Neither conclusion uses T=H! or
J=t!. All these powers already have their correct values by Section 2.

For any n>=1 and rho>=n, binomial unimodality and the factorial product
give, for j<=n,

```
binom(rho+n,j) <= binom(rho+n,n) <= (rho+1)^n.
```

Since T>=1, rho_H>=H and every required lower coefficient of the
H-factorial binomial is <=V_H<q. For the t-factorial there are two cases:

* If J>=1, rho_t>=t and its required lower coefficients are <=V_t<q.
* If J=0, rho_t=0 and its lower coefficients are `binom(t,j)<=2^t`.
  But T>=1 and H>=t imply `V_H>H^(2H)>2^t`; again they are <q.

This zero-candidate branch is necessary: the estimate by V_t alone is
false when J=0, because V_t=1 and interior coefficients may exceed one.
It is not omitted by assuming the intended factorial meaning early.

The accepted low-digit theorem therefore identifies both exact binomials
pointwise. Section 1 now identifies T=H! and J=t!.

## 4. The smaller reused numerator still bounds all remaining digits

Let `Q=(1+(t+1)T)^t+2`. The actual remainder rows imply B<TQ before
the product formula for B has been justified. The retained aggregate
inequality is `sum a_i+g=8B`, with every a_i positive. The parent proof,
using T=H!<=H^H, t<=R and 8<=H, therefore still gives

```
Q+t, a_i < H^((t+2)(H+1)).
```

Each remaining lower index k is at most R. Thus every needed lower
coefficient is bounded by `H^[k(t+2)(H+1)]`. To compare with the new
V_H, pair the factorial factors:

```
(H!)^2 = product_(i=1)^H i(H+1-i) >= H^H,
V_H^2 > ((H!)^2 H^4)^H >= H^(H^2+4H).
```

Since R>=4 and H>=R^4, `4R(R+2)<=H`. Consequently

```
2k(t+2)(H+1) <= 2R(R+2)(H+1) < H^2+4H.
```

Squaring positive quantities proves every remaining lower coefficient
strictly smaller than V_H, and hence q. This validates the product
binomial and all eight fused range-divisibility graphs. Only now is
the inherited product identity invoked to identify B with
`product_(i<t)(1+(i+1)H!)`. The proof therefore retains the crucial
noncircular order of the 407 parent.

## 5. H-only: the unchanged old t-numerator is dominated

Here only `rho_H=T*H^2` is changed and the radix is `q=B*(V_H+1)`.
The second radius stays `rho_t=(t+2)^(t+2)`. Before interpreting either
factorial, Section 2 already gives T>=1, so `V_H>H^(2H)`. Meanwhile

```
V_t=((t+2)^(t+2)+1)^t
    <=2^t(t+2)^[t(t+2)]
    <=H^[t(t+3)] <=H^H <V_H,
```

using H>=t+2 and `t(t+3)<=R(R+3)<=H`. Both factorial binomials thus
have all required lower coefficients <q: use the new-radius bound for H
and the old-radius bound for t. Recover their meanings, then apply the
same squared-V_H estimate from Section 4 to the other binomials.
This variant needs no assumption that an arbitrary old numerator is
bounded merely because t<=H; the displayed inequality supplies the bound
against the *new* H-numerator explicitly.

## 6. Completeness and literal natural projections

Choose a genuine finite proof certificate, padded horizon, carrier and
beta code exactly as in the accepted projected source. They determine R,H.
Set T=H!, J=t!, then choose their new local radius/ceiling witnesses
from Section 1 (the H-only t-witnesses stay the old ones). Compute the
true Q and CRT product B, choose the eight positive canonical CRT
representatives in [1,B], and the same canonical index
`C=(B-1)/T-1`. Their sum is <=8B, giving the aggregate slack.

Now set q to the displayed radius-dependent value. Sections 3-5 prove
all necessary digit bounds, so true powers and Euclidean witnesses satisfy
every exact/fused binomial row. Choose W from the resulting finite true
power data, then the canonical positive frame at index W, the common
seed-index unit period and the compatible common auxiliary base. The
ordinary oriented-quotient recurrence supplies each remaining natural
power quotient. This ordered construction proves completeness without
a global fixed-point assumption.

The source and its two majorant circuits are unchanged. The complete
independent raw export verifies all addition/multiplication gates and
all 17 signed difference-square gates, then restores every omitted affine
wire with no omitted free input. Every subsequent natural contraction is
checked by its exact rational sum-of-squares restoration, substituted in
every remaining row. Integer coefficients give integral restorations,
their nonnegative certificates give natural restorations, and every
residual remains quadratic. The final equation is the sum of their squares;
all six complete polynomial coefficient lists are independently expanded.

The resulting ordinary existence equivalence preserves the accepted
numerical C222/refutation source. It neither proves consistency nor
changes an external or ordinary proof into a new Lean/object-ZFC theorem.
