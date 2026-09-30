# Six constant deletions from complete75 give empty systems

Six literal ways to remove one addition or subtraction from the
[complete75 certificate](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md)
produce **74=41M+33A**, with the same30 positive witnesses and19 equations.
Each changed system has **no strictly positive solution**, for every
compiler covered by that theorem. These are rejected reductions, not a
new universal bound or a lower bound for more general circuit rewrites.

The first four obstructions are immediate nonsquare arguments. The fifth
uses both Pell indices and shows why the remaining successor in the
half-binomial kernel cannot simply be removed. The last explains why
the fixed odd input offset cannot simply be omitted.

| Deleted instruction | Redirect its uses to | Changed equation |
|---|---|---|
| `R9=tau_square-1` | `tau_square` | `(E^2+X)(KY)^2=T^2` |
| `R15=Delta*c^2+1` | `Delta*c^2` | `dmain^2=Delta*c^2` |
| `f_square_minus_one=f^2-1` | `f^2` | `(ic^2)^2=Delta*f^2` |
| `norm_rhs=Delta*kappa^2+1` | `Delta*kappa^2` | `mu^2=Delta*kappa^2` |
| `r1=R+1` | `R` | `K=R+hE` |
| `odd_index=2d*x+b` | `2d*x` | `kappa=2d*x+delta*Delta` |

Here `X=wq^3`, `Y=sq^3`, `E=XY`, `A=a+2`,
`Delta=A^2-1=a^2+4a+3`, and `H=4a+3`. The constants d,b
in the input expression are the fixed compiler numerals; `dmain`
is a separate Pell witness. Every unmentioned instruction and
comparison is retained. The checker records each entire acyclic DAG,
so the savings do not hide a new subtraction or an unpaid operation.

## 1. Four homogeneous norm equations have no positive solutions

For every positive a,

    (A-1)^2 < Delta=A^2-1 < A^2.

Thus Delta is nonsquare. An equality `z^2=Delta*v^2` with z,v
positive integers would make `sqrt(Delta)=z/v` rational, which is
impossible for a nonsquare integer. This rejects the main, auxiliary
and input norm deletions without any kernel or compiler argument.

For the first norm, put `V=XY^2`. Its changed equation is

    T^2=V(V+1)K^2.

Since `V^2<V(V+1)<(V+1)^2`, the same argument rejects it. In the
auxiliary deletion, the second auxiliary equation remains the literal
strong-square equation; its apparent expression through `Delta(f^2-1)`
must not be retained after the preceding norm changes. The checker
expands the strong-square form directly and needs no equation correction.

## 2. Removing the first-index successor contradicts auxiliary parity

Only change `K=R+1+hE` to `K=R+hE`. The unchanged outer equations,
before power or computation decoding, still prove

    q>=16, 3q+1<=R<q^4, X,Y>=q^3, E>2R, a>R.

The retained first norm has the positive fundamental unit
`(2V+1,2)` for `T^2-V(V+1)K^2=1`. Therefore, for n>=1,

    K=2*psi_P(n), P=2XY^2+1.

As `P=1 modulo E`, the changed index equation gives

    2n=R modulo E, hence n>=R/2.                         (1)

The main norm gives `c=psi_A(p)` with p>=1. We have `P>A` and
`c>YK>K`, so monotonicity gives `p>=n+1`. In particular p>=6.
The same preliminary estimates used in the
[half-binomial proof](pell_kernel_half_binomial42.md) now give

    c>A*Delta^2, c>2p, c>YK>2Yn>=YR>2R.                 (2)

The [strong auxiliary recovery](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md)
therefore supplies m with

    f=chi_A(m), c divides m, m>=c>2p,
    rho=ic^2=Delta*psi_A(m)>1.

In particular `U=jc-R>0`. The unchanged second auxiliary norm says

    (rho U)^2-(rho^2-1)y^2=1.

Its normalized positive index s is odd, because
`chi_rho(s)` is `+1` or `-1 modulo rho` at every even s and must be
divisible by rho here. The polynomial identities and plus-sign
step-down from
[the fixed-minus parity proof, Sections2–3](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md)
apply without assuming p odd: squaring the congruence
`U=-c modulo f` gives

    chi_A(2s)=chi_A(2p) modulo f,
    s=+p or -p modulo 2m.                               (3)

The comparison index2p is below m by(2). Consequently s and p have
the same parity, and **p is odd**. Reducing(3) modulo c and using
the other fixed-minus congruence gives `R=+p or -p modulo c`.
Bounds(2) imply `0<R,p<c/2`, so only `R=p` is possible.

Since `P>A` and `c>K`, we also have `n<=p-1=R-1`. Thus both
2n and R lie strictly between0 and E. Congruence(1) is equality:

    2n=R=p.

This makes p even, contrary to(3). Every positive solution has been
excluded; no canonical choice of the auxiliary index was assumed.
The original successor changes the equality to `2n=R+1`, which
is compatible with the required odd main index.

## 3. Omitting the odd input offset contradicts the index gap

Here the entire original kernel is retained. Its theorem gives

    q=2^t, a=Y(X+1) even, A=a+2 even,
    c=psi_A(R), 3q+1<=R<a+1.

Set `u=2d*x`. The unchanged strengthened raw bound gives
`0<u<q<R<A-1`. The input norm and positive gap still give
`kappa=psi_A(v)` for `0<v<R`. Modulo Delta the exact
representative of kappa is

    v if v is odd, and vA if v is even.

Both representatives are strictly between0 and Delta because
`v<R<A-1`. The changed index equation therefore forces equality
between u and this representative. The odd branch is impossible
because u is even. In the even branch the representative is at
least2A, whereas `u<q<A`. This excludes every positive solution.

This conclusion concerns precisely the deletion of b with the existing
bridge, gap and masks retained. It is not an obstruction to redesigned
input encodings or to a kernel whose index congruence has changed.

## 4. Evidence and scope

The [checker](complete75_constant_deletion_obstructions.py) imports the
actual complete75 schedule and audits114 independent source comparisons
across the six variants. Each retains41 products and33 additions or
subtractions,30 positive coordinates and19 equations. Its full source
expansion uses the literal strong-square auxiliary residual, avoiding
any dependency on the old preceding norm in the changed variant.

Finite checks cover the nonsquare intervals, the adjusted pre-power
index bounds, the two discriminant representatives, and both signed
parity lifts. They corroborate the displayed proofs; they do not search
all positive assignments, constitute a formal proof, or materialize
astronomical complete compiler witnesses. The adjacent JSON is a
reproducible receipt. An independent full proof/source review and fresh
default replay passed without findings. The dependency review checked
that the changed-index proof obtains its bounds and odd main index
without invoking the unchanged kernel theorem. The established complete
universal certificate remains75 operations.

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_constant_deletion_obstructions.py
