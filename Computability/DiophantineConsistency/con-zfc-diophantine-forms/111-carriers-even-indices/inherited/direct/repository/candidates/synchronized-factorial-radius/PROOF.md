# Self-bounding factorials in the synchronized direct equation

This is a new sibling of the reviewed synchronized 522/529/596-natural
family. It changes one primitive: the factorial radius is `f*n^2`, where
`f` is the proposed factorial output, instead of `(n+2)^(n+2)`. The
numerical C222 source, its factored axiom alternative, heterogeneous CRT
bounds, fixed majorant, shared positive-power frame, common product-index
certificate and deferred binomial radix are unchanged. All variables in
this candidate are **nonnegative integers**.

The argument below proves ordinary mathematical equivalence of zero
existence with the accepted parent. The inherited ordinary C222-to-sealed
ZFC-refutation calibration then applies to this sibling as well. It does
not assert consistency, the absence of zeros, a new Lean result or an
encoded internal ZFC derivation. Lean remains paused. In particular a
finite replay is not a substitute for any unbounded argument below.

## 1. The local factorial relation is exact

For arbitrary `n,f` in the naturals define

```
rho=f*n^2,    C=binom(rho+n,n),    P=(rho+1)^n.
```

The retained two natural rows are

```
P+C=C*f+r+1,    C=r+s+1.                         (1)
```

Here `P,C>=1`, including initially `f=0` or `n=0`. Eliminating `r,s`
shows that (1) is equivalent to

```
f-1 < P/C <= f,     equivalently f=ceil(P/C).     (2)
```

In particular (1) excludes `f=0`; positivity of the proposed factorial
is a conclusion, not a premise used to justify an earlier power call.
Conversely, (2) makes

```
r=P+C-C*f-1,    s=C-r-1
```

nonnegative integers satisfying (1).

If `n=0`, then `P=C=1`, so (2) forces `f=1=0!`. Assume henceforth
`n>=1,f>=1`. Write `F=n!` and `R=P/C`. Direct cancellation gives

```
R=F product_(i=1)^n (rho+1)/(rho+i),    0<R<=F.
```

Set `d_i=(i-1)/(rho+i)`. All `d_i` belong to `[0,1)`, and

```
sum_i d_i <= n(n-1)/(2rho) < 1/(2f).
```

The finite product inequality `product_i(1-d_i)>=1-sum_i d_i` gives

```
R > F*(1-1/(2f)).                               (3)
```

If (2) holds, then `f<=F` since `R<=F` and `F` is integral. Combining
`R<=f` with (3) yields

```
F < f/(1-1/(2f)) = f+f/(2f-1) <= f+1.
```

Consequently `F<=f` by integrality, and `f=F`. Conversely, set `f=F`.
Then (3) gives `F-1<R<=F` (indeed `R>F-1/2`), which is (2).
Thus (1) represents factorial for every natural input, without any
bound or uniqueness assumption on the candidate output.

The square in the radius matters. The tempting linear variant
`rho=f*n` admits the false fixed point `n=4,f=23`, although `4!=24`.
The independent controls retain this negative example.

## 2. Arithmetic licenses precede the semantic interpretation

The actual calls to factorial have inputs `H` and `t`, where

```
t=t0+1,
R=2+t+x+y+m+M0,    m=m0+1,    H=R^(2^23).
```

They are positive by addition/multiplication alone. Even with an
uninterpreted natural candidate `f=0`, the new internal arguments satisfy

```
rho+n>=n>=1,    rho+1>=1.
```

Thus each internal binomial has positive upper and lower arguments, and
the numerator power has positive base and exponent. No step assumes
`f=n!` to license these calls. `check.py` propagates lower bounds from
zero for *every* free candidate output and verifies positivity of all
actual power exponents and binomial/factorial inputs. Seven power bases
also have positive syntactic lower bounds. The eighth base is the
candidate `H!` itself in the modulus-product formula; its positive lower
bound follows from its exact natural row (5), which contradicts a zero
base before any factorial interpretation. The checker reports this case
explicitly. It also checks that no private Pell/index/modulus coordinate
enters an arithmetic argument.

There are exactly 25 distinct power pairs, 20 distinct exponent atoms,
8 distinct bases, 14 binomial pairs and 2 factorial inputs. Removing the
two old radius powers accounts for the reduction from 27/22/10.
The two new radius multiplication chains are literal in the artifacts.

## 3. Soundness of all shared powers is simultaneous

For every distinct atom used as any requested power base, exponent or
output, the unchanged frame imposes

```
W=2+sum(atoms),    Z=z0+1,
A^2-W^3(W+2)Z^2=1.                              (4)
```

In a natural zero, `W>=2,Z>=1` and `A>W^2`. Each requested `n,k,m`
is at most `W`. Its base modulus is a natural coordinate satisfying

```
2An=T+n^2+1.                                    (5)
```

The case `n=0` is impossible. Thus `1<=n<=W<A`, and
`T>=2A-2>=A>m`. The independently verified exponent licenses give `k>=1`.

An exponential bound, not merely `A>W^2`, is essential. Equation (4)
is the Pell equation at center `W+1` with ordinate `WZ`. Classification
of nonnegative Pell solutions gives

```
A=chi_(W+1)(j),    WZ=psi_(W+1)(j).
```

The recurrence modulo `W` gives `psi_(W+1)(j)=j mod W`. The positive
ordinate therefore forces `j` to be a positive multiple of `W`. Hence

```
A >= (W+1)^W > W^W >= n^k,    T>n^k.            (6)
```

Each exponent has an unchanged index certificate with variables `X,Y,S,R`
and one common auxiliary triple `U,V,B`:

```
Y>=k,       X^2-(A^2-1)Y^2=1,
U^2-(A^2-1)V^2=1,
S^2-(B^2-1)R^2=1,
V=(product_i Y_i^2)(v+1),
B=1+4V(q4+1)=A+U*bq,
S=X+U*sq,  R=k+4Y*rq.
```

Since every `Y_i>=k_i>=1`, these imply the divisibility, positivity and
congruence hypotheses of the inherited indexed-Pell criterion. It
identifies `X=chi_A(k),Y=psi_A(k)`. Finally the actual power row is

```
X+nY=AY+m+T*h.
```

The standard Pell power congruence identifies the residue of `n^k`
modulo `T`. The two strict bounds `m<T` and (6) force `m=n^k`.
This works pointwise for the current arguments of *all* power requests,
regardless of any candidate factorial/binomial meaning. The exact row
audit checks all 25 power interfaces, all 20 index interfaces, (4), (5)
and the common product conditions on the actual raw builder.

## 4. The binomial radix and factorials have no soundness cycle

The unchanged deferred binomial construction sets

```
K=sum(distinct binomial upper-argument atoms),    q=2^K+1.
```

After Section 3 all these powers have their exact meanings at the
current arguments. For each requested `binom(n,k)`, `K>=n` and
`q>2^n`. Every coefficient in the base-q expansion of `(q+1)^n`
is therefore less than q. The actual quotient/remainder rows select its
`k`-th digit, which is `binom(n,k)` (zero if `k>n`). They enforce
`remainder<q^k` and `output<q` by natural slacks. This argument is
pointwise and does not yet assume a factorial output correct.

Now both binomials and powers used in (1) are their true functions of
their present arguments. Section 1 applies and identifies each candidate
factorial. The original remaining semantic macros, CRT range/index tests
and numerical source are then interpreted in their accepted order.
The self-reference inside the radius is discharged by the local theorem;
it is not a hidden fixed-point premise of the global construction.

## 5. Completeness has an explicit finite schedule

Start with the genuine finite numerical-calculus witness used by the
parent source theorem. Choose its outer bounds and CRT data by the same
accepted construction. Compute the genuine `H!` and `t!` first. For each
factorial use `rho=n!*n^2`, choose its genuine binomial and power outputs,
and choose `r,s` by Section 1. The remaining genuine semantic macro
values and CRT columns are then determined as in the parent.

All 14 binomial upper arguments are now fixed independently of their
deferred radix. Set `K` to their literal distinct-atom sum and `q=2^K+1`.
Compute the internal digit powers and their Euclidean quotients and
remainders. All true power bases, exponents and outputs are now fixed.
Choose `W` from their literal atom set, then

```
A=chi_(W+1)(W),    Z=psi_(W+1)(W)/W.
```

The recurrence modulo W makes Z integral and positive; (4) holds.
At this common A choose `X_i=chi_A(k_i),Y_i=psi_A(k_i)`.
Let `L=4 product_i Y_i^2`. In the finite ring
`(Z/LZ)[s]/(s^2-(A^2-1))`, `A+s` is a unit with inverse `A-s`.
Some positive power is 1. Its Pell coordinates `U,V` satisfy
`U=1 mod L`, `V=0 mod L` and `V>0`. The norm gives `gcd(U,V)=1`;
U is odd, so `gcd(U,4V)=1`.

CRT gives `B=A mod U`, `B=1 mod 4V`, with `B>A` after adding a
positive common period. Set `S_i=chi_B(k_i),R_i=psi_B(k_i)`.
Recurrence congruences give exactly the two index congruences, and
monotonicity gives all oriented quotients nonnegative. The required
positive quotient `V/product_i Y_i^2` also exists. Finally, with

```
H_j=chi_A(j)-(A-n)psi_A(j),
H_0=1,    H_(j+1)=nH_j+T psi_A(j),
```

`H_k-n^k` is T times a nonnegative finite sum. This supplies the
natural `h` in every power row. A sufficiently large common offset
supplies the remaining outer signed congruence quotients.

Thus all rows have natural witnesses. This is a finite ordered
construction, not an appeal to an existential solution of a global
circular system. The finite ring and its positive period are proof
devices, not additional equation inputs.

## 6. Source inheritance and literal projection certificates

The copied synchronized constructor, source functions and shared-power
classes are byte-identical authenticated archive members. The only
overridden method is factorial. The source remains the direct 11-local-
coordinate C222 source: seven label/schema parameters bounded by m,
two accumulator states by y and two beta quotients by x. Its strict beta
remainders follow from the retained state bounds. Its factored axiom
alternative preserves the original zero set. The fixed majorant uses
the same 388-gate certificate with exponent 6,893,159 rounded up to
`2^23`; no encoded CRT column enters it. The accepted parent proof
therefore supplies the same CRT soundness and cofinal completeness.

The source/provenance review is
`PROPOSAL_REVIEW_SYNCHRONIZED_CERTIFICATES.md`, including all seven
actual calibration Git blobs at
`08200eb10fde2db408c69dffd840d6920a569b1f`. The local factorial proof
was independently reviewed in `PROPOSAL_REVIEW_SHARED_PELL_608.md`.
`SOURCE_PINS.json` binds the exact whole archives and every copied member.
No native machine-port calibration is introduced by this direct route.

The raw system has 1,597 coordinates and 1,481 rows. The independent
affine verifier checks all 1,277 actual positive triangular gate
definitions and reconstructs the 747 omitted affine wires. No free input
is omitted. This yields `source850`. Each later contraction is a literal
monic row `x=P` or its negative, with P independent of x and having
nonnegative coefficients. Its exact substitution is checked in every
remaining row. Every resulting residual stays quadratic. Reverse
restoration therefore preserves natural assignments and proves both
directions, irrespective of the optimizer's support heuristic.

The final equation in each directory is the sum of squares of its
listed quadratic residuals. Over the naturals it vanishes exactly when
all residuals vanish. Independent full expansion checks every integer
coefficient, exact quartic degree and use of every coordinate. No
polynomial coefficient is inferred merely from a modular sample.
