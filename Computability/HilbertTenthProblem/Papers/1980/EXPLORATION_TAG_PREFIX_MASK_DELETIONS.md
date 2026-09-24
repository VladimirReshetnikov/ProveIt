# Either single prefix-mask deletion admits a full false positive

The valid nine-field guarded-content tag construction retains both Boolean
prefix words `E` and `Ebar=ccH-E`. Neither mask can be removed by the direct
eight-field packing change. This note gives exact full positive outer
witnesses for the two resulting sources, at **102 = 51M + 51A** and
**100 = 50M + 50A** operations. The established parity-free44 converse extends
each witness to all seventeen positive Pell auxiliaries, so these are
counterexamples to the complete proposed sources, not just local bad reads.

Both use the same fixed zero-leading binary appendant and the same genuinely
nonhalting encoded input. The original
[nine-field104 proof](EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md) and checker
are unchanged. No improved certificate bound is claimed.

Author and two independent complete proof/source reviews and fresh witness
verification runs pass without findings. The maintained checker and receipt are
[explore_tag_prefix_mask_deletions.py](../verification/explore_tag_prefix_mask_deletions.py)
and [its JSON receipt](../verification/explore_tag_prefix_mask_deletions.json).

## 1. Exact rejected schedules

Use the coordinates, input convention, fixed constants, and paid true-radix
geometry of the nine-field104 source. In particular,

```
E=F_E-1 >= 0,  Ebar=ccH-E,
GN=N+jAH,
```

and its field order is

```
Gstar,Q,S0,S1,M0,M1,Ebar,E,GN.
```

The first six fields retain exactly their existing factored packing `Lo6`.
The old high part is

```
Pold = Lo6 + q^6 [ccH+(q-1)E+q^2 GN].
```

The proposed deletion of the `E` mask uses

```
P102 = Lo6 + q^6 [ccH-E+q GN].                    (1)
```

Computing `ccH-E` replaces the two operations `(q-1)E` and addition of `ccH`
by one subtraction. The final power product `q^8*q` is also removed, since
the new scale is `D0=q^8`. This saves two multiplications, yielding102.
The positive coordinate `F_E` and its content-transport uses remain.

The proposed deletion of the `Ebar` mask instead uses

```
P100 = Lo6 + q^6 [E+q GN].                       (2)
```

This removes the three packing computations `ccH`, `(q-1)E`, and their sum,
as well as the final scale multiplication. It saves three multiplications
and one addition, yielding100. No source comparison other than the changed
index and scale expressions is removed: `ccH` had no other runtime use in
this particular104 schedule.

Both variants retain **33 positive unknowns and 20 equality comparisons**.
The checker directly derives the complete DAGs from the unchanged104 source,
uses the three-product power chain `q^2,q^4,q^8`, and verifies all twenty
source polynomials in each fixed leading-symbol branch. It checks the
kernel norm-source correction at comparison17, rather than inferring full
source equality from an outer numerical sample.

## 2. Common program, geometry, and complete witness convention

Take

```
beta=2,  0 -> 0,  1 -> 01,
K=9, k=3, B=3, U=3, cc=1, Ut=1,
C=2187, j=972, A=81, R=CA=177147=3^11.
```

Here `C>max(K^3,K*3^2,2KU+3)` as required by104. Queue symbols occupy
least-significant ternary positions. The genuine initial word is `111`,
so `Ni=13, Li=27`. Its actual trajectory is

```
111 -> 101 -> 101 -> ... .                         (3)
```

It therefore never halts. Notice that the appendant starts with zero;
both failures satisfy that source-compatible restriction.

For either table below, with `t` source rows, set

```
q=R^t, H=sum_(i=0)^(t-1) R^i, v=q/R,
N=sum n_i R^i, E=sum e_i R^i, S1=sum s_i R^i,
Q=sum s_i*(lambda_i-1)/2 * R^i,
M1=sum s_i*lambda_i*R^i,
M0=sum (1-s_i)*lambda_i*R^i,
L=M0+M1, T=(N-S1)/3.
```

Supply

```
F_Q=Q+1, F_S1=S1+1, F_T=T+1, F_E=E+1, F_Nfinal=1,
Lf=3, alphaI=54, alphaH=6,
```

along with `A,R,q,H,L,v`. Thus the alleged final content is zero and its
length marker is the genuine one-symbol marker3. Every displayed supplied
outer coordinate is strictly positive; in particular `E>0` in both cases.
The two remaining positive index coordinates are defined in Section5.

The signed row expansions for `E` below are literal integer sums. A negative
row coefficient is not being declared a negative supplied unknown.

## 3. Removing the E mask: guarded extra content creates a false halt

Use the following six rows, then terminal `(n,lambda)=(0,3)`:

| Row | Content `n_i` | Length marker `lambda_i` | Selector `s_i` | Prefix quotient `e_i` | Retained `cc-e_i` |
|---:|---:|---:|---:|---:|---:|
| 0 | 13 | 27 | 1 | -242 | 243 |
| 1 | 91 | 27 | 1 | -27 | 28 |
| 2 | 28 | 27 | 1 | 0 | 1 |
| 3 | 12 | 27 | 0 | 1 | 0 |
| 4 | 1 | 9 | 1 | 0 | 1 |
| 5 | 3 | 9 | 0 | 1 | 0 |

All retained complement row values are ternary Boolean: `243=3^5`,
`28=1+3^3`, and the others are zero or one. Explicitly,

```
E = R^5+R^3-27R-242 > 0,
Ebar = 243+28R+R^2+R^4 > 0,
E+Ebar=H.
```

The omitted global word `E` is not ternary Boolean, even though it is
positive and below `H`.

Write `p_i=n_i mod9`. The deleted prefixes in the first two rows are
`d_i=3e_i+s_i=p_i-9t_i`, where

```
(t_0,...,t_5)=(81,9,0,0,0,0).
```

Both nonzero extras are single ternary bits. The content update becomes the
ordinary numerical append result plus `t_i`. In the first row the true
successor10 is changed to91. This exceeds its encoded length marker27 but
remains Boolean and fits the wide content guard. In the second row the
unadjusted value19 has a trit2; adding9 changes it to the Boolean value28.
The remaining exact transitions then reach the alleged short word.

The ordinary integer identities are checked row by row:

```
n_i-3e_i-s_i+U*s_i*lambda_i = K*n_(i+1),
lambda_i*(9 if s_i=1 else 3) = K*lambda_(i+1).
```

They telescope to both full packed transports, including the correct
original input and the terminal zero. No unverified row truncation is used.

## 4. Removing the Ebar mask: an overlong deleted prefix creates a false halt

Use four rows, again ending at `(0,3)`:

| Row | Content `n_i` | Length marker `lambda_i` | Selector `s_i` | Retained `e_i` | Omitted `cc-e_i` |
|---:|---:|---:|---:|---:|---:|
| 0 | 13 | 27 | 1 | 4 | -3 |
| 1 | 9 | 27 | 0 | 0 | 1 |
| 2 | 1 | 9 | 1 | 0 | 1 |
| 3 | 3 | 9 | 0 | 1 | 0 |

Here `E=4+R^3` is Boolean, since `4=1+3`. The omitted word is

```
Ebar=R^2+R-3 > 0,
```

which is not Boolean. The first deleted prefix is `d_0=13`, larger than
the allowed two-symbol prefix; it deletes the entire numerical source13
instead of the actual prefix4. The four content and length transitions
are exact and lead to the false halt.

Every content row in this second example is even below its encoded length
marker. Thus its failure does not depend on allowing content above that
marker. Both examples also have positive `Ebar`, so merely adding a global
nonnegativity bound for the omitted word would not repair either deletion.

## 5. Eight individual masks and the positive Pell extension

For both examples, `Q,S0,S1,M0,M1,Gstar` are the ordinary correctly typed
projector and length fields. Their source lengths are at most27, below
`A=81`. The retained prefix field has all its Boolean row digits below
`R`, as the tables show.

The row guard in `GN=N+jAH` is

```
jA=78732=4*3^9=3^9+3^10.
```

Every listed content number is Boolean and below `3^5`, so it has disjoint
support from this guard. Therefore `GN` is Boolean as well. All eight
retained fields lie in `[0,q)`, and `Gstar` has unit trit1. The checker
verifies each whole integer, rather than relying only on the row table.

Pack those eight fields using (1) or (2), call the result `P`, and set

```
D0=q^8, r=P+(D0-1)/2, betaP=D0-r.
```

This gives all nine exact outer comparisons. The index has native ternary
digits1/2 and unit2, `27<=r<D0`, `D0<r^2`, and `betaP>0`. Its central-binomial
valuation is exactly

```
v3(binomial(2r,r)) = 528   for the six-row102 example,
v3(binomial(2r,r)) = 352   for the four-row100 example.
```

Both indices are odd. The established parity-free44 theorem applies to both
parities and supplies all seventeen strictly positive auxiliary coordinates
for the new `D0,r`. Together with the exact source identities, this proves
existence of a full positive solution of each rejected20-equation source.
No auxiliary tuple from a different packing is reused, and these enormous
Pell auxiliaries are not claimed to have been materialized numerically.

## 6. Verification boundary

The fresh checker validates four complete symbolic sources: each deletion
in both leading-symbol branches. It reproduces the exact102 and100 ledgers,
all twenty source comparisons per branch, the two exact full positive outer
tuples, all eight individual masks per tuple, all retained geometry and
input/terminal conditions, and both exact new index valuations. It also
checks the actual infinite loop (3).

The source-level operation reductions are real, but the reduced systems are
unsound. This note establishes those two specific failures and does not
assert a lower bound against different prefix encodings or other schedules.
