# Saturated rank gives an old positive gap; transport remains

Subject to the existing Pell-theorem application and the reviewed floor
argument in `../current14-carrier64-pell-floor/`, every positive 64-candidate
zero with `R>=26` has an old **positive scalar representation of its gap** at
the same `q,R` and actual current ports. Its scale `s` is odd. This does not
by itself recover an old zero: a separate transport congruence remains.
The result is an external combinatorial argument, not a new Lean client or a
complete reverse-equivalence proof.

## Mask setup and the base gap

Write the actual fixed ports as `beta=2^B-1`, `lo=MC`,
`hi=MF-beta`, with `B=94517`. The checker verifies the raw and compressed
port hashes and the actual facts

```
0<lo,hi<beta;  lo=2 (mod 4);  hi=4 (mod 8);
popcount(lo)+popcount(hi)=B;  lo+hi>beta.
```

The previous floor packet gives `q=2^t=2^(B*h)`,
`J=(q-1)/beta=1+2^B+...+2^((h-1)B)`, and

```
popcount(R)=3t+v2(s)+2 >= 3t+2,
4q-1 <= G <= q²-q-1.
```

Put `b=q-1`, `A=lo*J`, `Z=hi*J`, and
`G0=q*(Z-1)+(A+1)`. The `h` repeated, nonoverlapping radix blocks give
`popcount(A)+popcount(Z)=t`. Because `J=1 (mod 8)`, `A=2 (mod 4)` and
`Z=4 (mod 8)`, so

```
popcount(G0)=popcount(Z-1)+popcount(A+1)=t+2,
A+Z>b.
```

The rank is `R=G*(q²-1)+A+q*(b+Z)`, and the fixed mask term obeys
`A+q*(b+Z)-G0=q²-1`.

## Saturation and old gap coordinates

First suppose `G<G0`, and set `d=G0-G>0`. Then `0<d<q²` and

```
R=(G+1)*q²+(d-1),       (G+1)+(d-1)=G0.
```

For two nonnegative `2t`-bit integers whose sum has at most `2t` bits,
the sum of their populations is the population of their sum plus the number
of binary carries, at most `2t-1`. Therefore
`popcount(R)<=popcount(G0)+2t-1=3t+1`, a contradiction.

So `G>=G0`. Put `d=G-G0`. Since `0<=d<q²`,

```
R=G*q²+(q²-1-d),
popcount(R)=popcount(G)+2t-popcount(d)
           <=popcount(G0)+2t=3t+2.
```

The previous lower bound forces equality throughout. Hence `v2(s)=0` and
binary addition `G0+d` has no carries. Split `G=q*h0+ell` into `t`-bit
blocks. Carry-freeness gives `h0>=Z-1`, `ell>=A+1`, and `ell<=b`.
Consequently `h0+ell>=A+Z>b`. The candidate upper bound on `G` gives
`h0<=b-1`, so `b<h0+ell<2b`. Its unique division by `b` is

```
G=b*u+r,    u=h0+1,    r=h0+ell-b,
2<=u<=b,   1<=r<u.
```

Therefore `F0=q-u`, `alpha0=r`, and `C0=u-r=q-ell` are strictly positive
old scalars with precisely the same `q` and rank. The strict actual condition
`lo+hi>beta` is essential to this proof: the checker also records a smaller
mask example meeting the other population/parity conditions, but not that
sum inequality, where saturation has no old positive scalar representation.

## The remaining transport congruence

Let the candidate's positive inputs be `F,C,z`, put `M=K+w`, and let
`d0=F0-F`. Equality of the gaps gives `C=C0+q*d0`. Since `0<C0<q` and
`C>0`, `d0>=0`; positivity of `F` gives `d0<F0<q`, hence `d0<b`.
The independently reviewed restricted-repair criterion gives

```
an old same-q,R,w positive repair exists  iff  b divides d0*(M+1).
```

Here positivity of the old `z` is automatic: `R>=4q³-1`, `q=2^t`, and
`X=wq=2^R` imply `w=2^(R-t)>=q`, so `M*C0-F0>0`. If the divisibility
holds, the old positive `z0=1+(M*C0-F0)/b` preserves transport and every
other factor, giving an old positive zero. In particular, coprimality of
`M+1` and `b` would force `d0=0`; no such general coprimality has been
proved.

Indeed it cannot be assumed in all possible exponent branches. The actual
ports satisfy `beta=1`, `MC=8`, `MF=1 (mod 10)`, and `K=0 (mod 11)`.
If `20|t`, then `q=6 (mod 10)`, `J=5 (mod 10)`, and the rank formula plus
odd `R` gives `R=5 (mod 10)`. Thus

```
11 | (q-1),     w=2^(R-t)=-1 (mod 11),     11 | (K+w+1).
```

This is a conditional arithmetic statement about that exponent branch, not
an assertion that a candidate zero with `20|t` exists. The remaining proof
obligation is to derive `b|d0*(M+1)` from the full equations or find a
different reverse normalization; the result here does neither.

## Reproduction and scope

The checker pins the reviewed Pell-floor receipt and current graph, verifies
all actual port hashes, checks repeated-mask prerequisites and base controls,
and screens 1,550,669 bounded small-mask/gap cases. It also checks the
mask-sum negative control and the finite residues used for the 11-divisor
branch. These controls do not replace the proof or show a full zero. No new
Lean run, native proof replay, PDF interpretation, or fully closed provider
ancestry is claimed.
The independent external review is in
`../../reviews/current14-carrier64-saturated-gap-independent/`.

```sh
python3 -I -S -B research/current14-carrier64-saturated-gap/check.py > /tmp/carrier64-saturated-gap.json
cmp /tmp/carrier64-saturated-gap.json research/current14-carrier64-saturated-gap/result.json
```
