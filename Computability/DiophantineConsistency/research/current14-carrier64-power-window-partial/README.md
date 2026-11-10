# Power-window partial witness outside the old scalar domain

At the actual current ports, transport, the first Pell norm, the rank window,
the necessary condition `X=2^R`, and the growth consequence `X<Y` can all
hold while **no old positive scalar representation has the same q and R**.
This is a partial assignment. The main, strong and auxiliary norms are not
solved, so it is not a full candidate zero and does not disprove a reverse map
that uses those norms or changes `q` or `R`.

The actual `beta=2^B-1` has `B=94517`, and `MC` is even. Set

```
q=beta+1=2^B, J=1, F=C=q-1,
G=q*(q-F)-C=1,
R=(q²-1)+MC+q*MF,
w=2^(R-B), z=K+w, s=2^R.
```

The exact fixed-port computation checks `R` is odd, `R>=26` and `R>3B`;
its bit length is 189036. Every displayed coordinate is a positive integer.
The identities `G=1` and `Nt=1` hold because

```
(K+w)*C+(q-F)-z*(q-1) = 1.
```

Moreover

```
X=wq=2^R,          Y=sq³=2^(R+3B)>X,
E=XY=2^(2R+3B)>R+1,    m=EY=2^(3R+6B).
```

These values are specified symbolically: `w`, `s`, and their powers are far
too large to materialize. The checker performs finite port operations and
checks exponent arithmetic without constructing them.

## First norm

Set `j=(R+1)/2`, a positive integer, and let `(x,k)` be the coefficients
of the symbolic Pell power

```
(2m+1+2*sqrt(m(m+1)))^j = x+k*sqrt(m(m+1)).
```

Its norm is 1, `k>=2`, and `x>k`. Because `E|m`, the reviewed Pell
induction in `../current14-carrier64-transport-proposal/` gives
`x=1 (mod E)` and `k=2j=R+1 (mod E)`. Hence
`n=(x-k+R)/E` is a positive integer. Choosing `eta=1`, `zeta=k-1` makes
the candidate's carrier `tau=x` and its first Pell norm exactly 1.

## No rank-preserving old scalar repair

The recovered direct-map coordinate is `alpha=q-F-C=2-q<0`. More strongly,
for any old positive coordinates with `C_old=q-F_old-alpha_old>0`, put
`u=q-F_old`; then `u>=2`, `alpha_old>=1`, and the old gap obeys

```
G_old=(q-1)*u+alpha_old >= 2q-1 > 1.
```

With the same fixed `q` and ports, rank is injective in the gap, so no such
old scalar coordinates have this `R`. This does not rule out a reverse
normalization changing `q` or `R`.

The construction demonstrates that the explicitly listed power, rank,
transport and first-Pell consequences alone do not recover the old scalar
domain. It does not show that those conditions exhaust the implications of
the remaining three norms. In particular the two-Pell-index main-norm
compatibility from `../current14-carrier64-scalar-repair/` is unproved here.

From the DiophantineConsistency directory:

```sh
python3 -I -S -B research/current14-carrier64-power-window-partial/check.py > /tmp/carrier64-power-window.json
cmp /tmp/carrier64-power-window.json research/current14-carrier64-power-window-partial/result.json
```

The checker authenticates the current graph and all four port payloads,
checks the fixed rank and gap facts, and verifies the local transport and gap
identities in an exact sparse polynomial ring. The Pell extension is an
ordinary symbolic argument using the independently reviewed induction in the
earlier packet. No Lean run, full-zero witness, native proof replay, or PDF
interpretation is claimed.
The independent external review is in
`../../reviews/current14-carrier64-power-window-partial-independent/`.
