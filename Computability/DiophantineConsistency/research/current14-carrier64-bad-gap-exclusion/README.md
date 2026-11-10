# Conditional exclusion of the fixed bad-gap family

The fixed-port partial assignment in `../current14-carrier64-scalar-repair/`
satisfies transport and admits a first-Pell solution outside the old scalar
domain. It **cannot extend to a full candidate zero**, provided the existing
`P72Exact.indices_ordinary` and `P72Power.power_of_mod` theorems are applied
to the standard natural numbers with the bindings below. This is an external
mathematical argument using those existing theorem statements; it is not a
new Lean client, a fresh proof of their provider ancestry, or a general
reverse equivalence for the 64-gate candidate.

Fix the actual four ports and the scalar coordinates

```
J=F=s=1, q=beta+1, C=2q-1,
w=1+(q-2)*K, z=3+K*(2q-1).
```

Keep `f,i,T,n,eta,zeta,y,gamma` arbitrary positive. The fixed scalar facts,
checked directly from the hash-pinned current port bytes, are

```
Nt=1, R odd, R>=26, R+1<E,
bit_length(X)=283975, bit_length(R)=378068, R>=bit_length(X),
```

where `X=wq`, `Y=q³`, `E=XY`. Thus `X<2^R` without materializing `2^R`.
The fixed port `q` is even and at least 32. The earlier packet gives the
first-Pell construction, but that alone does not satisfy the other norms.

## Hypothetical full-zero consequences

Suppose for contradiction that the complete candidate output vanishes.
With `S=i*Delta*c²`, the strong factor is
`Delta*(f²-Delta*i²*c⁴)`. Since `Delta>0`, cancellation gives a product
of five integer factors equal to 1. All are integer units. The first Pell
factor cannot be -1 by the consecutive-product descent in
`../carrier65-independent/PROOF.md`; the main and normalized strong factors
cannot be -1 modulo 4 because `Delta=a²+4a+3` is 0 or 3 modulo 4; and the
auxiliary factor is congruent to a square modulo 4. Thus all five factors
are 1. In particular

```
tau² - (E*Y)*(E*Y+1)*k² = 1,
D² - Delta*c² = 1,
f² - Delta*(i*c²)² = 1,
S²*(V²-y²)+y² = 1,
D = X+a*c+gamma*H.
```

Here `k=eta+zeta`, `c=Y*k+eta`, `a=E+Y`, `H=4a+3`, and
`V=f²*(c*T-R)-c`. The first carrier has `tau=E*n+k-R>0` because `R<E`.
The first Pell classification gives a positive index `j` with
`k=2*psi_(2EY+1)(j)` and `tau=chi_(2EY+1)(j)`. As in the prior packet,
`k=2j (mod E)` and the carrier gives `2j=R+1 (mod E)`; the strict
`R+1<E` makes this the natural remainder equality. The Pell recurrence also
gives `k=2j+4EY*t` for some natural `t`. The positive main root has a Pell
index `r` with `D=chi_(a+2)(r)` and `c=psi_(a+2)(r)`.

## Exact and power theorem bindings

The only non-immediate hypothesis is the auxiliary absolute-difference form
used by `P72Exact.indices_ordinary`. The strong norm gives
`S²=Delta*(f²-1)`. Since `c>=2`, it also gives `f²>c+1`. If `y=1`, the
auxiliary equation forces `V=±1`, but then `f²` divides the strictly
positive integer `c±1<f²`, impossible. Thus `y>1`; the auxiliary equation
then gives `y>|V|`. Set the theorem's natural offset `u=y-V>0`. Its two
absolute differences are `|V|` and `y`, respectively, and its auxiliary
equality is exactly the rearrangement

```
Delta*(f²-1)*V² + y² = 1 + Delta*(f²-1)*y².
```

The checker verifies this algebra as an exact sparse-polynomial identity.
Apply `P72Exact.indices_ordinary` with its `q,X,Y,k,R,g,c,a,y0,i',f,T,u`
set to the displayed values with `g=D`, `y0=1`, `i'=Delta*i`, first index
`j`, main index `r`, modulus `E`, and the Pell quotient `t` above. Its
listed positivity, size, congruence, main, strong and auxiliary hypotheses
are then the preceding facts. It yields `r=R` and `2j=R+1`.

Next apply `P72Power.power_of_mod` to these indices. The main carrier gives
`D = X+a*c (mod H)`; `eta,zeta>0`, `X>=q>=32`, and the remaining inputs
are as above. That theorem yields `X=2^R`, contradicting the fixed bit-length
inequality. Equivalently, `w=1+(q-2)K` is odd and greater than 1, so
`X=wq` has an odd divisor greater than 1 and cannot be a power of two.
Thus the particular fixed scalar family cannot give a full zero
under the stated theorem application. Other candidate inputs, including other
outside-guard points, are not excluded by this argument.

The same hypothesis binding gives a general **necessary condition**: any
positive 64-candidate zero with `q>=16`, `R>=26`, and `R+1<E` has
`X=2^R`, subject to those existing theorems and their model/provider scope.
Because `q|X`, its `q` must itself be a power of two. For the current fixed
`beta=2^B-1`, `beta | q-1` then implies `q=2^(B*h)` for a positive integer
`h`: dividing the exponent by `B` leaves a remainder `r<B`, and
`2^B-1 | 2^r-1` forces `r=0`. The rank-window assumptions are essential to
this application; no claim is made that every candidate zero satisfies them.

## Reproduction and boundary

`check.py` pins both generic theorem source files and the complete current
graph, verifies the four compressed and raw port hashes, checks the fixed
scalar inequalities and operation-independent auxiliary identity, and prints
the retained [result.json](result.json). It does **not** replay Lean or
mechanically discharge the source theorems' hypotheses for this graph. The
exact binding was independently reviewed in
`../../reviews/current14-carrier64-bad-gap-exclusion-independent/`; inherited
source/object, transitive-provider, model and external-file limitations remain.

```sh
python3 -I -S -B research/current14-carrier64-bad-gap-exclusion/check.py > /tmp/carrier64-bad-gap.json
cmp /tmp/carrier64-bad-gap.json research/current14-carrier64-bad-gap-exclusion/result.json
```
