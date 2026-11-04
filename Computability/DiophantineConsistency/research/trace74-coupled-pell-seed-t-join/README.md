# Constructing a strong Pell seed and compatible positive trace coordinate

`Trace74CoupledPellSeedTJoin.exists_seed_and_T` proves in every `IΣ₁`
model: for arbitrary internal `a,c,tau,j,N`, if `c,tau>0`,
`c=ycoord (4j+1) a`, and `N mod c=(4j+1) mod c`, there exist the
**same** positive internal `t,i,T` satisfying `c|t`,
`ycoord t a=c² tau i`, and, with

```text
phi=xcoord t a,  f=xcoord (2t) a,
I=delta(a)ycoord (2t) a,  s=f(N+c),
Q=oddQuotient (2(j+t(2s+1))) (I−2),
```

the identities

```text
phi²=1+delta(a)(i c²)² tau²,
f=1+2 delta(a)(i c²)² tau²,
I²+delta(a)=delta(a)f²,
Q+c=f(cT+N).
```

The proof combines the constructive divisible Pell seed with the checked
positive odd-shift T construction, and derives the two square shapes
from Pell norm and doubling. The main-ordinate and negative-rank magnitude
residue are explicit premises; this module does not provide CRT, carrier
coordinates, an actual graph zero, external payload binding or an iPRA
endpoint.

The Lean 4.32.0 author check used `LEAN_PATH=/tmp:` followed by
`/tmp/trace74-direct-four-block-1zltaw2f/lib` and
`/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`, `timeout 120`,
`-M3000 -j1 -DElab.async=false`, this directory as `--root`, and output
`/tmp/Trace74CoupledPellSeedTJoin.olean`. Actual session 84355 exited 0
without warnings and reported only `propext`, `Classical.choice`, and
`Quot.sound`.

Source SHA-256:
`107344f643bfa614f7e44f9908196a0ef000806a3cd1e585fba7b8196edfa262`.
Output object SHA-256:
`f3fe70d8a8a12f88faf11e24532b4f51532dc535dc1bd3fb7c42b37e3fa280cd`.
Direct imported `Trace74CoupledPellStrongSeed.olean` SHA-256:
`64ddb5b1ed1be97e7bc7160b5c811cd638529ce10c2cc377aec08dcc7c1a1329`.
The captured providers, full transitive/package/dynamic ancestry and
search-path resolution are not independently authenticated. This is not a
coherent current-source rebuild or an independent replay.
