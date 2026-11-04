# Constructing the divisible strong Pell seed

`Trace74CoupledPellStrongSeed.exists_strong_seed` proves in any `IΣ₁`
model that for arbitrary internal `a,c,tau` with `c,tau>0`, there are
the **same** positive `t,i` satisfying

```text
c|t,   ycoord t a = c² tau i,
f=xcoord (2t) a,   I=delta(a)ycoord (2t) a,
I≥2,   c|I,   f mod c=1 mod c,   I²+delta(a)=delta(a)f².
```

The proof uses the model Pell pigeonhole theorem to find an ordinate
divisible by `c² tau`, then takes a multiple of that index by `c` and
uses strong Pell divisibility. The doubled Pell identities discharge the
strong norm and `f` residue for that same index. These are arithmetic
model witnesses, not a full 74 graph valuation, a CRT rank construction,
external fixed-payload binding, or an iPRA endpoint.

The Lean 4.32.0 author check used `LEAN_PATH=/tmp:` followed by
`/tmp/trace74-direct-four-block-1zltaw2f/lib` and
`/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`, `timeout 120`,
`-M3000 -j1 -DElab.async=false`, this directory as `--root`, and output
`/tmp/Trace74CoupledPellStrongSeed.olean`. Actual session 48107 exited 0
without warnings and reported only `propext`, `Classical.choice`, and
`Quot.sound`. An earlier run failed on an elaboration of positivity.

Source SHA-256:
`6730ad271724a6926a32f9f3a1aa56c4f91260c7c6f9934076be6e2eaba43637`.
Output object SHA-256:
`64ddb5b1ed1be97e7bc7160b5c811cd638529ce10c2cc377aec08dcc7c1a1329`.
Direct provider object hashes:

```text
Trace74CoupledPellPositiveShift.olean   1f0d8d2a712f8c995dbba5af95db30f9f6f477ce94a90ac9f6cb9a4f2ca89383
ArithmeticPellPigeonhole.olean          c3eb02d03ffa9ab3b6f27cc09248a75fcca3c0ac33d6a18d3aa25d00abd944e1
ArithmeticPellStrongDivisibility.olean  c473cd309c31e118c0845048b6c9e755b60157dbe6b8ea9b822349a00d63ebd2
```

The captured providers, full transitive/package/dynamic ancestry and
search-path resolution are not independently authenticated. This is not a
coherent current-source rebuild or an independent replay.
