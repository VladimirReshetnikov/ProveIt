# Combined exact auxiliary Pell signs

`Trace74CoupledExactSigns.exact_pair` proves in every `IΣ₁` model that,
for the same internal quantities, set

```text
h=j+t(2s+1),  f=xcoord (2t) a,  Q=oddQuotient (2h) (I−2),
```

and assume `I≥2`, `c>0`, `I²+delta(a)=delta(a)f²`, `c|I`, `c|t`, and
`c=ycoord (4j+1) a`. Then

```text
(Q+c) mod f = 0,     Q mod c = (4j+1) mod c.
```

It joins the two checked even-half-index residue lemmas with the odd-block
Pell anti-period, preserving the same quotient, indices and modulus
variables. This is the exact sign combination used by the proposed
coupled-Pell strategy. It does not produce the norm/divisibility
assumptions, CRT rank, positive graph coordinates, a graph zero, or an
iPRA theorem.

The Lean 4.32.0 author check used `LEAN_PATH=/tmp:` followed by
`/tmp/trace74-direct-four-block-1zltaw2f/lib` and
`/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`, `timeout 120`,
`-M3000 -j1 -DElab.async=false`, this directory as `--root`, and output
`/tmp/Trace74CoupledExactSigns.olean`. Actual session 66654 exited 0
without warnings, reporting only `propext`, `Classical.choice`,
`Quot.sound`. An earlier attempt failed on rewrite direction.

Source SHA-256:
`5169fde2202a7323665ec6a2ecb79a255105edda1025229715c9cf291bf68e93`.
Output object SHA-256:
`7351915decc5e68515447bf5c506eb52423ec5e4c523fde7566deb82f679aceb`.
Direct imported object hashes:

```text
Trace74ExactAuxIndexResidue.olean cc2366efe799a1f9031f5f45817ec790a480211ad8f0c13c0f8ba2efcf80948e
Trace74PellOddAntiperiod.olean    da03fcc3c55f905487961e022aed28726b8b2741bb20cc033eed43e56a799e2e
```

The temporary captured providers and full transitive/package/dynamic
ancestry and search-path resolution are not independently authenticated.
This is not a coherent current-source rebuild or an independent replay.
