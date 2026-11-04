# Positive trace coordinate from exact residues

`Trace74CoupledPositiveT.positive_T_of_residues` proves in any `IΣ₁`
model that the explicit hypotheses

```text
f>0, c>0, (Q+c) mod f=0, Q mod c=N mod c,
f mod c=1 mod c, and f(N+c)≤Q+c
```

give an internal `T>0` with `Q+c=f(cT+N)`. This is the positive trace
coordinate equation when the signed rank is `−N`. The proof constructs a
divisibility quotient, uses model modular cancellation, and obtains a
positive second quotient from the stated size bound.

The size bound and all three residues are explicit premises. The theorem
does not produce them from a Pell orbit, bind any graph coordinates, prove
a 74 zero, or establish an iPRA theorem.

Lean 4.32.0 was run with `LEAN_PATH=/tmp:` followed by
`/tmp/trace74-direct-four-block-1zltaw2f/lib` and
`/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`, `timeout 120`,
`-M3000 -j1 -DElab.async=false`, this directory as `--root`, and output
`/tmp/Trace74CoupledPositiveT.olean`. Actual session 15765 exited 0
without warnings and reported only `propext`, `Classical.choice`, and
`Quot.sound`. A prior attempt failed on equality orientation.

Source SHA-256:
`a3e8e411d7909b6e6ea1314bc5c0147a30d870e38982a11b9a69a0c5ccd52152`.
Output object SHA-256:
`565f77a92282333715a11d08fbe9acec3dcc24a2cfdcb0e0252cf0f58be36038`.
Direct imported objects:

```text
Trace74CoupledExactSigns.olean           7351915decc5e68515447bf5c506eb52423ec5e4c523fde7566deb82f679aceb
ArithmeticModularCancellation.olean      c48382ae6b1af87fa6adab6ab5f54ad74d83a00d1e110fa611cf53ac57288448
```

The captured providers, transitive/package/dynamic ancestry and
search-path resolution are not independently authenticated. This is not
a coherent current-source rebuild or an independent replay.
