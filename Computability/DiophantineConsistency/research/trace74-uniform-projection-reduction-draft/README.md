# Variable-parameter projection reduction

`Trace74UniformProjectionReduction.reduce` proves an all-commutative-ring
consequence of the weighted projection, with an arbitrary ring parameter
`L` and `K=4L`. It turns divisibility of
`h X (X-K) (K X+1)` by `H=4Y(X+1)-1` into divisibility of
`h (4Y-1) (4(K+1)Y-1) ((K-1)Y-L)` by `H`. No positivity, graph zero,
standard-index, or power-of-two hypothesis is needed. The source comment
calling it an unchecked draft predates the author check below.

This does not produce its projection premise from a graph zero or prove
`K=4L` for the graph's odd model index. The strict height bound, same-tuple
join, reverse guard and iPRA endpoint also remain open.

The bounded author check used the following captured provider paths in order:

```text
/tmp/trace74-guardfree-projection-flwoh06_/lib
/tmp/trace74-graph-index-upper-sbqz0413/lib
/tmp/trace74-index-upper-lw94r446/lib
/tmp/trace74-index-order-vu44__7n/lib
/tmp/trace74-guardfree-residue-9rz_sl3r
/tmp/trace74-guardfree-offset-g91osrrh/lib
/tmp/trace74-odd-ordinate-bound-b8rmryeu/lib
/tmp/trace74-guardfree-fold-mqg70pbn/lib
/tmp/trace74-guardfree-adjacent-e85cpupi/lib
/tmp/trace74-guardfree-pell-jg0_m3mj
/tmp/trace74-arbitrary-root-wppvu6hp/lib
/tmp/trace74-direct-four-block-1zltaw2f/lib
/tmp/absorb89-chain-8h1sfgle/lib
/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

With those paths joined by colons in `LEAN_PATH`, Lean 4.32.0 was invoked as
`timeout 120 lean -M3000 -j1 -DElab.async=false --root=<this-directory> Trace74UniformProjectionReduction.lean -o /tmp/Trace74UniformProjectionReduction.olean`.
Actual tool session 9694 exited zero and reported only `propext` and
`Quot.sound`. Source SHA-256 is
`c3af141cde0c1d7a9e0824448f0714cc0a2e32804e6334612c6e29811707a115`;
output object SHA-256 is
`6a0cc98e1ec41e57cd816d3234c52e6d3e4cfbe06785227cc72f281614fc5f70`.
The direct `Trace74Projection.olean` has SHA-256
`6465507ef633e37d54e61182779c698d5d2da3aaf5f9c5c8963b62944b19bc77`.
This check does not authenticate the complete transitive provider or package
ancestry and is not an independent replay. A separate source review verified
the displayed algebra and its stated scope without running Lean.
