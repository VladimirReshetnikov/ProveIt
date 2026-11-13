# A linear internal lower bound for the odd Pell quotient

`Trace74AuxQuotientGrowth.index_le_odd_quotient` proves in every `IΣ₁`
model and for arbitrary internal `h,b` that

```text
2h+1 ≤ oddQuotient h b.
```

The proof uses the existing `time≤ycoord<xcoord` bounds, the next Pell
abscissa recurrence, the exact odd quotient and cancellation of the
positive base. It requires no additional induction. This is a general
growth lemma; it does not itself select an auxiliary shift, prove a graph
zero, or establish an iPRA theorem.

Lean 4.32.0 was run with `LEAN_PATH=/tmp:` followed by
`/tmp/trace74-direct-four-block-1zltaw2f/lib` and
`/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`, `timeout 120`,
`-M3000 -j1 -DElab.async=false`, this directory as `--root`, and output
`/tmp/Trace74AuxQuotientGrowth.olean`. Actual session 5497 exited 0
without warnings and reported only `propext`, `Classical.choice`, and
`Quot.sound`. An earlier attempt had an unqualified identifier.

Source SHA-256:
`370868d8195f9d595c00c5eca36851bf6775e4170fb0d1b7187bba64ae954806`.
Output object SHA-256:
`eab2a365d8486f28d6f1de64895f5bf09c9ab3350cc552ae6fcc3791135b1663`.
Direct imported `Trace74CoupledPellTJoin.olean` SHA-256:
`45ee424ee6f5baf1bcef8d75ed7e8ded07b5acebfcc73d6cb4b7c60e9df8899b`.
The captured providers, full transitive/package/dynamic ancestry and
search-path selection are not independently authenticated. This is not a
coherent current-source rebuild or an independent replay.
