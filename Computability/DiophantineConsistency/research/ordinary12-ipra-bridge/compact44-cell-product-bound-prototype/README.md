# Compact cell and symbolic-kernel product bounds

`CompactCellSizeBound.packedCell_lt_support` proves, in any model of IΣ₁,
that the actual represented `packedCell a d` is below `2^(67*3297)` when
`a ≠ 1` and `d ≤ 1`. The bound follows because every nonzero local digit
lies in the symbolic low-mask support, whose largest position is 3296. The
argument reconstructs the 8807-position cell from its 3297-position prefix;
it does not rely on evaluating the model word as an external numeral.

`CompactCellProductBound` casts the earlier proved natural inequality
`paramKernel rho < 2^592884` into the same model. It combines that inequality
with the cell bound to establish the concrete `hi_lt` product condition

```
(paramKernel rho) * x < 2^590069 * 2^590069
```

both for `x = packedCell a d` with `a ≠ 1`, `d ≤ 1`, and for
`x = packedCell a 0 + 2^(67*1063)` with `a ≠ 1`. This supplies a key
product-size ingredient for base and pulsed words, but does not establish
the remaining cell-sum, block-positivity or high-mask conditions, a complete
packing or graph zero. The symbolic kernel and mask remain subject to their
separate literal-byte binding limitations.

The guarded size check, session `87004`, exited 0. The product check's first
attempt exited 1 on two local notation/elaboration errors; its failed source
and log are retained. The corrected product check, session `21475`, exited
0. Both successful checks had unchanged direct import/companion guards, no
warnings or `sorryAx`, and all eight named axiom reports list only
`propext`, `Classical.choice`, and `Quot.sound`. The product runner built a
project-provider overlay with 517 distinct names and 338 overlapping pairs;
each pair had matching SHA-256 values and all recorded provider file hashes
remained unchanged after the run. The full inventories and observations
are retained; the `/tmp` providers are ephemeral. These are single-author
incremental checks, with inherited source/object, transitive, package,
dynamic-loading and between-observation ancestry; no independent paired
replay or authenticated complete closure is claimed.
