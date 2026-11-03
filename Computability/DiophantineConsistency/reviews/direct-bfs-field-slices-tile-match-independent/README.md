# Independent review: direct-BFS field slices and graph tile matching

This review checks frozen `DirectBFSFieldSlices.lean` and `DirectBFS80TileMatch.lean` and their accepted author receipts. `check.py` verifies current source, runner, copied source, output and logs against receipt hashes, pre/post pins and direct import snapshots, and first selection of all eight source-direct imports on the recorded `LEAN_PATH`. The runners explicitly resolve and pin their direct imports. Precise paths, hashes, and receipt hashes are in `check-output.txt`. This is not a Lean replay; full transitive provider selection, source-object, package and dynamic-library ancestry remain inherited. The finite vertical-position theorem's author report is `[propext, Quot.sound]`; the other printed declarations report `[propext, Classical.choice, Quot.sound]`. The logs show no error, warning or `sorryAx`.

The generic field-slices packet is conditional in an arbitrary `IΣ₁` model. `DirectBFSDecodedPayloadBits.bit` identifies one payload bit with its digit in the copied block assuming the block bound, uniform-band inputs, and the copy-word equality for the specified direct tile index. `DirectBFSVerticalFieldBits.fields` assumes **both** involved blocks have those inputs and the specified tile equalities, `0<N`, `h<N`, `s<N`, and all nine explicit vertical digit-matching equalities. It equates the first direct tile's slice `(25,9)` with the tile at `cyc N h s` slice `(8,9)`. The horizontal theorem assumes the corresponding two block inputs/tile equalities and eight horizontal digit matches; it equates slice `(17,8)` at h with slice `(0,8)` at `cyc N h 1`. These declarations do not independently derive their premises from a graph zero.

`DirectBFS80TileMatch.graph_tile_match` assumes all ten coordinates positive, actual `InternalZero (graph (integerPorts p)).output v`, and the four exact symbolic ports `p 0=betaNat`, `p 1=DirectBFSSymbolicKernel.paramKernel rho`, `p 2=lowNat`, `p 3=betaNat+highNat`, in an arbitrary `IΣ₁` model. It concludes existence of **one common** internal `N,W,s`, `0<N`, `s<N`, the q-exponential identity and the exact temporal-shift equation

```text
((rankNat p v - 67*(8807*N))/67) % (8807*N) = 8807*s.
```

For that N and W it has `Blocks 10 (row (Cnat p v) N 1) N W`: the word is bounded by `2^(10*N)` and its base-1024 digit at every internal `h<N` is the row index. For every such h it supplies indices `i,j,l : Fin 943` identifying the word rows at h, `cyc N h s`, and `cyc N h 1`, respectively, and proves the **natural label** equalities

```text
(row i).south = (row j).north
(row i).east  = (row l).west.
```

The proof reconciles the three separately obtained N values using exponent injectivity and nonzero-multiplier cancellation, then uses the same N in the word, decoder and field families; it joins field slices to typed direct-row labels using the same indices. The statement does not claim `s>0`, additional distinguished boundary colors, original-table conjugacy/lifting, machine halt, converse, iPRA derivation, or formal equality with the external equation's JSON/PDF bytes.

The accepted field-slices object is SHA `a05523b42e4f25203d88f1ab2aa3a2a1fe966fc0927633d47b9ab4c14bf97079`; the graph tile-match object is SHA `fdbb44ab0a96a8b835f168be5a261cefe05e1dc3a2b79ac6563969c25d732ed5`. Their direct imported word, marker, uniform-decoder, field-slice and tile-field object hashes match the previously reviewed frozen providers.
