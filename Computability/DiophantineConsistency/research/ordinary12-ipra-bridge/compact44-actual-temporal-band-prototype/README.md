# Actual-exponent bit rotation: model-only author exploration

`ActualTemporalBand.graph_temporal_word` checks a model-only step toward replacing the explicit temporal product in the graph-band congruence. Given `0<n`, positive `M=Exp.exp (67*n)-1`, `q=Exp.exp (67*n)`, `0<u`, `C=q-u-v`, `w=Exp.exp (R-67*n)`, and `(A+w*C)%M=F`, it proves:

- `(A+temporalWord n (R-67*n) C)%M=F`;
- the bit-rotated temporal word is below `Exp.exp (67*n)`;
- each of its radix-67 digits is at most `Exp.exp 67-1`.

`temporalWord` rotates at the **bit** level by `(R-67*n)%(67*n)`. Neither the theorem nor the proof assumes 67 divides the temporal exponent, or gives its digits the bound 3. It uses the source-word bound from `BandCarryInputs` and `CompactBitRotation.replace_temporal`/word and digit bounds. Its premises are explicit, and it does not itself call or instantiate a graph theorem.

The actual witness from `SymbolicGraphBand.fixed_symbolic_bands` supplies the corresponding facts with `n=8807*N`, `u=v 1`, the same `N,w`, and its original q,R,C: the q and w exponents require associativity, modulus positivity comes from the graph's positive port product after identifying the modulus, and `0<u` comes from positive coordinates. This is a proof route, not a checked fixed-graph client in this packet.

First `CompactBitRotation.lean` was rebuilt from its committed source on the coherent direct-K/band **author** overlay (attempt 20, compiler exit 0). Then `ActualTemporalBand.graph_temporal_word` checked in Lean session `68978` (attempt 21), compiler exit 0, no sampled stop or source drift, with source SHA-256 `ef5579337f2af02063c63ad6d2aa39dcbe864fbabfcb4512596cc4e0fbe2c1b9`. Its named declaration reports `{propext, Classical.choice, Quot.sound}`; these are Lean metatheory dependencies, not an internal PRA proof. Both exact logs and receipts are retained.

The tmpfs runner is retained in `compact44-model-band-cut-prototype/observations/runner.py`. It checked the 14 prior frozen source/object hashes and pinned the earlier `TwoBand`, `KCast` and symbolic-band-cast objects. The directly imported `CompactBitRotation` and `BandCarryInputs` objects were separately observed at SHA-256 `c81a52d9ec7e12a0f0f935c8a63359749601cac3357532483ebc1dd0f04dd1d8` and `ce2fc0fc17ae485f995c23b122c98341c20246147a9d55b152cef4cd349100e9`; the runner did not guard both at every boundary, run a separate exact `--deps` query for the client, or re-audit the inherited full provider. Attempt 21 sampled peak RSS 1,815,683,072 bytes and minimum tmpfs free 353,218,560 bytes. The custom monitor's observations are sampled; this is not guarded-pair machinery.

This does not prove the full finite-family weighted graph-column identity, any clean predecessor or stronger temporal digit bound, NoCarry or decoder premises, equality to retained bytes/display, machine equivalence or internal iPRA equivalence. A separate fixed same-witness client and a corresponding-side guarded replay remain needed.
