# Bounded aligned words and a reduced residual: author-side exploration

On the coherent direct-K/band author provider, four small IΣ₁-model lemmas checked facts useful for a future heterogeneous carry input:

- `source_word_bound`: if `q=Exp.exp (67*n)` and `0<u`, then `q-u-v < Exp.exp (67*n)`. This can be applied to the graph's `C=q-v 1-v 2`, but this lemma itself has no graph premise.
- `aligned_rotation_bounds`: if `0<n`, `C<Exp.exp (67*n)` and all its radix-67 digits below n have cap D, then any rotation by `e%n` remains below the same word bound and has the same digit cap. The graph's C digit bound can supply D=3 at the same witness.
- `residual_bounds`: for positive `M=Exp.exp (67*n)-1`, the reduced word `T%M` is below `Exp.exp (67*n)` and its digits are at most `Exp.exp 67-1`. This permits the general temporal product `T=w*C`; it assumes no radix alignment and does not claim a sharper temporal cap.
- `normalized_congruence`: if `(A+T)%M=F` and `0<M`, then `(A+T%M)%M=F`. Thus a separately proved graph-band congruence can use the reduced residual as a finite-family word.

Actual Lean session `29045` (attempt 19) exited 0 with no sampled stop or source drift. Each of the four declarations reports exactly `{propext, Classical.choice, Quot.sound}`; those are Lean metatheory dependencies, not axioms of an internal PRA derivation. The successful source SHA-256 is `99741977abae45163ecbb94dd4caa03daec0cf1db370dff0ca7ba641dbe29cf5`. Attempt 18 exited 1 because the proposed `mod_mod'` name was not in scope; its first three reports lack `sorryAx` but the failing fourth report includes it. The failed source and exact logs for both runs are retained.

The exploratory runner is the one retained in `compact44-model-band-cut-prototype/observations/runner.py`. Both runs used its coherent direct-K/band author overlay; attempt 19 sampled peak RSS 1,816,920,064 bytes and minimum tmpfs free 353,378,304 bytes, with a 128 MiB sampled stop and 120-second timeout. The receipt records the actual compiler exit separately from the runner's outer exit. These are sampled resource observations, not a guarded pair or full provider re-audit.

These lemmas do not themselves assemble the two 943-selector bands, two 41-copy bands, five bare rotations and one residual into the externally finite `CarryInput` family, prove its weighted mass bound or output bound from the graph, derive a clean predecessor, identify retained coefficient bytes or the displayed equation, establish a decoder or machine equivalence, or construct an internal iPRA proof. In particular the full-radix residual cap gives no clean-column or half-radix predecessor guarantee.
