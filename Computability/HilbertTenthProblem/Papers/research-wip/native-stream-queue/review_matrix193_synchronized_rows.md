# Independent review of the synchronized four-coordinate matrix orbit

**PASS; no requested change.** I read the full new proof and helper, the inherited context transfer and directed-marker proof, and the relevant first-row interface. The arbitrary-length reduction is exact for the stated group target. The emitted local equation is fully paid, but it does not by itself pack an unbounded history into a fixed-arity polynomial.

The reviewed immutable trio is:

| File | SHA256 |
|---|---|
| `matrix193_synchronized_rows.py` | `da55246efc8047b6b3f188579cf6c71bbabb067def3fe04ac47ba61b56517e52` |
| `matrix193_synchronized_rows.json` | `9ce8537fc12bff3a2d3d91297d65a47ee6a7af193ff4bb08f474216260ef4233` |
| `matrix193_synchronized_rows.md` | `ab768aa392841add5dc6dfcd8ed62564ca17fae2fe80e5ec39f1f4ceb36559d2` |

For a common sequence s, the two row accumulators represent H(s)C and M G(s). The conjugation K_i=C^(-1)H_i C gives the required right-action order, and the B phase of the original positive product is precisely G(s)^(-1), with reversed factor order. Both full matrices remain in H', so the inherited first-row theorem makes row equality equivalent to full equality. The lower-marker theorem supplies the reverse implication for every original product. The empty row orbit corresponds to the nonempty original product C; that boundary is correctly retained.

The local predicate is the product of 96 nonnegative quadratic factors. Each factor simultaneously tests both updates for one shared tile. Thus its zero set over the integers or reals is the union of the intended 96 graphs, without an independent selector for each row. Summing these nonnegative local predicates over a fixed number of steps, together with the endpoint sum of squares, is valid. The stated 2040d+5 bound includes every local source, the five endpoint operations and d combining additions. Its signed witness count grows with d, and it supplies no fixed-arity arbitrary-duration certificate. The exact ordinary-input index remains an external obligation in this particular interface.

I independently interpreted the saved source using exact rational sparse coefficients and reconstructed all 384 linear residuals and all 96 complete quadratic branch polynomials directly from the saved matrix entries. Every branch has coefficient 1 on next_x0 squared. Therefore the full product has coefficient 1 on next_x0 to the power 192, independently certifying the local exact degree. The complete source recount is 2039 operations, including 1103 multiplications; the author also checks full source liveness and all 95 finalizer multiplications. The degree claim is correctly weakened to an upper bound after fixed initial-state substitutions.

Fresh installed normal and optimized exact replays from `/` passed. They authenticate all five dependencies, reconstruct the actual 96 transition pairs, evaluate the complete 83-step accepted trajectory and all 96 branch fixtures, and compare 16 whole signed/rational evaluations. Their finite examples corroborate the unrestricted proof; they are not its basis. No frozen predecessor or archived program was executed or changed.

The complete universal bound remains 84 operations. The reduction provides a smaller exact state interface for subsequent history packing; its 2039-operation one-step source is not a claimed universal improvement.
