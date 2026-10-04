# Independent bounded reauthentication of the knot-interface review

PASS within the stated scope. I read the complete frozen review and independently read its six immutable source spans: `Topology/UnknotRecognition/README.md` lines 1–128, `synthesis/README.md` lines 1–58, and `synthesis/report.tex` lines 1–240, 384–433, 489–525 and 580–612 at commit `78333302d9babf0efb1a5d218e122f13c35bb306`.

A fresh, separate metadata checker authenticated the three frozen review inputs, the commit and parent, all three Git blob identifiers, complete-file sizes and SHA-256 values, line counts, and all six span boundaries, sizes and hashes. The totals are **3 files, 6 spans, 546 read lines and 32,366 span bytes**; the complete files contain 48,823 bytes. No discrepancy was found. This does not reconstruct the original reviewer's historical working-tree equality assertion.

## Conditional mathematical challenge

The computability boundary is sound: if a total computable map sends every machine/input pair to a valid finite diagram, and a total decider on that domain returns true exactly when the machine halts, composition would decide halting. The same argument applies to the decider's complement. Mapping into the promised valid domain is essential; a resource-capped procedure that can return `UNKNOWN` is not the hypothesized total Boolean decider. The frozen review maintains these distinctions and does not rely on an externally certified topology theorem for this conditional argument.

The alternative expression `exists T: D(g(M,x,T))` is correctly conditional on a separate proof that the family represents accepting histories. It is not a universality claim for arbitrary decidable `D`, and supplies no fixed-arity integer compiler by itself.

The stated iteration comparison also checks: assuming `g <= n^O(1)` and `L = O(log n)`, the logarithm of `L(g+1)^L` is `O((log n)^2)`. This controls the displayed iteration factor only. Encoded representation sizes, work per iteration and restart counts remain additional running-time obligations, exactly as the review says.

The read passages distinguish an exact-recognition interface from the open quasi-polynomial implementation target and preserve reported experiment limitations. I found no correction needed within this bounded interface scope. I did not certify recognizer code, topology lemmas, external theorem versions, empirical width estimates, benchmarks, data tables, omitted manuscript sections, or the unresolved detailed grid move-set obligation. There is no new arithmetic source, ordinary-integer encoding or universal-operation bound from this review.

## Frozen inputs and fresh evidence

The reauthenticated root review pins are:

- MD: `3b90ea02fa0b192d30c3d2c72036e25a672eaed293a00e459d7a365cbbf7b6a8`.
- JSON: `da5e6ed5a8ef9c507197957739cec761e24790ff5694db75757386e3ae667930`.
- Collector PY, authenticated as inert bytes only: `802ae783c28d8b9024d3bd157c577f4e56139195c6a97e346cb2d07e44caea91`.

The independent checker `/tmp/reauth_unknot_interface_78333302d.py` has SHA-256 `28df6b3a6cc4c8afb6e983128db73bdda4401646724889de1e114579eae6a7de`. Its receipt `/tmp/reauth_unknot_interface_78333302d.json` has SHA-256 `f0a61d16ec3796a143eda790843f2db8e075c49ef3c86caf5a883808bcb0dc9b`. Fresh normal and optimized (`-O`) exact replays from `/` both passed. Only this new standard-library metadata program ran, using read-only Git operations. No supplied, archived, frozen or copied predecessor program was executed or imported; no build, external fetch, repository edit or Git mutation occurred.
