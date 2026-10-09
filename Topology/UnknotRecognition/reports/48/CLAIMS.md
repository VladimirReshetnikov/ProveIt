# Claims and limits

**Proved here, with the standard exact SLP-equality primitive:** native compressed C2*C3 reduction, an O(s²(B+1)) arena-size bound, sound polynomial-size replay certificates, complete uncapped three-braid closure recognition, native singleton-forest recognition when every leaf has at most three strands, the full-matrix materialization obstruction, and a three-braid-exempt hybrid minority bound.

**Imported, not claimed new:** the explicit three-braid classification already present in fastunknot; polynomial compressed conjugacy in fixed hyperbolic groups; exact SLP equality; Bennequin's inequality; the closed-braid Alexander formula; singleton connected-sum topology; the existing local minority bound; rank-one Khovanov unknot detection.

**Complete composite algorithm, proved but not wired into this package:** with a complete exact 2^O(k)-time fallback, the cost is poly(g) + sum over unresolved wider factors of 2^O(kappa_i), where kappa_i is the minority-sign count. A quasi-polynomial bound follows when the largest exceptional kappa_i is O(log² g). The delivered forest API returns INCONCLUSIVE for unsupported factors rather than silently invoking a fallback.

**Actually tested:** 42 unit methods, 87,381 exhaustive braid words through length eight with replay and two algebraic controls, 400 random shared grammars and forced-fallback quotient checks, expansion-forbidden capacity and forest checks, and paired local benchmark samples. See results/ for exact counts and timing scope. Of the exhaustive words, 46,376 have one-component closures.

**Not done or not established:** a general quasi-polynomial algorithm on arbitrary knot diagrams, formal proof-assistant verification, actual upstream factory injection, the full maintained regression suite, a Rust port, production pipeline timing, a hard-knot corpus speedup, and a certified arbitrary-PD-to-SLP producer.

The certificate verifier is independent of producer reduction and LCP search, but shares exact string primitives and imported topology. Finite resource caps may yield INCONCLUSIVE even in a mathematically complete domain. The polynomial theorem concerns the uncapped procedure; increasing caps until it completes recovers that algorithm. No timeout is interpreted as a knot verdict.
