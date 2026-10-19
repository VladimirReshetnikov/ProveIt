The exact source snapshots, reviewer scripts, original note and records named
below are preserved in [history.json.gz](history.json.gz). This is a review of
the specified historical commit; later implementation does not change its scope.

---

Source review of e4f8bd17625cedbd302813d48c66e1281aa9545b, at merged HEAD 1989c67acb.

No substantive mathematical blocker was found in the complete 399-line `ArithmeticDagRun.lean` and 616-line `ArithmeticL2Lib254.lean` read. This is a source/API review, not local Lean elaboration or an axiom audit. The author reports zero-warning compilation in the commit message; the commit delivers only the two source files. Both explicitly set `maxRecDepth 8192` and `maxHeartbeats 4000000`.

`ArithmeticDagRun.Occ` (line 82) relates an externally fixed DAG edge, occurrence control, and exit map to literal interpreter rows. Its car/cdr exit maps match the sixteen `RMDag.Run` constructors, including decrement-zero break, break depth reduction, and cdr continuation/restart. `occ_of_occB` proves soundness of the finite Boolean occurrence test. `IRun` (134) is conditional on every such occurrence; it does not assert that an occurrence exists. `Reach` ignores the output file for halt, consistently with the absorbing numeric zero convention.

The key new proof is `run_iterate` (364): it fixes an occurrence before induction and uses `t ≤ N → ∃ s, run s (live c (G 0)) = live c (G t)`. The fixed control and exit-map parameters stay outside the arithmetic predicate. Explicit Σ₁ definability of `run` and `G` suffices; the intermediate file function `H` need not be definable, since it is used only in the step argument. This avoids incorrectly applying Σ₁ induction to the universally quantified `IRun` predicate, while permitting nonstandard internal `N`.

`ArithmeticL2.enc` (52), `lreg_enc` (67), and `lupd_enc` (92) reconcile the logical fields with physical order `[ws,pl,tw,p1,ac,s2,np,p2,s1]`. The logical-to-physical map is `[6,2,0,4,3,7,8,5,1]`. `IR` (112) specializes directly to `DagControl254.rowsLit/run`, hence the same packed 6,460-row interpreter used by W3's `ControlBisimRotation240.halts_iff` (88); it does not reuse the older Prog254 control numbering. The 19 primitive loop contracts match the predecessor L2 statements with internal values substituted for Nat: eleven transfers, six copies, and two clears. Their row shapes and register separation agree with `Dag254`.

`pair162` (528) proves the full-file effect `s2 := s2 + cantor s1 tw`, clearing `s1` and `tw` and preserving the other six fields. After the first nonzero pass, put `m = s1 + tw − 1` and `K = s2 + tw + 1 + triangle (m+1)`. The iteration maintains `tw = m−t` and `s2 = K−triangle (m+1−t)`. Triangle monotonicity supplies the subtraction bound; the final value is `K−1 = old s2 + cantor old s1 old tw`. The zero case is separate. This is an internal induction proof, not an induction restricted to standard counters.

The remaining integration obligations are substantive but are not defects in these deliberately partial modules:

- Prove the concrete root `occB`/`Occ` fact against the packed table, with the intended entry and exit map. Otherwise `IRun` remains conditional and can be vacuous where no occurrence exists.
- Port the unpair walk (`L2Lib254.body154`, `walk_pl`, `walk_ws`, `loop115`, `loop116`), then read/pop/push/constructors, equality/fetch/MP/DROP/NIP/AX, and the root-step relation. The current 19-loop census excludes the later unpair-walk loops. `L2Root254.root_step` (139) and `iter_iff` (207) remain Nat-level templates, not arbitrary-internal scheduler theorems.
- Identify the new file representation and seed with `ArithmeticEnumeratorSeed246.seedValue` (78), and prove both directions of internal halting equivalence. `Reach` currently provides an existential time, not positive time or cofinal root iterations; a root-specific positive/cofinal argument (or equivalent no-spurious-halt proof) is still needed. The forward structured composition rules alone do not give the converse.
- W6 still needs the packed Rotation240 table identified with its decoder and the arithmetic binary/bootstrap transport; W7 needs the final fixed sentence and PA composition. The separately checked external binary240 endpoint does not discharge these internal-model obligations.

The next useful Claude-lane step is the concrete root occurrence check alongside the internal unpair walk, followed by the existing L2 macro/root structure. No duplicate implementation was authored here. Minor header drift is nonblocking: `ArithmeticDagRun` still mentions `while_loop` and an obsolete `IRun` argument list; the actual APIs are `run_iterate` and `IRun e x X y`.
