# Independent review: squared-trace to trace75 ring map

**PASS.** Over any commutative ring, for arbitrary ring-valued ports p and
valuation v, `shift` changes only slot 4 from T to `f*T−d*rank`, where
`d=2*Delta*(v 3)^2*c^3*E` and the actual trace75 registers satisfy
`f=1+c*d`. The explicitly defined `oldV` is `f*f*(c*T−rank)−c`; `oldZ`
uses the actual trace75 carrier formula with V replaced by `oldV`; and
`oldValue` uses the actual output formula with those V and Z substitutions.
The source proves the intermediate V and Z identities and
`value75 p (shift p v) = oldValue p v`.

This establishes a ring identity for that explicitly defined parent, not a
binding to a selected old graph or external equation. It does not construct
positive witnesses or prove a halting or iPRA result.

The accepted `research/trace75-old-trace-map-prototype/observations/map-attempt01/`
terminal SHA-256 is `c9ca2fe3caa963fdcd7682f993139fea0d1cd09f7288787cf80938ffe95a0ff2`;
its regular object `/tmp/trace75-oldtracemap-qm52cj8c/Trace75OldTraceMap.olean`
has SHA-256 `037f11212356efaa43494a640dbb45af97a437f6cadd2812c955bcdbc6d8ec56`.
Source, copied source, runner, exact axiom report, eight input hashes, first
selected direct trace75 provider and resource samples were checked. Tool
exit 0 is author-reported; no separate outer receipt or independent Lean
replay is claimed. Full transitive, package, historical and dynamic ancestry
remains outside this review.

`check.py` SHA-256 `d1e8693acf49515648fa2256e50ecac9daf1b26aa1b507352d17ced6ced40c9b`;
`result.txt` SHA-256 `870704d15a7a2a04f75565dda1fdcb3f51daa291cf223e1ca634af17c5e7a95c`.
