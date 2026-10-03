# Bounded challenge: two batch-80 signal-publication claims

Scope: only the new compiler quantifier summary and quartic degree-minimality claim at publication `ef114b0bb400c2f21e1885dd16cc90a0e346b3f4`. I read the relevant theorem/proof contexts in the publication, the original source14/source15 TeX from their previously reviewed batch80 archives, and the exact canonical-diophantine classification definitions and statements. No original suites, global manuscript rereview, or repository mutation. The companion JSON records immutable article/README/definition object pins and original archive/member hashes.

## README compiler quantifier: correction needed

In `signal-machine-collision-certificates/README.md`, lines66–69 say that “a fixed” reversible mass-conserving CA “simulates every separated reversible two-counter machine,” immediately followed by the canonical gap and exact-clock/certificate properties. The source theorem has a different explicit compiler quantifier:

`for every finite separated reversible M, effectively construct F_M`.

The exact statement is `smc:tm:thm:compiler`, publication article lines3864–3872; it matches original `three-mass-report.tex` lines46–54. Its canonical configurations carry M's control state and use gap `12*2^a*3^b` for M's counter values. The source explicitly says that increasing the source table changes the finite type set and alphabet cost (original line85), and that the fixed-rule existence result follows by first fixing an existing universal source machine (original lines87 and692; article theorem `smc:tm:thm:threshold`, line3874).

Source15 likewise distinguishes wrapping and compiling a new finite source table from preserving one old CA rule: original `clean-target-report.tex` line36, publication article line4660. Its fixed exact-pair rule then comes from fixing a universal fresh-entry wrapped source; see original lines186–218 and publication `smc:ct:thm:main` at4662, `smc:ct:thm:equiv` at4816.

Recommended minimal semantic replacement: “every separated reversible two-counter machine M can be effectively compiled into a globally reversible, mass-conserving CA F_M …; fixing a universal source gives one fixed rule with undecidable pattern occurrence.” The publication's article introduction at line415 already states the compiler in this correct order. The primary publication reviewer owns the exact patch.

A fixed compiled universal source can of course simulate other computations through a further effective universal-input encoding. This finding does not refute that weaker computation-universality assertion. It corrects the README's conflation of that route with the direct M-dependent canonical encoding, rule/count construction, and per-source-step microtimes. Those are not one unchanged literal interface for all source tables.

## Quartic degree minimality: PASS with the stated class

README lines1055–1061 and publication article line6237 correctly apply `cdc:of:thm:classification` to source17's hit relation

`H = {(x,t) in N^2 : exists k in N, t=k^2+(2x+3)k}`.

The canonical report defines `Dplus_d(k)` by a fixed integer polynomial in the input and finitely many existential natural witnesses, nonnegative **jointly on the entire real nonnegative orthant** (classification definitions at article12607–12620; theorem label at12631; the explicit joint-hypothesis reminder is at12571). It concludes that every degree-at-most-three representation in that class has a semilinear natural projection, with no single-fold requirement.

If H were semilinear, its section at x=0 would be semilinear. That section is `{k^2+3k : k in N}`, an infinite set whose consecutive gaps are `2k+4`, hence unbounded. An infinite ultimately periodic subset of N has bounded eventual gaps. Therefore the section, and thus H, is not semilinear. This is exactly the source hit-time argument at `smc:fm:prop:hits`, article6178–6199, with d=7+x.

The supplied polynomial `(k^2+(2x+3)k-t)^2` is integer-coefficient, degree exactly four, and nonnegative on all real tuples, so it belongs to the claimed restricted class and realizes H by natural existential projection. Degree four is consequently minimal there, even if lower-degree competitors may use more witnesses or abandon single-foldness. The same obstruction already applies with a fixed natural x.

No correction is needed. This does not say arbitrary Diophantine representations need degree four: the unsquared residual is already quadratic and changes sign. Nor does real-orthant nonnegativity mean that existential real witnesses describe the same hit relation. The text correctly notes the real false witness at x=0,t=1; the lower-bound class still quantifies the auxiliary witnesses over N. An arbitrary nonsemilinear recoding of the inputs would also be a different interface; the claim here concerns the displayed natural input coordinates (x,t).

The nearby reference to `cdc:of:thm:singlefoldsl` at canonical article13024 is also accurately scoped: for a previously proved semilinear relation it supplies an effectively constructed jointly orthant-nonnegative quadratic with unique natural witnesses. It provides no small-operation bound for a concrete quantifier-elimination output.

These findings were sent directly to the primary publication reviewer. Only the README compiler quantifier needs a change; the original source theorems and quartic transfer are unaffected.
