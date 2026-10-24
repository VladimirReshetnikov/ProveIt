Final assembly addendum: the upstream exact transport identity was also applied to the new fused polynomial. Its final count is **96 operations at degree266**, not the provisional98 below. This is an identical-polynomial evaluation change, independently checked against the frozen98 circuit. The historical comparator discussion below records the state when the late sources were reviewed.

# Bounded late comparison review

Initial construction pin remains84e16e43092614bae262ca59651cb9d77e31a255. The untouched checkout still has that HEAD. Late review reads Git objects at56b4d15d128be25688c20a39049c10a59b0e9cb3 (2026-10-24 19:54:15 UTC). No upstream program was executed. Exact saved source texts and source/hash/URL ledger are under `late_head_evidence/` and `LATE_BASELINE_NOTE.json`.

## Required comparison corrections

1. Commit49379c31d969b78762b656d46b8881dfb335c45e adds complete ten-positive98operations/degree368 and103operations/degree340 graphs, polynomially identical to99/368 and105/340 parents. An independent inert backward traversal confirms98 and103 live operations. The proposed10-positive98/266 therefore matches the current cheapest operation count, lowering degree from368 to266; it does not introduce98 operations or save an operation against the late frontier. It dominates103/340 in both measures.
2. Commit01d07bd315bfaef3689187f48ce6fc7c5875788e accepts17 complete74-predicate quartics. Best measured variable count is601 integers,371 quadratic rows,9661 terms,height2445790974704. Lower-height606/8808/964213 and605/8724/45769499 remain tradeoffs. Replace any “current604-variable frontier” wording by601 if discussing the latest direct family.
3. Commit9babb7291eef363aa19574e8386d3206d548b1b6 proves73 source predicates by removing raw104's guard, but does not materialize a73-predicate projected quartic. Do not extrapolate598 variables from it. The latest measured family stays601.
4. Commit169e6f5859b636b64537cece2de62958296a173d screens the six e13 arrivals. It does not accept every ordinary reduction merely because33 full quartics,39 supported DAG counts and54 coefficient bindings pass inert checks. In particular prior11Z2240/206 and12Z1000/180 remain meaningful supplied comparison endpoints but require their own semantic review. No stronger new11–15Z complete endpoint appears in this late update.

## Proposed-result comparisons remain valid with these qualifications

-11Z688/126 improves prior11Z2240/206,2272/204,2912/200 in both arithmetic measures.
-12Z500/148 improves prior12Z1000/180 in both measures. Against scalar12Z1200/145 or1456/141 it lowers degree but costs3 or7 more operations.
-13Z274/129 improves536/135 in both measures.
-14Z108/119 lowers degree versus312/117 but costs2 additional operations. Do not call it dominance.
-15Z56/110 improves the fresh incoming15Z172/123 and170/134 integer points; the separate15-positive66operations/157degree point is a different domain.
-10positive266/98 improves degree at equal cost relative to newest368/98 and both measures relative to340/103.

The figures above use degree/operations when compacted in this section; native source domains and whole coherent coefficient tuples remain separate.

## Dependency and reproducibility findings

The entire scalar-carrier12, integer13-quadratic-trace, constructive-integer14-guard-reduced, ten-positive-zero-offset and ten-positive-direct-zero-offset directories are unchanged between the original and late pins. Their proof text and constants remain the same construction dependencies.

Placement240bf9e422 moves35 incoming archives into sources76–110 and deletes historical ZIP working paths. Latest56b4d15 adds a separate compatibility wrapper that supplies exact historical Git blobs temporarily, preserving sealed checker bytes. This is a reproduction change, not a mathematical correction. A self-contained release should retain its explicitly required archive/dependency closure rather than depend on a mutable working checkout or this new wrapper.

The incoming intake calls out a real obstruction to transferring a squared-factorial radius into the current direct source: removing the K-index guard loses the presemantic d>=K implication when d=f*K² is changed to f². Assuming f=K! first would be circular. None of the new small-variable norm constructions depends on that unimplemented source rewrite.

The intake reiterates the ordinary-calibration boundary and the full-residue interpolation quantifier order: select one strong witness first, then attain the required auxiliary residue. The corrected period is4*n0*f modulo f²; mere infinitude is insufficient. No new end-to-end internal-ZFC or Lean calibration is claimed. This is not a newly discovered contradiction in the imported ordinary texts, but a required proof interface when composing them.
