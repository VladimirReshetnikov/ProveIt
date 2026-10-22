# Phase17: a shorter combined proof

**The combined Lean check and independent evidence review pass.**
This source selection combines the [checked phase16 checkpoint](../phase16/README.md),
`d3ff74a6fa`, with frozen upstream `main` at
`140d832128fd43873f16e385766cd3cee08df8a9` on `codex/zfc-small-machine`.
Claude Code's work is preserved together with the additional cleanup below.

The main mathematical simplification constructs the full seed property directly
on the original model. For a named matrix `ψ`, including literal equality, use
`m = ¬¬ψ` and the fresh container name `enc(th m)`. The interpreted code proves
derivability; the model satisfies the named bundle itself. This avoids the
preliminary indiscernibility quotient and semantic encode/decode round trip.
The later tagged bisimulation quotient and well-founded interpretation remain.
The shared `FullSeed` and named bundle definitions keep their original names.

Other simplifications reduce repeated proof and certificate data:

* The enumerators compile `C222` directly. The restricted dominated-rho8 lemma
  supplies the unrestricted row inside the predicate of compiled contracts;
  the intermediate `CDom` translation leaves the endpoint closure.
* Decoder trees are computed from the maintained programs using `ptree`, replacing
  duplicated expanded literals. Program tables, certificate checks and binding
  theorem statements remain the same; the selected checks still use kernel evaluation.
* AX words record macros and infer successors from the actual program nodes.
  The checker still rejects mismatched macros or edges and requires the final
  gate. This removes 156 redundant successor numbers from each word.
* The single weak quotient construction and CP/GIC adapter are retained, together
  with phase16's twelve unused strong wrapper retirements and inline trace
  instance. Further constructibility, calculus and macro proofs share existing
  lemmas, combine identical cases and inline one-use local steps.

The additional local cleanup removes **18 Lean lines / 690 bytes**: inline the sole-caller
`FullSeed` constructor wrapper, reuse the existing seed-relation congruence lemma,
and correct the related prose. Removing the dead literal-tree renderer and its
unused imports removes **15 producer lines / 488 bytes** across six files. The producers
were reviewed as source data; no supplied generator was executed.

Static measures of the selected 215 endpoint closure are **174 project modules /
1,749,188 source bytes**, down from **176 / 2,028,295** in phase16. The direct seed
interface replaces two old route modules; `Code254Models` and `KCodeDom` leave
this closure. Separately, the 89 changed Lean paths across machine variants have
1,252 fewer physical lines and 1,522,387 fewer bytes. These physical-file figures
are source-review measures, not claims that every variant has been compiled;
they are not added to the closure reduction.

The successful combined check covers **213 providers**: 199 project modules and
fourteen typed clients, with 171 freshly checked providers and 42 exact-source reuse
records, plus two endpoint audits. All nine 215 site batches were checked fresh.
There were 172 provider compiler invocations for the 171 accepted fresh providers:
the profile-gate rejection was compiled once more after its explicit review.
The two endpoint audits and one diagnostic invocation are separate.
The thirteen existing clients retain exact source bytes. The new client checks
original-domain `FullSeed`, literal equality `x = y` without irreflexivity or an
equality-free premise, and the existing `FormSeed` interface.

One retained axiom report changes: `DecoderSourceBinding.source_tree_eq` now
reports **`[propext]`**, previously **`[]`**. Its source and `by rfl` proof are
unchanged; computed `t215` exposes the existing elaborated `toTree` recursion's
transitive dependency. The literal program nodes and independent `sourceTree`
remain axiom-free. The other retained profiles match their frozen expectations.
The original exact-profile rejection, diagnostic and independent mathematical
review are retained. No production source changed for this policy successor.
Both endpoint audits retain their ten standard-axiom reports. All three new
direct-seed client reports use exactly `propext`, `Classical.choice` and
`Quot.sound`. Accepted provider records contain 18 warning occurrences (17 fresh,
one reused); all fourteen clients and both endpoint audits have zero warnings.
Actual result SHA-256: `0ece73d070ab23aee17cf6067d9b9850bd657f1c63523c0567c1fe4ced66f1ee`.
The [owner audit](lean/result-review.json) and [independent readback](integration/resumed-peer/README.md)
agree on the complete selected scope. Every fresh warning headline already occurred
in the same module's earlier accepted log. The [evidence packet](lean/README.md)
retains the original profile rejection and the separate metadata-auditor failure.
The 215-state machine and endpoint statements are preserved. No PA
formalization or minimum-state theorem is claimed here.

Attribution: Vladimir Reshetnikov's upstream commits, coauthored by Claude Opus
5.5, supply the [direct seed](https://github.com/VladimirReshetnikov/ProveIt/commit/ff928ef0ecce89f961cd4ab8a049b07083c5bace),
[direct C222 compiler](https://github.com/VladimirReshetnikov/ProveIt/commit/fa92b88f8e622a22711f68d4f22f281cd0d18c40),
[computed trees](https://github.com/VladimirReshetnikov/ProveIt/commit/775267c38acd60f24d24c9512de54e4bc52f2d0d),
[AX words](https://github.com/VladimirReshetnikov/ProveIt/commit/4fb82d6f8424785376951c8b60c782fc46d78c86),
[quotient proof compression](https://github.com/VladimirReshetnikov/ProveIt/commit/a7b8f1ae67a9efff3c40f113136a5f200c92388e),
and [macro/seed cleanup](https://github.com/VladimirReshetnikov/ProveIt/commit/140d832128fd43873f16e385766cd3cee08df8a9).
Upstream build descriptions report their own partial scopes; this combined
check establishes acceptance of its frozen source selection independently.

Evidence: [source and closure measures](integration/closure-metrics.json),
[local cleanup](integration/local-cleanup-adoption.json), [Lean evidence](lean/README.md),
and [model/typed-client review](integration/model-review/README.md).
