# Origin 49e99c5b7c: merge boundary

The fixed upstream range is `437804fcdd5550fec6ece3b6073c616690d4625f..49e99c5b7cc6c2e164331961de28bad3904361fd`. It changes exactly ten paths: five existing Lean modules, one new Lean module, two research documents, one derivation input and one research renderer. The final census observed checked local commit `f97735aec688212be26bef07500088f2cd43252f`; all twelve protected current files equal its Git blobs. The index fields in the receipt are observations during root staging, not merge instructions.

`review.json` gives full base/head/upstream/current SHA256, Git blob IDs and modes, plus current index entries. `proposal-map.json` gives exact upstream raw-data destinations and per-path production decisions. `upstream/` holds all ten exact new blobs; `checked/` holds the twelve exact protected files. Neither snapshot is a canonical write.

## Exact decisions

| Changed path, relative to the Lean ZFC or formal rho8cd directory | Recommendation |
| --- | --- |
| `ConstructibleChoice.lean` | Keep checked 3728efad, importing `ZFModels`; upstream 50b11a53 imports a separately named duplicate semantic module. |
| `DominatedImplication.lean` | Keep checked a128ddd5. Preserve upstream bd07364a as a shared-basis candidate until its own maintained-producer/API/kernel integration. |
| `KQ1ZF.lean` | Keep checked 9feac68e, including explicit `InductiveAttempts` and `WFModelCore`; upstream 83b99f4b uses the broader `WFModel` wrapper. |
| `Lukasiewicz.lean` | Keep checked 5bae5186. Upstream 7d443a73 depends on the new generic core's K/Peirce/S exports; it cannot be adopted alone over the retained three-export core. |
| `ZFModelSemantics.lean` | Keep canonical path absent. Preserve upstream b0abb6bc as data. Its `models_ZF` statement and body exactly equal the already checked theorem in `ZFModels`; importing both would duplicate the same declaration. |
| `ZFNative.lean` | Keep checked 415c9b55 using `ZFModels`; preserve upstream 66b6ffbb's alternate split as data. |
| `PROVEIT_STATUS.md` | Reconcile as documentation: upstream's reported build is a submitted claim, not the result of our retained phase12 sources. |
| `README.md` | Reconcile similarly; distinguish the current three-goal pinned input from the new six-goal proposal and historical rendering commands. |
| `derivation_core.txt` | Keep f0a2e60d in place. Preserve upstream 4141248e separately. Maintained producer31fdd hard-pins f0a2e60d, so accepting the new input at that path would break its checked contract. |
| `generate_domrho8_cd.py` | Upstream63da860d may be imported verbatim as inert research data. It is not imported or executed by the maintained31fdd producer. Its commands must not be described as the current accepted regeneration route. |

The remaining protected files are the other four phase12 Lean writes (`L2Lib222`, `WFModel`, `WFModelCore`, `ZFModels`) and maintained `generate_l2k222.py` c720d5bf. Together with the listed three overlapping phase12 Lean writes, these are the exact seven-source/one-producer adoption. The receipt also pins unchanged `generate_dominated_implication_lean.py`31fdd, its three exact current input files and both retired-template absences.

The upstream idea is substantive: one restricted implication derivation exports K, Peirce and S in addition to the row/composition/lifting interface, and the unrestricted calculus instantiates domination as `True`. The current pair has287+524=811 lines; the exact upstream pair has300+101=401 lines. These are literal file counts, not a verified proof-size or runtime result; the upstream README's409-line number describes a different intermediate count. Reflection owns the independent mathematical/API assessment. This census makes no kernel claim for the new pair and executes no renderer.

## Validation and limits

The reader uses only Git read commands, file hashing, and an AST data read of the maintained producer's literal input-pin dictionary. Source bytes are re-read after the census. All ten upstream blob hashes and modes are exact; all eight phase12 adopted file hashes match the accepted adoption record; a128/5bae/f0a2/31fdd match their required pins. No Lean/Rocq/compiler/producer or delivered program ran, and no canonical, Git or index bytes were changed.

One own metadata-reader attempt tried `ast.literal_eval` on the pin dictionary before resolving its two literal name keys. It failed without completing a receipt; the script and reason are retained under `history/`. The successor resolves only the preceding literal `SOURCE`/`ADAPTER` values as data. This was not a proof or producer failure.
