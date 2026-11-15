# Historical architectures and all-size census

Pinned source: `VladimirReshetnikov/ProveIt@8d31445d858761a8f6150c2e5012adae8895e932`.
All paths below are relative to `Computability/BusyBeaver/Research/PA/` unless stated otherwise.

## What the numeric inventory measures

The current census recognizes 4,468 occurrences of complete numeric tables in supported literal/JSON formats, including recursive ZIP members. They reduce to 879 normalized labeled matrices and 721 spanning action-graph classes. Seven additional disconnected matrices are recorded by literal identity; they are not classified by the maximum-component hash. The entire 27,459-file PA/incoming snapshot was independently checked against its Git blob identities, totaling 1,253,117,203 bytes, with no mismatches. This is a corpus comparison, not a correctness certification of every matrix.

`current/all_size_distribution.csv` gives every observed size; `current/all_size_classes.csv` gives one row per spanning class or disconnected literal identity. `current/occurrences.json` retains every parsed locator. `current/all_source_blobs.csv` and `current/archive_references.json` supply the underlying file and nested-archive locators. The packet ledger accounts for 87 filed deliveries plus the six current incoming archives.

| Size | Matrix occurrences | Spanning graph classes | Interpretation |
|---:|---:|---:|---|
| 1, 3, 4, 5, 6, 9 | 116 | 13 | Small controls and incidental recognized matrices; five disconnected identities are separate. These are not proposed Con(PA) machines. |
| 193 | 274 | 54 | Rejected/diagnostic reductions: coefficient-three experiments, runtime-core startup failures, and the newly rejected loop continuation. |
| 194 | 1,988 | 139 | Main comparison frontier; two further disconnected diagnostic identities are separate. Full annotation is in `current/comparison194_annotated.csv`. |
| 195 | 139 | 28 | Genuine predecessor constructions mixed with rejected/search layouts. |
| 196 | 608 | 105 | Imported PA196 and many source-preserving or command/logical rewrites, plus auxiliary and rejected layouts. |
| 197–206 | 349 | 100 | Mostly unfolded parents, prototypes, and larger compilations of source reductions; not 100 independently calibrated theories. |
| 207 | 171 | 57 | Mostly attempted reductions in the older U208 line; the packet corpus does not promote these merely from state count. |
| 208 | 426 | 142 | U208 proposals and extensive local-search variants. |
| 209 | 48 | 13 | Both the earlier James Chang PA209 line and the separate U209 weak-covering lineage occur at this size. |
| 210–222 | 349 | 70 | Older U-line ancestors, raw/intermediate compilations and search tables. There is no observed 216-state table in this inventory. |

Counts in the banded rows are sums of the machine-readable distribution. Graph classes forget the chosen start state, not the operational need to specify it. The 139 spanning 194-state classes remain pairwise distinct even after state relabeling, any spanning root, left/right reflection, global bit exchange, and erasure of the final halting action. These extra symmetries were checked by exact canonical tuples for the 194-state frontier. Global bit exchange does not by itself preserve a zero-blank specification.

## Architectural comparison

| Family and representative sizes | What the machine enumerates | Changes responsible for the count | Calibration and proof boundary |
|---|---|---|---|
| U222 → U218 → U214/U213/U212 → U211/U209 → U208 | A numerical implication/quantifier calculus for unrestricted weak power covering plus irreflexivity, connected to the unary theory U and then PA. It uses dual Cantor coding with four tags and designated contradiction 1. | Source grammar reassociation and compatible context-sensitive decoder deletions. U209 Joint preserves 3,909 primitive instructions; its 18-selector reassociation combines three deletions. U208 adds an entry/history fold, including the three-cell 211→172 fold in native labels. | Written PA-formalizable simulations and retained U/PA interpretations; executable symbolic contracts. The machine-facing calculus is not the unary-positive stream described elsewhere in the U theory packet. No new end-to-end proof-assistant certificate is supplied by these U208 deliveries. |
| Imported James Chang PA209 | Earlier ordinary-PA numerical refutation search, with a standalone Lean project and literal arithmetic halting formula. | Earlier source/controller and grammar configuration. The literal 209-control table is distinct from the U209 constructions and has its own source and proof lineage. | Its documented Lean endpoint includes `PA ⊢ Nonhalt → Con(PA)` and external nonhalting/independence consequences under the stated metatheoretic assumptions. This does not automatically supply either iPRA direction. |
| Imported PA196 and first 196-state rewrites | PA-strength numerical calculus, restricted implication basis, six logical heads, and gated separation; register-machine source compiled into a binary TM. | Baseline has 3,812 source instructions. Early source rewrites include distributed gates, diagonal-vacuity factoring, separate diagonal heads, command-controller changes, physical register layouts, and source-tree reassociation. Smaller source trees can lose decoder helper sharing and therefore fail to reduce the literal state count. | Imported Lean development plus numerous ordinary written equivalence/calibration arguments. The current PA README explicitly keeps the machine-specific iPRA reductions open. Literal nonhalting→consistency in PA is not the full biconditional in iPRA. |
| Original PA195 | Bundled diagonal emitter; 3,700 source operations. | 134 fixed controls + 68 AX readers − 7 simultaneous folds = 195. It preserves the diagonal196 word and source graph but adds a compatible fold. | Written PA equivalence; full symbolic execution, quotient and startup evidence. The separate current Lean arithmetic endpoint remains conditional on machine-specific reductions. |
| PA195S / PA195C | Separate diagonal emitter; S preserves the source, C adopts the Combined controller. | S: 134 + 67 − 6 = 195. C uses the same grammar with changed Shift/MP behavior, 3,649 source instructions and a different startup. | Written mathematical proof and execution certificates; no completed end-to-end iPRA Lean theorem. |
| PA195DC / M195S8 | DC combines bundled diagonal with Combined command control; S8 changes scanner/decoder architecture. | DC: 134 + 68 − 7 = 195 and 3,676 instructions. S8 is a separate graph and physical layout. | Written relative/PA arguments; each must be distinguished from the failed 194-state follow-up candidate. |
| Main 194-state line | The same broad proof-search architecture, with different emitted calculi and command protocols. | Primary: 134 + 67 − 7 = 194; an alternative budget is 134 + 68 − 8. Main independent axes: radix 4/5/6; exchanged h6; diagonal A/D; ten/eleven-entry AX protocol; explicit generalization binder; cached-head/changed MP or halt controller; decoder association/history selectors; zero-register return; physical layout; local engine shortcuts. | These changes preserve different interfaces and cannot all be justified by renaming. The 139-class annotation distinguishes principal, supplementary, auxiliary, seed and rejected graphs. Revised AX11H supplies substantial written iPRA calibration; completed literal-machine Lean endpoints are still absent. |
| Rejected 193-state line | Several different attempted shortcuts, not a common accepted calculus. | Coefficient three causes an inconsistent numerical calculus; runtime193 has a clean-frame core but invalid blank startup; the newest continuation fold fails its source loop contract. | All three obstructions are local to the stated families. They are not a lower bound ruling out other 193-state machines. |

## Source anchors for the historical table

- `docs/U208_ConPA_2026-10-29/README.txt` and `report.tex`, especially the logical-calibration section. This explicitly separates the unary U interpretation, unrestricted machine calculus, and positive stream.
- `docs/U208_ConPA_2026-10-29/comparison/U209_ConPA_Joint_2026-10-29/README.txt`; the full retained archive is `docs/U208_ConPA_2026-10-29/reference/U209_ConPA_Joint_2026-10-29.zip`.
- `jamesyc-upstream/README.md`, `jamesyc-upstream/pa209/docs/result.md`, and `jamesyc-upstream/pa196/docs/result.md`.
- `docs/pa196_research_2026-11-13/README.txt` documents the 157-internal-node source tree and explains why its projected 195-state count failed.
- `docs/pa195_conpa_2026-11-13/README.txt`, `docs/PA195_ConPA_research_2026-11-14/README.txt`, `docs/pa195_diagonal_combined_2026-11-13/README.txt`, and `docs/pa195_followup_research/README.md`.
- The current `README.md` records the exact formalization boundaries. `docs/pa194_ax11h_research_2026-11-14_2/proof/` contains the revised written weak-arithmetic work.

This table groups proof-search and compilation architectures; it does not assert that all tables at a particular state count share one architecture or one proof status. The complete class CSV and per-occurrence locators retain distinctions below this level.
