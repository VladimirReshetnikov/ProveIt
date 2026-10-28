# Anthropic ETH release: pinned revision review

Observed 2026-10-27 03:26 UTC. Read-only source and published-CI inspection; no project code, Lean build, installer, or third-party script was executed locally.

## Immediate finding

The user's link is a release of the independent Claude result's paper **and full Lean development**, not just a revised informal claim. PR #31 is merged, and its published verification job has now succeeded through **both Lean's default kernel and independent nanoda**, with Comparator accepting the two advertised theorem statements. The earlier description “Lean proof unpublished” must be superseded. This review did not perform its own kernel run.

## Immutable identity and chronology

- Repository: `anthropics/formal-math`; PR title: `Add eth: paper and Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT"`.
- Requested head: `1a6eee293b9e00cb432eef6018a21f523623a9af` (commit dated 02:45:07 UTC).
- PR created: **02:46:32 UTC**, October 27, 2026.
- Review: approved by `rfurman` at 03:02:45 UTC, no review text.
- Merged: **03:07:22 UTC**; resulting commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
- CI uses GitHub's synthetic PR merge `80ee23547e985fd4c7fc71fbc6910af85207bcf3`. Git API confirms requested head, synthetic merge, and final merge all have exactly the same repository tree, **`ab1069cc17ae5088e175ec37fa16fe8bd273753d`**. Thus this is verification of identical source bytes, not merely a related revision.
- PR statistics: one commit, 1,063 changed files, 153,191 added lines, zero deletions. There are 1,062 files under the new `eth/`; the other change adds its root README row.
- Earlier parent report delivery was 03:06:14, before merge but after PR creation. Merger chronology alone cannot justify calling the proof unpublished at that earlier instant. Say the release was not established in the prior review and is now established, rather than claiming that the old cutoff necessarily preceded public availability.

Primary sources: [PR](https://github.com/anthropics/formal-math/pull/31), [requested commit](https://github.com/anthropics/formal-math/commit/1a6eee293b9e00cb432eef6018a21f523623a9af), [pinned project README](https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/README.md).

## What the released statements actually assert

`MainResults.lean` imports **Mathlib only** and contains definitions, not proof code. `Solution.lean` gives two closed theorems, with no extra theorem hypotheses:

1. `MainResults.ethIsFalse : MainResults.ETHIsFalse`: negation of `0 < s 3`, where `s 3` is the infimum of nonnegative exponents permitting deterministic finite-alphabet Mathlib multi-stack Turing-machine decision of 3-SAT in `O(2^(delta*n))`.
2. `MainResults.mainTheorem : MainResults.MainTheorem`: **one** deterministic finite-alphabet Mathlib `TM2ComputableAux Bool Bool` machine and **one** natural constant C, chosen **before k and the formula**, count satisfying assignments in

   `floor(2^(C * min(k*m/sqrt(log2(m)), k^2*n*log2(log2(n))/sqrt(log2(n)))))` steps.

   The premises are `k >= 1`, `m >= 2`, `n >= 4`, clause width at most k, no duplicate clause-list, and all n variables occurring. The input explicitly contains k and n in unary plus fixed-width literal slots; output is the count in n+1 binary bits. All stack alphabets, not only input/output alphabets, are required finite.

The small-size and occurrence conditions are explicit conventions, not hidden universal assumptions. This is a uniform-in-k theorem, not merely a family of separate fixed-k algorithms. Its C is not explicit.

Sources: [MainResults.lean](https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/MainResults.lean), [Solution.lean](https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/Solution.lean).

## Published CI evidence, distinguished from local execution

[Job verify (eth)](https://github.com/anthropics/formal-math/actions/runs/40440389861/job/121979112896), run `40440389861`, job `121979112896`, reports **completed / success**, started 02:46:47 and completed 03:22:05 UTC.

Actual fetched job log contains:

- 03:14:46: `Build completed successfully (9768 jobs).`
- 03:17:32: export of both named results from `Solution`; running nanoda on the solution.
- 03:21:26: `nanoda kernel accepts the solution`.
- 03:21:26: `Lean default kernel accepts the solution`.
- 03:21:26: `Your solution is okay!`, followed by `PASS comparator.json` and acceptance of the sole comparator configuration.

The only emitted sorry warnings are the two intentional placeholders in `Challenge.lean`; no prior project build cache was found. The step API separately marks both `lake build` and `Palomar bar (comparator accepts every declared configuration)` successful.

`comparator.json` names exactly `MainResults.ethIsFalse` and `MainResults.mainTheorem`, permits only `propext`, `Quot.sound`, `Classical.choice`, and enables nanoda. The CI script independently rejects any permitted axiom outside those three and forces nanoda on. This is materially stronger evidence than source grep or a README assertion. It remains published repository CI evidence, not our own independent reproduction.

Sources: [configuration](https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/comparator.json), [CI script](https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/.github/scripts/comparator-check.sh), [workflow](https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/.github/workflows/lean-projects.yml).

## Static inventory

Downloaded the exact public commit archive read-only. All 1,062 extracted `eth/` files match their Git blob hashes in the exact recursive tree. Archive SHA-256: `d3e7da579f14747a7991003a863f6f88685f0f8a88e6777ca51863970143b07b`.

Across all **1,052 .lean files**, a lexical scan with nested comments, strings and line comments removed finds only two `sorry`/`admit`/`sorryAx` occurrences: `Challenge.lean` lines 13 and 17. No axiom declarations, `unsafe`, `native_decide`, `run_elab`, `implemented_by`, `extern`, or `csimp` occurrences were found. A supplemental raw-word scan confirms `axiom` appears only in an explanatory comment. No file imports `Challenge`.

A static import traversal from `Solution.lean`, including Lean's `public import`, `private import`, and `import all` forms, reaches **810 internal source modules** plus Mathlib/Batteries; it does not reach Challenge. This is import-graph evidence, not kernel-level dependency extraction. A clean lexical scan cannot establish theorem correctness or kernel validity.

## Correspondence to the 49-page paper; residual boundary

The released `eth/paper.pdf` is 49 pages, authored Claude/Anthropic, dated October 26, 2026. Its main theorem has the same bound displayed above. A subsequent direct comparison with the prior ProveIt copy is recorded below: PDF bytes differ, but the main theorem and printed Lean definitions are unchanged after the stated normalization. Appendix E prints the trusted statement file and explicitly says human readers must judge whether these definitions state the intended mathematics. It also says the development was written by AI models, reviewed by other instances of those models, and at writing no person was known to have checked it. That historical assertion is not replaced by treating a short GitHub approval as a full human mathematical review.

The paper additionally reports leanchecker checks (including an earlier token-identical copy); this review did **not independently verify** those additional historical runs. The observed public CI proves the Lean/nanoda Comparator acceptance described above.

`proof/PaperIndex.lean` carefully records departures from the paper's step-by-step proof: polynomial-power overhead instead of constant-factor alternation; explicit table materialization and time-budget padding; cost-model conversions; different recursion induction; and decision/counting distinctions in intermediate results. These are not silently identical derivations. Crucially, the final checked statements count steps of the specified finite-alphabet machine, so a permissive internal operation model is not itself an extra assumption in the public theorem type.

The standard simulation/encoding bridge to the paper's word-RAM language is described but **not formalized in the two final statements/proofs**. README explicitly distinguishes kernel checking from paper-to-statement semantic correspondence. Do not claim all prose, all machine-model equivalences, or the exact printed proof has been machine-verified line for line.

Source: [PaperIndex](https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/proof/PaperIndex.lean), [paper](https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/paper.pdf).

## Effect on the working algorithm comparison

- **Proof status changes substantially:** the Claude development is now public and its two main theorem statements have repository CI acceptance by Lean and independent nanoda, rather than only an unpublished-formalization claim.
- **Asymptotic frontier does not change solely due to this release:** the fixed-k general rate remains `2^O_k(n log log n/sqrt(log n))`, with the clause-sensitive `2^O(km/sqrt(log m))` alternative and the stated universal-k constant. The user-provided 49-page manuscript already advertised this order.
- Our normalized wire-size coefficient refinements and density-sensitive envelope are different parameterized claims. This release supplies no common leading constant, no comparable implementation, and no evidence that our coefficient numerically dominates the independent crossing-decomposition algorithm (or vice versa).
- It supplies no practical SAT speed claim, polynomial-time claim, polynomial-space claim, or P-versus-NP resolution. README expressly calls the result purely asymptotic and says nothing about practical formula solving.
- It does not establish a new smaller logarithmic exponent or close the separate missing low-degree/compact-recursion compiler interfaces in our work.

## Local evidence retained

`eth_iteration3/anthropic_snapshot/` contains the immutable source archive, verified `eth/` source, GitHub PR/check/review/tree JSON, full verification job log, commit-tree equivalence JSON, static inventory JSON, import graph JSON, and extracted paper text. No pending check needs monitoring for this exact-source acceptance question: the relevant published job is terminal success.

## Addendum: direct comparison to the prior ProveIt 49-page PDF

Checked 2026-10-27 03:30 UTC. The local prior file at `eth_iteration3/incoming/3sat_round3_frontier_20261027/evidence/alternate/eth.pdf` exactly matches the requested prior Git blob `d2ad67d5b86add67c8256e4633fec11c48d0db44`; the iteration2 copy is byte-identical to it. Therefore this comparison is against the specified prior source, not an inferred similar manuscript.

| PDF | Bytes | Git blob SHA-1 | SHA-256 |
|---|---:|---|---|
| Prior ProveIt `Research/claude-2o-n-3sat/eth.pdf` | 868,673 | `d2ad67d5b86add67c8256e4633fec11c48d0db44` | `f0af035b6c87d04d3fcf07dae040df98029f4990c6493e3e9ab64c4ac714c0eb` |
| Anthropic PR31 `eth/paper.pdf` | 900,337 | `77f4a8f043f65cecf0ee8e4024bf026aff1066e8` | `7af518b09342c967ea371c74b8989806684c5d02aabe5763ca08554aff5025a0` |

Both have 49 pages and the title *A 2^o(n) Time Algorithm for 3-SAT*. The prior title/author PDF metadata fields were empty; the release fills them. The prior visible date included `October 26, 2026, 3:13 PM PT`; release gives only the date.

**No change found in the central mathematical claim.** Theorem 1's extracted statement, formula and absolute-constant qualification are identical after date, page-header and whitespace normalization. The entire printed `MainResults` Lean listing is also identical after removing comments, page headers and whitespace (1,815 remaining characters in either version). In particular, the universal machine/constant quantifiers, finite alphabets, all input conditions, `ETHIsFalse`, and `MainTheorem` type are unchanged. This is a text comparison of PDF extraction, not an independent mathematical proof or compiler parsing check.

**The release is not merely a proof-link patch.** Observed substantive reporting/editorial changes include:

- Appendix E replaces the explicit placeholder `[Link to the full Lean proof: to be added when a public location exists.]` with the public repository and checking instructions.
- Appendix E changes the reported development size from 1,881 Lean files to 1,050 Lean modules. These are the paper's reporting counts, not our all-file `.lean` count of 1,052, which includes two utility scripts.
- The replay claim is more qualified: ordinary `leanchecker` checking is described module by module; full-environment replay including Mathlib is attributed to an earlier copy whose code is claimed token-identical, differing only in comments and whitespace. We have observed public Lean/nanoda CI but have not independently verified this historical leanchecker run.
- MainResults comments expand the rationale for k>=1, m>=2, n>=4 and distinguish large-input big-O readings; the actual definitions are unchanged. Appendix E also stops phrasing the semantic equivalence explanation as “Lean proves that.”
- Adds discovery provenance (October 16/internal model/14M tokens) and acknowledgment/citation of the independent OpenAI preprint; adds a claimed literature-survey count of more than 800 papers. These are the authors' reporting claims, not independently audited facts here.
- Expands Table 1's already-defined parameter equalities, improves references and cross-references, clarifies notation, and adjusts formatting/figure placement. The normalized diff contains extensive PDF superscript/layout noise, so apparent isolated formula-token changes were checked in context rather than treated as changed mathematics.

Conclusion: **same advertised theorem and formalized statement, newly public formal proof with stronger directly observable checking evidence, plus reporting/editorial updates**. Do not describe this as a new asymptotic improvement or a correction to the central theorem. Nor claim every mathematical sentence is byte-identical: the PDF and explanatory text are revised.

Retained comparison evidence: `prior_paper.txt`, `paper_text.diff`, `paper_token_changes.json`, and `paper_statement_comparison.json` in `anthropic_snapshot/`.
