# Batch 144 manuscript 05 intake dossier

Reviewed 16 October 2026. Untouched arrival: `/tmp/zfc-intake-144-6ye0stcm/05-zfc_one_schema_research/zfc_one_schema_research`. All executable work and PDF builds used the separate copy `/tmp/zfc-review144-05` or generated outside outputs. No checksum-manifest or line-ending checks were run. No Lean/Coq build was run. The one-command driver unconditionally checks SHA256SUMS, so its mathematical stages were run directly instead.

## Reading, pins and placement

Read the entire article source (all seven section files, including every mathematical proof and the bibliography), article.tex, root/implementation/compiler READMEs, NOTICE, reference checker, its tests and validation driver, relational audit, and reproduction driver. Compiler generator and independent verifier also received a separate full cross-review by mira_backend_route; its dossier is `/tmp/zfc-report05-machine-review-jg3if93c/certificate-review.json`.

The stated research baseline is `6594795e9db81637c30959e42b3bcfc9eb77722f`. Four distinct requested commits are `b07d1a27bbe2814f2fd84cc55feef71c4de5b2db`, `83ef1da6b717338f710277c2744fb4ec644cedbc`, `67086c8d8802ea7b3625a2fc0765d39e2181e335`, and that baseline. Upstream is `297ab8df7e5de329605c3875b4934643b371a5e3`. Numeric Dag254 data, the consulted formula generator, and the unmodified MIT-0 Wade backend have explicit provenance. No blanket relicensing of Jeff's Coq sources is claimed or needed by the finite numeric data extraction.

Recommend a later-delivery addition to the existing `set-theory/zfc-closure-kernels` collection, expected local prefix 08 under root's placement table. Preserve report/member article as delivered and annotate the precise statuses in reconciliation. There is substantial new mathematical and compiler evidence, so this should not be treated as a duplicate merely because the saturation idea and backend are predecessors.

## Claims and assessment

The main new mathematical claim is equality-free, subset-seeded/subset-bounded PSC **alone**, with no Extensionality, profile congruence or irreflexivity, interprets Extensionality + PSC, hence foundation-free ZF; ordinary mathematical internalization yields `ZFC ⊢ Con(PSC) ↔ Con(ZFC)`. It is one effective infinite schema, not one finite axiom. Arbitrary negative matrices and arbitrary finite parameter lists are allowed. No new Lean proof or finite proof-code translator is supplied.

I found no mathematical flaw in the displayed argument. The important audited steps are:

* Full-profile E (incoming and outgoing agreement) supplies raw equality-free singleton-like classes and congruence. The gated decoder is locally subset-bounded before Union; its one/two-edge property uses E's outgoing agreement, not unproved D-congruence. Covers assert A⊆C, not A∈C.
* Exact constant-class formation, transitive covers, Separation and Union are actual equality-free PSC instances. D-saturation includes every incoming-profile copy and is subset-bounded by a raw union.
* H(a) means S(a) plus a transitive cover all of whose members satisfy S. It does not require S of the cover itself. Heredity is immediate. The reverse purity lemma uses one arbitrary transitive cover V and Separation U={u∈V:H(u)}; U is transitive by heredity. This avoids selecting covers or invoking coextensional Replacement.
* Translate equality as D and restrict variables to H. All raw members of H-objects are H, which proves both Extensionality and subset absoluteness. Run raw PSC on H(x)∧H(y)∧rho^H, then D-saturate its hull. Input/output invariance preserves initial closure, recurrent closure, and unrestricted global support; upward purity makes the saturated hull H.
* Extensional calibration correctly separates Russell root r∉A from A without Foundation, and avoids selecting local bounds in the reverse recursion proof. The Foundation/Choice and arithmetization arguments are ordinary relative-consistency bridges, not newly formalized artifacts.

The raw PSC-with-atoms and self-loop relative models are carefully scoped; PSC alone need not imply raw CG or IR. A theorem of a self-membership atom can be an inconsistency target after GEN/empty-set reasoning, but using that atom as the falsity constant inside every coded formula requires a separate argument. This distinction is explicit and pertinent to our experimental 252 table.

The independent compiler result preserves the **old** 219-node program exactly at register-operation level: 114 AX nodes become 102 by rebracketing the same 185-call word over 18 control-closed helpers, giving 207 decision + 62 framework = 269 working states. All 4533 related exposed-operation pairs are checked, including both decrement outcomes (2601 INC,1931 DECNZ,1 HALT). This is an all-register finite bisimulation, not a bounded run. Neither it nor edge re-extraction proves the binary framework's unbounded-tape simulation or initializer. The new PSC theory is not in this 269 table. No below-254 result or 254−12=242 inference is claimed.

The new reference checker uses genuine Bottom, iterative syntax/substitution, closed PSC axioms, and K/S/classical contraposition/UI/UD/MP/GEN. Its exact finite derivation specification is complete for that chosen ordinary calculus; the unbounded length-lex search is specified mathematically, while the delivered CLI census is bounded. Resource failures propagate, and the identity example is a valid non-refutation. No issue found in capture avoidance, binding/shadowing, parameter closure or prior-line checks.

## Current-tree gap reconciliation

* `Computability/BusyBeaver/Research/ZFC/subset_only.md:194–207` retains CG and explicitly says dropping it is not covered. This submission genuinely closes that mathematical gap, subject to independent formalization.
* `Computability/BusyBeaver/Research/ZFC/raw_psc.md:136–214` already proposes S/H saturation for equality-bearing raw PSC. It calls the proposal unchecked and uses a least-TC plus coextensional-Replacement route. The submission supplies a simpler purity-cut proof, the missing equality-free raw bootstrap, and whole-schema transfer. Do not claim historical novelty for hereditary saturation itself; the manuscript attributes Al-Johar/Crabbé.
* `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/PSCCalibration.lean:171–177` already proves first-order extensional PSC/ZF0 deductive/consistency equivalence; `:8–13` states that Foundation/Choice, computable proof-code translation and machine endpoint remain outside it. That predecessor is reused, not supplied anew by this paper. The new H-interpretation is not currently Lean-certified.
* `Computability/BusyBeaver/Research/ZFC/compiler_route.md:10–27` records the 281 reconstruction and separates edge extraction from framework correctness. The submission's unchanged-program 269 improvement is new relative to that control. Current experimental 252 changes theory/logic/encoding and has additional calibration gaps, so the 269 certificate remains independently useful.
* `Computability/BusyBeaver/Research/ZFC/theory_backend_experiment.md:178–195` already records base3/dual-rho6 experimental 252 and remaining correctness obligations. Neither that nor this new report completes the user's endpoint.

The ax467 proposal in research.tex is correctly qualified as a future experiment. Primary Metamath pages ax467/ax467to6/ax467to7 support its ordinary-negation basis equivalence. It must not be imported blindly into the relative F=Rel00 calculus: identity quantifiers and F=true validate the new ax467 row without supplying old rho6's EFQ. No state saving or exact-code equivalence is established by that citation.

## Executed verification on copy

All commands used `uv run --no-project python`, normal assertion-enabled execution.

1. `machine/rebracket_axioms.py --inputs machine/inputs --output /tmp/zfc-review144-05-machine`: PASS; control closure, exact AX word, DAG re-extraction, 207+62=269; 537 partial rows/538 total rows. Total table independently parsed as working states0..268,start0,halt269. Generated total-table identity is `b40b90fdcf3a09475d3a2314dc3707bcf51a6302a3fdbba3c6afcde6ed1109de`.
2. `machine/verify_rm_certificate.py --source machine/inputs/source_dag.json --candidate /tmp/zfc-review144-05-machine/rebracketed_dag.json --certificate /tmp/zfc-review144-05-machine/rm_bisimulation.json`: PASS, all4533pairs. Separate child also passed against actual vendored Dag254.v, confirmed numeric nodes/names against recover_wade_dag, and rejected four certificate mutations.
3. Extracted the exact baseline `kernel_metrics.py` with read-only `git show 6594795e9...:Computability/BusyBeaver/Research/ZFC/kernel_metrics.py` to `/tmp/zfc-review144-05-kernel_metrics.py`; ran `proof_checker/validate.py --upstream-kernel /tmp/zfc-review144-05-kernel_metrics.py --output /tmp/zfc-review144-05-checker-validation.json`: PASS,12tests,5000nestedbinders,12000substitution semantic comparisons,80-bit5-line identity non-refutation, all131071strings≤16bits (938valid,0refutations),6exact named-syntax PSC generator matches including negative/shadowed matrices. Stable mathematical results equal delivered validation.
4. `code/finite_saturation.py --output /tmp/zfc-review144-05-finite-results.json`: PASS, all530graphs on1/2/3labels;4970Econgruence,1962H-invariance,1338heredity,3221restrictedcongruence,2595quotientextensionality,2595subsetabsolute,1468conditionalpurity checks. All530 fail necessary constant-PSC consequences, so none is a PSC model or consistency witness. Full JSON equals delivered result.
5. `pdflatex -interaction=nonstopmode -halt-on-error article.tex` twice on copy: PASS,28physicalpages (26numberedtext+frontmatter), all17fonts embedded; final log0overfull,0underfull,0undefined references/citations/errors. Rendered and viewed physicalpage10 (interpretation/PSC transfer) at1600px; readable unclipped formulas and text.

The sole advertised stage deliberately omitted was SHA256SUMS manifest verification, per intake instruction. No line-ending audit was performed. No delivered file in the untouched extraction was modified.
