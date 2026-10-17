# Batch152 / manuscript02 / local source27

## Provenance, coverage and placement

Arrival `da6dabcd8976acf94c4f3652ed3eeae5713b3d2a`; archive `zfc_consistency_machine_research_2026-10-16.zip`,139files. Original `/tmp/zfc-intake-152-7x8qx8co/original/zfc_consistency_machine_research_2026-10-16/zfc_small_machine_report`; all execution/builds use separate `/tmp/zfc-review152-bic-0i02n42d/02`.

Title **Small Turing Machines for the Consistency of ZFC**. ProveIt pin `4747142d5d15213eb711bdadfa3cc7e769fcb7a7`; merged-upstream audit `c132d7eae8158cd3a9850ea3eb7251158c3dd821`; compiler inputs `297ab8df7e5de329605c3875b4934643b371a5e3`; public253 `0d544f2a2e3c18f12278441a74b7879f31cbe856`.

Read main and all nine sections, README, all three experiment READMEs, full `THEORY_FINDINGS.md`, full same-halting `PROOF.md`, source-specific `internalization.md`, and the new logical/machine/compiler checkers. Verdict **addition to zfc-closure-kernels**: same-size baseline decoder refinement +basis comparison continuing sources08/09/19, with calibration explicitly reused. No theorem retraction found.

## Mathematical and machine review

New frozen table is **253 working states**,506rows,start0,blank0,uncounted halt253. Its complete delta from public253 is compact37/0→42,37/1→48,42/0→41,42/1→50 (all writes unchanged, all R). The named new labels255/256/257 replace old labels12/128/110; they are not extra working states.

The ordinary same-halting proof is substantively stronger than a finite trace: exact whole-tape blank bootstrap reaches the old endpoint40moves earlier (312935 rather than312975); all8391 arbitrary-register/gap≥40 site cases pass a stricter port of the proof-bearing symbolic rules; every case has at least13 literal positive transitions; all four register-file primitives retain the conservative55row footprint; a mirrored2981-pair register certificate relates the closed reassociation to the baseline. Both DEC exits and exact increment multiplicities between tests are checked by independent tuple and string semantics. Strong induction on remaining finite TM halting time supplies the reverse simulation. Arbitrary spare suffixes and the updated gap/whole register file are included in concatenation. No unchecked prepared input or missing initializer was found. The paper's **ordinary ZFC-provable machine-to-machine equivalence** is supported by these finite certificates and unchanged general primitive proofs. It is **not** a new Lean/Coq-checked whole-machine endpoint or a state reduction.

The six-element upset-algebra counterinterpretation is correct: H={0,2,3,4,6,7}, only7designated; implication is actual Heyting implication; Q preserves7, distribution and oldrho6; all Eq atoms7 and Rel atoms4 validate the retained equality/atomic-vacuity rows. K/S hold, yet Peirce at Q(Rel→Bottom)=2 has value6. This refutes dropping classical implication from the genuine-Bottom *logical* system. It is neither a CP/GIC/PSC model nor the numerical F=Rel00 alias.

Logical certificates are exact substitution/MP derivations: attributed107-row public L→K/I/P/B/S;77-row new KSP→L (K21,S17,Peirce1,MP38);325-row KBP→S. The deduction-theorem explanations expand to closed certificates. Ex falso uses originalrho6 plus derived implication basis; it is not asserted to follow from a freely designated formula by pure implication alone. Propositional transport does not require injectivity of numerical constructors.

Both newbasis emitters preserve all remaining equality/quantifier/theory rows, GEN ordering, original4tags/Falias and gates; three independent scalar inputs remain. Their directly emitted **modified** AX words, not originalp254, are the RM certificate references. KSP268 (206+62,4750pairs) matches oldL268 (206+62,4533pairs); KBP269 (207+62,4713pairs). The changes in AX stream arity, stack selectors and fairness are still unproved source-enumerator obligations, and binary/compiler endpoint flags are false. No basis-to-state subtraction is licensed.

The source-specific ordinary internalization note correctly tracks finite proof trees, specialcodes0/1, SIR falsity, finite candidate scheduling, positive-progress reverse simulation, Foundation/Choice and exact presentation changes. It distinguishes ordinary mathematical reconstruction from a serialized arithmetic/Lean certificate. PSC saturation is explicitly prior research.

## Checks, broad replays, PDF

`uv run --no-project python -B code/reproduce.py --recompile`: all10 selected suites **PASS**. Logs at `02-reproduce.log`, complete per-suite logs under `02/data/replay_logs/`; summary `02/data/verification_summary.json`. Selected exact outputs and independent table/bootstrap checks, all three logical certificates and mutations,420countermodel conditions, strict8391sites, independent2981RM and all three frozen modified-basis certificates pass.

A separate selected-recompile invocation bypasses only the release input-manifest loop **in memory**, retaining functional source/spec/byte/table identity checks: `rerun02-no-release-manifest.py` → `02-selected-recompile/verification.json`. No line-ending work or original edits. All advertised broad searches also **PASS**: 128,000 basis proposals with 111,141 actual compilations, all238 local reassociations, and the four greedy families. Entire normalized stage records/histograms, all238 candidate records and all four greedy result records match the delivery. Normalization removes only runtime/path/provenance metadata and fills one omitted false default (`vary_bundle`); costs, recipes and outcomes are unchanged. The four greedy families test55,692 /116,269 /56,166 /55,692 affine candidates and finish253 /253 /254 /253states, respectively; the second accepts three folds but obtains no smaller table. Full search commands and reproduced result records are in `data/intake-152-source-27-verification.json`.

Three scratch pdflatex passes all exit0;24pages; zero warnings/overfull/underfull. PDF text and logs retained; pages10/12/14/15/16rendered, countermodel page14, machine introduction page15 and complete four-row table/ordinary equivalence theorem page16 visually clean. No Coq build.

Delivered Lean adapters were conspicuously **uncompiled by the author**, but intake independently compiled both unchanged on a copy: absolute Lean4.32.0 (commit8c9756b), LukasiewiczCertificate1.240763s and TarskiClosedBasis0.772627s. Seven axiom audits and three caller checks PASS (0.369s). The finite implication/exfalso/classical proofs are axiom-free; completeness uses only standard propext/Classical.choice/Quot.sound. Dependency cache `/tmp/zfc-infinity-l2-integration-1rmcfjvy` was reused, not rebuilt; scope is these two adapters, not a fresh full project or machine proof. Sources/logs/commands: `02-lean/`. Sole build slot was returned to root immediately. Eight additional targeted RM certificate mutations (including operation, entry, both DEC branch order and relation structure) were independently rejected; see `rm-mutations.json`.

## Current tree and limitations

The claimed missing `Lukasiewicz.lean` is a historical fact at4747142d, now stale as a project gap: current `Lukasiewicz.lean:509–522` derives `Tarski.classical` from the actual rows and gives unconditional named primitive-Bottom `complete`. Source02's uncompiled adapters are alternative portable integration material, not the first closure of that repository obligation.

Current `Code254.lean:464–476` has the corrected explicit-valuation/no-nonempty-EncBundle-model theorem, and `Enum254.lean:700–716` has the actual six-register numerical derivability endpoint. `QuotientZF0.lean:78–93` now proves a one-way ZF0-refutation→C254F→abstractEnum halt. `DecodeFresh254.lean:63,86–119` covers actual all-code label bounds/semantic freshness including0. These narrow the old formal gaps, while the reverse model/standard-ZFC and full literal253 runtime composition remain open. The reduced248–252calculus is still rejected; this253variant retains the complete original calculus and is distinct.

Recommended write status: accept same-size faster-boot variant with **ordinary** same-halting proof and explicit no-new-kernel caveat; logical obstruction/proof certificates and completebasis controls accepted at their exact layers. No new sub253 record.

## Durable intake evidence

Independent verification and PDF/build metadata: `data/intake-152-source-27-verification.json`. Placement is `b123527ff4`. Supplied sources remain unchanged; the project base article is unchanged. All advertised functional modes and bounded optional searches completed successfully; exact normalized comparisons are retained in that JSON. Ordinary mathematics, finite executable checks and kernel claims are distinguished above.
