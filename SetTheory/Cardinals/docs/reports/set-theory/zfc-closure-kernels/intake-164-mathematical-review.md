# Independent mathematical/source review of submission 8286787dd0 (245 states)

**Verdict:** no mathematical counterexample or substantive runtime/composition blocker found in the reviewed sources. This is a serious complete 245-state proposal, with an ordinary mathematical proof supported by executable induction certificates. It is not a new compiled Lean endpoint or a PA-internal consistency-equivalence proof. This receipt is source-only: I ran no supplied checker, simulator, compiler, proof tool or manifest verifier. Delivered PASS records were read as author evidence; independent fresh replay belongs to root's separate record.

Review root: `/tmp/zfc245-8286787-review/extracted/zfc245-proof-20261018`. File:line references below are relative to that root unless marked maintained.

## Exact object and comparison with checked 246

The canonical table has 245 working states, start0, dispatcher88, terminal245 and 490 transitions. It is SHA `17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13`; original-label table SHA `f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267`. I directly compared the archived reference canonical and original-label246 tables to the maintained candidate-prefix246 files: both are byte-identical. No manifest was consulted.

An independent static row comparison finds **104 changed surviving transition rows**, removal of original-label rows247/0 and247/1, and no added original working labels. This is a substantial reassociation of the decoder, not an isolated merge. The report explicitly recognizes this at report.tex:144. Labels74,177 and208 remain present with new semantic roles.

The actual new idea is joint optimization of closed source words, special left-entry routing and scanner length (report.tex:93–198). The old178 rotation is enabled by reassociating98 and rerouting218/0 through86. The released scanner label74 becomes the helper `(132,16)`. Absorbing the fixed177 routing role into the charged grammar yields118 framework roles plus128 grammar roles; shortening the scanner yields117+128=245. The final source zero-run bound6 is a search constraint; the paper correctly does not use it as a substitute for runtime correctness.

For a later Lean port, all46 rows of the following23 existing arithmetic/selector core states are unchanged as old-label transition triples: 73,83,95,109,75,255,131,112,48,63,60,44,31,56,38,40,28,64,69,2,4,6,20. This supports reuse of the existing pulse, box and mark proof structure. Canonical numeric codes must still be regenerated: old255 shifts when old247 is removed. The new program tree, its coverage, changed entry routes, padding64 and finite startup require new bindings/proofs.

## Source association and entry routes

`audit_routing_grammar.py:41–54` recomputes break/continue escape bounds of all context-labelled atoms and both children of original sequence roots. Closedness is essential; reassociation of arbitrary break/continue syntax would be unsound. The finite projection audit at lines176–211 checks both predecessor bits, the caller's actual written bit, old transparent rows and the new semantic endpoint. No reachability assumption on the predecessor bit is needed for those short routes. The proof of the 177 three-step routing identity and the bootstrap forced-prefix lemma match these exact tape/head effects.

The stronger source correspondence is the freshly generated segment bisimulation, not leaf-count equality alone. `build_routing_machine.py:100–121` checks equal initial increment counts; each related decrement tests the same register; both zero/positive successor segments have equal per-register increment counts and point to a recorded related pair; halt relates only to halt. The imported `rmpath.py:65–149` implements complete finite-tree path semantics and bounded segment discovery that fails when fuel is exhausted. A successful finite certificate therefore supports all register values, because intervening increments commute and no value-dependent branch occurs before the next matched decrement. Finite bisimulation generation does not extrapolate from selected numerical runs.

The exact original source is freshly parsed and compared before transformation in `build_routing_machine.py:230–232`. The emitted new complete path list, its physical/logical register conversion, and the finite source bisimulation are separate certificate objects. No logical axiom-row weakening or theory replacement is used.

## Universal all-values runtime

The admitted frame is the entire two-way tape, with header distance `64+n`, arbitrary nine primary naturals, arbitrary nonempty finite spare list, and zero exterior. This is stronger than the finite literal fixtures. The all-values mode is genuine:

- `full_symbolic_parametric.py:100–123` requires `--all-values` when alternate source paths are supplied, checks a complete prefix-free binary trie, then replaces inherited interval bounds by independent natural variables. In `case` (lines60–77), zero-decrement fixes only its named variable to0; positive-decrement represents it as1 plus an arbitrary natural variable. Other registers and the gap have separate arbitrary variables. The sentinel interval upper value9 is not an upper bound on those variables.
- The spare suffix is one arbitrary first block plus an arbitrary finite block list (`make_file`, lines26–27), so it includes every nonempty spare list. Increment appends a value-one block; no instruction consumes the last spare. The zero-decrement proof explicitly exposes the following block in the macro induction checker (lines263–268).
- `audit_existing_machine.py:19–29` installs the **candidate** table, clears the derived lemma registry, and rederives the four one-block lemmas, list identity, three arithmetic macros and nine marks before accepting affine oracles. Full-frame replay also installs the candidate table before `prove_blocks`/`prove_word_identity` at lines91–92.
- The primitive symbolic rules are sound unary self-loop induction and literal steps. A non-self-loop unknown run is peeled only when its affine constant is at least1. Run normalization checks all coefficients/constants are nonnegative. A self-loop may change the written bit; induction transfers exactly the indicated run and updated context. Zero repetitions are reflexive and are permitted.
- `check_macro_inductions.py:171–190,214–252` derives finite-list traversal only from previously checked same-state/same-orientation block endpoints with arbitrary untouched contexts. The special rewrite `C(A)1=1B(A)` and its reverse are genuine free-word identities proved by empty/cons induction; they are not execution assumptions. List width is interpreted as the finite encoded length, not an externally bounded sample.
- `parametric_prefix_affine.py:23–36` permits decrement only at the named physical register and only after a valid mark, and disallows another effect on a pending modified box. This matters to the opaque-oracle proof. The expanded full-frame pass independently removes that opacity.
- `full_symbolic_parametric.py:79–84` checks exact entire target configuration, nonnegative symbolic cost with positive constant, and head motion exactly minus pointer overflow. Thus its statement includes absolute head displacement, which should not be inferred solely from translation-normalized affine endpoints.

The supplied records report8391 guarded cases, including1931 zero and1931 positive decrements, with minimum13 literal steps; the expanded pass reports2312645 symbolic rules and490 rows. These are delivered observations, not fresh results of this review. The rule meanings above justify universal values if the complete runs pass. The8385 interval literal fixtures are useful independent regressions but are not universal premises.

## Composition and residual pointers

`verify_machine_frame245.py:75–126` checks the new complete tree, full-width successors and all8390 nonterminal residual-pointer identities. The full word, including trailing zeros and overflow, is retained before zero-extension decoding. Equality is checked at the constant padding part; appending the same arbitrary `n` zeros proves it for every gap parameter. Maximum leaf depth51 leaves at least13 constant cells with padding64.

The report's invariant is correct: `n' = n + positive_decrement + overflow`, and spare nonemptiness persists. Initial empty pointer and decoded leaf000 describe the same tape (`0^64 = 000 0^61`). These are the premises needed for indefinite source-step composition, and they are checked anew for this grammar rather than inherited from246's shallower tree.

Halting reflection in report.tex:304–311 and reviews/composition245.tex:164–185 uses strong induction on remaining binary halting time. A nonterminal source instruction has a finite positive segment ending in an active dispatcher frame. The deterministic run cannot halt earlier within that executable segment, so the remaining halt time strictly decreases. No infinite choice, uniform runtime bound or assumed nonhalting is used. A terminal source instruction is handled directly. The two directions compose with the source bisimulation.

## Blank initialization

The direct candidate replay and the contraction explanation are logically separate. The reported exact frame after407915 steps has head−5, marker−6, header176, distance181, physical values `(0,0,0,3,0,0,3,0,0)`,167 spares all1, and351 one-cells with zero elsewhere. `build_routing_machine.py:42–97` checks whole sparse/dense endpoints; `check_candidate_boot.py` independently uses a flattened transition array and dense tape and compares all occupied coordinates to the baseline frame. `verify_machine_frame245.py:129–144` reconstructs all351 coordinates from the claimed blocks, preventing stray one-cells from being ignored.

The contraction is valid only when cells x,x−1,x−2 are all zero. Old58→74→84→84 has moves L,L,R, identical tape, and endpoint84 at x−1; new58/0 takes L directly. `check_short_scan_boot.py:13–24` checks all three zeros at all1410 baseline occurrences. Its own exact replay concerns the scanner-only edit; the final grammar candidate also has a separate direct replay. The reported time arithmetic410735−2·1410=407915 is correct. Absence of74/1 alone would be insufficient, and the paper explicitly says so.

The54 row locks and short route blocks explain why reassociation can coexist with the initializer. The baseline-lock theorem in proof/routing_bootstrap_lemma.tex is explicitly a sufficient finite-bootstrap theorem, with the optional scanner contraction added afterward. It is not presented as a universal runtime theorem.

## Logical calibration and strongest justified scope

The logical seed is exactly maintained `LogicalSeed246.seed`; its safe formula/stack fields are zero. I checked the maintained theorem signatures for `Bisim254.prog254_halts_iff`, `DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0`, `NativeTheory254.c254_refutation_iff`, `WFTheory.native_refutation_iff_zf` and Choice calibration. The named seed specialization is correctly ordered. Physical spares are auxiliary tape storage, not extra logical registers. The source instructions use only the first nine logical registers.

The resulting ordinary mathematical argument is: exact blank frame → universal candidate runtime → finite new/original source bisimulation → known safe-seed refutation calibration. The retained Foundation/Choice adapters target conventional ZFC. The report explains ordinary set-coded completeness/model constructions rather than claiming that a universe-polymorphic Lean theorem automatically is a ZFC derivation. I found no new stronger-theory assumption in that composition.

The strongest advertised theorem is **ZFC ⊢ (¬Halt245 ↔ Con(ZFC))**, with no consistency assumption needed for the equivalence. Its new part is an ordinary mathematical certificate argument. The archive does **not** supply PA internalization, a serialized first-order ZFC proof, or a compiled Lean endpoint for245 (report.tex:71,414). Those remain distinct obligations. Consistency yields actual nonhalting and ZFC-unprovability of nonhalting; the report correctly retains a soundness requirement when claiming two-sided independence. This review does not upgrade author PASS reports into fresh execution evidence or prove the claimed ZFC internalization in a proof assistant.

## Findings and limits

No substantive mathematical counterexample or missing composition premise was found. No below245 optimality claim is established, and no smaller theory/coding improvement is part of this reduction. The finite failed seven-zero candidate and pair-merge searches are clearly historical diagnostics, not state lower bounds.

Two minor stale references do not affect the proof object identity: `proof/zfc245_runtime_proof.tex:16` names absent `gradient245-zero6/machine.tm` (use `machine/zfc245.tm` or `certificate/machine.tm`); `reviews/runtime245-README.md:6` names a root `renumbering.json` that is absent (use `certificate/renumbering.json` or `machine/renumbering.json`). The main README supplies the correct current paths and exact table identities. No delivered files were edited.

Recommended next formal unit is the exact Table245/Fast245 binding, followed by reuse of unchanged old-label pulse/box/mark rows, a new program/segment-bisimulation certificate and coverage with margin64, plus a407915-step blank bootstrap. The generic source-to-binary composition and logical seed calibration should be reused with new exact hypotheses; renaming the246 endpoint would be invalid.
