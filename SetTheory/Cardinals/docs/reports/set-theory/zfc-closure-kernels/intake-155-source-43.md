# Independent intake review: source43, batch155

**Disposition: accept as ordinary mathematics and finite diagnostics, with its pinned historical scope. No concrete mathematical defect, failed advertised functional suite, or refutation of a current repository theorem was found. No new calibrated machine is supplied.**

Original, left unchanged: `/tmp/zfc-intake155/zfc_consistency_research_2026-10-17/zfc_consistency_research_2026-10-17`.
Independent working copy and evidence: `/tmp/zfc-review155-source43-ppg5xyu3` (submission under `package/`). Delivery commit: `fab89c5d26b81cd2ccab2ee5d213ff23725c7726`. All Python and LaTeX executions occurred on that copy. No checkout file was edited; no Lean or Rocq build was run.

## Source, attribution, and artifact classes

Title: *Toward a Smaller Con(ZFC) Machine: Acyclic one-parameter closure, exact short-gap obstructions, and a targeted 252-state proposal*, dated 17 October 2026 UTC. Read the entire report, all seven sections, bibliography, README, BUILD_AND_QA, THIRD_PARTY, Makefile, the packaging driver, support checker, four machine audit drivers, preserved source35 adapter, machine audit notes, and relevant included upstream contracts/generator.

The declared ProveIt primary pin is `3d731d8cf44941560752abc625149f7bfa109930`; novelty recheck is `ba00775e2bf56b184d071346867db74f2eb0c621`. The public 253 comparison is PR20 head `0d544f2a2e3c18f12278441a74b7879f31cbe856`, and merged upstream254 is `297ab8df7e5de329605c3875b4934643b371a5e3`. These are historical pins, not claims about a later moving branch.

Mira-Cult's machine, Jeff Ketchersid's verification/executor, mira-emmy's253 reduction, and Wade's compiler are explicitly credited. Source35 gets the safe-start/dirty-root theorem and fixed-gap adapter; source36 gets the original normalized support countermodel and its basic Pairing obstruction. A focused source comparison confirmed the actual Prog254, symexec, and public generator against local pinned Git objects, and functional Python AST identity for the supplied source35 adapter. See `targeted-source-provenance.json`. Bulk manifests and formatting/line-ending checks were outside review scope.

The delivered `code/machine/upstream/` is sufficient for the advertised Python replay, not a proof-assistant source closure. For example, `symexec.py` is deliberately loaded only from its `SKIP` definitions onward; its unused standalone preamble references `tmlib`, which is not needed by this package's entrypoints. There is no advertised new Lean/Rocq module to compile. The four original component notices are retained; neither this review nor the submission interprets one notice as a blanket license for all contributions. The scholarly PDFs are linked, not redistributed.

Artifact classification:

- New ordinary proofs: normalized integer rays and all finite acyclicity; capacity-k support generalization; source-covered partial-functional Replacement; fixed empty-replacement ER iff Pairing; an ordinary ZFC reconstruction of the known CP/GIC/IR consistency comparison.
- New finite diagnostics: eight-gap fixed/affine censuses, representative literal countertraces, longer bounded blank observation, finite support examples/orbits.
- Reused research machine: the **old, unpermuted** public 253 fold deleting old5/8, not the new permutation252 machine. Its504 rows and252 working states are exact; its displayed old0 blank start remains uncalibrated by this submission.
- No new kernel certificate, serialized first-orderZFC derivation, PA formalization, state record, lower bound, or proof of actual nonhalting.

## Independent mathematical review

### Normalization, support, and EPSC1

The normal-code construction is sound. Two-sided integer indexing supplies an existing ray representative for every singleton of a ray object, so the excluded duplicate fresh singleton codes are precisely what makes `make(Ext(y))=y` and literal Extensionality true. Fresh-code structural rank decreases along membership until a ray is reached; after that the integer coordinate strictly increases. Thus every fixed finite-cycle prohibition holds while the represented whole ray has no minimal member, so Foundation fails. The ordinary ambient codes themselves remain well founded; interpreted membership is a different relation.

Heredity ensures that interpreted subsets really are subsets of whole extensions. The complete relative power carrier is the ambient set of all normalized subsets of that extension. This supplies set-sized exact fibers whenever the subset-bound premise holds, despite the entire interpreted domain being a proper class. No selection of arbitrary bounds is used: each exact fiber is unique, hence Replacement collects it over a set of inputs.

For capacity k, the stabilizer of the parameter support fixes the input and every matrix parameter. If an output leaks outside that support, its orbit uses every component of the complement. There are at least k+1 such components among 2k+1, contradicting the capacity of a common subset bound. This argument applies to arbitrary first-order matrices, with equality, negation, and unrestricted internal quantifiers. Iteration from the unique empty object therefore constructs the EPSC1 hull within the parameter support; starting with no seed members makes global support exact. The proof is schema-wise ordinary mathematics, not extrapolation from a finite test.

Union, the full relative Power Set, arbitrary-parameter Separation, and the pure codedomega remain in the domain. NativeCP is correctly obtained by omega closure under extensions and each exact relative power object, all within the original support. For local family-choice graphs, all chosen values and pair codes share the represented family's support; ambient Choice is explicit, and no equivalence of all weak-theory Choice formulations is asserted.

Source-covered Replacement is valid: source, inputs, and parameters that are members or subsets of the source all have support withinS. A unique output using componentj outsideS can be moved to an unused component outsideS union support(output), possible because2k+1 exceeds2k. The transposition preserves all free data and changes the output's intrinsic support, contradicting uniqueness. The exact partial image is then collected by ambient Replacement and Separation. Undefined inputs need no witness choice. This establishes a model property, not derivability from EPSC1 alone.

The Pairing/AU/EPSC2 failures are exact. The selected nonemptya andb requirek+1 support components in one containing object. Singletons make the specified observational equality and outgoing implication coincide with identity. The displayed equality-free two-parameter matrix has locally subset-bounded singleton fibers and forces every hull to contain botha andb. Neither global support nor hidden logical equality is needed for that failure.

The relative-model conclusion is correctly limited to Con(ZFC): interpret the definable class construction *inside* an arbitrary set-coded ZFC model, then take its externally set-sized interpreted domain. No external well-foundedness, transitive model, or assertion thatZFC proves its own model existence is assumed. Internalomega closure need not equal externally finite reachability; the proof only uses its internal successor/union identities.

### Fixed empty-replacement repair

Both proofs of ER iff Pairing are valid. In the stronger base, applying ER to the powerset of a singleton, with a singleton parameter, and taking Union gives the required exact pair. The proof covers empty/equal arguments. The sharper base also works without Extensionality or a Singleton axiom: Separation first supplies an empty object; if one argument is nonempty, its powerset contains that argument and an empty input, whose ER-image contains both desired arguments; a final Separation gives the exact pair. If both are empty, both occur in a powerset of any empty object, and Separation suffices. Conversely Pairing+Union bounds every ER output by A union{p}, and one fixed Separation pattern gives its exact image. No arbitrary Replacement schema is smuggled into the fixed ER sentence. The background axiom surcharge remains part of any compiler comparison.

The local membership-induction lemma from Separation, Foundation, and transitive containment is correct. Its proof does not supply the witness collection needed for arbitrary Pairing. The quoted literature comparison was checked against primary PDFs: Schindler/Schlicht explicitly retains Pairing for parameter amalgamation; Mathias section13, printedp48, supplies the asserted incomparable-supertransitive-model construction. Neither reference establishes EPSC1 in those models. Links are recorded in `review.json`.

### Ordinary native/ZFC consistency calibration

The upper comparison is sound without object Choice: rank+omega provides CP containers, and least witness-rank bounds plus Replacement provide full GIC, filtering the chosen rank level by unrestricted support. No arbitrary witness selector is required.

The lower comparison explicitly uses internally set-coded raw bisimulations, not all external relations. Given the known full CP/GIC quotient theorem, the internally defined cumulative-hierarchy well-founded part satisfies actual translated ZF schemas; Replacement collects outputs and their least levels. Its constructible inner class then supplies ZFC by the standard uniform finite-formula reflection and internal constructible well-order argument. External ill-foundedness of the starting set model causes no problem. Ordinary first-order soundness/completeness gives the stated consistency comparison *in ZFC*. This is a mathematical reconstruction of established interpretation results, not a new serializedZFC proof or a generic appeal to proof-assistant soundness. PA internalization remains explicitly separate.

No current repository theorem is refuted. The report strengthens source36's separation and leaves the consistency strength of bare EPSC1 open. Its theory does not furnish a new measured complete frontend.

## Every advertised functional suite reproduced

The adapter `run_without_manifest.py` parses `code/reproduce.py` and replaces **only** the body of `identities()` with an explicit skipped record. It skips the two bulk package/machine manifest loops. It preserves all child scripts, standalone source/table guards, generator/table equality, semantic JSON comparisons, complete tapes, and trace digests. No global assertion or digest removal was used.

Command, from the scratch package:

```sh
python3 -B /tmp/zfc-review155-source43-ppg5xyu3/run_without_manifest.py \
  --full --long-run --output /tmp/zfc-review155-source43-ppg5xyu3/replay
```

All seven jobs passed. Their measured wall times were support 0.124 s, public table 0.041 s, fixed census 15.829 s, affine census 14.696 s, representative traces 0.395 s,1M literal 0.760 s,100M literal 81.580 s. This runs the full/default suite families as a superset, with every declared gap checked; it is not a claim to have executed all three CLI aliases redundantly.

| Gap | Fixed pass/reject | Affine pass/reject |
|---:|---:|---:|
|32|7756/635|6357/2034|
|33|8135/256|7169/1222|
|34|8311/80|7806/585|
|35|8376/15|8150/241|
|36|8391/0|8311/80|
|37|8391/0|8376/15|
|38|8391/0|8391/0|
|40|8391/0|8391/0|

Each mode checks 67,128 guarded cases across eight gaps. All records agree with delivered outputs after removing only elapsed-time fields. The symbolic audits still rely on the attributed register-box summaries. A checker rejection is not automatically a bad concrete execution; a fixed gap passing is not a theorem for every larger gap.

Support diagnostics passed for capacities 1/2/3:16/256/4096 support pairs,9/205/3717 leaking pairs,36/3280/237888 impossible bounds. The 48 concrete objects pass 2304 extensional-pair and 288 automorphism tests, 123 subset-support checks, union/power checks, cycles1..8, and six rejected cross-component pairs. These are not finite EPSC1 models.

The prepared suite gives 16 different complete frames and four exact controls. Source35's prior rejected affine case is literally correct in 2794 moves. The prominent gap35 case763 returns after 702 moves with actual gap38 and altered primary values, while its gap36 control reaches the exact intended whole tape in 416 moves. Prepared frames are not claimed reachable from blank, and first-complete-frame mismatch does not rule out a later accidental target visit.

The full100M literal run matches the recorded whole final tape and counts: oldstate131, head4720,5429 ones,34073 dispatcher visits, greatest recognized gap32,13815 gap32 frames, and zero sufficient-gap frames. The recorded histogram is18:195,19:32,21:5,24:1,26:44,28:55,30:6,32:13815. This is finite-prefix evidence, not divergence or impossibility of initialization.

An independent exact first-write classification accounts for all252 blank-start states:240 reach one of the seven stated first-writer states0,7,20,42,83,95,112 and12 enter the three all-zero selfloop classes2,10,84. See `blank-start-classes.json`. The historical20M observations for other starts in AUDIT_NOTES were not redundantly replayed; all advertised replay-suite commands and the longer100M old0 trajectory were reproduced.

The separately advertised prior source35 command also passed:

```sh
python3 -B code/machine/source35_runtime252_short_gap.py \
  --upstream code/machine/upstream --limit 1000000 \
  --output /tmp/zfc-review155-source43-ppg5xyu3/prior_source35.json
```

Affine mode stops at rejected contract641 after52 distinct contracts; the corresponding literal instruction succeeds in 2794 moves. Fixed-gap mode reaches its declared million-register-step bound with 124 distinct contracts. Its `reason=fuel` is the declared bounded endpoint, not a proof of termination/nonhalting or an all-future binary trace.

Independent of the report's own executors, `independent_traces.py` reconstructs the504-row table directly from the original literal254 table and four public edits, checks equality with the frozen runtime table, parses all 6459 nodes/6460 leaves/8391 guarded cases, and replays all 20 prepared traces row by row. It checks every resulting tape cell, executed-row digest, and first complete dispatch return. It additionally replays oldstart0 through60606 moves, obtaining the exact gap19 root, head-4, primary[0,2,2,0,0,0,1,0,0],60 recorded spares and logical[1,0,0,2,2,0,0,0,0]. See `independent-traces.json`.

`prepare_archive.py` was read but not run: ZIP/manifest generation is packaging and excluded checksum work, not a missing functional verification family. Upstream Rocq build recipes were read as attributed evidence and not executed.

## PDF build and visual quality

`make pdf` completed all three pdfLaTeX passes on the copy. RebuiltPDF:28 physical letter pages,492978bytes,21 embedded font records with Unicode mappings. Final log has no warnings, undefined references/citations, overfull or underfull boxes. All 28 pages were rendered and inspected in two contact sheets; closure/CP page 13 and exact-corruption page 20 were enlarged and read. Layout, tables, formulas, path literals, references, and command blocks are legible, with no clipping or overlapping material found. Bounding-box extraction found no out-of-page word. Toolchain was pdfTeX1.40.22/TeXLive2022, so PDF byte identity with the author's TeXLive2023 build is not claimed.

Artifacts: `pdf-build.log`, `pdf-qa/contact1.png`, `contact2.png`, `enlarged13-13.png`, `enlarged20-20.png`, `geometry.json`, `fonts.txt`, `pdfinfo.txt`. ThisQA creates no hosted PDF or source edit.

## Current-tree gap comparison, with exact source locations

Review snapshotHEAD was `fab89c5d26b81cd2ccab2ee5d213ff23725c7726`; source hashes are in `review.json`. The submission repeatedly says its current-status statements refer to the two older pins, so later progress is reconciliation, not a retroactive error.

- Submission `sections/06_proposal.tex` recommends obtaining a complete252 machine and instantiating the literal-tree/shared-program comparison. Current `Bisim254.lean:3155` proves literal/shared halting equivalence for every register file, `:3162` gives literal halting iffC254F, and `ActualTree254.lean:10` identifies the complete unfolded literal tree. The separate3010-row certificate and all-site instantiation are now complete.
- Current `BinaryPerm252.lean:11–14` states the closed whole-frame composition. `:46` supplies actual coverage, `:50` supplies the82552-step actual blank frame, `:72` gives actual blank halting iff literal-register halting, `:78` gives iffC254F, and `:93` gives iffZF refutation. `:110` gives nonhalting iffZF consistency. These apply to the **different** permutation candidate, old-labelSHA`939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`, not this submission's old runtimeSHA`48e6354a1c5f3de4cf80ff7c293bd1fa7fd2fc2da8f370ffd6b182e30abdde87`.
- Submission `sections/02_native_calibration.tex:117–181` gives an ordinary internal-WF/L argument. Current `WFTheory.lean:38` already proves native numerical refutation iff fullZF refutation, includingFoundation; `:47` gives native/ZF consistency equivalence. The report's ordinary ZFC reconstruction is useful exposition and does not newly certify that existing module or finish constructibleChoice.
- `Code254Proof.lean:257` now gives C254n iff existence of an accepted finite Nat proof code, and `BinaryPerm252.lean:84` exposes that exact checker witness at the blank machine. The report's demand to separate external theoremhood from arithmetic formalization remains valid.
- Current `BinaryPerm252.lean:24–27` explicitly separates the standardZFC Choice comparison and internalPA formalization. `Research/ZFC/README.md:583–587` makes the same remaining obligations precise. Neither source43's ordinary semantic calibration nor the fresh binary endpoint alone discharges the user's original PA-provability target.

The smaller-gap old-runtime observations remain valid diagnostic data. They neither refute the new permutation252 endpoint nor require weakening it. No preplacement retraction is needed.

## Useful next step and remaining limits

The report's main machine recommendation has already succeeded by a different physical-register permutation. Its strongest reusable additions are regressions for any future gap36/37 symbolic adapter and the stronger acyclic support obstruction for proposed one-parameter frontends. The ER repair is a concrete alternative fixed sentence to cost againstAU only after all its background axioms and complete proof engine are charged. The compatibility-world and Foundation-augmented EPSC1 interpretations remain explicitly proposed/unproved; no benchmark follows from them.

Keep the current complete252 machine frozen while completingChoice and the internal arithmetic bridge. No new literal search, formal module, commit, or hosted documentation edit was made during this review.
