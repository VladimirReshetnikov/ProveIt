# Intake155/source45 — Smaller proof engines for ZFC consistency machines

Review date:16 October2026 local; delivery dated17 October2026.
Original: `/tmp/zfc-intake155/zfc_fused_transport/zfc_fused_transport`.
Executed/build copy: `/tmp/zfc-intake155-tests/45`.
Additional evidence: `/tmp/zfc-intake155-tests/source45-review`.
Reusable replay adapter: `/tmp/zfc-intake155/source45_adapter.py`.

## Placement and provenance

Addition to the existing closure-kernel report, continuing source28's contraction-complete proof engine and the same compiler/minimization programme. No pre-placement retraction is required: the new ordinary mathematics appears correct, while its repository frontier is historical at the stated pin. Preserve all new and retained constructions separately; the 22-control,24-control,26-control and265-state objects have different meanings.

Pin:`61e77836565f63582561f54745f633d50efd9c7d`. Requested commits:`6d8bc7f1ba02c83e54757366f019f61b966ed0b7`, `63c83cf79986f8a92bb75460848a1d4f863b7b15`, `0301aa64e0676bed17402a63de46996631252a51`. Upstream254 pin:`297ab8df7e5de329605c3875b4934643b371a5e3`; public253 pin:`0d544f2a2e3c18f12278441a74b7879f31cbe856`. Source28's four-map checker and stream codec are retained as comparators. Mira-Cult/Jeff/mira-emmy/Wade attribution and nested license boundaries are explicit; the root MIT-0 grant does not relicense the upstream Prog254 source lacking an upstream-wide license. No new Lean/Coq source or build is delivered.

The review read all main sections, both principal transport proofs, preliminary26-control note, README/provenance/notices, new kernels and translators, finite theory emitters, stream code and verification suites, and the machine abstraction/independent checker/compiler/assembly/specialization code. The earlier source28 syntax/calculus and unchanged Wade backend remain prior dependencies. Retained data is evidence of particular finite runs; it is not a mathematical proof or a compiled new consistency machine.

## Main mathematical findings

**Preferred22-control kernel.** Free names are integers F(z), bound variables are separately tagged de Bruijn indices B(j). Shifts change only F fields. GEN0 closes free0, while UI0 opens the displayed outer binder at free0 with no freshness restriction. This unrestricted UI is sound even when the body already has free0: the old free occurrences retain their value, and the opened bound occurrences receive that same value. Nested binders cannot capture a separately tagged free field. The body is scope-checked under one additional binder, and theorem generalization is used only with a closed nonlogical theory and no open-assumption instruction.

Arbitrary named GEN and UI follow by conjugating with a uniform shift, whose negative and positive components are available. To implement a simultaneous substitution, first generalize *every* original free name, then instantiate the newly added binders in reverse order at the intended target names. No original name remains free before instantiation starts. An introduced target is never confused with a still-bound occurrence, so collisions and signed names are safe. The code follows exactly this argument and checks literal conclusion equality. This is stronger than naively applying sequential free-name replacements, which would be wrong when targets collide with later sources.

The forward translator replaces the source28 swap/contraction rules by those theorem-producing macros, translates arbitrary-name quantifier rules by shifts, and remaps proof references. The reverse translator derives unrestricted UI0 from fresh UI and a whole-formula contraction in the original kernel. Exact formulas are checked at every source-line boundary. A final identity operation on a closed earlier theorem may legitimately truncate the dead tail; correspondence is explicitly against the full expansion. The checker itself accepts only two shifts and fixed-zero quantifier rules; the support-aware completeness compiler is external, not an uncharged checker subroutine. Its underlying GEN/UI/MP admissibility mechanism is standard and already occurs in source18, as the report credits.

The stream inventory is11+11=22 separately counted variable-output controls. It pays only for name passes. It excludes syntax recognition, binder traversal, axiom emission, reference lookup, copying, storage, enumeration and blank initialization. No binary-machine state saving follows from subtracting this count from46 or253.

**Two-map-only24-control theorem.** Let u(z)=z+1 and w(0)=1,w(1)=−1,w(z)=z−1 otherwise. The intermediate H=wu maps0→2,1→0 and fixes all other names. Protected-hole routing realizes an adjacent swap on any chosen finite live set; a four-part repaired contraction and ordinary shifts then simulate the source28 four-map factorization. Decrement on a nonempty finite support S is implemented by u^a w^(a+c) u^c, where a=max(0,1−minS),c=max(0,maxS). Shifted live names lie on the positive orbit, and w crosses1→−1, producing the required one-unit offset. Every stage updates its live image before constructing the next macro. This proves agreement on the specified finite set, not global equality with a finite permutation: any word containing w is globally noninjective.

Both narrow minimality proofs are sound. Powers of one map commute on any finite set they each permute, so one primitive cannot provide both noncommuting three-point transpositions. If the other primitive is upward shift and decrement is modified at only one input k, either the defect has absolute value≥2 and every word preserves pairwise differences modulo that value, or the defect is−1,0,1 and both maps are monotone. Neither case realizes all finite maps. These are instruction/presentation bounds under the exact architecture, not lower bounds on stream or TM states. They do not conflict with22 controls, where quantifier rules supply extra substitution power.

The particular simple pair's historical priority is not claimed. The publisher bibliography verifies Sierpinski's1935 citation; its download returned403 during this review. [Hyde–Péresse, Theorem1.1](https://arxiv.org/html/1211.6284v1) confirms the classical countable-transformation/two-generator theorem and its attribution. This literature is context; the submitted explicit finite-support proof is independently checkable and does not assume that arbitrary global permutations are generated by u,w.

**Fixed object theories and search.** The primary frontend emits equality-free CP and full parameter GIC with support; no IR sentence is added. The optional inherited `alternative=True` is EPSC2, while the separate unary interface is EPSC1 plus exact binary Union, fused into every schema instance. The false matrix yields the Union sentence, so fusion preserves its logical content and does not erase its implementation cost. The emitters choose helper names outside the matrix free-name set, close all remaining parameters and preserve nested bound indices. The unary interface restricts free slots0/1/2 to input/output/parameter while leaving quantifier depth unrestricted.

Candidates contain exactly matrices and a proof; they cannot provide a different theory or target. Acceptance reconstructs actual BOT. Shortlex enumeration reaches every finite valid byte certificate. The parser avoids a configured decimal-digit cap, and resource failures propagate as errors rather than being turned into logical rejection. Ordinary refutation completeness rests on the general syntax/proof transport and explicitly inherited theory calibration, not on the bounded tests. The full observational-equality interpretation of the equality-free source is not an assertion that raw equality-free GIC implies native-identity GIC in the same structure; it does not contradict `DuplicateProfiles`.

## Machine experiment and actual scope

A five-atom product abstraction of nine unbounded natural registers is computed over all6,460 literal Prog254 leaf positions. Increment/zero/positive-decrement transfers are sound, including≥4→{3,≥4}; successor paths use exact same-length binary carry, break/continue suffix stripping and a zero-extended walk. The independent checker recomputes every edge and initial inclusion without importing the producer/backend. From N=0 and N=2 with other eight registers0, both certificates have6,456 non-bottom leaves and8,384 nonempty edge obligations. Non-bottom does not imply actual reachability.

At the two displayed paths, scratch1 and topwff respectively are always0. Their complete closed transfer loops therefore return normally without changing any register and may be replaced by BREAK0. Closed no-op contexts can then be simplified without discarding an escaping break/continue. This is a sound ordinary register-level guarded specialization. It does not prove the independently assembled binary interpreter or its bootstrap.

Exact sharing of the unchanged source gives the already known203-node DAG. Under this backend it produces265=203+62 working states/530 total rows. Replacing the loops gives271=209+62; simplifying closed no-op contexts gives269=207+62. All406 baseline decoder edges are independently re-extracted, and every named/numeric table row and source leaf word is checked. The15×18=270 guarded-identity choices have histogram203:1,204:1,205:16,206:1,207:14,208:29,209:208. The unique203-node winner is byte-identical to the original baseline. The family is ranked by decoder nodes; only its winner is emitted, so it is not a full-state optimizer or a global lower bound.

The one undefined Wade row1.inc/read1 is totalized to one final move into halt. This preserves halting from every configuration under the undefined-row-means-halt convention, without proving the row unreachable. The supplied265-state artifact has no new blank-start simulation or end-to-end consistency theorem. The report correctly keeps these limitations explicit.

## Current-tree corrections and overlap

At current review HEAD `fab89c5d26b81cd2ccab2ee5d213ff23725c7726`:

- `report/overview.tex:249–253` lists the literal-tree/DAG certificate, binary runtime and Foundation comparison as remaining work. Current `Bisim254.lean:3154–3163` proves `Halts Prog254.program ⟨[],R⟩ ↔ Halts pathDag254 ⟨[],R⟩` and the literal program/C254 endpoint. Current `BinaryPerm252.lean:93–112` proves the252-state literal blank-halting/ZF-refutation and nonhalting/ZF-consistency equivalences. Those historical gaps must not be restated as current.
- `WFTheory.lean:37–49` already gives numerical/native consistency equivalence to full ZF including Foundation and Power. Choice and internal PA proof coding remain distinct; they are not the whole unproved native/ZF comparison.
- `permutation252_phase_analysis.md:36–53` already identifies precisely these two impossible positive-decrement guards and four unreachable leaves, with the same paths and8,384 feasible nonhalting transfers. The report's five-atom domain additionally covers N=2 and per-position zero masks; its guarded270-choice identity search is a new finite control experiment. It is not the first current identification of those guards.
- `register_lifetime.md:20–45` already distinguishes destructive clear/transfer/pair/unpair contracts from naive syntactic liveness, and lines47–71 give a nine-live macro obstruction with no blank-reachability claim. The report's failed36-pair product-abstraction test is another sufficient test, not a proof that no8-register algorithm is possible.
- The source28 four-map kernel and source18 GEN/UI/MP collision mechanism are correctly attributed. EPSC1+BU is now placed source39, and the other 'incoming' entries at the old pin are also processed. The report supplies no new proof of those object theories' full calibration.
- `Code254Proof`/`Code254ProofCompiler` and the newly checked ordinary-Nat `Code254History` are later external finite-data constructions. They do not automatically apply to this package's different proof syntax or count as an internal PA bridge.

No mathematical defect or false *current* assertion requiring a separate retraction was found. Retain the source's original audit under its pin and add these corrections in reconciliation.

## Reproduction and PDF

The parent first ran `uv run --no-project python -B reproduce.py --extended` on `/tmp/zfc-intake155-tests/45`, with the root manifest call replaced by `manifest_count=None` on that copy. All eight suites passed; evidence:`/tmp/zfc-intake155-tests/source45-functional.log`. Review found that the nested machine driver still ran its two bulk hash-validation loops. That incidental manifest pass is preserved as history only and was not repeated.

The independently prepared adapter `/tmp/zfc-intake155/source45_adapter.py` accepts a package path and optional `--extended`. It monkeypatches the root manifest function and strips exactly three nested bulk-manifest loops from the AST in memory, without rewriting submitted source. All underlying functional jobs and literal Prog254 identity guards remain. Twenty-three generated direct-child machine TM/JSON artifacts are compared byte-for-byte before/after regeneration, without reading a manifest. Its extended replay passed all eight suites and all23 output comparisons. Log:`source45-review/adapter-extended.log`. This is the adapter for the eventual offline helper. Source44's release suite needs no bulk-manifest adapter.

Reproduced counts include:

- Preferred map suite:2,271 scalar/orbit identities;20,400 interval-swap points;23,040 sparse-live macro points;8,610 decrement points;all3,413 maps on supports of sizes1–5;150 signed maps;100 signed source words;854 atomic scanner cases;100 nested formula maps.
- Integration:802 whole-formula scanner comparisons;62 forward and61 reverse proof cases;collision example10→178→1,019 rows;33 closed theory axioms;288 direct unary-wrapper semantic cases;28 malformed-interface checks;5 shortlex roundtrips.
- Shift22:288 theorem substitutions on up to4 names,30 signed cases,27 forward/340 reverse cases,31 rejected malformed/prohibited cases,122 scanner comparisons,13 closed emitted axioms. The direct source19 collision axiom is one row, its generic translation76, and reverse translation10; compact contraction adds4 rows.
- Independent24-map check:765 protected swaps/5,610 values;4,944 collapse supports/22,065 values;4,944 downshift supports/22,065 values;15,050 orbit values;2,001 H=wu identities.
- Independent26-map and both extended preliminary suites pass with the retained counts. Machine producer/independent invariant checks, all four table assemblies and the full270-choice grammar search pass. All non-timing JSON evidence comparisons in the root driver remain enabled.

The submitted unbounded consistency searches were not launched. No Lean/Coq build is advertised or claimed.

Three scratch pdfLaTeX passes passed in1.650/1.347/1.238s. The rebuilt report has34 pages,28 embedded/subset font resources, no overfull boxes, no unresolved references or LaTeX warnings, and three underfull paragraphs. Pages1,4,9,12,18,24,30,34 were rendered and visually inspected: title, main theorem, narrow lower bounds, fixed-theory endpoint, invariant/specialization and implementation plan/references are legible, with no clipping/overlap/missing glyph observed. Build logs and PNGs are in `source45-review`; original PDF untouched.

The immutable package contains94 files/2,887,845 bytes; `source45-review/inventory.json` lists all paths by group. Main/report/preliminary sections, proof/stream code, fixed emitters, invariant certificates, tables and ledgers are substantive. Delivered PDFs and manifests retain their historical role and are not normalized.

## Recommendation

Keep22 and24 as complementary complete-calculus interfaces. The22 route uses quantification to avoid arbitrary substitution passes;24 proves the stronger map-only universality under a fresh-UI architecture. Both are plausible compiler inputs, not measured full-machine improvements. The next meaningful cost comparison must compile the complete retained four-map control, two-map kernel and fixed-zero kernel with the same theory, formula storage, scheduler, decoder and actual blank initializer. The signed free/bound representation and new UI interface require a checked codec/runtime adapter; the existing252 endpoint is not that adapter. Guarded identity alternatives are a useful secondary compiler choice, but the included complete270-choice test produced a negative result.

