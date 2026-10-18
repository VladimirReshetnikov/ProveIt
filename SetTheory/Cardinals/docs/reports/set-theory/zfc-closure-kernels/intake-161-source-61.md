# Source 61: independent Prefix247 mathematical and verifier review

Review date: 2026-10-17. Arrival: `96030114f5` (`New research report (247-state)`). This review is source-only: no report checker, simulator, Lean/Rocq compiler, dependency build, or version query was executed by this reviewer. The root agent owns the independent suite replay and must append its actual result separately.

## Conclusion and exact scope

I found no new mathematical blocker in the three-state reduction, its universal selector argument, or the composition with the existing prefix-carry contracts. The source supports a serious **247-working-state candidate with an ordinary mathematical proof and executable certificates**. It does **not** supply the original goal's PA-internal equivalence, a new kernel-checked exact247 binary endpoint, or a freshly rebuilt inherited logical closure. These exclusions are stated accurately and prominently in the submission.

The main novelty is real and local: revisit a runtime-unused branch after the arithmetic redesign, choose its startup action so its state duplicates an existing state, and recheck startup. Ordinary minimization of the unmodified250 table would miss this opportunity. The current250 formalization remains useful because all prefix arithmetic rows and their universal contracts are retained.

## Inputs and extraction

The exact committed archive was read using `git show 96030114f5:docs/incoming/zfc-prefix247-research-20261017.zip`, saved as `/tmp/zfc-intake-161-247/opening-source.zip`, and safely extracted under `/tmp/zfc-intake-161-247/opening-extracted/zfc-prefix247`. It has150 entries,6,586,159 expanded bytes. Extraction rejected absolute/traversing/backslash paths, duplicate names and symlinks and imposed size/count caps; see `opening-extraction.json`. The separate root extraction is under `/tmp/zfc-intake-161/zfc-prefix247-research-20261017/zfc-prefix247`.

The claimed/current logical-source pin is `e0b512a63e2c1ca6a1698fa437b8568f1643ff6b`. All12 provided source snapshots listed in `results/current-source-audit.json` independently compare byte-for-byte with both that Git revision and current maintained files. This is source identity, not evidence of successful compilation; see `opening-source-identity.json`.

The canonical247 table identity is `58bbbda620daf6d4d62f486db05f54d0dccb8373c080c1b5a0b26533e7a3a669`; the old-label identity is `0d37614f3caf37139b0be127837630539224acd1c45d748cf5704abfc3230b42`. The input250 table is the exact already-reviewed `fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43`. No checksum manifest was checked. These explicit identities bind mathematical/program inputs rather than a bulk manifest.

## Reduction and universal behavior

1. **The final recipe is precise.** Change old row `(60,0)` from `(0,R,0)` to `(0,R,20)`, delete states0,1,3, and retain every other surviving row and start97. Canonical start0, dispatcher89, halt247;494 rows. The two independent construction functions (`code/audit247.py:50`, `code/verify_runtime247.py:42`) check deleted-state entries, totality and exact canonical numbering. The inherited reconstruction also checks the single halting row, preserving its final write and move.

2. **Selector transport covers zero-valued registers.** A plain block is `0 1^(v+1)`, not `0 1^v`. The last selector separator therefore always moves onto one, even when v=0. Old0/read1 and20/read1 are both `(0,L,2)`. The selector-index induction and unchanged return rows2/4/6 preserve arbitrary exterior tape and return before inspecting the left context. Exact marking time is `2*w(prefix)+3`. The finite set of nine selector choices contains independently quantified unary values; it is not nine numerical samples. The induction checker checks endpoint and head motion; the closed marking-time formula additionally follows from the paper's explicit induction (the checker records the inferred affine cost rather than asserting that separate formula).

3. **The quotient is unconditional only after the branch edit.** The intermediate248 table deletes1/3 and changes0/read0 to `(1,L,2)`. Its state0 and20 then have identical two-row behavior. The496 row equations prove a genuine one-step configuration homomorphism, with only halt mapped to halt. This preserves arbitrary-tape finite executions in both time and halting. It does not justify250's old blank startup; the report correctly makes that distinction (`report.tex:171–212`).

4. **Arithmetic reuse is justified by actual row dependencies.** The four one-block identities, finite-list lifts, `C(A)1=1B(A)`, and three arithmetic contracts use retained rows. The new wrapper substitutes its exact candidate table before calling the induction templates and rejects access to deleted labels. Zero decrement explicitly exposes a following block; nine primaries plus a nonempty spare suffix supply it even for index8. Increment needs the right blank exterior and appends one value-one spare. Positive decrement grows the file origin by one and inserts the corresponding boundary one. No bounded spare reservoir is consumed.

5. **The symbolic interpreter has an intelligible unbounded meaning.** Its self-loop scans are natural induction with a valid zero case. Its other run peels require a positive constant term. Register oracles match the physical register in the CD guard, track one effect, and cannot silently apply a second marking/update. The complete source parser rejects residue and checks a rooted forward6459-node tree;6460 leaves yield8391 guarded cases. The separate full-PC audit retains overflow and trailing-zero cells, so abbreviated counters are reconciled by complete tape equality. Each accepted returning case includes positive literal progress. Macro and literal accesses to deleted labels are separately covered.

6. **The global halting argument does not infer nonhalting from testing.** The complete recurrent frame includes both blank exteriors, clean PC, gap at least40 and nonempty spares. Cleanliness rebases arbitrary reached PCs to the checked leaf paths without changing zero-padded tape. Gap never decreases and spares are preserved/appended. Forward finite simulation is direct; reverse halting reflection uses strong induction on the binary halting time and an active endpoint after a positive segment. This avoids an unstated uniform bound on instruction duration or choice of an infinite sequence of witnesses.

## Startup and logical root

The final table has a separate741,241-step startup claim. `audit247.py:84–148` uses different sparse old-label and dense canonical-label simulation loops, compares whole tape support, and checks the exact block decoding. Its claimed endpoint is old96/canonical89, head−5, marker−6, header245, gap250, nine physical values `[0,0,0,3,0,0,3,0,0]`,235 value-one spares and487 one-cells. The two simulations share the constructed table/renumbering, so their implementation independence concerns transition execution and tape representation; they are not independent discoveries of the table. The exact delivered files are compared with reconstruction by the suite. These finite equalities still await the root's replay in this independent review.

The physical permutation gives logical `(N,T,W,A,D,H,X,Y,L)=(3,0,0,0,3,0,0,0,0)`. The source interfaces really permit it:

- `Bisim254.prog254_halts_iff` (`sources/Bisim254.lean:3155`) quantifies over every register file.
- `DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0` (`:94`) has exactly this encoded root and native-refutation conclusion.
- Alternatively, `EnumSafeStart254.zero_formula_start_iff 0 3 3` (`:125`) matches the six-field root through `L2.toAS`; its counter-tail completeness uses the explicit padding lemma (`:79`) and `complete_from` (`:109`). Starting at counter3 is therefore not justified merely by analogy with counter2.
- `NativeTheory254.c254_refutation_iff`, `WFTheory.native_refutation_iff_zf` and `ConstructibleChoice.zf_refutation_iff_zfc_refutation` have the composition endpoints cited by the paper.

`proof/RootCalibration247.lean` is a reasonable source-level composition of these exact statements. I did not compile it; the file expressly disclaims compilation and any binary theorem. The new manuscript's set-coded ZFC argument uses set models, internally defined well-founded/constructible subdomains and finite syntax. It does not mistake an externally ill-founded Henkin model for a transitive model or infer ZFC-internal provability merely from Lean's standard axiom list. This review checks the composition and stated boundary, not the entire inherited model-construction closure. Stronger PA proof-code transport remains unfinished independently of the state saving.

## Replay guidance and verifier behavior

After source review, the exact substantive invocation for the root is:

```sh
# Run in a separate writable copy of the extracted package, with PYTHONOPTIMIZE unset.
python3 -B code/verify.py
```

There are **seven checks total**: one inline252→250 reconstruction and six subprocess stages: printed table, final table/quotient plus dual startup, universal macros/all guarded instructions, independent full-source/full-PC, finite literal instructions, finite arithmetic. The latter two are correctly marked finite-only. Expected counts are8391 symbolic cases,33,564 literal instruction cases and16,200 arithmetic cases, with minimum13 literal steps. Recorded timings are not mathematical checks.

The driver uses standard library only, performs no network request/compiler/dependency installation, disables optimization in child environments, and writes fresh results plus a temporary directory. No manifest verifier is called. Hardcoded table/program/checker identities are deliberate input binding. It preserves reference250 files. The suite itself has no timeout/memory cap; root should supply its usual outer bound. The driver's `current-source-audit.json` is inherited evidence and is not refreshed by offline replay; this review independently checked those source bytes.

No source-only defect requires changing the delivered checker before this replay. Optional unused arguments/imports and historical naming in comments do not affect its mathematical checks. In particular the retained literal-instruction `--baseline` argument supplies attribution/hash data, while candidate behavior is evaluated directly against the247 table; the inherited baseline construction is a separate substantive stage.

## Read inventory and reusable next work

See `review-61-inventory.json` for exact file hashes and read coverage. I fully read the new README, main TeX report, additional dead-return proof, bootstrap review, provenance, five Python scripts and root Lean fragment; reread the entire actually imported nonstdlib verifier closure (affine, induction, rebuild, both literal checkers); read six complete logical interface sources and relevant intervals of Bisim/L2Root/RegisterPathClean. All13 reference250 Python files compare byte-identical with the already independently reviewed source59 package; prior review is `/tmp/zfc-intake-162/review-162-symbolic.md`. Other inherited theorem bodies were only identity-checked, not represented as freshly reviewed.

For formalization, preserve the completed250 literal table and frozen fast/checkpoint drafts. Parameterize/reuse prefix arithmetic contracts by the unchanged old-label rows, prove the selector endpoint with old20/read1, then add an exact247 table and a separately chunked741,241-step bootstrap. The exact248→247 quotient is a cheap finite lemma but cannot replace the new startup proof. Root calibration can be a small independently checked logical module. These improvements do not discharge the ongoing PA-internal compiler goal.
