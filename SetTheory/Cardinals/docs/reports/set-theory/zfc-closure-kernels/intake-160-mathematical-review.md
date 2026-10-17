# Independent source review: prefix250, intakes 161 and 162

## Conclusion and scope

The exact prefix250 table is a credible two-state improvement over permutation252. I found no fatal mathematical defect in the new carry/rollback contracts, nonempty-spare invariant, pulse retiming, all-gap symbolic execution rules, whole-frame simulation, or dirty-root composition. Intake162 strengthens the ordinary proof and independent finite audits of the **same machine** submitted in161; it is not a second state-count improvement or a new discovery of the prefix/pulse mechanism.

This is a source review, not a new proof-assistant verification or a certification of the entire inherited dependency closure. I read the161 report and proof fragments, the162 report and substantive proof sections, the relevant symbolic checker source, and selected inherited theorem declarations and proofs. I executed no supplied code, Lean/Rocq/compiler, checker, version query, or dependency build. Only source reads, identity comparisons, and this review's own hashing were performed. Root separately reported a fresh six-stage161 verification PASS in12.137 seconds; that execution belongs to root's evidence, not this review. Included162 PASS files are supplied records unless root separately reproduces them.

The report's ordinary ZFC argument does **not** complete the user's original requirement that the equivalence be provable in PA. Nor is the modified table covered merely by the already checked252 endpoint. The report explicitly preserves these boundaries (`report.tex:323–339`, `sections/frame_and_calibration.tex:484–509`). The sentence that the requested state target is met is defensible for the numerical target only; it must not become a claim that the original PA goal is complete.

## Exact identity and chronology

Use maintained-source pin `80e26b89e905bf3e5dfc322befdc1c6eaf25a109` for162. The historical161 pin `a3f06a2059dd786ad385079106454efb84b87d3c` remains provenance of recovered working material, not the current reference pin.

- Canonical250 table: SHA256 `0626819c4842f224001e7685366d8061897a7bc9470c015129a1d1cf22efb36e`.
- Original-label250 table: SHA256 `fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43`.
- Input252 table: SHA256 `939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`.

The two delivered table forms are byte-identical between161 and162. The construction removes old states43,59,85, adds255, changes seven surviving rows, and keeps every other surviving row. The count is252−3+1=250, including blank initialization. Canonical start0 and halt250 are distinct; all500 binary transition rows are supplied. The old-label start is97, dispatch96, halt254. This review's JSON pins the actual files read and compares selected reference snapshots directly with Git objects at80e26…; it does not use package checksum manifests as proof evidence.

## Why the new interpreter mechanism works

For `B(v)=0 1^(v+1)` and a marked selected register `B(A)00 1^x B(S)`, the critical contracts are:

1. Positive decrement (`x>0`): entry95 at file origin0 returns48 at0 after `2*width(A)+4` steps, with tape `1 B(Dec(V))`. The file origin moves right one cell; the old origin becomes1. This extra cell is carried explicitly by the symbolic oracle.
2. Zero decrement (`S` nonempty): entry95 returns **112**, head−1, after `2*width(A)+7` steps, restoring the entire plain file. The next valid block's initial01 distinguishes this branch from the blank tail. The112 exit is not interchangeable with the old interpreter's zero return.
3. Increment: entry73 returns48, head−1, after `2*width(V)+7` steps, with `B(Inc(V) ++ [1])`. Appending a value-one spare is intentional.

Nine primary blocks followed by a nonempty finite spare suffix is inductive: increment appends, and every other instruction preserves the suffix. It supplies the zero test at physical register8 for arbitrarily long computations. The spare values may be arbitrary naturals; they are separate from the zero tail of the logical register function.

Intake162's independent macro checker materially improves confidence. Its literal/power rules refuse to inspect opaque exterior contexts. Four one-block results preserve entry state and orientation and have arbitrary untouched contexts; the list rule at `code/check_macro_inductions.py:171` is consequently justified by structural induction. The independently checked word identity `C(A)1=1B(A)` explains the moving prefix. `prove_macros` and nine symbolic marking cases then use those derived results. This is a small trusted mathematical checker, not a Lean kernel. The separate24-row marking footprint plus paper induction also supplies an independent marking route.

## Pulse retiming and finite startup

The two possible right-neighbor bits at75/read0 give exact three-step identities between the auxiliary and final runtimes, in arbitrary exterior tapes. Both end at head x−1, with cells11/state131 or cells01/state112. Outside the internal set{97,255}, the sole entry is75/read0; all other external rows agree. Thus finite blocks of length1 or3 compare entire runs, including halts, not just startup samples (`sections/retiming.tex:63`).

For the final machine, the only incoming edge to97 is255/read0, and the only incoming edge to255 is75/read0. The latter has already written1 at the cell to which97 returns. Therefore97/read0 is used only for the actual blank start; it cannot recur later. This universal graph invariant is what licenses initializer reuse.

The585,431-step supplied startup endpoint is a complete tape claim: state96, head−3, header225, distance228, empty PC, physical primaries `[0,2,0,4,0,0,1,0,0]`, and210 value-one spares. The listed438 one-cells specify both exterior tails. Finite execution must be reproduced separately; the mathematical review checks how this exact endpoint is consumed.

## Full source, full PC, and unbounded simulation

The affine interpreter represents each uniform run by `a*n+c`, with nonnegative coefficients and `n>=0`. Its only unbounded tape steps are direction-matching self-loops, justified by induction on the finite run length. Peeling requires `c>0`; canonicalization only merges equal-bit runs, drops zero-length runs, and absorbs far-left zeros into the blank exterior. The box-boundary fallback reads the guaranteed leading0 and must write0/moveL. Guarded decrement names the same register as the marked box. Single-effect tags prevent a second opaque update.

Intake162 additionally reparses every token of the pinned6459-node source table, checks forward child bounds and unique indegrees, and expands its6460 leaves. The independent full-PC implementation (`code/review_affine_source.py:114–225`) retains all increment and overflow zeros. It targets gap `n+40+positive_dec+overflow-len(successor)`. It covers8391 guards, including both branches of each1931 decrement. Its oracle checks and alternate successor arithmetic are useful additional checks; the literal binary symbolic engine is shared, so this is not an independent second binary semantics implementation.

The whole-frame proof requires **total head-to-header distance** at least40, not merely gap at least40, plus the inherited clean-PC property. Because consumed depth is at most34, `P 0^gap = Q 0^(distance-len(Q))` rebases every legal source onto a covered leaf. `RegisterPath.step` really applies `execute` to the consumed path, matching the checker. A complete target frame, not a numerical visit to state96, determines return. Header distance and spare nonemptiness are preserved.

Every accepted guard has positive literal progress (reported minimum13). The reverse halting direction in162 is correctly proved by strong induction on finite binary halting time: a positive segment ending in an active frame has length strictly smaller than a remaining halting time, by absorption. This avoids any appeal to fairness, an infinite choice of segments, or a uniform runtime bound. Forward simulation is finite concatenation.

## Dirty root and set-coded calibration

The register permutation sends the startup to logical `(N,T,W,A,D,H,X,Y,L)=(1,0,0,0,4,0,0,0,2)`. `T=H=0` and `W=0` supply the formula/stack safety witnesses. `Bisim254.prog254_halts_iff` is universal in the register file, and `DirtyProgram254.path_halts_iff` accepts this safe dirty state. The stronger concrete `six_nonformula_path_iff 1 0 4 0 0 2` also matches. Completeness from the nonzero counter/pointer is inherited from the virtual-state absorption and padded-program cofinality arguments, not inferred from startup or retiming tests.

The162 calibration section identifies the numerical/native/ZF/ZFC refutation interfaces and supplies a sound outline for reading those specific model arguments in ZFC. Crucial distinctions are explicit:

- GIC is indexed by actual first-order formulas, not arbitrary external binary relations.
- Henkin completeness produces set models, without assuming transitivity or external well-foundedness.
- The quotient WF domain uses a first-order **internal** predicate quantifying over represented subsets. The exact definitions in `WellFoundedPart.lean:32–61` match this reading. Closure uses the specific GIC witness formula; it does not infer full Collection from arbitrary ZF without Foundation.
- Internal L is a subset of a set model's domain; its satisfaction is ordinary set-structure satisfaction. The displayed Choice calibration invokes its own ZF/Power/Regularity/V=L results.
- The argument is not a generic translation of universe-polymorphic Lean proofs or their three standard axioms into ZFC.

This removes several plausible semantic confusions and makes the claimed ordinary ZFC proof credible **using the identified inherited mathematical lemmas**. This review has not re-audited or rebuilt the entire inherited model-theory closure. It supplies no internal PA translator and no derivation that ZFC itself is consistent. The report correctly distinguishes nonhalting unprovability under consistency from full two-sided independence requiring an additional soundness assumption.

## Work that would turn this into the requested endpoint

Port the exact250 table, universal marking/three arithmetic contracts, nonempty-spare frame, and positive-decrement boundary cell into the maintained binary framework. Regenerate all site certificates for this table and prove its actual585,431-step complete blank prefix. Compose with the already general dirty-root theorem. Separately finish the ongoing PA internalization of the native/ZF/ZFC proof comparison. The arithmetic simulation lemmas use ordinary finite induction; reducing the metatheoretic strength of the calibration is a separate substantive obligation.

No concrete fatal defect was identified within this review's scope. The review result is **credible250 construction; improved ordinary proof; exact-table kernel and PA endpoints still open**.
