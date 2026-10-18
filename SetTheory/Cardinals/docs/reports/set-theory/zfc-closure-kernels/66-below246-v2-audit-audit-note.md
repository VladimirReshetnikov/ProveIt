# Independent audit of the inherited 246-state proof

Audit date: 18 October 2026 (UTC). This note records a source review and fresh computational checks. It does not report a local Lean or Rocq rebuild. The audit found no mathematical gap in the reviewed register-induction, instruction-coverage, complete-frame, or dirty-root arguments. The remaining formalization boundary is real: the exact 246-state table is supported by an ordinary mathematical proof and executable certificates, while its own closed proof-assistant endpoint and a serialized PA derivation are not supplied.

## 1. Sources and their identity

The audited incoming package is `zfc-context246`, recovered from ProveIt's `docs/incoming`. Its original-label table has SHA-256 `303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`; its canonical table has SHA-256 `89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc`. Canonical labels are start 0, 246 working states, and separate halt 246. Original labels are start 95, dispatcher 96, and halt 254.

The package pins ProveIt to `e0b512a63e2c1ca6a1698fa437b8568f1643ff6b`. Six critical inherited files were independently fetched through the GitHub connector at the current inspected revision `8cdc55ff9281b0aaba49bf74b0b225d57f12b893` and compared byte for byte with the package: `DirtyProgram254.lean`, `DirtyRoot254.lean`, `EnumSafeStart254.lean`, `Code254Proof.lean`, `WFTheory.lean`, and `ChoiceCalibration254.lean`. All six are identical. All 32 files in the package's Lean snapshot manifest also match their declared SHA-256 hashes. The six current comparisons are recorded in `current-source-comparison.json`.

All Lean source paths below are relative to `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/` in [the inspected ProveIt revision](https://github.com/VladimirReshetnikov/ProveIt/tree/8cdc55ff9281b0aaba49bf74b0b225d57f12b893/Computability/BusyBeaver/Lean/BusyBeaver/ZFC). Python and incoming-report paths are relative to the extracted `zfc-context246` package.

## 2. Upstream 254-state verification is substantive

The upstream branch `zf-254` was independently pinned to Jeff Ketchersid's commit `c132d7eae8158cd3a9850ea3eb7251158c3dd821`. All files in `ZF/m254/` were fetched, together with selected calibration files. Every one of the 97 downloaded blobs matched its Git blob hash. The independent local call to `ZF/m254/check.py:check_table` passed, and the script's nested-comment-aware admission scan found no forbidden `Admitted`, `admit`, `Axiom`, or `Parameter` in the m254 sources.

The upstream [push workflow](https://github.com/jeff87654/busy-beaver/actions/runs/38516597751) for that exact commit has a successful `zf-m254` job, number `115696687623`. Its fetched log records compilation of 157 source files, identity of the literal table and machine file, all three end-to-end theorems closed under the global context, and `CHECK PASS`, in 990 seconds. This is observed upstream CI evidence, rather than a local rebuild. `upstream-ci.txt` preserves a short excerpt and the exact identifiers.

The actual endpoints are in [E2E254.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/e2e/E2E254.v), lines 35–46. They identify halting with refutation of the native theory SIR, library ZF, and library ZF plus Choice. The proof connects the literal binary table to the register program, enumerator, numerical calculus, native first-order calculus, and set theory.

One naming qualification should be retained. `ZFc` excludes Foundation, and the theorem named `zf254_halts_iff_ZFC` adds Choice to that theory. This does not weaken the intended consistency calibration: [Z_main.v](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/stdzf_r3/zfc/Z_main.v), lines 83–86, proves `ZFCReg_equicons`, which adds both Regularity and Choice. Thus standard ZFC follows by composing the supplied equivalences. The native axioms are explicitly CP, formula-indexed global-image collection, and irreflexivity; see `ZF/m254/coq/settheory/S_def.v`, lines 10–14 and 26–44. Extensionality is obtained in an interpretation, rather than silently assumed of the raw native relation.

## 3. Universal register operations

The register block is

\[
B(v)=0\,1^{v+1},\qquad C(v)=1\,0\,1^v.
\]

`code/check_macro_inductions.py` was read in full and rerun. Its proof rules have the following ordinary mathematical justification.

* Lines 130–169 execute either one literal transition on a provably present cell, or a unidirectional self-loop across an arbitrary unary run. The latter is induction on the run length, including length zero. A non-loop cannot consume an unknown run unless its constant length is at least one.
* Lines 214–237 check four one-block lemmas with opaque arbitrary left and right contexts: seek at 73, forward carry at 95, return at 48, and rollback at 112. Their endpoints retain the same state and direction and move across exactly one block. Lines 171–193 therefore legitimately extend them to every finite list by structural induction. The checker cannot inspect an opaque context.
* Lines 239–252 justify the word identity `C(A)1 = 1B(A)` by the empty case and one arbitrary cons cell. Reversal supplies the corresponding identity for a leftward scan. Its use in normalization is equality of the whole encoded word, not a tape-erasing abstraction.
* Lines 254–271 compose these lemmas into increment, positive decrement, and zero decrement. Nine separate marking checks follow at lines 274–301.

The nonempty-spare condition is essential and explicitly present. In the zero-decrement proof, lines 264–268 expose a following block `B(y)` with arbitrary natural value `y`. A last primary register has such a successor because the spare suffix is nonempty. Its value need not be zero. Increment appends a spare block of value one; positive decrement preserves the spare list while shifting the file boundary; zero decrement preserves the entire file. Consequently an initially nonempty finite spare suffix remains nonempty indefinitely. It cannot be exhausted, and no bounded-value premise is being smuggled into a universal statement.

The fresh run passed all four one-block lemmas, three full macros, and nine marking cases. Exact traces and affine costs are in `context246-audit-results.json`. This audit reused the supplied induction engine; it is an independent mathematical review and execution of that engine, not an independent implementation of it.

## 4. Symbolic instruction checker

The entire 87-line `sources/prior/prefix_affine.py` was reviewed. Runs denote lengths `a*n+c`, with nonnegative coefficients and `n >= 0`. Peeling requires `c > 0`; whole-run scanning requires a literal self-loop in the scan direction. Removing a zero-length run and recentering the zipper change representation only. Dropping far-left zeros is sound because the represented exterior is an infinite blank half-line.

The register oracle, lines 17–28, is guarded in three significant ways. A decrement must name the marked physical register; an increment/decrement effect cannot be marked again as an unchanged box; and the numerical guard remains attached to that same register. A fallback at the box boundary is permitted only for an actual `0 L` transition, which preserves the compulsory first zero. The `extra=1` case is exactly the positive-decrement boundary shift proved by the macro. Acceptance requires at least one literal transition, independently of scans or macro summaries whose minimum length might otherwise be zero.

`code/review_affine_source.py` was also reviewed and rerun. Its parser consumes the complete literal `Prog254.v` table, rejects unmatched tokens, checks the exact source hashes, requires strictly forward node references and the correct indegrees, and establishes a rooted full binary tree. It independently reconstructs all sites and compares them with the cached list. It independently implements full-width increment and strip operations, retaining overflow zeros and trailing zeros.

The fresh results were:

| Check | Result |
|---|---:|
| Source decoder nodes | 6,459 |
| Distinct source leaves | 6,460 |
| Guarded instruction cases | 8,391 |
| Decrement zero / positive cases | 1,931 / 1,931 |
| Increment / break / continue / halt cases | 2,601 / 128 / 1,799 / 1 |
| Explicit oracle checks | 342 |
| Overflow cases | 3 |
| Minimum counted literal progress per instruction | 13 |

All passed. This establishes a finite family of universally quantified instruction contracts, once the reviewed rule interpretations and macro inductions are supplied. It is stronger than a bounded replay, but remains an ordinary proof with an executable certificate until the checker is imported into a proof-assistant kernel.

## 5. Complete-frame composition

The relevant invariant is the complete tape

\[
0^\infty\,1\,P\,0^{d-|P|}\,1\,B(V(R)S)\,0^\infty,
\qquad d\ge40,
\]

in dispatcher 96, with the head immediately right of the left marker, a nonempty finite spare list `S`, and logical registers above index eight equal to zero. The physical positions of `(N,T,W,A,D,H,X,Y,L)` are `(6,2,0,4,3,7,8,5,1)`.

The clean-path predicate is indispensable: after a decoder leaf consumes `l` bits, all stored bits beyond `l` are zero. `RegisterPathClean.lean` proves the empty base, preservation under a successful logical step, and the whole-word rebasing identity `gap_consume`. Since every leaf depth is at most 34 and `d >= 40`, each reached frame is represented by one of the checked symbolic source sites. An arbitrary bit string that merely fits before the header is insufficient.

The original permutation252 frame adapters have different physical spare effects from prefix246. In particular, old permutation252 positive decrement appends a zero spare. They must not be instantiated unchanged for prefix246. The incoming mathematical proof explicitly replaces those effects with the new macro contracts, preserves a nonempty spare suffix, and uses the unchanged path and register-index lemmas. That adaptation is the correct composition route.

For halting reflection, use strong induction on a binary halting time. A nonterminal source step has a positive finite binary segment ending in an active complete frame. Its length is strictly below the available halting time, since an absorbing halt cannot later become active. The induction hypothesis applies to the remaining time. Complete decoder coverage separately excludes a failed walk masquerading as a halt. The generic argument appears in `RuntimePerm252.lean`, lines 39–48 and 85–123. No infinite choice of segments, uniform clock bound, or fairness principle is needed.

## 6. The dirty root is genuinely within the theorem's scope

Both original and canonical 246 tables were replayed from blank for exactly 410,735 transitions. The independent dense canonical interpreter agreed with the sparse interpreter on the complete one-cell set. The endpoint has original state 96, head −5, marker −6, header 176, empty PC, distance 181, 351 one-cells, and 167 spare blocks all of value one. The logical primary vector is `(3,0,0,0,3,0,0,0,0)`. Results are in `context246-boot-audit.json`.

The exact specialization is `DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0`, at lines 94–99. The formula fields `T`, `W`, and `H` are zero, supplying numerical truth, the empty good stack, and numerical truth. All six other fields are universally quantified. Physical spare values are distinct from the logical zero tail; they are not extra logical registers.

The underlying reasoning was checked in source. `DirtyRoot254.virtual`, `stage_virtual`, and `virtual_formulas` (lines 73–94) make scratch/accumulator fields clean while preserving both the continuation after fetch/read and all formula data. `EnumSafeStart254.complete_from` (lines 109–118) chooses a padded refutation program with code at least the initial candidate counter and proves it is reached unless an earlier candidate already halts. Thus beginning at candidate three does not discard all refutations. `Bisim254.prog254_halts_iff` transfers the literal decoder to the 219-node DAG for every register file, rather than only for the public root with counter two.

## 7. Logical strength and inheritance by a smaller machine

The reviewed finite transition transformations, unary/list inductions, source-path arithmetic, and finite-bootstrap comparisons can be expressed in PA using coded finite words and tapes. A new state reduction that proves the same complete-frame contracts can therefore inherit the machine-to-register halting equivalence by a PA-formalizable argument. A new blank initializer must reach an admitted root, or have its own safe-root proof.

The full PA equivalence with the chosen arithmetic `Con(ZFC)` has a separate outstanding obligation: explicit internal proof-code translations for the set-theoretic consistency calibration. The inherited Lean sources themselves state that PA internalization is not yet claimed. An ambient Lean theorem using its standard axioms, or an axiom-free Rocq theorem, is not by itself a serialized first-order PA derivation.

The ordinary ZFC calibration has a clear mathematical route. Work inside ZFC with set-coded syntax and countable first-order theories. Henkin completeness supplies set models, not transitive models. The native quotient and internally well-founded subdomain are set constructions with explicit first-order interpretation formulas; the internal constructible subdomain of a ZF model is a subset of its set domain. These interpretations, soundness, and completeness yield the native/ZF/ZFC refutation equivalences. `WFTheory.lean`, lines 21–45, and `ChoiceCalibration254.lean`, lines 23–67, expose the corresponding interfaces. The incoming report describes this particular set-coded argument rather than claiming a general translation of Lean's metatheory into ZFC.

Accordingly, a successful new reduction may be presented as an ordinary mathematical proof of the requested ZFC-provable nonhalting/consistency equivalence, with exact computational certificates and the inherited calibration identified. It should not be called a newly kernel-checked exact-table endpoint unless such a build has actually been performed. No inconsistency or external soundness hypothesis is needed to prove the equivalence itself. Two-sided independence requires more care: consistency alone excludes a proof of the nonhalting/consistency side by the second incompleteness theorem, while excluding a proof of a false existential halting assertion generally uses an additional soundness assumption.
