# Rocq proof simplification: concrete findings and a data-tested prototype

Snapshot: ProveIt commit `b6fb232916d008383e7cf2990d68ddb30fded7db`.
Investigation date: 2026-10-21. Historical worktree was not changed.

### Latest-main addendum

A targeted GitHub connector recheck at `e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad` found identical Git blob SHAs for `Cert215Offsets.v`, `Source215.v`, `OffsetBisim230.v`, and `Dense215.v`. Thus none of the proposed changes to those four files had landed by that snapshot. The large certificate response omitted content but returned the exact same blob SHA as the fully inspected baseline. This was not a complete repository diff or rebuild. Details: `latest_status.json`.

The count **4,479** in the Python experiment means **2 outgoing test-branch obligations × 2,239 nonhalt certificate rows + 1 initial branch obligation**, separately in each direction. It is **not** a count of binary certificate tree nodes, even if a separate binary-tree representation happens to have the same number of nodes.

## Executive result

The best immediate Rocq simplification is not another rewrite of the dominated-rho8 proof: that rewrite has already been done. The next large target is the source-equivalence certificate.

1. **All 2,240 entries of `Cert215Offsets.v` have offset zero.** Consequently, this candidate does not need an offset relation between registers. Its certificate fits the existing, simpler `K230P.Bisim230` checker after deleting the zero field. The two checkers have the same path/segment semantics; the ordinary checker compares increment counts directly instead of doing integer-offset arithmetic.
2. **The certificate is 1,499,170 bytes, 82.26% of the complete 42-file K215 extension.** A lossless binary encoding of its paths produces a 178,532-byte Rocq source file, an **88.09% reduction in that certificate**. Holding the other files fixed, this would reduce the extension from 1,822,399 to 501,761 bytes, **72.47% fewer source bytes**. This is a source-size result, not a measured proof-object or compile-time improvement.
3. I validated every packed path/index against the old certificate and independently replayed the ordinary checker in Python: **4,479 branches in each direction passed**. There is one halt row; the largest increment/break/continue segment before a test is five steps. All 2,240 rows are graph-reachable and have distinct paired checkpoints, so trivial dead-entry pruning is not a useful next step.
4. **No Rocq compiler was found in this environment.** `PackedCert215.v`, `Source215Plain.v`, and `PackedCertAudit.v` are uncompiled research prototypes. Their Python/data checks are not a substitute for a kernel check. The existing published proofs remain the only kernel-validated endpoints considered here.

The architecture recommendation is: keep one semantic/calibration development, one generic compiler/runtime simulation, and small candidate-specific checked data. For a new 215/214-state table, prove a local relation to the already verified reference instead of repeating the logic and set-theory argument.

## 1. What is already proved, and what was already simplified

The dense endpoint is only 18 lines, and its proof is already the right shape:

`dense TM halts ↔ sparse TM halts ↔ p215 halts ↔ dagPerm halts ↔ StandardZFC proves contradiction`.

The dense theorem rewrites `dense_sparse_halts_iff` and applies the sparse theorem; the nonhalting theorem follows by rewriting under negation. The source theorem `p215_dagPerm` quantifies over **every natural-valued initial register file**, not merely the boot state. Preserve that useful strength.

Published evidence boundaries:

- The original full 237-source closure (195 reference modules plus 42 K215 modules), four closed endpoint assumption reports, and recursive full endpoint `coqchk` belong to the baseline proof closure reported at commit `613f9cf28ac36eaa929f7ef909b0eb7905facc5d`.
- The later simplification at `65c60db4e43b4e3b472b01fb776a20d0971e41f4` compiled seven changed/dependent modules, reused 230 audited source/object pairs, printed four closed endpoint reports, and recursively checked the **focused `K215F.DomRho8` target**. It did not freshly run the complete endpoint's recursive kernel closure.
- `DomRho8.v` already shrank from **921,691 bytes / 12,897 lines to 23,678 bytes / 1,239 lines** (97.43% fewer bytes). Its proved symbolic interpreter uses 297 shared term entries and 780 instructions derived from 674 retained original certificate nodes. Invalid instructions return truth, and the checked final output must be the exact general rho8 formula. Its untrusted optimizer is not in the trusted proof argument.
- The recorded 8.174s versus 1.432s DomRho8 compile invocations are explicitly not a controlled performance benchmark.

Sources:

- [CorrectDense215.v, lines 1–18](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/CorrectDense215.v#L1-L18)
- [Correct215.v](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Correct215.v)
- [Source215.v, lines 8–14](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Source215.v#L8-L14)
- [Full build README](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/README.md)
- [Simplification evidence README](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/rocq/README.md)
- [Exact earlier/new DomRho8 comparison](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/rocq/comparison.json)
- [Seven-module result and scope](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/rocq/actual/result.json)

## 2. Measured source size and duplication

The 42 files in `coq/215` total **1,822,399 bytes, 10,009 lines, and 656 occurrences of `Proof.`**. The last number counts proof blocks syntactically, not independent theorems or trusted axioms. Exact per-file hashes/counts are in `source_stats.json`.

| File | Bytes | Lines | Proof blocks |
|---|---:|---:|---:|
| Cert215Offsets.v | 1,499,170 | 2,245 | 0 |
| ProgLibPerm.v | 37,951 | 780 | 88 |
| DomRho8.v | 23,678 | 1,239 | 14 |
| CD222.v | 22,865 | 230 | 111 |
| Runtime230Core.v | 19,622 | 450 | 26 |
| DagPerm.v | 16,615 | 495 | 0 |
| L1_CompPerm.v | 15,406 | 351 | 41 |
| Complete222.v | 14,506 | 314 | 29 |
| L2RootPerm.v | 13,059 | 254 | 18 |
| OffsetBisim230.v | 7,886 | 177 | 9 |
| Dense215.v | 6,725 | 155 | 15 |

The literal proof certificate occurs byte-for-byte in both `inputs/215/Cert215Offsets.v` and `coq/215/Cert215Offsets.v`. This duplication serves input/proof-binding auditing, but it need not mean two maintained implementations: retain one generated canonical data artifact and bind the proof instantiation to its exact hash. Git already deduplicates identical blobs internally, so eliminating the second path primarily simplifies packaging, not Git object storage.

There are **seven byte-identical `OffsetBisim230.v` copies** across the 215, 217, 218, 221, 225, 226 and 227 generated directories, plus the template. These should be a shared module rather than separately compiled namespace copies.

More importantly, **13 calculus files in K215 are identical to K217 after replacing only `From K217F Require` with `From K215F Require`**: Codes222, Thm222, CD222, Prop222, G222, L224Def, L224Prop, L224Meta, L224E, Interp222, Sound222, Complete222, ThmDom. Together these are **96,926 bytes and 1,803 lines**. The comparison is recorded in `calculus_duplication.json`. `regenerate215.py` explicitly copies these from the older variant. Sharing them through a stable semantic namespace is lower-risk than rewriting their mathematics.

`ProgLibPerm.v` is derived from the older 218 program library by textual renaming; `L2RootPerm.v` additionally replaces an AX lemma and dispatch/root block. Much of its 780 lines is generic structured semantics, register updates, determinism, sequencing, and loop rules. Separate those generic rules from candidate-specific node addresses.

Sources:

- [Certificate literal](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Cert215Offsets.v)
- [Generator copying the calculus and program library, lines 59–115](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/regenerate215.py#L59-L115)
- [ProgLibPerm.v](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/ProgLibPerm.v)

## 3. Immediate simplification: zero-offset projection and compact paths

### Existing unnecessary generality

`OffsetBisim230` stores `(path1, path2, z, successor_nonzero, successor_zero)`. Its invariant is `R1 i = R2 i + delta z i` over integers, with only register 5 allowed to differ. A tested register must have zero offset. The K215 certificate happens to set every `z` to zero, so this invariant is just register-file equality.

The reference's ordinary `Bisim230` already proves soundness for `(path1, path2, successor_nonzero, successor_zero)`, with identical test/segment structure. Its `cnt_eq` checks equality of increment multiplicities. Dropping `z` therefore removes a 177-line K215 checker fork and an unused mathematical generalization from this candidate's dependency path. Do not remove the offset checker from variants that actually use it.

### Prototype

`prototype.py` reads the exact committed certificate and programs, emits paths as positive binary integers, and reconstructs list paths by a structurally recursive Rocq definition. The encoding preserves length, including leading/trailing zero bits, by using a terminal one bit. It never treats a numeric path as a register-machine code. It uses neither a hash oracle nor a trusted external parser in the proposed final proof.

The generated `Source215Plain.v` simply runs the old verified ordinary checker on the decoded certificate and applies its `check_iff`. The optional `PackedCertAudit.v` checks, by proposed `vm_compute; reflexivity`, that all old offsets are zero and decoding equals the old certificate with offsets erased. That audit need not remain in the production endpoint closure once the change is reviewed. The final existing checker still checks every semantic obligation; an incorrect generator cannot make the kernel accept a false theorem.

Executed validations:

- Original certificate SHA-256: `32197f6f31bd3c7c7bf5fb94af0e721434f1238d64a64a715b8c9d2cbdd4e728`.
- Exactly 2,240 entries parsed; all offsets zero.
- All 4,480 paths and all successor indices round-tripped exactly; 4,332 distinct paths, 276,072 literal path bits, maximum length 176.
- Independent Python implementation of the pinned path/segment semantics passed 4,479 branches in each direction, including the initial branch. There are 2,239 nonhalt rows and one halt row.
- Mutating a path, successor index, or offset was rejected.
- All certificate entries are reachable in the certificate graph. No duplicate paired checkpoints were found.

Not executed: Rocq parsing/typechecking, VM checking inside Rocq, compiled proof-object comparison, or final endpoint `coqchk`. Compiler availability, not a logical failure, is the current blocker. Do not claim the emitted files are formal proof artifacts until those checks run.

Sources:

- [Offset checker, lines 10–73](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/OffsetBisim230.v#L10-L73)
- [Pinned ordinary checker](https://github.com/elliotglazer/k230-rocq/blob/3142e4dd980f0be12f4abb636c4ae2528afc17eb/coq/prog/Bisim230.v)
- [Pinned path semantics](https://github.com/elliotglazer/k230-rocq/blob/3142e4dd980f0be12f4abb636c4ae2528afc17eb/coq/tm/RM.v)

## 4. Remove duplicate verification, not just duplicate text

Both ordinary and offset Rocq `check_iff` currently ask for forward and mirrored checks. A stronger generic theorem can prove that a passing certificate's mirror also passes. The checks are symmetric: paired test registers agree, increment counts agree, and successor paths are swapped. For offsets, negate the offset and use symmetry of the integer equality.

Recommended sequence:

1. Prove ordinary `check_mirror` once by lemmas for `getc`, swapped paths, `cnt_eq`, branch checks, and `forallb` over a mapped list.
2. Define `check_iff_one` from one check and `check_mirror`; keep the old API as a compatibility wrapper if desired.
3. Apply the ordinary version to K215 after the all-zero projection. Only add the more general offset mirror theorem for variants that need it.

This removes one full semantic certificate evaluation rather than merely hiding it behind a tactic. Kernel proof checking of the generic mirror theorem still occurs. Actual speedup must be measured. The Python experiment's short segments suggest that repeated list lookup, tree traversal, and certificate representation can dominate over segment length.

A second, less urgent computational improvement is to move certificate indexing from repeated `nth_error`/`N.to_nat` over lists to a proved array/trie or pre-indexed representation, and memoize site/segment summaries. Prove a refinement theorem to the existing checker; keep the original simple checker as the specification. Do not replace proof-producing computation with an unchecked external `true` result.

The existing offset segment fuel is 1,000; the observed maximum is five non-test steps. Merely lowering fuel is not a soundness problem when the existing theorem permits it, but a useful change requires making the fuel parameter explicit and rebuilding the theorem/check. This is lower priority than eliminating duplicate evaluation and list indexing; it should not be advertised as a measured performance win.

## 5. Replace runtime forks and brittle scripts with small interfaces

### Dense relabelling

`Dense215.v` proves a generic fact for a particular pair of finite deterministic TMs, then repeats it across variants. Its `transition_commutes` proof uses the hard-coded tactic `do 216 (destruct n ...; destruct b; vm_compute; reflexivity)`.

Prove a shared theorem parameterized by a state map and initial configuration mapping. Its inputs should be a finite transition-commutation check, terminal reflection/preservation, and the machine definitions. Instantiate with the dense label list. A finite `forallb` over state/symbol enumeration replaces the numeric destruct tactic. This avoids coupling proof text to the state count.

The existing proof already shows that no inverse-state axiom is needed: it uses progress in the dense machine and simulation in the sparse machine. Preserve that constructive approach instead of introducing an unnecessary global bijection or classical choice. Check the terminal state and both symbols, not only reachable working states.

### Generic runtime/compiler theorem

`regenerate215.py` copies a group of K230 runtime files and edits namespace, transition table, disabled labels, boot trace, source program, register map and depth bound. Several facts are generic and should move to shared modules:

- tape/list zipper operations and correctness of executable stepping;
- binary-recursive trace checking and trailing-blank trimming;
- register-block layout algebra;
- correctness of symbolic site execution;
- the whole-program simulation theorem, parameterized by program well-formedness, a boot specification, register permutation and successful site checks.

A candidate then supplies only its literal dense table, source/DAG data, boot registers and trace/check result, site certificates and renaming map. The existing `Interpreter230Check.all_leaves_check` is already a useful reflection boundary; build on it rather than replacing it with generated hand proofs.

### Structured program library

Separate `ProgLibPerm` into generic `run_det`, register-state model, `sem`, sequencing/loop/closure lemmas, and small node-specific instantiations. The current mutable `Ltac elem ::= ...`, bare numeric node names (`w117`, `pair162`, etc.), fixed expansion fuels, broad `repeat`, and whole-record destructs are maintenance risks when nodes move or register allocation changes. They are not evidence of unsoundness.

Prefer a verified symbolic block evaluator with an explicit specification for arithmetic register effects and side conditions, or a stable library of named macros with a checked address map. Keep the important opacity discipline: pairing/formula constructors are intentionally opaque because numerical formula codes can be enormous. Do not solve this by globally unfolding `P`, `wim`, or full set-theory encodings. `DomRho8` already demonstrates symbolic reflection with a small semantic interface.

Sources:

- [Dense transition identity and tactic, lines 63–76](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Dense215.v#L63-L76)
- [Constructive converse simulation, lines 128–155](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Dense215.v#L128-L155)
- [Runtime generator](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/regenerate215.py)
- [All-leaves checker](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Interpreter230Check.v)
- [Simulation invariant and site composition](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Sim230.v)
- [Binary bootstrap execution and soundness](https://github.com/VladimirReshetnikov/ProveIt/blob/b6fb232916d008383e7cf2990d68ddb30fded7db/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Boot230.v)

## 6. Proof transport for other 215-state candidates and a future 214

There are two useful reference boundaries, and they should not be confused.

**Semantic reference:** `dagPerm` plus `dagPerm_iff_standardZFC`. Preserve the logic/calibration proof once. Program optimizations are certified against the reference at structured control-flow boundaries. Use a compositional library for selector permutation, increment-drain rotation, clean-scratch aliasing, dead branch deletion, and block relocation. The relation must state register equality/permutation/offset and its preconditions explicitly. A local pass needs a context-congruence theorem; test traces alone are not enough.

**Literal TM reference:** the accepted exact dense 215 table. For a nearby alternate table, prove `candidate halts on blank ↔ accepted215 halts on blank` and compose with the existing endpoint. If the tables differ only by state relabelling, a finite transition identity suffices. If they share/merge states or alter the boot sequence, a reachability invariant or macro-step relation is normally needed. The last edge into the halted configuration and initial blank tape must be included.

For stuttering/macro-step transport, require progress: a source transition must take positive target steps or strictly decrease a well-founded rank while stuttering. Otherwise a simulation that permits infinite zero-step stuttering can conceal divergence. A simple transition graph quotient without a tape/reachability invariant is not enough to justify a 214-state fold.

For candidates that differ only at a routine with a clean scratch invariant, prove that routine's contract once and reuse it at every call site. This is potentially much easier than a complete new end-to-end compiler proof, and it offers a fair proof-cost comparison between equal-state candidates: count new semantic invariants and changed blocks, not merely changed rows or certificate bytes.

None of these general transport plans proves a particular alternate candidate correct without its exact transition table and discharged invariants. The prototype here changes proof representation only; it does not construct a smaller TM.

## 7. Suggested implementation/acceptance order

1. Keep the accepted machine/table and theorem statements fixed. Run the optional zero-offset and packed-decoding audits, then the two existing ordinary checks. This is the smallest first change.
2. Rebuild the current endpoint from a clean source closure with the documented Rocq 9.1.0/OCaml 4.14.2/rocq-stdlib 9.0.0 toolchain; print all endpoint assumptions and run recursive full `coqchk`. Bind logs, source hashes, exact imports and table hash. Do not confuse focused or incremental checks with a fresh full check.
3. Add one generic mirror theorem; remove the second certificate computation and compare peak memory, compile time, `.vo` size and kernel time in repeatable serial runs.
4. Share the 13 unchanged calculus files and generic checker modules without changing theorem statements. Then factor the dense-relabel theorem.
5. Only after those low-risk wins, parameterize the runtime/compiler and develop local optimization certificates. This yields the reusable proof path for candidate search.

The endpoint itself is already short. The valuable simplification is a smaller maintained proof dependency graph and compact checked evidence, not golfed endpoint tactics or a weaker correctness claim.

## Local deliverables and reproducibility

- `prototype.py`: standard-library-only lossless codec and independent plain checker.
- `PackedCert215.v`: 178,532-byte packed ordinary certificate (not compiled).
- `Source215Plain.v`: candidate source-equivalence instantiation (not compiled).
- `PackedCertAudit.v`: optional exact old/new decoding and zero-offset audit (not compiled).
- `prototype_result.json`: actual executed data/Python checks and hashes.
- `additional_tests.json`: reachability and negative mutation outcomes.
- `source_stats.json`: exact size/hash/proof-block counts for all 42 source files.
- `calculus_duplication.json`: exact namespace-only comparison for 13 files.
- `snapshot/`: committed source inputs, plus the pinned reference checker and RM semantics used to inspect the prototype.

Reproduce the executed local test with `python3 research_proof_simplification/rocq/prototype.py`. This command deliberately does not claim to run Rocq. No compiler installation, historical worktree modification, commit, push, or remote write was performed.

## Further investigation: canonical CFG and two local commutations

The targeted follow-on analysis found a stronger simplification than certificate packing. The original full ordered primitive CFGs differ, but **only by 256 adjacent independent-increment swaps arising from two shared dagPerm nodes (188 and 190)**. Reversing those two nodes alone produces exact ordered-CFG equality with p215. Alternatively, the original programs already have identical increment-count block normal forms. Their 2,240 old checkpoint rows canonicalize to 1,426 test/halt sites, revealing 814 semantically redundant path representations.

See `CFG_REPORT.md`, `cfg_rewrite_result.json`, `cfg_swap_locations.json`, and `two_node_swap_result.json` for complete counts, two-node edits, operation profiles, proof architecture, and verification limits. These are new Python-validated structural findings, not kernel-validated replacement proofs. The prior report's literal certificate counts and lossless packing experiment remain valid; the CFG route is a stronger proposed follow-on.

### Reproducibility hardening

The Python research checkers now fail closed under `-O`, `-OO`, or a `PYTHONOPTIMIZE` environment variable. A shared import-time guard enforces literal, immutable SHA-256 pins for the three source inputs before parsing, and the Boolean parser rejects non-Boolean tokens explicitly. `test_hardening.py` records isolated negative controls and ordinary reruns in `hardening_receipt.json`; no generated formal `.v` bytes or semantic claims are changed. This hardening does not turn the experiments into kernel proofs.
