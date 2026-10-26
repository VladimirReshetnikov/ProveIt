# Trust-preserving simplification and validation review

## Results and limits

The reviewed revision is `60e9c5d620c6c387d932876cfa2d9376f64ea56c` of
VladimirReshetnikov/ProveIt. The source manifest independently records the
retrieved Git blob hashes. The toolchain is Lean **4.32.0**; the manifest pins
Mathlib to **81a5d257c8e410db227a6665ed08f64fea08e997**.

**Actually performed:** read-only lexical analysis of all 546 files under
`Computability/DiophantineConsistency/Lean`; dependency/import inventory;
manual inspection of representative audit/check files and project build
configuration; Python helper unit tests. **Not performed:** Lean elaboration,
Lean kernel replay, a fresh `#print axioms` run, performance benchmarking,
repository generator execution, or dependency/toolchain installation. Neither
`lean` nor `lake` was on PATH; no installed Lean toolchain was found. The bundled source snapshot is focused, not a complete buildable
repository with all imported dependency libraries.

The comment/string-masked source scan found no `sorry`/`admit`/`sorryAx` code
hits, explicit `axiom` declarations, `native_decide`/`decide +native`/`bv_decide`
uses, native reflection symbols, or `unsafe`/`extern`/`implemented_by` hits in
that active source scope. This is a **lexical negative result, not a transitive
axiom certificate**. The parser is deliberately not a Lean parser; macros,
external dependencies, actual elaboration, and resulting theorem types remain
outside its guarantee. In particular, names containing `Native` and prose
about ZFC axioms are not uses of Lean's native evaluator or Lean axiom
commands.

| Source-level measure | Result |
|---|---:|
| Active `.lean` files | 546 |
| Physical lines | 73,971 |
| Nonblank code lines after masking comments/strings | 59,832 |
| Source bytes | 3,293,801 |
| `#print axioms` commands | 2,163 |
| `#guard_msgs` commands | 0 |
| `decide +kernel` occurrences | 525 |
| Check/audit files by path/name | 220 |
| Check/audit physical lines | 7,114 |
| Check/audit `#print axioms` commands | 2,126 |
| Check/audit `example` declarations | 835 |
| Check/audit theorem/lemma declarations | 85 |

The active 546-file scope is distinct from 165 additional archived/inherited
`.lean` files elsewhere in the requested subtree. None of the filename-defined
check/audit modules is imported by another active module. This is a source
import graph fact; it does **not** assert which modules Lake glob expansion
builds. External imports include the `Diophantine`, `BusyBeaver.ZFC`,
`BoundedZFCConsistency`, `FirstOrder`, and Mathlib libraries. Their axiom closures
must be established through the elaborated endpoint proofs, not by extending
the conclusions of this local grep.

## The concrete simplification opportunity

There are **60** files whose non-comment code consists only of imports, open /
namespace commands, and `#print axioms`. Together they occupy **739 physical
lines / 33,098 bytes** and contain **530 print sites**. A declarative manifest
of fully qualified endpoint names, required imports, test group, and expected
axiom policy can replace their hand-maintained scaffolding and generate
sharded probes. This is maintenance simplification, not 739 lines of
mathematical proof eliminated: all 530 checks and their names must remain.
Of the 217 already fully qualified printed names across the current source,
all 217 are distinct; this study does not claim measured duplicate endpoint
checks. Unqualified names must be resolved in their actual namespaces before
centralization; copying bare names into one global file can silently change
resolution or fail.

Do **not** delete all `Checks`/`Audit` files as boilerplate. They contain 835
examples and 85 theorem/lemma declarations. For example:

* `NativeCyclicCarryAudit.lean:34–70` checks wraparound, a reset case, and a
  genuine nonuniqueness example. These protect against incorrect assumptions
  about cyclic carries.
* `CurrentHighDigits2011Checks.lean:10–36` tests boundary cells and the origin
  subtraction. Its `:48–54` check preserves the implication from polynomial
  zero rather than supplying the desired mask property as an assumption.
* `Carrier65Checks.lean:18–49` fixes coordinate slots and negative-tau behavior.

Keep these behavioral/regression assertions even if the mechanical
`#print axioms` suffixes are generated from a manifest. Retain small named audit
shards to preserve fast targeted rebuilds; one giant umbrella test can be slower
and obscure the failure source. The pure wrapper list is in
`pure_print_wrappers.json`.

## Make auditing enforce a policy

`#print axioms` reports transitive dependencies but does not reject unexpected
axioms by itself. Source-level `#guard_msgs` wrappers are absent here. The
pinned repository root has no `.github` entry; the inspected root `scripts/`
contains source counters and a report-consolidation checker, not an axiom gate.
The README supplies reproduction commands and reports the intended three-axiom
policy (`README.md:908–939`). **No failure-producing axiom policy was found in
these inspected committed locations.** This is not evidence that an external
CI or private validation process does not exist.

For each baseline and candidate checkpoint, accept only a subset of
`{propext, Classical.choice, Quot.sound}`. Reject *every other axiom*, rather
than checking only known bad spellings. This covers `sorryAx`, legacy
`Lean.ofReduceBool`, future native-evaluation axiom names, and custom
assumptions. Preserve successful compiler exit status independently of the
log checker. Require every expected endpoint to have a result; an empty log
must not pass. Store source/config hashes and the raw merged stdout/stderr.

`check_axiom_log.py` is a small standard-library implementation of this log
policy. It rejects missing or empty endpoint sets, unknown axioms, incomplete
or malformed axiom reports (including an unmatched second report after a valid
one), compiler errors, and sorry warnings. It accepts wrapped lists and
apostrophes in declaration names. Its result is explicitly `PASS_LOG_ONLY`:
it neither authenticates a log nor proves that a Lean process ran successfully.
`test_tools.py` exercises positive and adversarial cases. `EndpointAudit.lean`
provides 35 selected top-level and local regression targets, all **uncompiled
in this review**; it is not a claim of exhaustive theorem coverage.

For concrete finite certificates, keep proof-producing methods (`rfl`,
`decide`, the existing `decide +kernel`, and proved reflection checkers).
Do not substitute `native_decide` simply to make generated proofs shorter or
faster. This changes the trusted computing base. A generator may remain
untrusted if it emits data and proof terms whose exact assertions Lean checks;
a hash establishes identity of data, not its mathematical correctness.

## Candidate acceptance gates

1. **Scope and provenance:** full checkout at the exact pinned commit, original
   toolchain and lockfile, all dependencies already installed, baseline built.
   Review every external generator before running it. This review ran none.
2. **Statement preservation:** retain public fully qualified names, universe
   parameters, implicit/explicit binders, typeclasses, and exact conclusions.
   No added hypotheses; preserve existing independent parameterization rather
   than specializing to the current literal data. Keep compatibility aliases
   where internal API packaging changes.
3. **Definition preservation:** unchanged displayed theorem text is insufficient
   when its referenced definitions change. Freeze those definitions or prove
   an explicit bridge back to the old semantics. For circuits and certificates,
   verify literal tables, coordinate order, row permutations, source binding,
   positivity domains, index conventions, degree, operation counts and
   reachability independently of source-code size.
4. **Elaboration and consumers:** compile new generic modules first, then
   compatibility modules, all changed modules and reverse dependencies, the
   explicit main library target, and every existing check/audit file. No build
   success is established merely because a proposed helper elaborates.
5. **Trust gate:** new and old endpoint axiom sets are subsets of the three-name
   whitelist. Apply the policy to every newly introduced helper used by the
   public endpoints as well as the endpoints themselves.
6. **Regression examples:** preserve boundary tests, negative examples and
   closed certificate assertions. Intentionally mutate one coefficient or
   index in a disposable test fixture and confirm its certificate is rejected;
   this is a test of checker coverage, not a substitute for a soundness theorem.
7. **Performance and size:** compare clean and incremental runs with fixed Lean,
   Mathlib, machine, parallelism and cache state; retain raw times and maximum
   resident memory. Measure generated bytes separately from handwritten
   maintenance surface; report theorem counts, elaborated expression-node
   counts if available, `.olean` size, and full-suite time. `.olean` file size
   is not proof-term size. A shorter tactic script can create a larger proof or
   worse elaboration. Do not quote unmeasured speedups or post-refactor savings.

The safest rollout is one helper/manifest shard at a time, retaining old named
lemmas as aliases until all consumers and behavioral checks pass. Only then
remove duplicated implementation bodies. Consolidation of audit machinery and
certificate rendering is engineering compression; changing the shared
mathematical invariant or inductive argument is mathematical compression.
Report the two separately.

## Primary references

All repository links below are pinned:

* [Build and policy instructions](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/README.md#L908-L939).
* [Library configuration](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/lakefile.toml#L118-L124).
* [Toolchain pin](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/lean-toolchain).
* [Compiler endpoint audit](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/checks/CompilerAxioms.lean#L1-L85).
* [ZFC endpoint audit](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/checks/ZFCAxioms.lean#L1-L24).
* [Small certificate audit wrapper](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/checks/GapCertificate66.lean#L1-L6).
* [Cyclic carry regression checks](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeCyclicCarryAudit.lean#L34-L78).
* [Current high-digit regression checks](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentHighDigits2011Checks.lean#L10-L59).
* [Lean reference: axiom dependencies](https://lean-lang.org/doc/reference/latest/Axioms/) and
  [Lean reference: decide/native_decide](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/).
  The live manual explains the general trust distinction; the project itself
  remains pinned to 4.32.0. No claim that newer native-axiom spellings match this
  project version is needed by an allowlist that rejects all extra axioms.
