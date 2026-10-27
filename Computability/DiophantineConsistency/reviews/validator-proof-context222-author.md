# Actual C222 internal contexts: author checkpoint

Author: `/root/circuit_reduction`. Status: the two new leaves are frozen and
freshly checked; independent acceptance is separate. No existing proof source,
shared documentation, Git state, or accepted dependency object was modified.

The final source is `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorProofContext222.lean`
(387 lines), SHA256 `591495f9085abdd82f5428172310d12185f57ac8585abf7b7a30c210fcba267c`.
Its focused checks are `ValidatorProofContext222Checks.lean` in the same folder
(87 lines), SHA256 `5d2d03286b440d8c4ac0044a94fca36776b6a93e8bfbadcbe83ddb671c771b07`.

## Mathematical scope

Every statement is over an arbitrary `ORingStructure V` satisfying internal
`IΣ1`. Contexts, list lengths, lookup indices, source formulas and finite-set
codes are elements of `V`; they are not restricted to standard natural numbers
or externally finite Lean lists. The fixed finite propositional certificates
use `Kalmar.Der` with Lean lists, but their soundness uses the actual C222
`cProv_classical` theorem. All unbounded context lengths use the existing
internal Σ₁ vector-induction principle.

The module defines `imps`, `Der`, `negEnc`, `seqC`, `shiftList`, and `Enum`.
It supplies fixed Σ₁ graphs for all six, correctness of those graphs, and
the explicit identity
`Der G g ↔ ∃ d, ArithmeticHistory222.value d = imps G g + 1`.
Thus the context rules preserve actual internal C222 proof witnesses.
The public rules cover theorem lifting, modus ponens, hypotheses at every
internal index, deduction and undeduction, context subsumption, contradiction,
negated-encoding and shifted-list lookups, free-environment tailing, and
enumeration existence. `seqC_enum_iff` removes dependence on enumeration
order or duplicates using the proved subsumption rule.

`enumDef` exposes a numeric `y < s` guard before HFS membership. Its equivalence
to the unrestricted membership condition uses the actual `lt_of_mem` theorem,
not an additional boundedness premise. The source shift theorem retains its
explicit assumption that every listed source code is a well-formed formula.

The only import is `ZFCinPA.ValidatorFormulaEncoder222`. Its syntax-only
EnvironmentLabels254 dependencies are reused; its equality atoms use the
actual C222 `Eind` encoder. The fully read `R2Ctx.lean` supplied the context-list
proof structure as an adaptation guide, but neither it nor CProv254 is imported.
No primitive-equality/vacuity equivalence, arbitrary source axiom image,
source-proof interpretation, tagged seed interpretation, closed ZF-to-C222
reduction, or new HA equivalence is asserted.

Focused checks cover an actual history witness at an arbitrary internal
index, empty context, duplicate contraction, exchange, both directions of
deduction, cut, contradiction, encoded lookup, nested universal/existential
source shifting, empty sequent, and enumeration independence. The false
singleton check proves equivalence with `CProv 1`; it does not assert a
refutation exists.

## Authenticated execution

The minimal current-source import closure was traversed and authenticated
before any compilation. Its frozen inventory is
`reviews/validator-proof-context222-cache.json`, SHA256
`1291c1b923dd64dcebcb323cec22cde4d5afb437d830f9b315ee2792c15b4dd4`:
152 cached modules, including 117 Foundation modules, 503 cached artifacts,
and 39 explicit toolchain/package boundaries including implicit `Init`.
The accepted independent root-fresh Instances, FormulaEncoder254,
EnvironmentLabels254, and FormulaEncoder222 objects were selected. All
current sources, imports, selected artifacts and external boundary objects
were rehashed; inherited Lake/historical provenance remains in the records.
This was authenticated reuse, not a fresh replay of those dependencies.

Only the new main and checks were compiled in
`/tmp/validator-proof-context222-author-b4vpgdet/lib`, using Lean 4.32.0,
`-M6000 -j1 -DElab.async=false`, `LEAN_NUM_THREADS=1`, no `LEAN_SRC_PATH`,
regular non-symlink output files, and a 512 MiB free-space guard. The complete
new sources and drivers were read before execution, and the final full pair
was reread after execution. No Foundation or prerequisite build occurred.

The final runs passed in 23.903 and 2.359 seconds. The main log is empty;
the checks contain exactly 16 axiom reports, all restricted to `propext`,
`Classical.choice`, and `Quot.sound`. Final objects:

- main: `648b8a6bf9dd8090f9f51afc0004dc9cb336fb13c89da4db89a47dfea5dc0ee3`;
- checks: `22f6c1edad75a842137a7adea27fdb06781a62f3060cf8f8398d72ec24dbc49d`.

The final attempt records 2,105 pre/post pin observations. Replay summary:
`reviews/validator-proof-context222-replay.json`, SHA256
`0c0a194536c1d10633838ee69c258d5eef0dfb5105bea5ffb0b03f55103ff65c`.
The 37-file author evidence manifest is
`reviews/validator-proof-context222-author-replay/FILES.json`, SHA256
`05fd1e45be667513f61fd6b66fc67805eec7fa54df25cede0882c1aacf6de5db`.

## Development record

An unexecuted first check mistakenly requested an unconditional proof for a
false singleton sequent. Full source review caught it before the compiler was
run; the original draft is retained, and the check was corrected to the exact
equivalence with C222 refutability. The first main execution then failed only
because the new explicit Enum graph used a set-bounded quotation for which the
syntactic hierarchy tactic did not establish Σ₁. The explicit numeric guard
above repaired that graph without changing the mathematical predicate.
The second pair passed, with one unused-binder warning. Renaming that unused
binder yielded the final clean pair. Every source/driver snapshot, plan, log,
timing, pin record, and prior successful object is preserved in the bundle.
