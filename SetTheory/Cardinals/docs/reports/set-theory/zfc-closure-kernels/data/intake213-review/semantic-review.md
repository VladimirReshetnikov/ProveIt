# Archives 03 and 05: semantic imports and shared named logic

This is an ordinary source review of the proposals delivered in commit
`4b16429bf6d2557b7b168792efa5f487443d6e77`. It compares them with the maintained
sources captured in `comparison.json` at `d0c2880c48830748e568f2e5fd4912d1f0690f15`.
No delivered program, Lean compiler, Rocq compiler, checksum-manifest validator,
or proof object was executed. Only the adjacent, newly written inert source
reader was run. No repository file was changed by this review.

The best immediate change is archive 03's broader semantic import cut. Archive
05 independently implements a smaller part of the same cut and supplies useful
targeted build records. The two `models_ZF` extractions are alternatives, not
additive improvements. The shared named-logic proposal is mathematically sound
on this reading, but increases total source size; it is a maintenance choice.

## 1. Import separation: useful and compatible with the current proofs

Both packets move the existing theorem `ZFNative.models_ZF` into a small module
importing `InternalOrd`, retaining its namespace and exact theorem body. Archive
03 names that module `ZFModels`; archive 05 calls it `ZFModelSemantics`. The
theorem extracts precisely the six-field `ZFAxioms`, powerset, and Regularity
facts from satisfaction of the explicit `ZFax_s` predicate. It does not depend
on an enumerator, physical machine, or an assumed consistency statement.

The legacy `ZFNative` module imports the new module and retains every other
declaration unchanged. `ConstructibleChoice` needs only this semantic model
view, so its import can be narrowed while the constructibility, Choice
transport, and final refutation equivalence bodies remain identical.

Archive 05 also changes `KQ1ZF`'s import from `WFTheory` to `WFModel`. Archive 03
goes further: it splits all 14 general well-founded-domain declarations into
`WFModelCore`, keeps `quotient_models_ZF` in the old compatibility module, and
imports the core from `KQ1ZF`. The general theorem retains all explicit
hypotheses: ambient `ZFAxioms`, closure of internally well-founded sets under
sets of well-founded members, and exact powersets. It introduces no external
well-foundedness, Foundation, or Choice assumption. Separation and Replacement
still use the actual translated `Form`; the two guarded arguments of
`replacementForm` remain unchanged. The old CPGIC specialization still supplies
those premises in the compatibility wrapper.

The explicit `InductiveAttempts` import in the 03 `KQ1ZF` avoids losing the
infinity lemma that formerly arrived through the larger chain. Finally,
`L2Lib222` uses `Code254` and register-machine semantics, not `Enum254`'s
enumerator. Its sole proposed source edit is `Enum254` → `Code254` in the
import. Its producer has exactly the corresponding one-line substitution.
That generator was read as text, not invoked.

The own source reader established:

- All 15 original `WFModel` declaration statements and bodies partition into
  14 core declarations and one compatibility declaration, with identical
  non-comment tokens.
- Both `models_ZF` extractions and all remaining legacy `ZFNative` declarations
  have identical non-comment tokens to the maintained file.
- The five consumer-file comparisons across the two proposals differ only in
  import lines; all other bytes are exact.
- No cycle or unresolved project import appears in the four-root virtual
  closure census; the sole external boundary is `Init`.

The exact **current source** projection is:

| Overlay, rooted at `KEndpoint215` | Modules | Source bytes | Source lines |
|---|---:|---:|---:|
| Current | 192 | 2,362,942 | 45,135 |
| Archive 05 import cut | 181 | 2,164,432 | 42,002 |
| Archive 03 broader cut | 179 | 2,129,439 | 41,170 |
| Archive 05 named logic only | 193 | 2,364,908 | 45,231 |
| Archive 03 imports + 05 named logic | 180 | 2,131,405 | 41,266 |

Thus the broader cut removes 233,503 source bytes and 13 modules; the smaller
cut removes 198,510 bytes and 11 modules. These are import/source measures,
including comments and literal data, not proof-term size, assumptions, memory,
runtime, or a machine-state reduction. Archive 03's own 180→167 count was
explicitly BusyBeaver-local; the full four-root count above is a new static
projection and must not be confused with a fresh endpoint build.

The broader cut removes 15 old modules and adds `WFModelCore` and `ZFModels`.
Compared with archive 05 it additionally removes `Enum254`, `QuotientZF0`, and
`WFModel` while adding one core. Full added/removed lists and per-module hashes
are in `comparison.json`.

Adoption should select **one** name for the moved model theorem and retain the
legacy facades. Import narrowing can affect tactic, notation, instance, and
simp availability despite unchanged proof text. A source-only review cannot
discharge elaboration. Check the selected cores/consumers, the unchanged
endpoint clients, and the legacy facade clients; regenerate the L2 files with
the maintained producer only after that producer's execution is authorized.
The machine, source tree, and physical-site definitions are untouched.

## 2. NamedDerived: one guarded structural argument, larger source

I read the complete proposed `NamedDerived`, `TarskiDerived`, `KThmK`, and
`NamedDerivedAudit` files. The generic layer takes an arbitrary theorem
predicate on the existing named formulas, the existing classical implication
interface, and exactly four quantifier rules: theorem generalization,
distribution, commutation, and `exists i (all i a) → a`.

The crucial guard is explicit. `Admissible eqAllowed` recurses through the
formula and requires `eqAllowed a b` at an equality atom. The unrestricted
client uses `True`; the restricted `ThmK` client uses `False` and proves
admissibility only from its original `EqFree` hypothesis. No unrestricted
equality-vacuity rule is imported into `ThmK`. Its primitive calculus,
equality helper, `EqFree`, `QF`, and later substitution/alpha-renaming proofs
are unchanged.

The common vacuity induction is sound on this reading. Atomic cases use only
the explicit fresh-label premises. Falsity uses ex falso. For implication,
vacuity of the antecedent produces vacuity of its negation via existential
elimination and double-negation elimination; distribution then supplies the
negative and consequent cases, combined by the classical implication-case
lemma. For a quantified formula, universal monotonicity and the stated
commutation row suffice. Every generalization acts on a theorem of `D`, never
on a temporary deduction hypothesis. `Occurs` is preserved literally; the
proposal does not silently weaken it to another free-variable predicate.

The own token comparison finds all 26 old `TarskiDerived` and 40 old `KThmK`
declaration names retained. Exactly 38 old theorem bodies become generic
transparent aliases (21 + 17); the two vacuity proofs become specializations.
All other old declaration tokens are identical. In particular the three
executable declarations `ThmK`, `EqFree`, and `QF` are exact. The aliases retain
the expected mathematical argument order and predicate specialization on
manual inspection; this review does not pretend to infer Lean types without
elaboration. The supplied typed audit exercises those interfaces but its run
is delivered evidence, not a new run here. Transparency changes from theorem
to `abbrev`, so compatibility should still be checked with actual callers.

The total rises from 21,694 bytes / 503 lines to 23,660 bytes / 599 lines.
The gain is one maintained proof of shared reasoning and a clearly guarded
vacuity theorem, not literal source compression. It stacks logically with the
import cut but adds one module; the module reductions cannot simply be summed.
For the current concise-proof goal, prioritize the import cut and decide
separately whether this abstraction is worth its wrappers and extra source.

## 3. Other reviewed or deferred interfaces

Archive 03's complete `OptionContracts` and `FairSearch` modules were also read.
Their finite option-bind and finite-counter induction arguments are sound.
`Returns none x` permits an actual early halt; it does not itself establish
soundness of a proof enumerator. `visit_or_halt` uses an explicit finite
advance premise, transitivity, and backward propagation of halting. The
concrete fetch/drain, reset, soundness invariant, and cofinal killer candidate
remain required. These standalone lemmas are not an endpoint simplification
until their actual EnumPerm clients are refactored and checked.

Archive 05's report correctly keeps its semantic-site proposal separate:
positive physical progress, the full consumed path, both decrement branches,
arbitrary gaps/registers, and the unproved `PrimitiveContracts` premise are
explicit. The report says its CB1 pilot still needs every intended occurrence's
routing and `leftCheck` guard. Nothing in this semantic/import review discharges
that coverage obligation or retires any of the 4,751 leaves / 6,176 outcomes.
The machine-specific five-file implementation and archive 03's uniform-decoder
proofs are outside this source peer's mathematical scope; their prose was used
only to reconcile boundaries with the current phase-nine work.

The submitted import-cut run is a selected 123-module check, the named-logic
run a selected 16-module check, and the site pilot a separate 27-module overlay.
They are not a combined fresh machine-specific closure. Archive 03 explicitly
labels its broader import patch uncompiled. No new Rocq check is undertaken or
recommended as part of this Lean-only review.

## 4. Provenance and next step

Both packets are pinned to `2ca3a5c16f0876d2cab842056353c03a1ed2f5f0` and retain
their `NOTICE.md`, project license, and inherited K215 provenance. The moved
semantic proofs remain inherited ProveIt work; these packets contribute the
module separation and refactoring, not a new machine or a new consistency
theorem. Original submitted evidence and limitations must remain attributable.

**Recommended next checkpoint:** isolate archive 03's import cut, use one
semantic module name, preserve all legacy declarations, synchronize its single
producer substitution, and compile only the correctly invalidated closure plus
typed endpoint/facade clients. No mathematical defect was found in the reviewed
source. Acceptance remains conditional on those kernel and regeneration checks.

## Historical measurement correction

The first census ran during the root agent's uncommitted merge and saw a transient
15,764-byte upstream `Lukasiewicz`, not the 28,731-byte checked module in
immutable HEAD. Its original records are retained in `history-transient-merge/`.
The post-read gate detected the restoration and prevented a silent final source
claim. This successor reruns only the own inert comparison against the restored
checked source, verifies every captured source against immutable HEAD, and
corrects the absolute totals by +12,967 bytes / +210 lines. The import-module
counts and reduction deltas are unchanged. No compiler ran on that transient
source, and neither proposal is blamed for the measurement correction.
