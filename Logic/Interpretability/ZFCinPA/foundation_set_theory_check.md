# Checked Foundation set-theory dependencies

The validator translation imports Foundation's Zermelo development. Its
missing dependency branch now has fresh checks, using the repository's
pinned Foundation source at `32e1a0956a8622fad067328ca1959729a7634428`.
These are model-relative library results; they do not assert existence of a
model of Zermelo set theory or establish the final PA consistency theorem.

| Module | Fresh result | Probes / typed callers | Warnings |
| --- | --- | --- | --- |
| `Foundation.FirstOrder.SetTheory.Basic.Model` | [PASS](results/foundation-set-model-verification.json) | 5 / 5 | 0 |
| `Foundation.FirstOrder.SetTheory.Basic` | [PASS](results/foundation-set-basic-verification.json) | 2 / 2 | 0 |
| `Foundation.Vorspiel.ExistsUnique` | [PASS](results/foundation-exists-unique-verification.json) | 5 / 5 | 1 |
| `Foundation.FirstOrder.SetTheory.Z` | [PASS](results/foundation-set-z-verification.json) | 12 / 12 | 0 |

`Basic.Model` supplies subset, empty/nonempty, successor-formula and submodel
interfaces for arbitrary set structures. Its unchanged source and audit took
2.876 and 1.456 seconds, using default proof limits, one thread, 4,096 MiB
and a shared 120-second deadline. All probes report only standard Lean axioms.
All 45 recorded inputs and the four newly generated module artifacts were
unchanged after the audit.

The exact previously checked `Basic.Misc` and `Basic.Axioms` source/object
pairs are reused. Their original check had older execution and capture
conventions, which the new record discloses. Current hashes of their module
companions are captured without attributing those captures to the old run.
CounterModel and Mathlib Cardinal.Basic remain explicit cached boundaries;
this is not a fresh verification of the complete Foundation or Mathlib cache.

The initial attempt failed during import resolution: Lean selected the first
Foundation namespace root and could not find CounterModel there. The repaired
guard mirrors existing cached Foundation branches into the scratch namespace,
reserving the exact reused modules and the new output. It records and checks
all 57 mirror links. No source, theorem, audit or proof limit changed.
The [publication](results/foundation-set-model-publication.json) and
[history](foundation-set-theory/model/history.json.gz) retain the original
failure, both prepared layouts, successful run, exact source snapshots and
dependency route.
The [independent review](foundation-set-theory/model/peer-review.json)
checks the repaired layout and actual result; its
[history](foundation-set-theory/model/peer-history.json.gz) also retains the
original finding and reviewer correction.

The five-line `Basic` public-import aggregator also passes, using the actual
Model result and the same explicit cached boundaries. Its two callers check
the inherited theory-inclusion and subset APIs; no new theorem body is
attributed to the aggregator. Source and audit took 1.101 and 1.376 seconds
under the same limits, with 61 recorded inputs unchanged. Its
[publication](results/foundation-set-basic-publication.json) and
[history](foundation-set-theory/basic/history.json.gz) preserve that check.

`ExistsUnique` now has a fresh check of its unique-choice and conditional
choice interfaces over arbitrary sorts. Source and audit took 0.673 and
0.721 seconds, with all 26 recorded inputs unchanged. The source's existing
deprecated `Mathlib.Logic.IsEmpty` import emits one warning, preserved in
the [publication](results/foundation-exists-unique-publication.json) and
[history](foundation-set-theory/exists-unique/history.json.gz). IsEmpty is
an explicit cached boundary. The old cached ExistsUnique object is recorded
as historical data and excluded from the new output location.

The unchanged 763-line `Z` module also passes. Its audit checks extensionality,
empty set, pairing, union, power set, definable Separation, internal omega
and its definable-predicate induction, successor, and Foundation. In
particular, `separation_exists_eval` supplies the interface consumed by
Translation. These theorems retain the nonempty set-structure and Zermelo
model assumptions. Internal omega is not identified with the external
natural numbers.

Source and audit took 21.184 and 1.510 seconds under the same default limits.
The guard combines actual Basic and ExistsUnique results: five selected
fresh prerequisite modules, three explicit cached boundaries and Init.
All 102 recorded inputs, four fresh module artifacts and 193 namespace
links remain unchanged. The [publication](results/foundation-set-z-publication.json)
and [history](foundation-set-theory/z/history.json.gz) preserve the exact
check. This closes the missing Foundation Z branch. The subsequent
[Translation check](translation_check.md) now combines it with the checked
bounded-consistency development.
An [independent guard and API review](foundation-set-theory/z/peer-review.json)
confirms the exact parents, namespace layout, artifact captures and limits.
Its [history](foundation-set-theory/z/peer-history.json.gz) retains a
corrected reviewer metadata check. This review runs no proof checker and
does not add a full independent mathematical review of the Z source.
The [route archive](foundation-set-theory/route-publication.json) preserves
the dependency inventory, source reviews and authoring scripts separately
from the actual proof results.
