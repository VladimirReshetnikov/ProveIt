# Slim model-natural divisibility reflection: source-only proposal

The natural-79 endpoint's zero-w divisibility client imports
`DiophantineConsistency.BFS943.Direct80NaturalProjection` solely for its
generic `TenPositive80NaturalProjection.natural_dvd_of_signed` theorem. The
[bounded natural-79 provider cut](../ordinary14-natural79-qualified-provider-cut/README.md)
shows that this one import brings an extensive 10-input BFS943 graph chain into
the selected-P72 **lexical** source boundary. This packet proposes an isolated
alternative to that import. It has not been checked by Lean.

`NaturalDvdReflectionSlim.lean` copies the generic theorem **byte-for-byte**
from `Lean/DiophantineConsistency/BFS943/Direct80NaturalProjection.lean`
(the project source retains attribution), with a new namespace and just two
explicit direct imports:

```
import DiophantineConsistency.ModelDifferenceRing
import Mathlib.Tactic.Ring
```

The copied statement concerns any `IΣ₁` arithmetic model: a divisor relation
between embedded natural-model values in `DiffRing V` implies the corresponding
natural-model relation. Its written proof takes either sign of the difference
ring witness. These imports are a proposed small source interface, **not** a
claim that Lean has checked them or that they are provably minimal. Instances,
notation, `nonneg_or_nonpos`, `ι_eq_neg_ι`, rewrite/tactic resolution, axiom
closure and the exact dependency environment remain to be checked.
An [independent review](../../reviews/ordinary14-natural79-dvd-reflection-slim-independent/README.md)
also identifies a likely missing direct Foundation model import. A separate
[inert repair](../ordinary14-natural79-slim-reflection-import-repair/README.md)
proposes that import; its dependency cut must be rechecked before selection.

`Natural79ZeroWDivisibility.lean.src` is an **inert alternative** snapshot of
the original client. It changes only its direct import and the corresponding
single qualified theorem reference to the new helper. The original Lean source,
prior natural-79 overlay and all existing receipts remain unchanged. The new
helper is a source draft, not a selected build artifact. Its `#print axioms`
command has not run.

The deterministic checker pins the original theorem, both new source files,
current 79 overlay and the 79/80 provider cuts. It checks byte-for-byte identity
of the copied theorem body and the exact two client replacements. It then
**projects** a source-level qualified-import cut using that alternative client
and the helper's two simple headers. At this point in time, the selected-P72
lexical cut has **five** missing qualified project source candidates rather
than 44, **41** project frontier objects rather than 46, and five guarded
package Mathlib names; all five source candidates are also in the prior
natural-80 cut. The 39 eliminated project source names are listed in the
receipt, with no claim that those names or providers are globally unnecessary.
The helper adds one bare draft module to the 195-module overlay; this projection
does not materialize or validate a combined overlay, derive an ordered build,
scan future output collisions, or run Lean. `ReducedNormSigned` remains an
additional frontier source/object relative to the natural-80 cut.

The source and object paths and hashes are point-in-time observations, not
producer authentication or complete compiled-import, companion, transitive,
runtime or toolchain closure. A future combined snapshot must independently
review both changes and its exact imports, authenticate all providers and
companions, satisfy resource/exclusive-slot safeguards and output-collision
checks, then elaborate and audit its theorem axioms. Nothing here establishes
an iPRA derivation or binds symbolic coefficients to external bytes or the
separate Carrier65 PDF.

Run from the repository root while the retained P72/package roots exist:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-dvd-reflection-slim-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-dvd-reflection-slim-draft/result.json
```
