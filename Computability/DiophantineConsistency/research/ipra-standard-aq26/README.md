# Standard-theory AQ26 client: proposed single-overlay replay

The two files in `draft` are an uncompiled client of the AQ26 native bridge
and of `IPRAStandardTheory`. They adapt the AQ29 client mechanically. The
intended first result is a derivability statement *inside* `standardTheory`:
no zero of the positive-shifted AQ26 literal is equivalent to the negation of
the mapped native refutation predicate. The second identifies that negation
with the Gödel–Gentzen translation of the mapped selected Foundation ZFC
consistency sentence. These are separate statements and do not assert that the
untranslated classical sentence has been derived. No correctness claim follows
from this source preparation alone.

The proposed guarded run starts from the independently audited historical AQ29
author provider. In one fresh output and one namespace overlay it must compile
all 24 AQ28 → AQ27 → AQ26 sources, the four standard-presentation sources,
and these two client sources. The single additions manifest pins every source
to the same Git commit and specifies all axiom reports. The runner must guard
its parent and all imports before and after the run; separately produced AQ26
and standard-theory object files are not combined. Retain the final state,
logs, exact terminal exit and frozen inputs and arrange an independent audit.

Even a successful run would be an author-only historical hybrid result, not a
matched author/peer replay, a statement about the current PDF, or a full audit
of dynamic and transitive package provenance. The independent source-only
AQ29 author/peer replay and AQ26 v2 final checks should be left undisturbed.

`plan.py` checks the tracked source blobs at commit `1eac7a1ac8`, source-line
import order against the pinned parent module list, and 79 declared report
names, and generates `author-additions.json` (SHA-256
`1a04dbd22330a61cb2f134f6875513e9457190fca0da7127f500fe6098db1f8b`). The
production runner's source-manifest verifier also accepted the 30 entries.
For abbreviated source report names, the planner checks only the suffix of the
expected fully qualified name; the actual runner requires the exact names in
Lean's final diagnostic output. These static checks do not compile the client,
audit the provider, or certify dependency resolution. The guarded runner must
resolve and protect imports and outputs at execution time.
