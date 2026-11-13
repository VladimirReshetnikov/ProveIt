# Standard-theory AQ26 client: single-overlay author replay

**Promoted (3 November 2026).** The Lean files of this directory were copied byte for byte into `Lean/DiophantineConsistency/` and built there against current sources; see the [promotion record](../../reviews/aq22-28-current-source-promotion/README.md). The tree copies are now canonical; the copies here are retained as the audited historical inputs.

The two files in `draft` form a client of the AQ26 native bridge and of
`IPRAStandardTheory`, adapted from the AQ29 client. They compiled in the
[single-overlay author trial](../../reviews/ipra-standard-aq26-combined-author-trial/README.md),
which exited 0; its [independent artifact audit](../../reviews/ipra-standard-aq26-combined-independent-audit/README.md)
also exited 0. The first result is a derivability statement *inside* `standardTheory`:
no zero of the positive-shifted AQ26 literal is equivalent to the negation of
the mapped native refutation predicate. The second identifies that negation
with the Gödel–Gentzen translation of the mapped selected Foundation ZFC
consistency sentence. These are separate statements and do not assert that the
untranslated classical sentence has been derived. The compiled result remains
author-only and historical, with the inherited provenance limits below.

The guarded run started from the independently audited historical AQ29
author provider. In one fresh output and one namespace overlay it compiled
all 24 AQ28 → AQ27 → AQ26 sources, the four standard-presentation sources,
and these two client sources. The single additions manifest pins every source
to the same Git commit and specifies all axiom reports. The runner guarded
its parent and recorded imports before and after the run; separately produced
AQ26 and standard-theory object files were not combined. The final state,
logs, terminal exit and frozen inputs are retained in the trial packet.

This is an author-only historical hybrid result, not a
matched author/peer replay, a statement about the current PDF, or a full audit
of dynamic and transitive package provenance. The independent source-only
AQ29 author/peer replay remains in progress.

`plan.py` checks the tracked source blobs at commit `1eac7a1ac8`, source-line
import order against the pinned parent module list, and 79 declared report
names, and generates `author-additions.json` (SHA-256
`1a04dbd22330a61cb2f134f6875513e9457190fca0da7127f500fe6098db1f8b`). The
production runner's source-manifest verifier also accepted the 30 entries.
For abbreviated source report names, the planner checks only the suffix of the
expected fully qualified name; the actual runner requires the exact names in
Lean's final diagnostic output. These static checks alone do not compile the
client, audit the provider, or certify dependency resolution. The guarded runner must
resolve and protect imports and outputs at execution time.
