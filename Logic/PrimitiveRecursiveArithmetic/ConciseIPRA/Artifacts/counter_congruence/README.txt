COUNTER CONGRUENCE SUFFICES FOR iPRA
==================================
Prepared for Vladimir Reshetnikov, November 10, 2026.

RESULT AND LIMIT
----------------
Root-left equation replacement plus congruence ONLY in the counter of the
existing successor-seeded recursor derive all numerical congruence and all
object-formula transport. Both computation equations R0 and RS remain
unchanged. The proof of numerical context representation uses cases, not
equation induction. The explicit numerical congruence expansion adds 56
inference nodes to its supplied equality proof, independently of the
template's syntactic depth; term labels and byte sizes still grow.
The complete native calculus is contextually equivalent
to the inherited iPRA presentation, with whole-domain, actual-equality
bi-interpretations and effective consistency reductions explained in full.

THE REQUESTED SIGNIFICANT NEW AXIOMATIZATION IS NOT ESTABLISHED.
The inspected corpus minima are 281 tokens / 315 AST nodes / 685 bytes,
attained by different complete programs. Incidental Python edits improve
them separately to 280 / 314 / 672. These implement the inherited theory;
no single variant is below all three old minima. The readable checker for
the new calculus measures 1617 / 1822 / 6834. Absolute simplestness and a
significant structural checker-size breakthrough are not claimed.

The positive mathematical contribution is fixed-counter equality
completeness using unchanged R0/RS. The numerical construction specializes
an inherited compiler, and the older initializer-position reduction and
compound-transport lifting are explicitly attributed. Novelty is claimed
only relative to the inspected source corpus.

A two-element rule interpretation also proves that deleting root replacement
from the new calculus loses even reflexivity. This concerns that specified
calculus, not every possible changed interpretation.

The report also proves two term-definability obstructions to deleting the
initializer, and documents why naive reversal of the paired binder fails
the intended formula roundtrip. These do not rule out every changed-domain
or relational bi-interpretation.

OPEN FIRST
----------
ipra_counter_congruence.pdf    Compiled complete research report.
ipra_counter_congruence.tex    Standalone TeX source, no local includes.
report.tex                    Modular editable report source.
theory/                       New theorem, obstructions, attributed bridge.
code/checker.py               Complete standalone trusted module.
code/FORMAT.txt               Exact rules, syntax, scope, and proof protocol.
code/producer.py              Untrusted targeted certificate generator.
code/certificates/            24 symbolic positive/negative certificates.
code/independent_audit.py      22 independent rule/binding boundary checks.
ancillary/                   Complete small variants of the old checker, their
                             inherited fixtures, finite tests, and measurements.
experiments/compact/         Nonwinning compact RL/CC attempts, with their
                             validation limits and 52 finite smoke-test runs.
evidence/                    Measurements, audits, source manifests, build log.
reference/corpus/            All nine original current archives, unchanged.
reference/                   Frozen frontier checkers, measurer, historical
                             evidence, inherited source, and upstream license.
CLAIMS.json                   Machine-readable status and verification limits.
MANIFEST.json                 Exact SHA-256/length inventory of all payloads.

REPRODUCE
---------
With Python 3.9 or later, from the extracted directory
(recorded metrics use CPython 3.12.14):

    python3 reproduce.py

This verifies the distributed manifest, regenerates/checks the symbolic
examples under ordinary and optimized Python, runs the independent audit,
remeasures all complete comparison modules with the unchanged source
normalizer, and checks the ancillary implementation variants. Receipts are rewritten, so manifest verification should begin
from a fresh extraction. It does not execute old corpus checker sources.

To repeat the exhaustive frozen archive/source inventory:

    python3 audit_corpus.py

To build the PDF with an installed PDFLaTeX distribution:

    python3 build.py

The standalone TeX file also compiles directly. No network access, shell
escape, external bibliography processor, or proof-search oracle is needed.

VERIFICATION BOUNDARY
---------------------
48 complete CLI runs passed (12 positive and 12 negative cases, twice each).
22 independent boundary checks passed. The ancillary suite passed 434
complete-program runs, 15 guard-deletion controls, and 57 opener situations.
New source uses tagged named input
and capture-avoiding de Bruijn substitution. The producer's auxiliary names
are chosen fresh for the delivered examples; it is not a universal proof
compiler. General compound transport has a written proof, not an implemented
general transformer here. There is no Lean/Rocq verification, external human
peer review, or verified Python runtime. Real resource limits can reject
large valid proofs; mathematical completeness assumes sufficient resources.

PROVENANCE
----------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 2fdcf5bf988bead821c416649f713f98b7ed8776
Current folder: docs/drafts
Nine direct archives; 14 distinct archives including nested historical
sources; 342 Python source occurrences; 164 distinct Python source hashes.
Source retrieval was read-only. No repository changes were made.
The full historical fixed-position proposal was separately checked.
The upstream MIT No Attribution license is included; intellectual
attribution is retained throughout the report and evidence.
