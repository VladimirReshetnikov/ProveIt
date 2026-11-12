AN AUDITED 502-BYTE PRESENTATION OF iPRA
Prepared for Vladimir Reshetnikov, 12 November 2026

RESULT AND LIMIT

The observed compact-checker envelope, including the four incoming archives
at the inspected snapshot, is 253 significant Python tokens / 275 AST nodes /
506 normalized UTF-8 bytes. These minima belong to three different programs.
They are empirical records, not a proved lower bound.

This package improves the byte coordinate from 506 to 502. The new complete
program has 269 tokens and 301 AST nodes. A 505-byte companion has 266 tokens
and 301 AST nodes, improving all three coordinates of the byte incumbent.

THE REQUESTED MATHEMATICAL SIMPLIFICATION TARGET IS NOT ACHIEVED. Neither direct program is
below the global token and AST records. No globally simplest axiomatization,
new arithmetic axiom deletion, or new proof-assistant verification is claimed.

A separately reported packed reproduction has 18 tokens / 19 AST nodes /
459 normalized bytes and contains its entire fixed payload. It therefore
beats all three literal source thresholds. However, applying the identical
packing to the old 506-byte incumbent ALSO gives 18 / 19 / 459. The matched
packed comparison is a tie. Both fixed wrappers and byte-identity checks
are included under illustrations/. No mathematical rule is simplified by
this encoding, and it is excluded from the direct-checker frontier above.

The implemented theory is the inherited guarded scalar-iterator presentation
of full first-order intuitionistic primitive recursive arithmetic. The report
states every primitive axiom and rule, the public/auxiliary language boundary,
both interpretations, and their internal composites. Numerical domains remain
whole, equality is actual, and both numerical comparison graphs are x=y.
The new checker refinements preserve this bridge; they do not replace it.

NEW COUNTEREXAMPLE

Deleting the entry goal scan from the 253-token global-floor checker produces
a tempting 250-token program. It is unsound. A supplied 17-packet certificate
proves, in that modified checker, the closed guarded formula

    D_{x,y} ( I(y,0;u.x) = I(y,0;u.Sx) ),

which ordinarily says that some number equals its successor. The public goal
is well formed. A numerical coordinate outside the current proof scope is
silently substituted while checking a major, then interpreted differently
when the caller exports the original raw major. The original checker rejects
the certificate. The 502-byte candidate also rejects it at the first major's
entry scan, before its local-scope convention can differ from the global one.

The deliberately unsound program is under tests/counterexample/ and is only
a negative control. It is not an eligible candidate or a recommended checker.

READING ORDER

1. ipra_502_scope_audit.pdf (compiled paper) and its .tex source.
2. code/checker_readable.py for the expanded, standalone validated interface.
3. code/checker_502.py and code/checker_505.py for the measured compact programs.
4. tests/counterexample/README_scope_counterexample.txt for the negative result.
5. evidence/metrics.json and evidence/validation.json for exact measurements
   and execution receipts.
6. illustrations/README.txt for the packed-source accounting comparison.

REPRODUCTION

    python3 reproduce.py
    python3 build.py

The first command needs only Python's standard library. Exact source metrics
use CPython 3.12.14. The second requires pdfLaTeX and the packages listed in
the TeX preamble. On minimal Debian installations it can create a local format
and font map from installed TeX files; it does not alter the system TeX trees.
Three passes settle references and the longtable layout.

Example compact proof check:

    python3 code/checker_502.py < tests/fixtures/zero__computation_zero_local.json

Use the actual supplied local-scope fixture names. The frozen token control
uses a different, global-scope protocol; do not interchange general proof
files between those protocols.

INPUT CONTRACTS

Compact profiles: exact integer/list JSON trees, a canonical closed guarded
Eq/D public goal, and the documented four-field instruction format. They do
not independently validate the entire public grammar. Exceptions reject;
acceptance requires normal exit and exactly ACCEPT followed by one newline.
Unused prefixes are permitted, as in the predecessor.

Readable profile: additionally validates exact JSON types throughout the
certificate and the closed public grammar. Its FULL standalone size is
605 tokens / 700 AST nodes / 2629 normalized bytes. It is not an uncounted
dependency of either compact candidate.

The compact source imports only json. The census, measurements, proof
generators, reference proofs, and validation utilities are outside the trusted
checking boundary. No proof-producing script is needed to verify a certificate.

VERIFICATION

The delivered reproduction completed 414 checker processes, both ordinary
Python and python -O, with zero unexpected outcomes:

  380 inherited-fixture runs (38 files, five checkers, two execution modes),
   20 exact-JSON-type rejection checks,
   14 scope-counterexample runs (seven programs, two modes).

The 12 canonical positive fixtures were preserved. Among the three compact
byte profiles the sole inherited-suite difference is the documented empty
administrative truth alias. The 250-token negative control accepts the false
certificate in both modes; all six sound comparisons reject it. The generator
reproduces its exact 912 bytes and 17 packets.

Both packed files are additionally checked for exact fixed-loader structure
and byte-for-byte payload identity. The packed candidate is one of the five
programs in the main fixture suite. An earlier independent 152-process
packed-versus-expanded comparison is retained in illustrations/validation.json;
it is separate from the 414-process main reproduction receipt.

The source-corpus audit verifies 1380 Git blobs, 5825 repository paths, and
the classification ledger for 106 smaller utility scripts. It parses those
archived sources without executing them. All 90 package tree hashes match.
Finite tests support the written proofs; they do not themselves establish
universal soundness or bi-interpretability.

PROVENANCE

Repository: VladimirReshetnikov/ProveIt
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Inspected commit: b1b3ae103314a9668b9f87c76594ecfcc5c177e6
Research tree: 76de155aec9da910a74320fd692ed9ed790515c9

The Research tree is identical at the inherited census commit
62396b06020f794fa6dc01b4025a6a5db9d4d28a. All four incoming archives were
also inspected. Exact source identities are in evidence/SOURCE_PROVENANCE.json.

reference/foundations/ contains attributed inherited mathematical proofs.
reference/Lean/ is a set of exact reference excerpts, not a standalone Lean
project. The existing Lean development was not rebuilt here, and it does not
automatically verify these Python programs. The upstream permissive license
is included at reference/LICENSE-upstream.txt.

MANIFEST.sha256 covers the delivered files except itself. The build directory
and transient TeX products are excluded from the archive; build.py recreates
them when necessary. No repository commit or pull request was created.
