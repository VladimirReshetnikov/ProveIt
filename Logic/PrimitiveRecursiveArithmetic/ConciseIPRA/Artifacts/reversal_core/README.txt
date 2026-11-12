A SMALLER CHECKED PRESENTATION OF iPRA
Prepared for Vladimir Reshetnikov, November 11, 2026

START HERE

  ipra_reversal_core.pdf       Complete research report and inherited proofs.
  ipra_reversal_core.tex       Self-contained compilable LaTeX source.
  code/checker_rev_typed.py    Recommended standalone checker.
  code/readable_checker.py     Descriptive standalone expansion of that checker.
  reproduce.py                Portable measurements, checks, and optional PDF build.

RESULT

The native scalar terms and formulas remain unchanged. Replace equality
transport and Q elimination by versions that reverse a root equation in the
conclusion. Restrict equality transport to a source that is not literally
zero. A constant template now gives unrestricted reversal using one fixed
computation equation. A transparent wrapper J(a)=I(0,a;u.0), satisfying
J(a)=a, gives reflexivity, zero joining, transitivity, and full congruence.
The equality normalization uses no arithmetic induction, successor
computation, numerical case analysis, or substitution into derivations.

Both translations preserve every sequent of the current native kernel.
Consequently the existing whole-domain, actual-equality bi-interpretation
with full first-order intuitionistic PRA, and both identity composites,
transfer to this presentation. The report states every primitive rule.

MEASURED SIMPLIFICATION

Recommended full Eq/Q/D checker with exact integer/list validation:
  Old matched typed control     532 tokens / 618 AST / 1365 bytes / gzip9 614
  New shared implementation     450 tokens / 514 AST / 1049 bytes / gzip9 540
  Recommended REV checker       456 tokens / 520 AST / 1055 bytes / gzip9 545

The recommended program is 310 normalized bytes (22.71%) smaller than the
matched old control. The shared syntax validator and neutral-premise choice
produce the savings; reversal itself adds six bytes. The old full typed
control is an explicitly constructed extension of a frozen upstream source.
It is not represented as an upstream-published file.

Under the separate compact/canonical-input convention, scalar-neutral truth
saves one byte: 526 -> 525. In another program it saves one AST node:
283 -> 282. The 259-token frontier is NOT improved. No one program achieves
all minima. The 525-byte compact implementation uses unreversed certificates
for the provably equivalent inherited calculus; the REV compact program is
531 bytes. Global minimality is not claimed.

INPUT CONTRACT

The recommended checker reads a JSON array of instruction packets followed
by a canonical closed Eq/Q/D goal. Instructions are consumed from the right.
Each used packet has four fields. Every JSON value must be an exact integer
or list. An unused well-typed prefix is permitted. Acceptance means exit
status zero and exactly ACCEPT followed by a newline. Exceptions reject.

The raw administrative triple [B0,B1,B2] is read symmetrically as the
conjunction Q(B0) AND Q(B1) AND Q(B2). Canonical Q uses three identical
entries. This explicit administrative interpretation is needed to justify
unconditional root reversal on noncanonical intermediate triples.

The mathematical presentation uses the current Lean kernel's direct QI
progress rule. The compact certificate protocol uses witnessed DI progress.
The report supplies the two short derivations relating those interfaces.

RUN

  python3 reproduce.py
  python3 reproduce.py --pdf
  python3 tools/audit_validators.py
  python3 code/checker_rev_typed.py < tests/certificates/zero_neutral/conditional_zero_symmetry.json

Python checks require only the standard library. Measurement was performed
under CPython 3.12.14. PDF generation needs pdflatex and the ordinary LaTeX
packages declared in the source. For a PDF-only build:

  python3 reproduce.py --pdf-only

VERIFICATION STATUS

The portable package reproduction records 362 REV process expectations,
72 readable-checker expectations, 40 neutral-marker comparisons, and 260500
parser comparisons, all with zero mismatches. The receipts record the exact
packaged program hashes. These finite checks are not
proofs of universal soundness or bi-interpretability. Universal results are
written mathematical proofs. A same-goal zero-symmetry certificate shrinks
from 114 commands / 5435 JSON bytes to 37 / 1259; this is one example,
not a general proof-length bound.

formalization/Reversal.lean is an UNCOMPILED proposed extension. It uses no
proof placeholders or added axioms, but Lean/Lake was unavailable here.
No new machine-checked metatheorem is claimed. To compile it, copy the file
into the pinned repository's configured ConciseIPRA Lean project.

CONTENTS

  code/          Complete candidate programs and the readable expansion.
  controls/      Frozen controls and clearly identified new matched controls.
  tests/         Untrusted producer, named certificates, process harness.
  tools/         Measurement and parser/neutral-marker audits.
  evidence/      Metrics, gzip files, receipts, provenance, written audits.
  theory/        Editable source sections used to assemble the main .tex.
  formalization/ Uncompiled proposed Lean extension.
  reference/     Pinned README, Lean sources, inherited arithmetic proofs,
                 80 primary small checker sources, and the upstream license.

The standalone .tex compiles directly. To regenerate it after editing its
source sections, run python3 tools/assemble_report.py before the PDF build.
MANIFEST.sha256 records the delivered files. Verify it before reproduction,
which rewrites generated receipts and, when requested, the PDF.

BASELINE AND ATTRIBUTION

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 1517d9d79ce33f631e0f82960c849427cbba23bf
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The scalar arithmetic language, conditional binders, intuitionistic logic
macros, predecessor, equality reflection, pairing, primitive-recursion
compiler, and original arity codec are inherited and attributed in the
report. Reused ProveIt code and texts are distributed under MIT-0; see
reference/LICENSE-ProveIt.txt. Exact frozen-file checks are recorded in
evidence/source_inventory.json and evidence/provenance.json.
