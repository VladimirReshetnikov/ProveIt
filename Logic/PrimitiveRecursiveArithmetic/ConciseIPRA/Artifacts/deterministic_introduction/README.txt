DETERMINISTIC INTRODUCTION FOR INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
Research prepared for Vladimir Reshetnikov, November 11, 2026 (Pacific)

START HERE

ipra_deterministic_introduction.pdf  Complete research report.
ipra_deterministic_introduction.tex  Standalone editable LaTeX source.

THE MATHEMATICAL RESULT

In the existing raw guarded Eq/D calculus, the introduction rule no longer
takes a supplied witness term, parameter index, or witness-mode bit. Given
the matrix B and the parent numerical scope, it selects:

  r, if B is literally C(y,0,x)=C(y,0,r), with r outer scoped;
  the newest existing numerical parameter, otherwise;
  zero if that numerical scope is empty.

Here C(y,a,b)=I(y,a;u.b), with u unused in b. The selected witness is
determined before the new step eigenparameter is added. A literal naming
match has priority. All other primitive rules, including full formula
transport, remain explicit.

The paper proves exact equivalence of EVERY OPEN CONSEQUENCE with the
unrestricted guarded calculus. The central structural proof establishes
algebraic cut first, then repairs numerical weakening by induction on the
original derivation height, and only afterwards proves general cut and
unrestricted introduction. It does not assume its own structural theorem.

The identity-language equivalence composes with the pinned guarded/native
and native/iPRA bridges. Both numerical interpretation domains are whole;
equality is actual equality; both numerical composite graphs are x=y; both
formula composites are preserved. Equiconsistency follows as well.

THE SIZE LIMIT MUST NOT BE MISSED

This mathematical rule has a smaller interface, but its complete readable
checker is LARGER than the tightly matched unrestricted-witness control:

                            Bytes       Tokens      AST nodes
  Unrestricted control       3442         1078           1252
  Deterministic Intro        3688         1159           1339

Thus this is not a demonstrated improvement under complete-checker size.
No absolute smallest axiomatization is claimed. It is a proved restriction
of independent witness data, with an honest measured implementation.

SEPARATE IMPLEMENTATION REFINEMENT

implementation/code/native.py implements the EXISTING native calculus,
not the new deterministic-introduction calculus. By sharing its public
grammar check with its first scope traversal, its complete source improves:

  Native control: 780 bytes, 360 tokens, 409 AST nodes.
  Refined native: 656 bytes, 333 tokens, 379 AST nodes.

The full public-goal validation contract is retained, and successful traces
and unused instruction prefixes agree. Earlier packages already proposed
the general traversal-sharing idea; this is a smaller implementation at the
current frontier, not a new mathematical basis.

An explicitly optional compact profile is 506 bytes versus 508. It merely
uses the integer identity ~(-k)=k-1, and adds one AST node. It has no new
mathematics and retains the inherited canonical-public-goal contract without
a separate public-goal validator. Do not attribute either compact size to
the new deterministic rule or conflate these contracts.

REPRODUCTION

From the extracted directory:

  python3 verify_manifest.py
  python3 reproduce.py
  python3 build_report.py
  python3 code/checker.py < code/examples/accepted/arbitrary_witness_translated.json

The last command prints ACCEPT and exits zero. A direct negative example is:

  python3 code/checker.py < code/examples/rejected/naive_scope_weakening_changes_witness.json

The latter prints REJECT with nonzero exit status. All acceptance-critical
checks also run under Python -O and do not depend on assert statements.

Python 3.12.14 reproduces the exact source measurements; only standard-library
modules are used. Building the PDF requires pdfLaTeX and the standard packages
named in the source. The standalone .tex requires no external input files,
images, shell escape, internet access, or bibliography processor.

The modular builder reads preamble.tex, deterministic_introduction.tex,
bridge.tex, implementation.tex, references.tex, and the normalized checker
listing. A rebuild can change PDF metadata or reproduction receipts; the
checksum manifest describes the delivered payload, so verify it first.

VERIFICATION

The new calculus: 10 accepted deterministic certificates, 11 control
certificates, 18 rejected certificates, 78 ordinary/optimized CLI runs,
five binding regressions, ten deterministic-to-control embeddings, one
nontrivial arbitrary-witness translation pair, and a naive numerical
weakening failure with a successful naming repair.

An independent audit adds three positives, three negatives, five direct
binder checks, and 12 CLI runs. It tests formula transport under nested D
binders and hidden eigenparameter escape in unused iterator bodies.

The separate implementation suite checks 20,030 arbitrary JSON initial
scans, 10,000 generated grammar/scope scans, 42 full trace pairs, and 84
paired CLI comparisons (168 actual processes). See the recorded receipts.

These are finite implementation checks. Universal equivalence is established
by the written proofs. There is no new Lean/Rocq verification, and the
upstream Lean project was not rebuilt. The new-to-control certificate
elaborator is complete; the opposite transformation is proved mathematically
and illustrated by an explicit pair, not supplied as a complete compiler.

CONTENTS AND PROVENANCE

  code/             New complete checker, matched control, format, generators,
                    exact examples, normalized sources, executed receipts.
  implementation/   Separate smaller inherited native checker, optional
                    compact profile, frozen controls, proof and reproducer.
  reference/        Exact pinned source fragments for the guarded/native,
                    ordinary, and arithmetic bridges; one Lean interface.
  evidence/         Independent mathematical review and aggregate receipts.
  PROVENANCE.json   Repository commit, source identities, incoming archive hashes.
  CLAIMS.json       Supported results and explicit limits.
  SHA256SUMS        Checksums of all other delivered payload files.

Baseline: VladimirReshetnikov/ProveIt, commit
11814771b7490dfbea0ed5fcf0f5b23586334764,
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA.

The six incoming archives at that commit were included in the comparison.
The naming mechanism and other inherited constructions are attributed in
the report. The scope of the novelty comparison is this repository snapshot;
no literature-wide priority claim is made. The included upstream sources
carry the MIT No Attribution license preserved in LICENSE-ProveIt.txt.

Further research questions appear in the report.
