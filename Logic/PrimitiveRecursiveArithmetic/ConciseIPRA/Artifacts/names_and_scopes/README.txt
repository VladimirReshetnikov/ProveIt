NAMES, SCOPES, AND A RESTRICTED PRESENTATION OF iPRA
13 November 2026

START HERE

Read ipra_names_and_scopes.pdf. Its LaTeX sources are
ipra_names_and_scopes.tex, implementation_results.tex, and
finite_template_names.tex.

RESULT AND LIMIT

The new mathematical result restricts the deterministic Alias/Back
presentation. Both backward substitution and ordinary alias export act on
equations only. Specialization and introduction select the newest parameter,
or zero in an empty scope. The only extra compound capability required is

    Name(t) = D_{x,y}(I(y,t;u.x)=t).

Equivalently, the sole allowed compound alias export is Name(b) -> Name(t)
under a fresh b=t. A written constructive proof recovers full formula
transport, arbitrary specialization and introduction witnesses, and full
Alias. Thus all open consequences and the existing full first-order iPRA
bi-interpretation are retained.

Equation-only export without that naming capability is incomplete. A
growing-active-domain evaluation refutes Name(1). A stronger nonstandard-cut
argument shows that finitely many parameter-instantiated naming templates,
even including successor, do not replace the full naming scheme.

THE REQUESTED SINGLE CHECKER BELOW THE ENTIRE CURRENT FRONTIER WAS NOT
OBTAINED. No global simplicity, lower-bound, historical-priority, or new
Lean/Rocq formal-verification claim is made. The new calculus has a readable
reference checker, not a compact size record.

SEPARATE EXACT-BINDING CHECKER REFINEMENT

exact_bindings/ refines the existing native scalar calculus, independently
of the naming theorem. Its whole-JSON exact-syntax envelope improves from
321 tokens / 361 AST nodes / 627 normalized bytes to 317 / 358 / 614.
Different programs attain the three minima.

The optional expression-input profile has 324 tokens / 379 AST nodes /
605 normalized bytes, with the inherited restricted-expression reader.
Its parser has a fixed physical nesting limit; it is a distinct input
contract. The preferred whole-JSON byte profile is proper_bytes_tuple.py.

The older compact seeded-sequent controls still reach 238 tokens and
455 normalized bytes, and another compact control reaches 255 AST nodes.
They rely on different public-syntax and sequent-context contracts.

REPRODUCE

Use Python 3.12.14 for exact source-normalization measurements.

    python3 reproduce.py
    python3 reproduce.py --tests

The first verifies every file in MANIFEST.sha256 and independently measures
the complete standalone programs. The second also runs the existing test
suites in temporary copies so the delivered receipts and manifest stay
unchanged. No network access is needed.

    python3 names/names_kernel.py < names/tests/name_one.json
    python3 exact_bindings/proper_bytes_tuple.py < exact_bindings/examples/bytes_induction.json
    python3 build.py

The last command compiles the report with installed TeX and fonts. It has
a private-format fallback for source installations without cached formats.
Rebuilding the PDF updates generated files; verify the original manifest
before rebuilding.

EVIDENCE

The naming compiler passes 19 inherited closed fixtures, two additional
closed translations, a direct naming certificate, and 13 open translations.
There are 60 standalone normal/optimized checker executions, with no
failures. A separate naming/binder audit has 240 terms and 1,440 checks.

The exact-binding refinements pass 750 isolated normal/optimized
executions, with no mismatches. These finite tests support the written
correctness arguments; they do not prove those universal arguments.

CONTENTS

  names/             Proposed restricted kernel, untrusted compiler,
                     liberal source checker, fixtures, tests, and receipts.
  exact_bindings/    Five complete refinements, unchanged matched controls,
                     local proof, fixtures, and 750-run receipt.
  reference/         Pinned article sources and selected frontier controls.
  evidence/          Measurements, independent review, and PDF verification.
  PROVENANCE.json    Snapshot and all ten incoming archive hashes.
  STATUS.json        Exact claim boundaries.
  MANIFEST.sha256    Hashes of delivered files, excluding the manifest itself.

SOURCE SNAPSHOT

https://github.com/VladimirReshetnikov/ProveIt
fc05b10f0e03f22edbfdde9298a29fb2fee5dc59
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The persistent/rank method, diagonal introduction, and whole-domain iPRA
bridge are inherited and credited. The new work is the joint-restriction
boundary, the one-shape naming repair, its compiler, the finite-template
obstruction, and the separately stated local checker refinement.

The ordinary bi-interpretation uses the whole numerical domain, actual
equality, identity comparison graphs, and both formula round trips.
The growing domains used for the negative theorem are not its domains.
The closing repository check observed 0198424b74acc33db20c5180c8019ecd7d14a75a.
That commit files seven of the already included incoming packages; it does not
change the article or README. See evidence/closing_repository_check.json.
No remote repository files were changed.
