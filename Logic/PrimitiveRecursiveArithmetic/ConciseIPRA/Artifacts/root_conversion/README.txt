ROOT-ONLY COMPUTATION FOR iPRA
=============================
Prepared for Vladimir Reshetnikov, 12 November 2026.

RESULT AND LIMIT

This package gives a seven-rule native presentation of full first-order
intuitionistic primitive recursive arithmetic using counter-aware recursion,
variable-only crossed substitution, and reversible computation at the LEFT
root of an equation. A three-row packet derives unrestricted equality
transport. The report gives the native equivalence, ordinary logical macros,
and whole-domain bi-interpretation with actual equality and identity
numerical comparison maps.

The requested overall simplicity target was NOT achieved. The current
pinned directory, including incoming archives, has a compact coordinate
envelope of 242 significant tokens / 262 AST nodes / 469 normalized bytes,
attained by different programs. The new validated readable checker has
1108 tokens / 1301 AST nodes / 3875 normalized bytes. Its maximum-gzip
size is 1402 bytes (both raw and normalized source here).

This is a proved local computation restriction, not a new smallest
axiomatization. It changes from counter-blind iteration to counter-aware
recursion; it does not settle root-only completeness in the old language.
Reverse root steps remain necessary to the present proof.

CONTENTS

  report.tex / report.pdf       Main paper, including a tree-domain appendix
  code/checker_seven.py         Complete primary checker, seven rules
  code/checker.py               Complete eight-rule control
  code/verify.py                Untrusted proof generator and concrete tests
  code/certificates_seven/      Five generated certificates/examples
  code/certificates/            Corresponding eight-rule examples
  code/proof_notes.txt          Detailed construction and encoding notes
  evidence/                    Metrics, receipts, provenance, written reviews
  reference/                   Selected pinned sources and baseline modules
  reproduce.py                 Nonmutating offline verification
  build_pdf.py                 PDF builder with a private-format fallback
  CLAIMS.json                  Explicit claims, dependencies, and limitations
  MANIFEST.sha256              Complete delivered-file hashes

RUN

  python3 reproduce.py

This verifies the manifest, remeasures the full standalone modules,
rebuilds the certificate suites in a temporary directory, and exercises
public-interface rejection boundaries under normal and optimized Python.
The original package is not changed. It requires only standard-library Python.
Exact metric reproduction uses CPython 3.12.14.

To check one CLOSED certificate directly:

  python3 code/checker_seven.py < code/certificates_seven/nested_conversion.json

The open_transport, zero_witness_transport, and binder_transport files are
open-sequent fixtures, containing a numerical scope and a context. The
verification script checks them through the internal typed interface.
The public CLI only accepts a closed {goal, proof} object.

Rebuild the PDF using an installed TeX distribution:

  python3 build_pdf.py

The builder uses installed TeX files only; its private format/map fallback
does not change global TeX configuration or download packages. It is adapted
from the pinned whole_json_refinement package, with defaults changed to this
report. The original MIT-0 license is retained in reference/.

PROOF AND NOVELTY STATUS

The packet, rule-equivalence, and bi-interpretation metatheorems are written
mathematical proofs. Finite certificate tests do not replace those proofs.
No new Lean/Rocq proof of the checker or metatheorems is claimed. The
inherited Lean development was not rebuilt.

The seven-rule inventory, single witnessed introduction, three-row naming
strategy, and fresh-variable symmetry argument are inherited. The new local
result is the packet using the recursor's old counter to expose every needed
row using ONLY root computation. The novelty claim is relative to the
inspected repository, not a claim of literature-wide priority.

The binary-tree appendix is an alternative bi-interpretation with explicit
nonidentity comparison maps. It has no delivered checker or size advantage
and is not used by the primary result.

PIN

  https://github.com/VladimirReshetnikov/ProveIt
  6874c85a4cea45d881de73620284fcc75d740942
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The census includes integrated sources, 12 incoming ZIPs, and 7 nested ZIPs.
The intentionally unsound 465-byte no_parity diagnostic is excluded.
The primary direct-source baseline modules are copied exactly and hashed.
No repository commit, branch, pull request, or external message was created.
