WHAT CAN BE TRANSFERRED FROM GRH-LEAN?
Research review dated 25 November 2026 (Pacific time).

START HERE
==========
Read report.pdf. Editable source is report.tex plus sections/*.tex.

Main finding: the repository exports Dirichlet GRH over Q. It yields
classical consequences for abelian Dedekind zeta functions, Lindelof
bounds, least quadratic nonresidues, primes in progressions, and
RH-equivalent problems. The report extracts reusable quantitative and
analytic interfaces and develops a precise additional research target:
RH for the splitting field of X^3-X-1. An explicit one-sided bound for
principal ideal powers would imply that new target, but the bound is
NOT proved here.

PINNED SOURCE
=============
Repository: https://github.com/lsernau/grh-lean
Commit: 72fead102f663d5c7a407964a13dc0cf9d977207
Lean toolchain: leanprover/lean4:v4.35.0
Mathlib commit: 56a005855ea17e0b0958f73ec801ae140b0a1679

VALIDATION BOUNDARY
===================
Completed locally:
* Source inventory, import graph, lexical watchlist scan.
* Matching all 1,625 source-file hashes in the independent verifier's
  manifest, plus the hash of the complete tracked git archive.
* Matching 23 downloaded verification evidence files against the
  publisher's checksum manifest (a selected subset is packaged).
* Exact integer computations for the cubic example, including all
  168 primes through 1,000 and the first 500 theta/Euler coefficients.
* PDF compilation and visual rendering checks.

Not completed locally:
* A full Lean build or proof replay of the upstream repository.
* Compilation of lean/DirectCorollaries.lean.
* A proof of the new principal-ideal inequality.

Published independent proof-checker results for the matching snapshot
are documented at https://math.mit.edu/~drew/shortgrh/ . Hash agreement
establishes content identity; it is not another proof-checker run.
The report distinguishes these claims throughout.

ARCHIVE LAYOUT
==============
report.pdf                  Complete report.
report.tex, sections/       Complete editable LaTeX source.
lean/DirectCorollaries.lean Four consequence/interface proofs,
                            without placeholders; UNCOMPILED DRAFT.
scripts/static_audit.py     Static inventory and source audit.
scripts/verify_published_hashes.py
                            Offline source/evidence hash comparison.
scripts/build_report.sh    Rebuild the PDF on a normal TeX Live setup.
audit/                     Audit results, inventories and provenance.
evidence/                  Selected published machine-generated logs
                            and SHA-256 manifests.
computation/               Exact standard-library Python experiment,
                            JSON results, and complete CSV tables.
SHA256SUMS                 SHA-256 of all other packaged files.

RECOMPUTE THE EXACT EXPERIMENT
=============================
Run from this directory with Python 3:

  python3 computation/cubic23_exact.py --output-dir recomputed

No external packages or network are required. All comparisons are exact.
The coefficient check is finite, not a proof of an infinite theta
identity or of a zero-location theorem.

REPRODUCE THE SOURCE AUDIT
=========================
  git clone https://github.com/lsernau/grh-lean source
  git -C source checkout 72fead102f663d5c7a407964a13dc0cf9d977207
  python3 scripts/static_audit.py source --out new-audit
  python3 scripts/verify_published_hashes.py source evidence --out new-hash-comparison.json

The static scanner is not a complete Lean parser, a theorem-dependency
tracer, or a proof checker. The evidence directory contains a selected
subset of the downloaded evidence. Reproduced log counts therefore
depend on which published files are present, while all 1,625 source
hashes and the entire git archive are checked.

FORMAL VERIFICATION
===================
Install the pinned Lean toolchain and the dependencies required by the
repository and Comparator. Consult the exact instructions and scripts
at the independent-checker URL above, particularly for sandbox setup,
tool paths, and memory requirements. A compact-edition starting point:

  cd source/grh-compact
  lake exe cache get
  lake build
  lake env lean scripts/PrintAxioms.lean
  ulimit -s unlimited
  lean_bin="$(dirname "$(elan which lean)")"
  PATH="$lean_bin:$PATH" lake comparator --paranoid

Then copy lean/DirectCorollaries.lean from this archive into the edition
root and run:

  lake env lean DirectCorollaries.lean

The draft imports Main and includes four #print axioms commands.
It does not supply a formal Dedekind-zeta factorization.

REBUILD THE REPORT
==================
On a standard TeX Live installation with the listed packages:

  bash scripts/build_report.sh

Packages: fontenc, inputenc, lmodern, amsmath, amssymb, amsthm,
mathtools, geometry, booktabs, longtable, array, enumitem, xcolor,
graphicx, tikz, microtype, fancyhdr, hyperref, bookmark.
No BibTeX/Biber run or external assets are required.

Verify packaged checksums from this directory:

  sha256sum --check SHA256SUMS

INTERPRETATION
==============
The report does not claim a new proof of a further open conjecture,
priority for its extracted lemmas, or independent local kernel replay.
It identifies immediate consequences, proves explanatory reductions,
and specifies the missing arithmetic work for a genuine extension.
