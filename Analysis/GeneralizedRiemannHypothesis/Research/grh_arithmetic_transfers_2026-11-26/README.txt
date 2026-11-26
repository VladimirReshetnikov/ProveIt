TRACE CONGRUENCES AND ARITHMETIC TRANSFERS FROM GRH-LEAN
Prepared for Vladimir Reshetnikov, 26 November 2026

START HERE
  report.pdf             Complete mathematical report.
  report.tex             Main LaTeX file.
  sections/              All included TeX sections.
  references.tex         Pinned sources and primary literature.

MAIN RESULTS
  Under full integral matrix span, finite-level intertwiner modules
  are cyclic and their exact length is the trace-congruence depth.
  This removes the rank factor in the upstream scalar bound for the
  global conjugate-dual congruence term.

  The report evaluates that term for every Tate twist of Ramanujan's
  representation over Q(sqrt(-23)), outside the six classical
  exceptional coefficient primes. It gives an exact bad-prime
  counterexample, finite trace tests, a global trace-ideal budget,
  and a rank-two Euler-factor bridge.

  Appendix A independently revalidates an inherited density-gap
  theorem. It is attributed to the supplied earlier report.

STATUS
  The mathematical proofs are in the report. Classical ingredients
  are attributed; no worldwide novelty claim is made.
  Python checks are exact finite certificates, not formal proofs
  of all universal statements or Galois realizations.
  No full new Lean build or kernel replay was run for this package.
  Nonabelian RH, BSD, Bloch--Kato and new K-group vanishing are not
  claimed. Each missing arithmetic hypothesis is stated.

SOURCE PINS
  lsernau/grh-lean:
    72fead102f663d5c7a407964a13dc0cf9d977207
  VladimirReshetnikov/ProveIt:
    5cc267af75a635199ac5d93a7d49cbce521daefc

BUILD THE PDF
  On a normal TeX Live installation with standard LaTeX packages:
    pdflatex -halt-on-error report.tex
    pdflatex -halt-on-error report.tex
  The report uses article, Latin Modern, AMS math, geometry, booktabs,
  tabularx, longtable, microtype, fancyhdr, enumitem and hyperref.
  No BibTeX run or external graphics are required.

REPRODUCE THE FINITE CERTIFICATES
  Python 3.10 or later is required. Two checkers use SymPy
  (tested with SymPy 1.14.0); the others use only the standard library.
    python3 checks/run_checks.py
  To replay the two original, larger density computations as well:
    python3 checks/run_checks.py --replay-inherited
  Certificates are written into certificates/.

REPRODUCE THE STATIC UPSTREAM AUDIT
  Obtain a complete checkout of the pinned upstream commit, then run:
    python3 checks/upstream_audit.py /absolute/path/to/grh-lean
  Or add --upstream /absolute/path/to/grh-lean to checks/run_checks.py.
  The scan is not a substitute for compilation or an axiom/kernel audit.

UPSTREAM FORMAL REPLAY
  Follow the pinned upstream README, using its specified Lean 4.35.0
  and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
  Inside grh/ or grh-compact/:
    lake exe cache get
    lake build
    lake env lean scripts/PrintAxioms.lean
  These commands are instructions for reproducing upstream, not a
  record that this package ran them.

EVIDENCE
  evidence/prior_audit_ledger.csv and .json:
    All 46 earlier packages, exact hashes and actual review depth.
  evidence/prior_archive_identity.json:
    Downloaded archive identities checked against Git blob hashes.
  evidence/source_map.json:
    Selected upstream source paths, URLs and SHA-256 hashes.
  evidence/upstream/:
    Unmodified selected upstream evidence, with licenses and
    attribution. This is not a standalone build of the whole project.
  evidence/prior_density/:
    Unmodified inherited proof sections and original checkers, with
    a provenance note. Their work is not claimed as new authorship.
  notes/:
    Detailed source analysis, audit notes and mathematical review.
  MANIFEST.sha256:
    SHA-256 hashes of the files in the final package.

INTERPRETING RESULTS
  Raw congruence lengths use v_pi(pi)=1.
  For a ramified coefficient ring with e=v_pi(ell), the source's
  normalized length is raw length divided by e.
  A finite arbitrary list of Frobenius traces gives upper bounds.
  Exact finite certification needs a valid lower-bound certificate
  or generation of the group/joint representation image.

THIRD-PARTY SOURCE
  Selected grh-lean files are Apache 2.0, copyright 2026 Anthropic,
  PBC; accompanying license, notices and attribution are retained.
  Prior ProveIt material is included only with explicit provenance.
