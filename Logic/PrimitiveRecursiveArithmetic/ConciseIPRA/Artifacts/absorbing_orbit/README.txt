ABSORBING ORBITS IN A CONCISE PRESENTATION OF iPRA
51-node predecessor; 632-byte fully validated native checker
Prepared for Vladimir Reshetnikov, 12 November 2026
==========================================================

RESULT AND LIMIT

This package proves two reductions relative to ProveIt commit
e85c5e24dba535a296c46cd18fa66a146ce36b8e, including all ten incoming ZIPs.

1. A scalar predecessor shrinks from 57 to 51 fully expanded constructor
   occurrences, a 10.53% reduction. Its equations are proved internally
   using only computation, equality, and induction on literal equations.
   No primitive symbol or logical/arithmetic axiom is added or removed.

2. The fully input-validated native checker shrinks from 637 to 632
   normalized Python bytes, from 344 to 343 significant tokens, and from
   392 to 390 AST nodes. A direct proof establishes identical acceptance
   on arbitrary parsed JSON inputs. Tests cover 106 fixtures, both
   programs, and ordinary/-O execution: 424 isolated runs, zero failures.

The user's stronger target is NOT established: the separate compact
records remain (244 tokens, 267 AST nodes, 479 bytes), attained by distinct
programs under weaker input contracts. No globally simplest axiomatization,
new primitive axiom deletion, or proof of a universal complexity lower
bound is claimed. The new strict envelope is (334,387,632), again attained
by different programs; only the strict byte coordinate is a new record.

The ordinary realization remains bi-interpretable and equiconsistent with
full first-order intuitionistic primitive recursive arithmetic. Both
numerical domains are whole, equality is actual, and both comparison
graphs are x=y. The paper states all native schemas and inference rules,
proves the new term, and includes the attributed inherited bridge.

START HERE

ipra_absorbing_orbit.pdf
    Complete compiled report, new proofs and attributed foundations.

ipra_absorbing_orbit.tex
    Flattened standalone LaTeX source, including the checker listing.
    Modular editorial sources are in paper/ and reference/.

checker/checkers/strict632.py
    Complete recommended checker for arbitrary JSON input. It imports
    only the standard JSON library. No local helper is needed.

    python3 checker/checkers/strict632.py < checker/fixtures/strict_proofs/computation_zero_local.json

    Acceptance is normal process exit with exactly ACCEPT and a newline.
    Any other outcome rejects. No acceptance gate uses assert or __debug__.

mathematics/predecessor51.py
    Fully expanded term constructors, exact node counts, literal term
    evaluation, and separately labelled finite numerical checks.

checker/verify_checker.py and checker/verification.json
    Reproducible regression runner and full results. cases.json includes
    expectations, descriptions, provenance and fixture SHA-256 hashes.

evidence/
    Baseline identities/measurements, source coverage, independent review
    notes, exact constructor counts, and verification results. A source
    census measures programs without executing the historical corpus.

controls/
    Exact compact record sources and native607 control. These are retained
    for measurement and comparison, not promoted as new results.

REPRODUCE

    python3 verify_manifest.py
    python3 reproduce.py
    python3 reproduce.py --pdf

Run the manifest check before rebuilding, since reproduction rewrites some
environment-specific evidence. Exact reference metrics use CPython 3.12.14.
PDF rebuilding needs installed TeX assets with the standard packages
declared in the source. The included helper can build a private format
and font map when generated caches are absent; it downloads nothing and
changes no global TeX configuration. The standalone TeX may also be
compiled directly with two pdflatex runs in a conventional installation.

PROVENANCE AND PROOF STATUS

Repository: https://github.com/VladimirReshetnikov/ProveIt
Snapshot: e85c5e24dba535a296c46cd18fa66a146ce36b8e
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The 57-node predecessor, strict637, logical macros, ordinary interpretation
bridge, and sorted arity codec are inherited and attributed. The new
absorbing factor, 51-node term and rejection-sentinel edit are distinguished
in the report. The inherited MIT No Attribution license is retained.

The new universal statements have written proofs, not just numerical
evidence. No new Lean or Rocq formalization is included, and the upstream
Lean build was not rerun. Independent analysis-agent review is not external
human peer review. No literature-wide novelty claim is made.

No repository commit, pull request, or external publication was created.
