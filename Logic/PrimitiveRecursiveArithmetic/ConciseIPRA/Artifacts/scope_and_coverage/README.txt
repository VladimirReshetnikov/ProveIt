SMALLER iPRA CHECKING AND COVERAGE WITHOUT INJECTIVITY
Prepared for Vladimir Reshetnikov, 10 November 2026

RESULT AND LIMIT
----------------
The requested significant new simplest axiomatization has not been achieved.
The package contains a smaller COMPLETE checker for an inherited theory, two
new arithmetic lemmas without successor injectivity, explicit native axioms
and rules, and the attributed full-domain iPRA equivalence proofs.

Complete program                  normalized bytes  tokens  AST  gzip-9 raw
Current byte incumbent                        542     263   309     343
code/checker_compact.py                        529     266   310     333
code/checker_explicit.py                       537     266   308     337

The new programs improve source bytes, not the independent 261-token and
291-AST minima. The 529-byte program combines existing lexical scope, arity,
neutral-major and dispatch techniques. It is not a new arithmetic basis.
The explicit-list version is recommended for direct inspection. The separate
readable_checker.py is also complete; it does not wrap another checker.

The new self-seeded arithmetic lemmas prove:
  * For each fixed k>=1, S^k(a) != a, without numerical induction.
  * With literal-equation induction, a finite-case right predecessor P,
      n=0 or n=S(Pn), and S(P(Sn))=Sn,
    without successor injectivity or a coverage axiom.
They do NOT prove P(Sn)=n, successor injectivity, or bi-interpretability of
that weakened precursor with iPRA. The measured checker instead implements
the already established initialized-iterator theory, whose whole-domain
bi-interpretability and equiconsistency are reproduced in the paper.

OPEN FIRST
----------
ipra_scope_and_coverage.pdf  Compiled paper with proofs and attributed appendices.
ipra_scope_and_coverage.tex  Standalone source, compilable without local inputs.
report_main.tex, theory/    Modular editable source.
code/                      Complete public checkers and maximum-level gzip files.
evidence/                  Source census, measurements, reviews and verification.
validation/                Untrusted producers, explicit packets and diagnostics.
reference/                 Exact attributed comparison programs and prior proofs.
source_corpus/             All 484 distinct historical Python sources, frozen.

REPRODUCE
---------
From a fresh extraction, using Python 3.12 for the recorded source metrics:

    python3 reproduce.py
    python3 build.py

The first command uses only the Python standard library and needs no network.
It checks the delivered hashes, remeasures all complete comparison modules
and the frozen source corpus, runs the checker subprocess suites, and repeats
the arithmetic transcription diagnostics. Historical corpus files are parsed,
not executed. The second command needs PDFLaTeX and the standard packages
listed in report_main.tex; it uses no shell escape. Rebuilds can change PDF
metadata and therefore the delivered manifest. Experiment in a working copy.

RUN A CERTIFICATE
-----------------
    python3 code/checker_explicit.py < validation/composition/fixtures/I0_arbitrary_seed.json
    python3 code/checker_explicit.py < validation/composition/fixtures/canonical_false.json

The first accepts and the second rejects. Acceptance means exit status zero
AND exactly ACCEPT followed by a newline on stdout. An exception rejects.
The JSON array ends with the closed goal; earlier [m,s,u,t] packets are
consumed backwards. Unused prefixes are inert. No certificate is executed as
Python. Real memory and recursion limits can reject very large valid proofs.

PROVENANCE AND NOVELTY
---------------------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: b9c4d74a0018bdafc5bc06e755a0145f4ed2b8d6
20 direct archives; 35 distinct recursively embedded archive payloads;
2,744 Python occurrences; 484 distinct Python sources. All direct archive
lengths and Git blob SHA-1 identities were checked. Original paths and hashes
are retained in evidence/corpus_manifest.json and copied_sources.json.

A deterministic progression/closure binder was rederived during this work,
then found already present in a nested all_starts.tex. It is explicitly
excluded from novelty claims. The prior source already fuses its Step and
Base rules noncircularly using tau(r,s)=I(r,s;u.Su).

The repository's MIT No Attribution license is retained in reference/.
Intellectual attribution is preserved throughout the paper, including for
inherited passages whose historical wording says 'new'. No GitHub repository
change, publication, issue, comment or message was made.

VERIFICATION BOUNDARY
---------------------
The implementation suite records 596 process expectations and ten targeted
mutation observations for the compact composition and matched ablations.
The package-level reproduction additionally checks the actual public compact,
explicit and readable modules. Finite arithmetic diagnostics are standard-
model transcription checks, not proofs in nonstandard models. The universal
metatheorems are written mathematical proofs reviewed by independent assistant
instances; there is no Lean/Rocq formalization or external human peer review.

FURTHER RESEARCH
----------------
The concrete remaining question is whether the self-seeded precursor can
derive a left inverse of successor. A proof would remove the currently
charged injectivity axiom; a countermodel must satisfy the full precursor,
not just have an acyclic noninjective successor graph. Other questions and
the exact representation and source-cost limitations are in the paper.
