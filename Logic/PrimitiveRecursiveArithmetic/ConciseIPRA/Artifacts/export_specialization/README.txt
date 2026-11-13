EXPORT AND VARIABLE-ONLY SPECIALIZATION FOR iPRA
Prepared for Vladimir Reshetnikov, November 12, 2026
================================================

OPEN FIRST
  report.pdf
  report.tex  (source; also needs the supplied results_table.tex)

STATUS OF THE REQUESTED TARGET
  A new axiomatization below the entire current checker complexity envelope
  has NOT been established. The package supplies a conservative refinement
  with a complete equivalence proof, smaller matched implementations, and
  a separate compact byte-only improvement. It does not prove absolute
  minimality or a general size lower bound.

MATHEMATICAL RESULT
  In the existing normalized deterministic-Export calculus, all ordinary
  clause Uses may specialize at the newest parameter only. They carry no
  numerical target. An introduced name and the existing Export rule supply
  the alias substitution. Arbitrary reflexivity and arbitrary Intro
  witnesses are retained. The result holds for all open clause sequents,
  by a strengthened translation over arbitrary injective scope renamings
  and context embeddings. A raw five-family companion is proved in writing.

  The existing alias_back/equation_aliases work already proves newest-only
  Use with a primitive Alias rule. The present refinement combines that
  argument with the existing deterministic Export so no extra Alias is
  primitive. Naming and the proof-family method are credited prior work.

  Composing the exact consequence equivalence with the pinned arithmetic
  and logical bridge preserves full first-order intuitionistic
  bi-interpretability with iPRA: whole numerical domains, actual equality,
  and identity numerical comparison graphs x=y. No new Lean or Rocq proof
  is claimed. The universal proofs are written, not inferred from tests.

MEASURED COMPLETE MODULES (CPython 3.12.14)
                                      tokens    AST    normalized bytes
  Explicit-Refl source                   669     754          2117
  Explicit-Refl newest Use               663     748          2093
  Exact upstream clause source           653     729          2058
  Newest Use / inferred Refl target       654     731          2049
  Exact incoming compact source          272     306           477
  Separate compact composition           274     306           476

  The compact candidate implements the OLD guarded scalar calculus. The
  new mathematical presentation is measured by the first two matched pairs.
  The compact corpus envelope was 244 tokens / 265 AST / 477 bytes, attained
  by different programs and input framings. Only its byte coordinate moves.
  The stronger native and strict interfaces are compared separately.

FILES
  report.tex, results_table.tex, report.pdf
      Complete report: primitive rules, proofs, exact claims, interpretation
      dependencies, implementation comparison, and further research questions.
  newest_use/
      Four complete standalone normalized checkers, bidirectional proof
      compiler, substantive certificates, negative controls and test receipts.
  compact476/
      Complete 476-byte checker, exact 477-byte control, baseline profiles,
      66 fixtures, relative correctness proof and 264-run receipt.
  proof_node_audit.py
      Counts inference nodes in real compiled proofs; checks n+3u, the exact
      formula proved in the report (n source nodes, u source Use nodes).
  review/
      Independent in-run mathematical and implementation reviews, including
      a scoped obstruction to deleting recursive major verification.
  reference/
      Pinned inherited source chapters and README. These reference fragments
      are not standalone build targets and are not imported by a checker.
  PROVENANCE.json, CLAIMS.json, MANIFEST.sha256, LICENSE.txt
      Source identities, precise claim boundaries, checksums and MIT-0 license.
  reproduce.py
      Replays all included verification in temporary copies, preserving the
      delivered files and their manifest.

REPRODUCE
  python3 reproduce.py

  Uses only the Python standard library. Exact metric reproduction uses
  CPython 3.12.14. Other Python versions can change AST/unparse counts.

  Example of a complete accepted new-calculus certificate:
  python3 -I -S -B newest_use/checkers/newest.py \
      < newest_use/tests/successor_congruence.json

  Success means normal termination with exactly ACCEPT and one line feed.
  An exception or resource exhaustion is rejection, not acceptance.

REBUILD THE PDF
  python3 build_pdf.py

  Or, in a conventional TeX installation:
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

  Requires the normal TeX packages declared in report.tex. No network is
  needed. The supplied PDF is compiled from these sources.

PINNED COMPARISON
  Repository: https://github.com/VladimirReshetnikov/ProveIt
  Commit: 2fa4637b3bf922beea0052a5210c22b14482950b
  Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
  The consolidated article, relevant artifact sources and all seven incoming
  archives at this snapshot were inspected. No remote repository change,
  commit, pull request or external publication was made.
