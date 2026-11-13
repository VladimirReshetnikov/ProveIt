UNIFORM TERMINAL CERTIFICATES FOR iPRA
Prepared for Vladimir Reshetnikov, November 12, 2026
=================================================

OPEN FIRST
  report.pdf
  report.tex  (uses mathematics/obstruction.tex, also supplied)

RESULT
  A smaller certificate presentation of the inherited guarded scalar
  calculus. Every proof call consumes a packet, and one membership test
  recognizes either a retained hypothesis or a computation equation.
  The no-image scope traversal is a partial retraction. This proves the
  new projected computation match sound. Canonical proof translation
  supplies the extra terminal packets and preserves completeness.

  With the pinned arithmetic/logical bridge, the presented theory is
  equiconsistent and bi-interpretable with FULL first-order intuitionistic
  primitive recursive arithmetic: whole numerical domains, actual
  equality, and identity numerical comparison graphs x = y.

METRICS OF COMPLETE STANDALONE MODULES (CPython 3.12.14)
                            tokens    AST    normalized bytes    gzip-9
  Old token profile           243     271          616              343
  Old node profile            248     264          613              336
  Old byte profile            270     308          474              314
  New checker_tokens.py       242     268          565              331
  New checker_ast.py          247     263          553              331
  New checker_bytes.py        272     306          469              309

  The observed compact envelope changes from 243 / 264 / 474 to
  242 / 263 / 469. Each coordinate is attained by a DIFFERENT program.
  gzip is maximum compression of normalized source, with mtime=0.

LIMITS OF THE RESULT
  No one new program is below all three old coordinate minima at once.
  Thus that stronger interpretation of the requested target is still open.
  The result changes the proof format and its implementation; it does not
  remove an arithmetic axiom or claim a new mathematical breakthrough.
  No absolute simplicity optimum or general checker-size lower bound
  is proved. The old envelope is an observed set of upper bounds.

  Compact input promises a canonical closed guarded Eq/D public goal and
  exact integer/list certificate data. The program is not a complete
  public-grammar or JSON-alphabet validator. Native-goal and whole-input
  validation are separate contracts, whose records are not improved here.

  The stream modules use global fresh-scope allocation. The old node
  minimum uses local allocation, so translations include renaming.
  The byte module uses local allocation and a single-array framing.
  Arbitrary raw certificate languages differ; canonical theorem sets agree.
  The stream implementation uses tail recursion. The mathematical
  completeness result follows the baseline's unbounded-resource convention;
  physical recursion limits can reject large valid certificates sooner.
  No runtime or certificate-length improvement is claimed.

FILES
  code/checker_tokens.py      Complete 242-token stream checker.
  code/checker_ast.py         Complete 263-node stream checker.
  code/checker_bytes.py       Complete 469-byte array checker.
  code/controls/             Exact leading incoming baseline sources.
  tests/                     Portable proof translators and fixtures.
  evidence/                  Metrics, 584-run receipt, frontier/provenance.
  mathematics/               Written dependency audit and finite diagnostics.
  reference/article/         Complete pinned upstream article LaTeX sources.
  reference/lean/            Principal pinned bi-interpretation interfaces.
  CLAIMS.json                Explicit claims and nonclaims.
  MANIFEST.sha256            Hashes of all delivered files except itself.
  LICENSE.txt                Upstream MIT No Attribution license.

VERIFICATION
  54 exact proof-trace translations.
  3,122 checked scope fixed-point instances in those translations.
  584 isolated process runs, including Python -O and negative controls.
  Zero failed expected outcomes and zero failed translations.
  These are finite implementation checks, not a replacement for the
  universal written proof. No newly compiled Lean/Rocq proof is claimed.

REPRODUCE
  python3 reproduce.py --manifest-only
  python3 reproduce.py
  python3 reproduce.py --pdf

  Verification runs in a temporary copy and preserves the delivered files.
  The Python standard library suffices. PDF compilation additionally needs
  pdfLaTeX and the ordinary packages declared by report.tex.

  To compile directly:
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

EXAMPLES
  python3 code/checker_tokens.py < tests/fixtures/stream/uniform/tokens__global_guarded_induction_with_used_hypothesis.jsonl
  python3 code/checker_ast.py < tests/fixtures/stream/uniform/ast__global_compound_implication_elimination.jsonl
  python3 code/checker_bytes.py < tests/fixtures/bytes/uniform/direct_zero_seed.json

  Acceptance is exit status zero and exactly ACCEPT followed by a newline.
  The profiles have different packet protocols; their input files are not
  generally interchangeable. Each measured checker imports only json.

ATTRIBUTION AND BASELINE
  Repository: https://github.com/VladimirReshetnikov/ProveIt
  Commit: 12197d86f63e9ec73b2d91399c4de2a8cb0077ee
  Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
  All five docs/incoming ZIP archives at this snapshot were inspected.
  The core, codec, bi-interpretation, direct-leaf lemma, mode-selector
  technique, controls, and original fixtures are inherited and credited.
  The two-point obstruction is a corollary of the article's existing
  finite-range theorem, checked here for deterministic-row Export.
  No remote repository mutation or publication was made.
