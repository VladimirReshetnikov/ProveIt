A simpler elimination rule for intuitionistic primitive recursive arithmetic
===========================================================================

RESULT

Primitive equality transport can be restricted to sources that are not
syntactically the literal term 0. Every removed instance is derivable using
the remaining rules. This preserves the complete native consequence
relation, including retained assumptions and formulas under Q and D.

As a result, the source term can select exactly one elimination major:

    source is literal 0:  require Q_v F(v)
    otherwise:            require source = target

In both cases the minor premise is F(source), and the conclusion is
F(target). Together with the retained computation schemas, hypothesis rule,
D elimination, case introduction, and literal-equation progress introduction,
this is the complete proposed calculus. The complete inventory, freshness
conditions, and derivability proof are in report.pdf and report.tex.

This is a syntactic restriction, not an arithmetical nonzero test. An
iterator such as I(2,1;u.0) remains an allowed source although it denotes zero.
The ordinary realization remains whole-domain bi-interpretable with full
first-order intuitionistic PRA, with actual equality and identity composites.

READ FIRST

    report.pdf                  Complete report, including inherited bridge
    report.tex                  Main LaTeX source
    proofs/zero_source_admissibility.tex
                                New universal admissibility derivation
    CLAIMS.json                 Machine-readable scope and limitations

The proof establishes 0=t |- t=0 without zero-source transport. Its key
invariant is n=I(n,t;u.Su), with t fixed under equation induction. A scalar
singleton-one test and an unconditional zero-filter identity finish the
argument. Equality algebra then gives atomic transport, and external formula
induction extends transport through Q and D. The report explicitly avoids
assuming unrestricted numerical substitution before it has been recovered.

COMPLETE CHECKER SIZES

All main counts are for complete standalone modules, after removing genuine
docstrings and applying ast.unparse plus one final newline, on CPython 3.12.14.
The same JSON input and ACCEPT-newline verdict contract is used throughout.
The gzip-9 column is informational and uses mtime=0.

                                      Tokens   AST nodes   Bytes   Gzip-9
    Byte predecessor                     266         310     529      333
    New code/checker_bytes.py            266         305     526      330
    AST predecessor                      263         289     613      349
    New code/checker.py                  263         283     607      348
    Token predecessor                    261         292     576      345
    New code/checker_tokens.py           259         289     572      339

The attained minima across 56 frozen baseline modules are 261 tokens,
289 AST nodes, and 529 bytes. The new family attains 259, 283, and 526,
respectively. These three minima are attained by different programs.
Neither a universal lower bound nor an absolute simplest theory is claimed.

The selected AST and byte checkers use a local fresh-name supply. The token
checker uses the inherited global protocol. See code/FORMAT.txt. The three
programs are not claimed to accept identical serialized certificates.

RUN

Python 3.12 is the tested runtime; the code uses only the standard library.
Run these commands from the extracted directory:

    python3 reproduce.py
    python3 code/checker.py < tests/certificates/contextual_induction_local.json
    python3 -O code/checker_bytes.py < tests/certificates/transport_under_Q_local.json
    python3 code/checker_tokens.py < tests/certificates/transport_under_D_global.json
    python3 tools/measure.py

Expected accepted-certificate output is exactly ACCEPT followed by a newline
and a zero exit code. An exception/nonzero exit is rejection. The checkers
do not import any producer, reference module, proof database, or helper.
The full certificate generators and proof transformer are untrusted inputs
to these standalone checkers.

The reproduction script checks frozen source hashes, regenerates and audits
the proof certificates, runs the named cases and rejection controls in normal
and optimized Python, and writes receipts under evidence/reproduced/.
The packaged run passed all 212 expected-verdict checks: 148 acceptances and
64 rejections. This includes a comparison in which the old contextual proof
is accepted by its baseline checker but rejected by the new primitive
interface; the transformed proof of the same conclusion is accepted.

To rebuild the PDF (a LaTeX installation is required):

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

The PDF is included, so TeX is not needed to inspect or test the construction.

ARTIFACT MAP

    code/                       Three compact kernels, gzip copies, readable
                                self-contained expansion, packet format
    proofs/                     New mathematical proof
    tests/normalizer.py          Generic zero-source proof transformation
    tests/native_producer.py     Local native proof-tree and packet producer
    tests/global_producer.py     Global packet producer
    tests/generate_certificates.py
                                Four derived examples and primitive audit
    tests/certificates/          Local/global JSON proofs and verdict receipt
    reference/checkers/         56 frozen complete baseline checker modules
    reference/bridge/           Unmodified inherited mathematical sources
    evidence/                   Measurements, source identities, review,
                                provenance, and reproduced verdict receipts
    SHA256SUMS                  Hashes of the distributed files

PROVENANCE AND LIMITS

Baseline repository: VladimirReshetnikov/ProveIt
Commit: b17dd5487f34adea473a0204c5320fb3eeb8910e
Research tree: 1770db22fe06b1e5c3089b557d9165625a133574
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The scalar arithmetic, Q/D macros, arity codec, certified-zero normalization,
and the ordinary/native/iPRA interpretation bridge are inherited. The new
mathematical contribution is the admissibility of every removed literal-zero
source transport. The byte and AST profiles additionally compose small
implementation changes, separately explained in the report.

The inherited foundations reproduced in the appendices retain their own
local notation and historical discussion. Their source identities and URLs
are recorded in evidence/reference_provenance.json. The repository's MIT-0
license is supplied as reference/ProveIt_LICENSE.txt.

The new universal theorem is a written proof with separate assistant reviews
and executable instances. It has not been mechanized in Lean or Rocq, and the
upstream Lean build was not rerun. Finite execution evidence does not replace
the universal proof. No claim is made about shortest proofs, fastest proof
checking, literature-wide priority, or an internal consistency proof for iPRA.
