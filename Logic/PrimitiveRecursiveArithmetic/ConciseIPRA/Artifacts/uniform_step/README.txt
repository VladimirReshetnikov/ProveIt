ONE SUCCESSOR STEP FOR EQUALITY AND COMPUTATION
Research package for Vladimir Reshetnikov, 11 November 2026

RESULT

On the existing zero-normal scalar iterator syntax, all arithmetic
computation and equality inference follow from reflexivity and one rule:

    I(c,a;u.h) = t       I(S c,a;u.h) = r
    ----------------------------------- Step
                   r = h[t/u]

At c=0 the first source is definitionally a. Only zero-counter
iterators normalize; substitution is capture-free and normalizing.

For J_s=I(S0,s;v.v), Step applied to s=r and J_s=J_s gives J_s=r.
Then Step applied to s=t and J_s=r gives r=t. This two-Step pivot
recovers symmetry, transitivity, arbitrary term congruence, and the
original crossed one-template transport rule. No induction is used
in this equality argument.

With the existing reusable-clause logical interface, the complete
calculus has five primitive schemes:

    Use, Refl, Step, DE, DI.

Its formula grammar is equality plus the binder
D_(x,y) B = exists x (B(x,0) -> forall y B(x,y)).
The report specifies every rule, scope condition, and normalization
operation. The single DI chooses progress only at a literal equation
with literal witness zero; all other instances use cases.

The written proof establishes exact native-kernel consequence
equivalence and, through the inherited arithmetic bridge, whole-domain
bi-interpretability and equiconsistency with full first-order iPRA.
Equality is actual equality and both composites have graph x=y.

WHAT IMPROVES

The three alternatives in the current raw computational-equality rule
become one successor pattern. Compared with a matched zero-normal
clausal checker, the computation instruction and template-taking
transport are replaced by Refl and Step. All syntax validation,
normalization, scoping, clause storage, and the public interface count.

Complete normalized-source measurements, CPython 3.12.14:

                                   Bytes   Tokens   AST   gzip-9
New uniform Step                    2950      829   902     1005
Matched zero-normal Comp/Tr          3048      860   949     1018
Matched raw three-case Eval          3094      853   969     1026
Incoming canonical clausal           3305      946  1072     1073

Gzip uses level 9 and timestamp zero and is informational.
True docstrings are removed before ast.unparse normalization plus LF.
The cleanest controlled reduction is 98 bytes, 31 tokens, 47 AST nodes.
The original delivered checker, including documentation and formatting,
is 3507 bytes and compresses to 1274 bytes at gzip level 9. Both original
and normalized source compression sizes are recorded.

The repository already contains five-rule clausal work, so five rules
alone is not new. It also contains much smaller heavily encoded
checkers, including a 516-byte guarded profile and an incoming
866-byte fully validated profile with another certificate protocol.
This package does not establish a global size minimum. Its result is
the arithmetic rule simplification and the matched complete-verifier
reduction.

FILES

report.pdf                  Complete research report and inherited proofs.
report.tex                  Standalone LaTeX source; no local inputs needed.
source/                     Readable source fragments used to assemble it.
code/checker.py             Entire primary trusted checker.
code/control_zero.py        Matched normalized computation/transport control.
code/control_raw.py         Matched raw three-case Eval control.
code/reference/             Exact upstream comparison modules.
code/normalized/            Normalized primary modules and gzip-9 files.
code/verify.py              Finite clausal proof producers and boundary tests.
code/review.py              Independent opening/capture audit.
code/clausal_certificates/  188 positive/control/negative fixtures.
code/native/               Explicit-sequent checkers, full proof translations.
examples/                   Small selected primary certificates.
reference/                  Authenticated inherited mathematical sources.
evidence/                   Verification receipts, metrics, provenance.
CLAIMS.json                 Explicit claim and limitation ledger.
SHA256SUMS.json             Integrity hashes for the delivered files.

RUN

Python 3.10 or later is needed for structural pattern matching.
Reference measurements and execution used Python 3.12.14.
There are no nonstandard Python dependencies.

    python3 code/checker.py < examples/induction_uses_hypothesis.json
    python3 reproduce.py
    python3 reproduce.py --pdf

The last command requires TeX Live with the packages named in report.tex.
It builds the standalone source and runs three pdfLaTeX passes.
The source can also be compiled directly with normal pdfLaTeX.
The build script includes a local-cache fallback for an installation
whose package files exist but whose format/font-map caches are absent.

Successful checking prints ACCEPT and exits zero. Rejection exits
nonzero. Acceptance does not rely on Python assertions and was also
tested with python -O.

EVIDENCE AND LIMITS

The final primary suite passes 376 standalone process checks, including
83 positive certificates in each matched calculus and 22 negative cases,
all in normal and optimized Python.
The native suite passes 38 positive certificates, 12 negatives,
100 command-line checks, and 38 checked translation round trips.
The independent audit passes 2104 semantic opening comparisons,
13 malformed/eigenvariable-escape controls, and a positive DI check.

These are implementation checks, not proofs of the universal
metatheorems. The new equivalence is a written proof with independent
review. This package contains no new Lean or Rocq formalization.
The inherited native/scalar/iPRA bridge is documented by the supplied
repository's Lean sources. Ordinary numerical agreement alone is not
used as a substitute for either interpretation round trip.

PROVENANCE

Frozen ProveIt commit:
6ca328039cafa1537d81ee6b67ee2dc54ffa5a4e

https://github.com/VladimirReshetnikov/ProveIt/tree/6ca328039cafa1537d81ee6b67ee2dc54ffa5a4e/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Both incoming archives ipra_clausal_canonical.zip and
ipra_scalar_uniqueness.zip were inspected. Clausal contexts,
zero-normalization, the scalar arithmetic bridge, and the single
introduction convention are inherited and are credited in the paper.
The exact inherited license is reference/LICENSE-ProveIt.txt.
