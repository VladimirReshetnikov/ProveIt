COUNTER EVALUATION FOR INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
Prepared for Vladimir Reshetnikov, November 11, 2026

RESULT

The proposed new arithmetic/equality interface consists of reflexivity and
one inference schema:

    s = t,   R(S s, a; i,u.h) = r
    ---------------------------------
    r = h(t, R(t,a; i,u.h))

The seed, update body and passive parameters stay fixed. Substitution is
capture avoiding. R is the repository's existing counter-aware,
successor-seeded recursor; its zero-counter body is canonically erased,
so R(0,a;h) is definitionally S(a). This normalization is part of the
complete checker, not an omitted axiom implementation.

Root composition is two evaluations through the counter-projection frame.
Congruence in any fixed numerical term context is also two evaluations.
With the inherited Eq/D clause logic, the full presentation has five
inference patterns: Refl, CounterEval, clause Use, DE, and DI.

The paper proves bi-interpretability with full first-order iPRA, including
both whole-domain interpretation composites. No new Lean/Rocq verification
is claimed. The arithmetic basis, direct PR compiler, canonical zero
convention, clause logic and five-pattern count are inherited; the new
contribution is the uniform counter-evaluation interface and its equality
recovery theorem.

FILES

ipra_counter_evaluation.pdf  Complete paper.
ipra_counter_evaluation.tex  Complete LaTeX source, including checker listing.

code/counter_eval.py             The complete standalone trusted checker.
code/control_counter_transport.py  Matched same-language control.
code/control_*.py                Additional complete comparison checkers.
code/proof_macros.py             Untrusted independent proof producer.
code/translate.py                Checked proof translations both ways.
code/verify_independent.py       Main finite validation suite.
code/verify_translations.py      Open/closed proof-translation checks.
code/verify_controls.py          Supplemental comparison-control checks.
code/measure.py                 Complete-module source measurements.
code/certificates/              Accepted/rejected and translated examples.
code/control_fixtures/          Prior examples for the scalar controls.

evidence/                       Reproducible machine-readable results.
reference/                      Pinned baseline, audit, source excerpts,
                                provenance and the original MIT-0 license.
reproduce.py                    One-command reproduction entry point.
SHA256SUMS.txt                   Checksums of the deliverable files.

RUN

    python3 reproduce.py

To rebuild the PDF as well:

    python3 reproduce.py --pdf

The checkers and validation scripts require only Python's standard library.
CPython 3.12.14 is the exact metric reference. The PDF uses standard
pdfLaTeX packages; no network access or shell escape is needed.

Example certificate:

    python3 code/counter_eval.py < code/certificates/used_induction_zero.json

The public checker reads one JSON
object with exactly goal and proof, and accepts only a closed goal.
Acceptance is exit status 0 and the line ACCEPT; other outcomes reject.

Proof conversion:

    python3 code/translate.py reverse INPUT.json CONTROL.json
    python3 code/translate.py forward CONTROL.json RETURNED.json

The translators verify their input and output and preserve the end
formula literally. They are not imported by the standalone checker.

MEASURED COMPARISON

Complete normalized programs             Bytes   Tokens   AST nodes
Same counter language, computation+Tr     3272      929       1063
Proposed CounterEval                     3004      854        987
Scalar zero-normal single-case Eval      3061      884       1025
Incoming raw scalar CE5                  3046      853        993
Raw scalar with known root-case removal  2999      848        986
Incoming canonical clause checker        3305      946       1072

The matched same-counter reduction is 268 bytes (8.19%). The raw
two-case scalar variant is five bytes smaller than the new checker.
The existing compact 516-byte encoding is not surpassed. This is a
local structural simplification, not a proof of absolute minimality.

VERIFICATION

37 positive and 15 negative public certificates; 104 normal/-O process
checks; 44 open arithmetic/substitution checks; 29 nested-template
congruence/transport pairs; 570 finite numerical/compiler checks;
37 closed and 4 open bidirectional proof round trips. All expected
outcomes hold. Detailed counts and cases are in evidence/.

Finite checks do not establish the universal metatheorems. Those are
the written proofs in the paper. The independent substitution and
numerical evaluators deliberately differ from the trusted checker.

BASELINE

Repository: VladimirReshetnikov/ProveIt
Commit: 831081033253cca2115196cf86bb99c77ed2aeae
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Both filed research packages and all five incoming archives were
considered. See the paper's attribution appendix and reference/.
No repository changes were published.
