INITIALIZER EVALUATION FOR iPRA
Executable artifacts accompanying the written equivalence proof

RESULT

The new arithmetic rule is:

    a = b,  I(S c, a; u.h) = r
    -------------------------------- Seed
    r = h[I(c, b; u.h)/u]

All substitutions are capture avoiding and zero normalizing. In particular,
I(0,b;u.h) denotes b. The counter c and update body h stay fixed; only the
displayed initializer slot changes from a to b. The surrounding clause logic
and entire numerical/formula grammar are unchanged.

The previous Step rule instead uses I(c,a;u.h)=t as its first premise and
concludes r=h[t/u]. Both arithmetic interfaces derive each other using only
reflexivity and their shared c=0 instances. A general Seed instance takes
three old Step instances; a general old Step takes seven Seed instances.
At c=0, both translations use the original single common instance.

The full calculus still has five schemes: Use, Refl, Seed, DE, and DI.
The written paper, rather than these finite tests, establishes the exact
consequence equivalence and inherited whole-domain bi-interpretation with iPRA.

MEASUREMENTS AND THEIR LIMIT

Full normalized acceptance modules, CPython 3.12.14:

                                      Bytes   Tokens   AST nodes
Shared-walk Step control                2804      758       815
Shared-walk Seed checker                2802      756       815
Exact shipped Step checker              2950      829       902
Literal Seed adaptation                 2950      829       902
Exact shipped computation/transport     3048      860       949

The arithmetic change alone saves two bytes and two tokens in the shared-walk
implementation and ties in the literal shipped style. The larger saving
against the shipped checker comes from consolidating syntax validation and
opening into one traversal. It must not all be attributed to the new rule.
AST counts tie for each arithmetic-only comparison. The historical 516-byte
compact profile and 788-byte goal-validated profile remain smaller.

The clearer proof-certificate improvement is independent of variable names
in Python: computation now starts from a=a instead of I(c,a;h)=I(c,a;h).
The two canonical computation certificates have the same three inference
nodes. When c is not literal zero, compact JSON removes one occurrence of
the full predecessor-iteration tree from the proof.

FILES

checker.py                         Complete primary Seed checker.
control_step.py                    Matched Step checker using the same walker.
seed_literal.py                    Literal shipped-style Seed adaptation.
control_step_literal.py            Byte-authenticated pinned Step checker.
control_computation_transport.py   Byte-authenticated older Comp/Tr control.
proofs.py                          Untrusted arithmetic proof macros.
translate.py                       Untrusted checked proof translations.
verify.py                          Reproducible measurements and finite checks.
verification.json                 Recorded results of the final local run.
FORMAT.txt                        Input syntax and rules of the primary checker.
provenance.json                    Pinned repository source map and blob hashes.
fixtures/                         Pinned, generated, translated, and negative cases.
reference/                        Exact upstream producer, README, and license.

RUN

    python3 checker.py < fixtures/seed/induction_uses_hypothesis.json
    python3 verify.py
    python3 translate.py step seed INPUT.json OUTPUT.json

The other translation mode is control, for the separate computation and
transport interface. The translator checks its input and output and preserves
the final formula literally. No proof producer or translator is imported by
any standalone checker.

The primary checker reads exactly a JSON object with goal and proof. Success
means exit status zero and precisely ACCEPT followed by a newline. Exceptions
reject. Acceptance uses no Python assertions and is checked under python -O.
Only the standard library is needed. Ordinary runtime memory and recursion
limits still apply to large finite certificates.

ASSURANCE

The recorded run covers all 83 frozen upstream positive certificates, new
arithmetic and logical examples, both proof-translation directions and their
round trips, malformed inputs, variable escape attempts, independent numerical
and substitution evaluations, and fixed-passive-parameter cases. Detailed
counts are in verification.json. In particular, tests check that counter and
body occurrences resembling the old initializer remain unchanged.

Finite tests supplement the written proof; they do not establish universal
soundness or bi-interpretability. No new Lean or Rocq verification and no
global minimum are claimed.

The pinned comparison is ProveIt commit
443cff49563457a48ee0f663012d56c4bdb58fa0.
Inherited sources retain the MIT No Attribution license in reference/.
