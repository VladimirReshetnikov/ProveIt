FULL NORMALIZATION: FORWARD CHECKER AND PROOF COMPILER

This directory is self-contained and uses only the Python standard library.
It supplies a transparent forward implementation and an executable compiler
from the incoming zero-normal six-rule calculus. The main report also measures
a separate goal-directed implementation; this forward implementation is not
claimed to beat the smaller zero-normal forward control.

Run all included checks from any working directory:

    python3 /path/to/this/directory/verify.py

Check one certificate:

    python3 checker.py < examples/exceptional_case_zero.json

The checker prints ACCEPT and returns status zero exactly when its check
succeeds. Rejections return nonzero status. The mathematical interpretation
uses the customary unbounded-resource model of the program.

TRUSTED / UNTRUSTED BOUNDARY

checker.py is the complete trusted forward checker. It imports json and sys
from the standard library and does not import any local file.

compiler.py is an untrusted elaborator. Its output is always checked by
checker.py. The compound-envelope construction is entirely in this untrusted
file; no envelope macro or additional logical rule is built into the checker.

verify.py is a reproduction script. It checks 64 included source certificates
with the byte-exact reference/zero_normal/checker.py, compiles them, checks each
new certificate, and compares it with its archived output. It then runs every
new fixture through the command-line checker in ordinary and optimized (-O)
Python. It also performs finite normalization regressions. Its assertions are
test machinery, not trusted proof-checker guards.

CONTENTS

    checker.py                         complete forward checker
    compiler.py                        untrusted proof translations
    FORMAT.txt                         syntax and certificate rules
    examples/                          65 positive and one negative fixture
    verify.py                          complete reproduction command
    evidence/forward_validation.json   observed validation and source metrics
    reference/zero_normal/checker.py   unchanged comparison checker
    reference/zero_normal/certificates/ 64 checked comparison certificates
    reference/zero_normal/LICENSE.txt  inherited MIT-0 license
    reference/provenance.json          pinned source and fixture provenance

The fixture exceptional_case_zero.json is deliberately more than reflexivity:
it proves D_{x,y}(y=1) from the case argument with contradictory base 0=1.
Full normalization changes a zero-denoting witness into literal 0 and would
make a naive introduction use progress instead of cases. The compound envelope
repairs that change. reject_naive_normalized_case.json records the invalid
unrepaired proof of the same true conclusion and is correctly rejected.

MEASUREMENT

Metrics use ast.unparse(source) plus one newline, significant tokens, AST
nodes, and gzip.compress(..., compresslevel=9, mtime=0). The forward full-normal
checker has 3,100 normalized bytes; the unchanged zero-normal control has
3,095. The main construction's size improvement must be assessed using the
report's matched goal-directed measurements, not attributed to this auxiliary
forward implementation.

NORMALIZATION SCOPE

Both iterator computation equations are definitional. Input terms must already
be canonical, but substitution can expose computations and normalizes them.
This is a total recursive normalizer in the metatheory, not a primitive
recursive uniform evaluator postulated inside iPRA. Finite regression tests
support the implementation; the report supplies the mathematical termination,
confluence, soundness, completeness, and interpretation arguments.
