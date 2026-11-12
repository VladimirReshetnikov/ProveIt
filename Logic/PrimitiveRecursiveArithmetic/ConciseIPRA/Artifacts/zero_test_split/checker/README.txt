SCOPE HEADER EXPERIMENT FOR THE COMPACT GUARDED iPRA CHECKER
=========================================================

This is a one-byte implementation improvement, not a new arithmetic calculus
or a mathematical simplicity breakthrough. It is supplied separately from the
parent report's mathematical theorem.

Measured complete modules, CPython 3.12.14, ast.unparse plus one final LF:

                            Tokens   AST nodes   Normalized bytes
  controls/compact479.py      272        304          479
  code/compact478.py          271        305          478

The corpus minima 248 tokens and 270 AST nodes remain unbeaten. Combining the
new byte program with the old token/AST programs gives the exhibited envelope
(248,270,478); no single program has those three coordinates. This is an upper
bound attained by implementations, not a proved lower bound or global minimum.

INPUT CONTRACT

The alphabet is finite integer/list JSON trees. The public goal is a closed
canonical guarded formula of the inherited two-sided gated presentation: its
atomic matrices have the form I(y,0;u.h)=I(y,0;u.j). In particular, at least
one numerical zero occurs in every public goal. This is the same guarded
presentation used for the compact479 comparison. The full native Eq/D grammar
is NOT the public grammar of this compact experiment. No public-grammar
validator is included or silently assumed to have been measured.

The old last certificate element was the public goal A. The new last element
is [A,k], where k is an initial numerical parameter floor. The instructions
before it are unchanged and still consumed backwards. The initial context is
the fixed neutral [0]. The function has exactly three positional arguments,
so the header cannot inject extra context assumptions. The canonical adapter
uses k=0. Successful execution prints exactly ACCEPT and one LF, with exit0.
An exception or other verdict is rejection; ignored prefix data stays inert.

RUN

  python3 measure.py
  python3 verify.py
  python3 compile_certificate.py < old.json > new.json
  python3 code/compact478.py < new.json

--offset -3 additionally shifts canonical negative rigid names and chooses
initial floor -3. This option illustrates the admissible extra-parameter
interpretation; it is not needed for completeness. Offset0 is the exact
all-input old-to-new trace adapter.

CONTENTS

code/compact478.py          Complete measured standalone module.
code/readable.py            Explanatory standalone expansion.
controls/compact479.py      Byte-for-byte frozen inherited control.
controls/LICENSE-ProveIt.txt Inherited MIT-0 license.
fixtures/                  Inherited positive and negative regression data.
compile_certificate.py     Untrusted certificate adapter.
measure.py                 Untrusted reproducible metric calculation.
verify.py                  Untrusted isolated-process regression harness.
compact478_verification.json Reproduced 546 checks, all passing.
provenance.json             Pinned archive identity and source hashes.
proof_scope_header.txt      Universal argument and exact limitations.

The control and candidate import no supporting code, fixture, proof database,
or adapter. No new Lean/Rocq verification is asserted. Finite regression tests
supplement the written argument and inherited calculus-to-iPRA bridge.
