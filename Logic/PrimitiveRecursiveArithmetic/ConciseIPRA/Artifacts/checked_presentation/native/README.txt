A SMALLER FULLY VALIDATED CHECKER FOR THE NATIVE iPRA PRESENTATION
================================================================

checker.py is a complete standalone Python proof checker. It validates the
whole input's integer/list alphabet, then checks a closed Eq/D public goal
and its proof. The existing logical and arithmetic calculus is unchanged.

CPython 3.12.14, complete source after ast.unparse plus one final newline:

                                    Bytes   Tokens   AST nodes
Existing matched fully typed Eq/D     849      370       426
New fully typed Eq/D                  673      344       393

The 656-byte intermediate control validates the initial goal but has a
different contract for inactive certificate data. It is supplied for the
source-comparison proof, not advertised as a matched fully typed baseline.
The separate compact profile elsewhere in the overall research package
has a different input contract and can remain smaller.

RUN
   python3 reproduce.py
   python3 checker.py < fixtures/computation_zero_local.json
   python3 checker.py < fixtures/old_atomic_case_local.json

Acceptance is exit zero and exactly ACCEPT followed by a newline. All other
results reject. The JSON proof stack is consumed from its end. The final
item is the public goal; unused integer/list prefixes are allowed.

FILES
checker.py          The entire new acceptance implementation.
control849.py       Exact matched fully typed existing checker.
control656.py       Exact source of the fused public validator.
AUDIT.txt           Contract, universal comparison proof, and limits.
PROVENANCE.json     Pinned repository paths, Git blobs, and SHA-256 hashes.
fixtures/           Frozen native-calculus regression certificates.
reproduce.py        Untrusted reproducibility and comparison harness.
validation.json     Executed results and complete-source measurements.

The general equivalence is a written proof using the inherited native
calculus and its iPRA bridge. No new Lean or Rocq verification is claimed.
This is not a new arithmetic axiom deletion or a proof of global minimality.
