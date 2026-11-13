PUBLIC-COORDINATE PARITY REFINEMENT

Run:
    python3 verify.py

The five complete standalone proof checkers are in code/.
Matched original programs are in controls/.
PROOF.txt gives the exact local transformation and its phase-dependent proof.
transforms.json records provenance, source hashes, and the literal edits.
fixtures/ contains inherited genuine proofs, invalid public goals, malformed
alphabets, and explicit scope/capture/contradiction attacks.
verify.py performs AST-transformation audits, whole-module measurements,
matched CLI executions under normal and -O Python, and arithmetic examples.
The verification report is written to evidence/verification.json.

The checkers read the inherited whole-array JSON proof format from stdin and
print ACCEPT only after a successful check. A nonzero exit, other output, or
failure to terminate is not acceptance. The native programs validate the
public goal; the strict programs also validate the entire input alphabet.

These are smaller implementations of the same inherited presentation of
iPRA. They give new observed envelopes in the two validating interfaces;
they do not improve the smaller compact interface and are not a new
mathematical axiom system or a proof of absolute minimality.

The final strict programs compose the coordinate simplification with the
noncallable rejection sentinel in the later incoming absorbing_orbit package.
Its frozen strict632 source is retained in reference/late_strict632.py and
credited in PROOF.txt. This sentinel is inherited, not claimed as new here.
