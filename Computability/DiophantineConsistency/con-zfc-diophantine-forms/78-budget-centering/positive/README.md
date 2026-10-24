# Positive-domain descent composition

- eleven/p11_positive_degree277.json: 11 strictly positive unknowns,
  exact degree 277, 111 live binary arithmetic operations.
- twelve/equation.json: 12 strictly positive unknowns, exact degree 78,
  103 live operations.

Run python3 eleven/verify.py and python3 twelve/verify.py. Both use Python's
standard library only; both also pass with python3 -O. The first verifier
rebuilds its literal graph directly; the second rebuilds in a temporary
directory. The fixed compact44 payloads are present and authenticated.

The statements are ordinary ZFC-formalizable existence equivalences with
finite syntactic ZFC refutations. PROOF.md gives the mathematical changes,
section.tex contains an integration-ready article section, upstream/ retains
the two main source proofs, and SOURCE_PINS.json authenticates their origins.
No new end-to-end Lean/Rocq consistency certificate is claimed.
