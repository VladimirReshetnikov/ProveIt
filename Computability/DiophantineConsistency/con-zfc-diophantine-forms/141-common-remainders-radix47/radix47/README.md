# Complemented-label radix47 consistency equation

A complete indexed943/shared-marker specialization with all34 label bits
complemented. The new carry bounds29/12 allow radix2^47. Its15-positive
P66 polynomial retains66 live arithmetic operations and exactdegree157.
All four fixed integers are supplied, totaling207214 canonical raw bytes.

Read `radix47/radix47_proof.md` for the full ordinary proof and theorem
boundary. `radix47/INDEPENDENT_REVIEW.md` records the independent fullproof
review; its final source hash binds the reviewed text. The prior idea of
color complementation is explicitly attributed to compact54.

Reproduce the equation and finite certificates:

```sh
python3 materialize_radix47.py
python3 verify_radix47.py
python3 audit_radix47_peer.py --root .
```

Both checkers also pass under `python3 -O`. They import no producer modules.
`radix_probe.py` and `materialize_radix49.py` supply shared decoding and
oldK reconstruction helpers to the producer only. They are included for
a self-contained computational closure. No external package is required.

`sources_pinned/` and `sources/` preserve the37 retained source files
identified by DEPENDENCIES.json. The complete final coefficient tuple,
straight-line program,51native geometry identities and exact receipts are
in `radix47/`. `equation.tex` there is a complete standalone formula source.
The enclosing research report package supplies its rendered PDF.

This is an ordinary new encoding proof plus exact finite verification,
composed with retained P66/K215/refutation correctness sources. It is not
a new Lean formalization or a global minimum claim.
