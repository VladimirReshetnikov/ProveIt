# Start-only4127 specialization of all three ten-positive equations

Three explicit ordinary polynomials in ten **strictly positive** integer
unknowns retain the exact degree/gate tradeoffs 240/82, 232/85, 214/87, while
coherently replacing all four fixed ports with the whole Start-only4127 native
tuple. The complete coefficient payloads total 97,046 raw bytes, versus
295,388 for the prior positive10 tuple. This is a coefficient-size improvement,
not a reduction in degree, operations, or unknowns.

`PROOF.md` contains the full arithmetic proof and the new native-interface
composition. `native4127/START_ONLY_PROOF.md` supplies the complete new native
encoding and controller; `MATHEMATICAL_REVIEW_NATIVE.md` is the independent
ordinary interface audit. All source proof texts, numerical payloads and
reconstruction recipes are local. `CLOSURE_MAP.md` resolves source roles.

The actual equations are `start4127_positive10_degree*_ops*.json`. Each graph
binds all four ports to `native4127/start_only_ports/`; do not select individual
ports from another encoding. `round21_graphs/` and the old inherited tuple
remain historical sources, not the current specialization. No change to the
separate eleven-unrestricted-integer six-port family is claimed.

Run `python -B replay.py` to reconstruct and verify an offline clean copy.
It checks every graph gate by exact free-ring cuts, all register leading forms,
508 single-operator corruptions, complete new coefficient reconstruction and
finite controller geometry in both ordinary and Python-optimized execution.
The finite checks are not substitutes for the explicitly retained ordinary
native/Pell/refutation theorem, nor a new end-to-end formal-kernel proof.
