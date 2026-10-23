# A 45-integer quartic

`quartic45.json` specifies 45 unrestricted integer unknowns and 28 quadratic
residuals. The sum of their squares is the supplied polynomial. Its exact
degree is four, uniformly certified by the coefficient 1 of tau^4.
`QUARTIC45_PROOF.md` proves the domain reduction, with its inherited
unbounded dependencies stated explicitly.

This reduces the selected 50-variable quartic by five variables. Its 407
expanded symbolic terms exceed the parent's 362; no operation-count or
monomial-count improvement is claimed.

Run, from any current directory:

    python3 /path/to/quartic/build_verify.py

Python 3's standard library suffices, including under `-O`. The script checks
all pinned inherited hashes, authenticates the four complete coefficient
payloads, reconstructs the new residual packet from inert source data, and
expands the quartic with exact sparse arithmetic. It overwrites only its
three named generated outputs: `quartic45.json`, `quartic45_expanded.json`
and `AUDIT.json`.

The active complete tuple is package 34's B=2^1064921 instance under
`upstream/34-integer14/coefficients/`. Its four ports are beta,K,MC and the
already shifted MF_source; the equation aliases K0=K and MF=MF_source.
It is independent from any smaller tuple used elsewhere in the combined
report. The supplied native builder and independent auditor can additionally
reproduce/check that tuple; their source bytes are retained unchanged.

`SOURCE_PINS.json` gives the immutable repository commit and the SHA-256
and Git-blob identities of every inherited file. The literal K215 table
was restored from its canonical repository path because package 34's intake
omitted that duplicate. Original licenses and notices are retained.

Finite symbolic checks and ordinary proofs are supplied. No new complete
kernel certificate or literal object-language ZFC derivation is claimed.
