# Eleven integers with a linear strong-Pell multiplier

The complete ordinary proof is `PROOF.md`; `section.tex` is a typeset article
section. This component supplies two explicit ordinary integer polynomials:

| Polynomial | Variables | Exact degree | Live binary operations |
|---|---:|---:|---:|
| `linear_multiplier11_direct440.json` | 11 unrestricted integers | 440 | 126 |
| `linear_multiplier11_centered412.json` | 11 unrestricted integers | 412 | 127 |

The six fixed coefficients are fully supplied in `coefficients/`, with an
unchanged, authenticated finite reconstruction recipe. They are fixed numerals,
not extra unknowns. No radical, division, variable exponent, or hidden universal
interpreter occurs in either literal circuit.

The new mechanism replaces the squared strong multiplier by a linear input r.
A coprime product-square argument, a negative-square obstruction modulo3, and
variable3-adic weights recover r=u² without another coordinate. Supported-modulus
Pell interpolation reconstructs the divided auxiliary coordinate in the converse.

The ordinary proof composes with the retained source34/native/compiler calibration
to establish the ZFC-provable unsolvability/Con(ZFC) equivalence. It does not prove
consistency, claim global minimality, or supply a new end-to-end proof-assistant
certificate. This component uses the native/K215 lineage; the separate direct
C222 component in the overall article has its own calibration.

Against the newest inspected Round15 paired forms (degree456/124 operations and
degree416/125 operations), the new equations lower degree by16 and4 respectively
and use two extra operations. These are Pareto tradeoffs, not dominance claims.

## Reproduce

Python3.10 or later and the standard library suffice. No network or CAS is needed.

    python3 verify.py --receipt /tmp/linear_multiplier_check.json
    python3 -O verify.py --receipt /tmp/linear_multiplier_optimized.json
    python3 verify_coefficients.py

`verify.py` imports neither the builder nor the DAG utility. It checks the whole
coefficient tuple and retained source identities, all68 exact register identities
in each circuit, the full eight-factor norm, exact total degrees and nonzero
attained coefficients, live-coordinate closure, and seven corrupted gates per
variant. Small signed-radicand tests are labelled finite regression controls.

`verify_coefficients.py` is retained unchanged from the credited parent. It
reconstructs the six integers and compares the complete minimal bytes. Its source
recipe intentionally requires normal Python; the wrapper launches that unchanged
recipe normally even if the wrapper is invoked with optimization.

Regenerate circuits in a separate directory:

    python3 build.py --output-dir /tmp/linear_multiplier_rebuilt

The two circuit files and `METRICS.json` are deterministic. Each circuit is an
unexpanded specification of one polynomial. All named registers abbreviate earlier
polynomials and add no unknowns. Squaring costs one multiplication, and multiplying
by a fixed numeral is included in the operation count.

## Provenance

Comparison snapshot: ProveIt commit `f4d8db99e060339f3306a04d507c35bc1d0d68c5`.
The principal arithmetic source is the incoming Weak_Carriers_and_Shared_Signs
packet. `source/POWERED_PROOF.md` retains the supported-modulus interpolation proof
from the incoming Round15 package's preserved Round14 source. `SOURCE_LEDGER.json`
records every retained source byte hash. Historical source prose may refer to its
former archive layout; those paths are provenance, not new runtime requirements.

The circuit emitter utility, sparse-polynomial auditor utility, coefficient reader,
and coefficient replay script are credited adaptations or unchanged copies of the
Weak_Carriers packet; the paired final norm schedule and absorbed81 guard scale are
credited to Round15. The new transformation and its proof are identified in
`PROOF.md`. Inherited notices remain under `source/` and `UPSTREAM_NOTICE.md`.
AI assistance was used in developing and checking this component.
