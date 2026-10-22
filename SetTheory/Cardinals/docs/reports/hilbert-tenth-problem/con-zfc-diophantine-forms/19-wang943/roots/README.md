# Twelve-positive-variable root amalgamation

The final preferred variable-count result is in `ROOT12_SATURATED_PROOF.md`.
The earlier `ROOT12_PROOF.md` is preserved as a derivation record.

| Artifact | Positive variables | Operations | Exact degree |
|---|---:|---:|---:|
| `root12_saturated_product.json` (preferred) | 12 | 139 = 93M+46A | 1257 |
| `root12_saturated_system.json` | 12 | 135 = 91M+44A | residuals 7,2,1248 |
| `root12_product.json` | 12 | 140 = 94M+46A | 1545 |
| `root12_scaled_y_product.json` | 12 | 140 = 94M+46A | 1625 |
| `root12_system.json` | 12 | 136 = 92M+44A | residuals 7,2,1536 |
| `root12_scaled_y_system.json` | 12 | 136 = 92M+44A | residuals 7,2,1616 |

The final preferred construction applies rational auxiliary Pell saturation
before recovering gamma. It needs neither a restriction on i nor a scaled
auxiliary root, and its completeness preserves the original witnesses.
The older primary construction restricts the old strong multiplier to i=Hj and
uses a finite Pell-unit period in its completeness proof. The alternative
compresses the scaled auxiliary root r=(Q-1)y, preserves every old positive
strong multiplier, and uses the rational auxiliary Pell saturation lemma.
Neither variant claims a degree or circuit-cost improvement over the
13-positive-variable products. The improvement is exactly one fewer
positive variable, with the costs shown above.

All displayed registers are computed expressions, not extra unknowns.
The norm is emitted as a literal finite circuit, and its soundness proof
explicitly excludes irrational/spurious resultant branches. Recovered
main and auxiliary root signs are handled by the signed-domain argument.

The compiler coefficients and literal ZFC-recognizer calibration remain
external dependencies. Consult the selected coefficient binding in each
JSON rather than mixing ports from different recipes. In particular the
MF input is the shifted MF_source, never the native mask.

Reproduce the locally authored arithmetic checks with:

    python build_root12.py
    python check_root12.py

The checker requires the already available NumPy package. No repository
program is imported or executed. Upstream JSON is read only as arithmetic
data. `SOURCE_PINS.json` records fetched proof/circuit inputs, while
`ROOT12_TEST_RESULTS.json` records independently evaluated quotient-algebra
norms, finite-field degree diagnostics, liveness, and synthetic kernel
witnesses. These finite checks do not prove the inherited compiler theorem,
machine calibration, or Con(ZFC).

Independent mathematical reviews are in the sibling audit directory,
particularly `FINAL_WEIGHTS_AND_INTEGER26_AUDIT.md` and
`RATIONAL_AUXILIARY_PELL_SATURATION.md`.
