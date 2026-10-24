# Four roots with a coprime carrier

Two explicit consistency polynomials in **fourteen unrestricted integers**:

| Literal circuit | Exact degree | Live binary operations |
|---|---:|---:|
| `crt14_degree540.json` | 540 | 160 |
| `crt14_degree568.json` | 568 | 147 |

The incoming fourteen-integer comparison points include degree652/230
operations, degree696/150, and degree792/137. The new degree568/147 point
strictly improves696/150. Degree540/160 gives a lower-degree tradeoff.
No global minimum or worldwide novelty claim is made.

Read `PROOF.md` for the complete formula and proof; `section.tex` is the
corresponding editable article section. All six fixed integers remain the
source34/source71 tuple. Their actual payloads, finite reconstruction,
ordinary calibration texts, and original notices are in `upstream/`.
The original parent remains verbatim; its larger verification artifacts are
retained so its release manifest and proof-dependency records remain useful.

The new idea retains the guard square witness explicitly, combines only four
Pell roots, deletes the now-unnecessary main-root amplifier, and uses one
coprime carrier for both the cubic-scale residue and the main Pell residue.
Centering the four roots lowers the degree; a unit-product finalizer joins
the norm and the guard without squaring the norm.

Run from any working directory:

```
python3 build.py
python3 verify.py
python3 -O verify.py
```

The build rewrites only the two authored circuits. Verification is read-only
unless `--output /path/to/receipt.json` is supplied. It checks every generic
norm coefficient, exact centered-root defects and leading coefficients,
reconstruction of all literal fixed coefficients, graph liveness and binary
operation counts, and finite transcription diagnostics. Successful normal
and optimized receipts are included.

Both equations are existence-equivalent by ordinary mathematics to the
specified normalized signed native kernel. Composing the retained ordinary
native/K215/refutation theorems yields the ZFC-provable no-solution/Con(ZFC)
biconditional. No new end-to-end kernel certificate or exported encoded-ZFC
derivation is claimed. The component proves neither consistency nor
inconsistency. The calibration boundary remains explicitly documented.

New work is AI-assisted research for Vladimir Reshetnikov's ProveIt project,
23 October 2026, Pacific time. The original source licenses and notices are
preserved. `SOURCE_PINS.json` identifies the exact repository snapshot and
incoming parent/comparison archives.
