# Formal status

| Layer | Status |
|---|---|
| Human mathematical argument | Developed in the PDF, with explicit finite estimates and domain qualifications |
| Exact finite arithmetic checks | Executed; see `evidence/finite_core.json` |
| Analytic numerical regression | Executed, high precision, diagnostic only; see `evidence/numeric_validation.json` |
| Canonical-product tail certificates | Rational theorem bounds plus diagnostic finite evaluation; see `evidence/product_certificates.json` |
| Lean host-level finite core | Scaffold supplied; static audit passed; not compiled in the artifact-building environment because Lean was unavailable |
| Lean analytic interfaces | Explicit certificate structures and theorem dependency plan; not a proof by themselves |
| ProveIt object-language derivations | Target formulas and compilation plan supplied; main analytic derivations remain to be implemented |
| PDF | 54 pages; built, preflight checked, and visually reviewed page by page |

The report deliberately distinguishes a mathematical proof from an executable
regression check, and both from a kernel-checked object-iPRA derivation.
