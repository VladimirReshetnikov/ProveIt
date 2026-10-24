# Fully centered low-degree consistency polynomials

New ordinary arithmetic endpoint:

- `equation.json`: **15 unrestricted integers, exact degree 48, 108 live operations**. The fully centered first-root carrier improves the predecessor's 15/56/110 endpoint in both degree and gates. Full inverse zero-set maps are in `PROOF.md`.

Credited evaluator adaptation:

- `twelve/equation.json`: **12 unrestricted integers, exact degree 500, 139 live operations**. This is pointwise the same polynomial as the predecessor's 12/500/148 endpoint, evaluated through an inherited compact norm schedule. It does not claim a new twelve-variable semantic reduction or invent the norm identity.

`specification.json` files give complete ordered scalar abbreviations; `equation.json` files charge every binary arithmetic gate. All fixed numerals are bound to the complete authenticated payloads in `coefficients/`. `section.tex` and `section12.tex` are report-ready proofs; `standalone.pdf` is the three-page proof of the new 15-variable endpoint.

The source closure is retained once at `../prior/ZFC_Diophantine_Coprime_Projection/`, never rewritten. The new 15-variable result reduces to its prior 15-variable theorem, which supplies the normalized native/compiler/refutation chain. The twelve-variable optimization is pointwise identical to its pinned prior polynomial. No consistency proof, global minimality, new encoded object-language ZFC derivation, or new end-to-end proof-assistant certificate is claimed.

## Reproduce

From this directory:

    python build.py
    python review/audit.py
    python -O review/audit.py
    python twelve/build.py
    python twelve/review/audit.py
    python -O twelve/review/audit.py

The builders use the Python standard library. The exact auditors require SymPy. They use explicit exceptions, not assertions, and pass under optimized Python. The separate independent review under `../review/lowdegree/` audits the new proof and literal DAG without importing these builders. The delivered PDF was compiled with pdfLaTeX and all three rendered pages were visually inspected.
