# A cubic supercongruence for OEIS A348410

Research note prepared for Vladimir Reshetnikov, 19 September 2026.

## Main result

For integers u,v, define

    A_{u,v}(n) = [x^n] (1-x)^(-u*n) (1+x)^(-v*n).

For every odd prime p and positive integer N divisible by p, the manuscript proves

    v_p(A_{u,v}(N) - A_{u,v}(N/p)) >= 3*v_p(N) - epsilon_p,
    epsilon_3 = 1, epsilon_p = 0 for p >= 5.

Taking (u,v)=(2,1) proves the supercongruence recorded by Peter Bala in
OEIS A348410. No condition that the remaining multiplier be coprime to p is needed.

The proof is in Sections 2–4 of `article.pdf`. It is an elementary formal-power-series
argument over rational numbers with denominators prime to p. It does not depend on
numerical verification, the algebraic generating function, or a framing theorem.

The manuscript also derives a cubic Möbius-transform denominator restriction, proves
sharp uniform small examples, and gives explicit period-three counterexamples.
Appendix A audits the precise statements in arXiv:2104.10754v1: its explicit
prime-by-prime framing conclusion and weighted harmonic assertion fail on the
examples displayed there. This does not assert that a single bad prime refutes an
unspecified finite-exception version.

## Files

- `article.pdf`: 14-page manuscript.
- `article.tex`: complete, self-contained LaTeX source, including bibliography.
- `bibliography.bib`: the same reference metadata, supplied separately for reuse.
- `code/verify.py`: exact-arithmetic checks; Python 3.9+; standard library only.
- `code/symbolic_checks.py`: optional polynomial certificates using SymPy.
- `requirements-optional.txt`: the tested SymPy version.
- `data/`: complete CSV records, machine-readable summaries, and execution logs.
- `oeis_proposed_annotation.txt`: mathematical annotation draft, not submitted.
- `source_audit.md`: source dates, versions, and the scope of the status check.
- `SHA256SUMS.txt`: checksums of the delivered files other than the checksum file itself.

## Reproduce the checks

From this directory:

```text
python code/verify.py
```

The command generates its results in `data/`. A different index cap is supported:

```text
python code/verify.py --max-n 20000
```

The saved default run used `--max-n 5000`, Python 3.13.5, and exact arithmetic.
It passed 229 original-sequence congruence tests and 2,048 parameter-family tests,
as well as independent coefficient computations and checks of the proof's local
lemmas. The largest original-sequence index in that sweep was 4913. Complete
ranges and counts are in `data/verification_summary.json` and the script.

For the optional polynomial certificates:

```text
python -m pip install -r requirements-optional.txt
python code/symbolic_checks.py
```

SymPy is not needed for the main checker or the supercongruence proof. The optional
run verifies that the generating-function resultant equals the displayed quartic
exactly, and that its parametrized substitution has identically zero numerator.

In PowerShell, the corresponding script path can also be written
`python .\code\verify.py`.

## Build the PDF

With a TeX distribution containing the packages used in the source:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `pdflatex article.tex` three times to resolve the contents and
cross-references. The source uses the standard NewTX text/math packages. The
bibliography is inline, so BibTeX is not required. No external graphics are used.

## Research status

The claim about open status is specifically that the OEIS entry still displayed
Bala's supercongruence as a conjecture on the inspection date. Related generating-
function work is acknowledged; exhaustive historical priority is not established.
The document presents a complete proof but has not been independently refereed or
formalized in a proof assistant. The computations are checks, not a substitute for
the universal proof. No OEIS edit or external communication was performed.
