# Report 221

**Fixed couple ménage rows: Exact differences, concavity, uniform expansions and inverse enclosures**

The PDF is the full article. It proves the two conjectures displayed in A332709, all discrete-concavity and log-concavity equality cases, a uniform all-orders row expansion, an exact all-row total-variation identity and sharp asymptotics, and carefully scoped inverse-model/range/threshold results.

The fourth-column A258667 refinement is compatible with its posted leading-equivalence theorem. No certified numerical onset for inverse rounding or inverse-envelope constants is provided. No global historical-novelty claim is made. SOURCES.md records the bounded literature checks and access limitations.

## Files

- Report221.pdf and Report221.tex: article and editable source
- code/menage.py: exact counts, exact rational coefficient engine, exact total variation, guarded public APIs and cap-independent integer serialization
- code/check_exact.py: deterministic exact tests and negative controls
- code/diagnostics.py: high-precision floating-point diagnostics, explicitly noncertifying
- receipts/: exact normal/optimized/low-digit-cap receipts, separately labeled diagnostic receipt
- source_pins.json and SOURCES.md: inspected-source fingerprints, URLs and historical scope
- build.py, requirements.txt and MANIFEST.sha256: portable build and integrity information

The ZIP contains no private notes, private review reports or third-party paper PDFs. It requires no network access for reproduction once dependencies are installed.

## Reproduce

Requirements: Python 3.10 or newer; for full reproduction, mpmath 1.3.0; TeX Live with pdfLaTeX and the standard packages used in Report221.tex (including Latin Modern, AMS, mathtools, geometry, microtype, booktabs, xurl, hyperref, enumitem and fancyhdr). Poppler is useful for optional visual inspection but is not needed for the build. The exact tests require only the Python standard library.

From the extracted directory:

    python3 code/check_exact.py
    python3 -O code/check_exact.py
    PYTHONINTMAXSTRDIGITS=640 python3 code/check_exact.py
    PYTHONINTMAXSTRDIGITS=640 python3 -O code/check_exact.py

These four outputs must be identical. All correctness checks remain active under optimization. The 600-row integer serialization test exceeds 640 decimal digits and preserves the caller's global digit limit. Public functions return exact Python integers/Fractions; use integer_decimal, parse_integer_decimal and fraction_decimal when serializing large results independently of Python's configurable limit. parse_integer_decimal is intended for trusted computed output; it imposes no length limit, so callers must bound untrusted input separately.

For the complete build:

    python3 -m pip install -r requirements.txt
    python3 build.py

The build runs all four exact test modes, regenerates the separate diagnostics, compiles the PDF to stable references, checks for unresolved references/missing glyphs/overfull boxes, writes SHA-256 manifests and creates Report221.zip. It makes only local output changes. It uses writable isolated TeX caches, no shell escape, a fixed epoch and fixed ZIP timestamps/modes.

Additional modes:

    python3 build.py --checks-only
    python3 build.py --pdf-only
    python3 build.py --package-only

A full `python3 -O build.py` exercises the same workflow. To check relocation and reproducibility, extract Report221.zip into a fresh directory, rebuild there and compare the resulting PDF, ZIP and receipts with the originals. Exact receipts are platform-independent. Identical PDF bytes require the same TeX distribution/fonts; diagnostics use the pinned mpmath version. Archive determinism means identical member bytes yield identical archive bytes; it does not promise identical TeX output across different TeX installations.

## API domains and limits

- fixed_count(n,s): n >= 3, 1 <= s <= n-2
- triangle_count(n,k): n >= 3, 3 <= k <= n
- adjacent_difference(n,k): 4 <= k <= n; includes the separate zero center case
- circular_count(n): n >= 0; signed values 1,-1,0 at n=0,1,2
- line_count(m): m >= 0; line_count(0)=1 is not a center difference
- row_series(order,distance): nonnegative order, positive distance q; distance=None selects the stabilized interior coefficient regime
- circular_series, line_series and tv_series: nonnegative finite order
- exact_total_variation(n): n >= 3, computed directly as a Fraction

Boolean and floating-point indices are rejected. No finite upper domain is imposed, but runtime and memory grow with requested size/order. The default suite is deliberately finite. Numerical model evaluation in diagnostics.py is not a certified inverse API and may reject points outside its positive-factor domain.

The proofs establish all finite-order asymptotic statements independently of the tests. Finite tests are corroboration and implementation checks, not universal mathematical proofs.
