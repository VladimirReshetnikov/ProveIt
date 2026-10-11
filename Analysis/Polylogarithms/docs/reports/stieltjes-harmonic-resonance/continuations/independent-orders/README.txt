INDEPENDENT ORDERS AND EXACT REDUCTIONS IN POLYLOGARITHM–ZETA CALCULUS
ProveIt research continuation, 11 October 2026 (UTC)

READING AND BUILDING

Independent_Orders_and_Exact_Reductions.pdf is the complete article.
Independent_Orders_and_Exact_Reductions.tex is its standalone source.
article.tex, preamble.tex, sections/, and references*.tex are the modular
source from which the standalone file is generated.

The source snapshot is ProveIt commit
5a790187c8e186e41e2b990b4941cb7a1a3c7b6b.
The provenance directory contains the exact archive inventory and hashes.
No source repository is needed to compile this package, and no repository
changes or pushes were made as part of this delivery.

To regenerate the standalone TeX and PDF:

    python3 code/build.py

Requires a TeX distribution providing pdflatex (or lualatex), Latin Modern,
AMS mathematics, mathtools, mathrsfs, geometry, hyperref, bookmark,
microtype, xurl, booktabs, longtable, enumitem, fancyhdr, and standard
graphics/color packages. There is no shell escape or network dependency.
The build script uses three passes and records warnings in results/build.json.

To regenerate only the standalone TeX:

    python3 code/build.py --flatten-only

MATHEMATICAL CONTENT AND CLAIM BOUNDARIES

1. Entire Hurwitz interval functions with independent spectral indices.
   The one-endpoint function is exactly the interpolant of Ihara,
   Nakamura, and Yamamoto (2025), and is explicitly credited as such.
   The article supplies an explicit prefix-residue proof and develops
   two-endpoint composition, shifts, Gamma generating functions,
   Stieltjes jets, nonpositive-inner reductions, and normalized primitives.
   This answers the analytic-normalization component of Exact Identities
   Question 8; the requested smallest Gamma-separated kernel remains open.

2. Every admissible cubic Tornheim direction is reduced to ordinary
   zeta derivatives plus the diagonal coordinate Omega and an explicit,
   absolutely convergent logarithmic Gamma series kappa. Exact cyclic
   and conic families eliminate kappa. This is a finite spanning result,
   not arithmetic independence or ordinary-constant closure.

3. Arbitrary weighted colored sums with mixed integral inner orders have
   a finite nested-polylogarithm normal form with one free complex outer
   order, positive remaining indices, a preserved cumulative alphabet,
   and a constructive depth bound. Repeated colors are included. The
   theorem answers Question 11 of the directional-zeta report. All
   Laurent constants at nonpositive outer orders have finite local
   formulas; higher regular coefficients may need a global remainder.
   Explicit triple identities include an ordinary convergent zeta value
   and a complete Bernoulli pole classification.

4. Equality on all sufficiently large integer samples implies equality
   of finite power–logarithm germs. This gives the complete finite
   single-centre criterion for any number of twists, answering the
   sampled-identity question in the mixed-spectral report. It does not
   assert independence of individual special values.

The short Gaussian S6 and revised S8 candidates remain conjectural.
An incomplete bounded S6 search is documented separately. It yielded
neither a membership certificate nor a nonmembership conclusion.

REPRODUCIBLE CHECKS

Install the Python packages in requirements.txt if needed, then run:

    python3 code/verify_all.py

The runner executes exact coefficient/algebra checks and independent
high-precision diagnostics, writing separate JSON records and logs to
results/. The analytic proofs in the article establish the unrestricted
theorems. Finite checks do not replace those proofs, and floating-point
residuals are not interval-certified error bounds.

The exploratory S6 search is deliberately excluded from this runner.
Its exact generator, target, finite-field program, and unfinished scope
record are in exploratory/s6/. Large generated matrices and binaries
are not shipped. Read its README.txt before reproducing that experiment.

EXACT MIXED-ORDER COMPILER

    python3 code/reduce_mixed.py --input examples/mixed_input.json \
        --output results/example_reduction.json

An input has integer "orders", exact nonzero "colors" in the closed unit
disc, and positive integer "weights". For example:

    {"orders":[1,1,-2],"colors":["1/2","1/2","1/2"],"weights":[1,1,1]}

The result is a finite sum of terms Li_(C+offset,inner...)(colors...).
The output stores both cumulative and relative colors. Cumulative colors
govern convergence; relative colors may have modulus greater than one.
Every inner output order is positive. The outer order C remains free,
so its derivatives are legitimate. The fixed input integers must not be
treated as free spectral differentiation variables in the final formula.

The compiler uses exact SymPy expressions and rejects floating-point,
symbolic, zero, or uncertifiable-domain colors. Large algebraic root
alphabets can be expensive; no optimal complexity claim is made.

INTEGRATION AND PROVENANCE

integration/INTEGRATION.txt maps the self-contained sections to the
existing research questions and gives suggested status language.
integration/claim_ledger.json records proven, recovered, partial, and
unresolved statuses. Other integration notes record independent reviews,
not formal proof certification. Section 6 of the article contains the
proposed source corrections and qualifications.

The SHA256SUMS file checks package integrity:

    python3 code/verify_manifest.py

The PDF visual audit records page coverage and geometry in results/;
temporary page images are omitted. To regenerate them, use
code/inspect_pdf.py with a separate preview directory.

The package makes no literature-wide priority claim for every derived
specialization. It distinguishes classical inputs, a recovered published
theorem, advances relative to the pinned repository, and still-unreduced
analytic coordinates throughout.
