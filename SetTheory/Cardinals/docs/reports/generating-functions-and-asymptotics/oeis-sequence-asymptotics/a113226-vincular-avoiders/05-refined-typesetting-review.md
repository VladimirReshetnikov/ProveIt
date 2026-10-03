# Report and visual verification

Initial verification 1 October 2026; fresh report/proof comparison and nine-page visual inspection 2 October 2026.

The PDF has nine pages. Every rendered page was opened and inspected, including every page after the final layout changes. Equations, theorem statements, running text, references, page numbers, and cross-references are legible with no clipping or overlap. The long first-saddle exponent is kept on one page. The final TeX compilation has no overfull/underfull-box warnings or unresolved references.

The report faithfully restates the companion proof's exact marking, record/cycle inverse bijection, analytic expansion, complex-uniform contour proof, marking phase gap, both-saddle algorithms, explicit first corrections, Gaussian/local and conditional Poisson laws, and scope limitations. The displayed numerical example is taken directly from the stored validation output. Higher-order programs and exact data are supplied separately.

The accompanying mathematical review is a separate review of the proof, rather than an assertion that visual inspection establishes the mathematics. These checks are not formal verification or conventional peer review.

Final TeX SHA-256: b4fe1a9e86c48cd1534f0da53915adf98022345857d625b7a65e36871f71b252

Final PDF SHA-256: b15521c08d28df34e96f675df9ce85e365b4f76b9d6bb9fcc1c88e173424823e


## Final correspondence check

The fresh check read the complete TeX and companion proof on the hashes listed below. Sections 1–2 agree on both marked statistics, the transfer integral, record cuts and inverse sorting, the cumulant factor m!(m−1)!, and all local singular coefficients. Sections 3–5 agree on the complex contour hypotheses, approximate-circle residual phase, continuously chosen endpoint connectors, marking phase gap, two Gaussian algorithms, b1 and b2, and the interior-density local-count normalization n^(-4/3). Section 6 agrees on the mean constant, positive variance, local limit, conditional and unconditional Poisson corrections, and the summable Cauchy estimate for total variation. The third corrections are supplied by the separate symbolic output rather than displayed in the report. The report's numerical examples match validation.json, including the slow-convergence warning at density 0.2. Its attribution and exclusions preserve the proof's scope.

Fresh PNGs were regenerated from the final PDF using Poppler and all nine were inspected individually. The current PDF was not modified. Page 9 contains the reference list; the proof and conclusions finish on page 8. No missing glyphs, clipped formulas, overlap, or broken equation references were found.

Companion-proof SHA-256: c35244db96cba1e42f338ba86203c8cbf4c6637013b2c1bd1133036ba1613ed8
