EXACT OBSERVATION ORDER FOR FABIUS CONDITIONING
1 October 2026

Result
For common exponentially tilted uniform coordinates with divisible caps, an earlier observation mask deterministically reproduces a later coordinatewise mask by taking residues modulo the later caps. The same map works under every integrable total-sum reweighting. This gives exact finite-parameter Blackwell and convex-divergence comparisons, including overlapping masks and countably many observations.

The report constructs a unique weakly continuous exact-sum conditional law on every interior sum value and proves the same comparison there. Equality is treated separately; nonconstant periodic reweightings can give equality. In the reciprocal-integer Fabius model with the standard phase convention, the earlier-versus-later prefix overlap ordering is strict for every n>=3 and 1<=m<n.

Scope
The cap divisibility assumption is essential to the exhibited residue map. This is not a theorem for all cap ratios or a complete sharp-rate classification of arbitrary observation masks. Exact-conditioning endpoints are not prescribed. The equality characterization for likelihoods is for dominated reweightings; full-configuration exact conditioning may be singular. Classical integer/fractional exponential independence and Blackwell comparison principles are explicitly credited. The proof is ordinary mathematics, not externally refereed or Lean formalized.

Contents
- exact_fabius_mask_order.pdf: seven-page research report
- exact_fabius_mask_order.tex: complete editable proof source
- SOURCES.txt: pinned repository source and primary literature
- checks/: standard-library exact regression programs, results and logs
- validation.json: mathematical verification scope and PDF quality record
- SHA256SUMS: checksums

Verification
Run python3 checks/run_all.py. No third-party Python packages are required.
The grid checker verifies 6,144 involutions, 205 mask comparisons, 41 nonconstant periodic-equality cases, 1,107 exact-total mask identities, and 30 common-observation identities. The separate continuous slice checker proves 775 rational moment identities, including internal sum breakpoints, and checks a strict total-variation example exactly. These finite checks test accounting and formulas; the universal continuous proof is in the report.

PDF build
Run bash build.sh with a standard TeX Live installation providing pdfLaTeX, Latin Modern, AMS packages, geometry, microtype, hyperref, xurl and booktabs. Three passes resolve references.
