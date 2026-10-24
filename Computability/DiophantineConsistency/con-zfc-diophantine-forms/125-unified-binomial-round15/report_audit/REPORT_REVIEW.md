# Independent final report audit

Status: **PASS for report content and PDF**. Final archive integrity is checked separately after packaging.

The final 37-page PDF has SHA-256 `fde0bac43c2d8088a651b54a1435dcd568e3a35d17f3209727a306ea7e193fc0`. Every page was rendered and visually inspected. No clipping, overlap, missing glyphs, malformed exponent text, or altered mathematical tokens were found. The final title/contents update and the page-22 spacing correction were separately reinspected; the other 34 pages were pixel-identical to the already inspected build.

A separate clean directory received only the editable TeX sources and packaged build script. Its fresh private TeX format and three-pass build succeeded without overfull boxes or LaTeX warnings in the final log. All 37 rendered pages exactly match the delivered PDF at 90 dpi. Different PDF byte hashes are due to build metadata, not rendered content.

All six complete TeX proof transcripts match their authoritative proof texts after removal of layout/markup and whitespace. Every formula token is retained. The six proofs cover the primary scalar construction, literal norm degree/cost, weak-Y split carrier, its degree/cost, unified-binomial natural architecture, and signed direct compiler. A separate typeset equation reference agrees with those complete definitions.

The report handles the unrestricted integer versus nonnegative and strictly-positive domains separately; states all four degree/cost tradeoffs accurately; and distinguishes exact collected quartic height/support from residual counts and arithmetic-circuit operations. Independent reconstruction verifies every coefficient of the 442-integer and 329-natural quartics, all variables and live nodes, the four literal operation counts, and all six complete fixed coefficient payloads.

The inspected proofs preserve the initial zero/sign cases, extraction before the weak-Y carrier decoding, signed ranks before powered projection, fixed strong-witness interpolation order, actual leading-degree cancellation, and recovery of private Pell witnesses instead of an unsupported pointwise bijection. The report names and bundles the inherited calibration/Pell boundary rather than asserting a newly kernel-checked endpoint. It makes no proof of Con(ZFC), global-minimum, or historical-priority claim. It explicitly acknowledges the already supplied 37-integer giant-coefficient quartic and distinguishes incoming packages from the active public source at commit 45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6.

The omitted 446-integer companion is explicitly labeled an audited comparison, not a packaged endpoint.
