# Compact proof certificates for ZFC consistency

Round 13, 24 October 2026. Prepared for Vladimir Reshetnikov.

This package contains explicit fixed Diophantine equations, ordinary mathematical proofs, actual coefficient payloads, and offline exact checks. It does not prove consistency, claim a global minimum, or supply a new end-to-end Lean/Rocq certificate. The report states the exact inherited calibration needed for the no-zero/Con(ZFC) equivalence.

## Start here

Read ConZFC_Compact_Proof_Certificates_Round13_2026-10-24.pdf. The same-named .tex is the complete editable source, with no external section inputs. PDF rendering is optional and is not part of mathematical verification.

The selected direct quartics are:

- direct/projected: 1859 nonnegative integer variables, degree 4, 1581 rows, 12275 collected monomials, height 63924066.
- direct/projected_integer: 3179 unrestricted integer variables, degree 4, 2074 rows, 23157 monomials, height 63923766.
- direct/forward: sparse alternative, 2560 nonnegative variables, degree 4, 2217 rows, 11074 monomials, height 63923744.
- direct/projected_signed_template and direct/projected_guarded_integer are required compilation intermediates, not additional selected endpoints. The former has mixed coordinate domains. The old 2170/4087 checkpoint payloads are omitted; the mathematical derivation is retained.

The new radicals12/integer12_degree2048.json has 12 unrestricted integer variables, exact degree 2048 and 233 live binary operations. Its universal degree proof includes an explicit positive leading monomial coefficient. It composes the supplied full-residue interpolation theorem with coprime quintic carriers and fixed-prime radical separation.

The other radical graphs use unrestricted integers: 13/1072/192, 14/378/145, 15/172/123, 15/170/134, 16/98/138, in the order variables/degree/live binary operations.

The ten-integer norm graphs have operations/degrees 467/1245324, 470/1179788, 473/1114252, 507/1080888. They preserve the corresponding pinned parent polynomials exactly. Degree 1080888 is proved minimal only under arbitrary polynomial translations of the final coordinate with the stated short-guard prefix fixed.

The primary comparison is the frozen ProveIt commit 7e533c33819ee1f703b69f2778a767cdc069940d. It is not a claim that the repository or the mathematical frontier has stopped changing. Different domains, degrees, coefficient heights and operation costs are not collapsed into one unspecified measure of simplicity. The late_review directory records additional incoming comparisons and credits the projection/sign-normalization ideas used in the final composition. Its separate original archives and nonportable checkers are not bundled or included in the offline-replay claim.

## Offline verification

Requirements: Python 3.12 or later and SymPy (tested with Python 3.12.14 and SymPy 1.14.0). The release does not access the network or execute downloaded upstream code. On a machine with these dependencies installed, run from this directory:

    python verify.py

Optionally save a new timing receipt outside the release directory:

    python verify.py --report ../my-round13-replay.json

The optimized driver is also supported:

    python -O verify.py --report ../my-round13-optimized-replay.json

The driver authenticates all release files, copies the package to a fresh temporary directory, and executes normal and optimized checks there. It leaves the release unchanged. Failure exits nonzero. A successful receipt records the actual suite inventory and times. Python optimization must not remove the mathematical checks.

There are 24 top-level invocations, not 24 independent theorems:

1. The direct clean rebuilder invokes five builders in each mode and compares all 26 output JSON files per mode (52 comparisons).
2. The direct independent audit wrapper runs five audit/control jobs in each mode (10 internal invocations).
3. Seven ordinary component jobs run in each mode: architecture check/rebuild, radical rebuild, radical checks, centered identity, second radical audit, norm rebuild, norm checks.
4. A second independent norm audit runs in each mode.
5. Three twelve-integer programs (deterministic rebuild, arithmetic checks, independent exact audit) run in each mode.

The architecture check rebuilds three selected matched alternatives in each mode. The radical rebuilder compares all five graph files and its metrics file; the norm rebuilder compares all four graph files. The polynomial expansions, norms, sign certificates and actual coefficient degree witnesses are checked exactly. Signed modular samples and deliberate corruptions are supplemental diagnostics. The release checker does not run a bounded search for zeros of any consistency polynomial.

## Contents and dependency boundary

- direct, direct_audit and late_direct_audit: selected literal quartics, raw circuits, every residual, affine restoration, radius and sign certificates, all local builders, independent exact checks, and inert direct-calculus/Pell calibration sources.
- architecture: proofs of the radius and all-forward ideas and fully reproducible negative-CRT/factorial-carrier benchmark alternatives. These benchmark counts are not the final recommended minimum.
- radicals and radicals_audit: five complete norm graphs, six actual fixed coefficient payloads, parent five-row system, inherited ordinary proof/calibration sources, exact universal norm checks and degree certificates.
- radicals12 and radicals12_audit: the complete twelve-integer quintic-carrier equation, all fixed numerals, the inherited full-residue interpolation and normalized signed-kernel proofs, exact leading coefficient, and independent checks.
- norm and norm_audit: four shorter exact graphs, twelve actual fixed integer leaves and finite recipes, exact parent graphs, the fixed-prefix translation lower bound and independent audits.
- review: frozen-source comparison records. Their historical file paths identify the sources inspected in that earlier review, not runtime dependencies of this release. The release does not claim to re-fetch or re-execute the entire upstream repository or every historical archive.

Every runtime dependency is included except the stated Python/SymPy and optional LaTeX software. Inert Lean files retain their original imports and notices as provenance; the entire external Lean project and its transitive imports are not bundled or claimed to be rebuilt. The inherited unbounded calibration is ordinary mathematics, not established by finite byte reconstruction.

MANIFEST.sha256.json hashes every release file except itself. Component manifests retain their narrower producer/auditor scope. RELEASE_REPLAY.json is a recorded clean-copy replay of the final mathematical payloads and programs. The subsequent clean-extraction receipt is kept alongside the delivery, outside the immutable ZIP; a fresh one can be generated with the --report option above. A receipt is not a proof of a universal arithmetic theorem. Sources preserve their own licenses and notices.

## Rebuild the report

With an ordinary TeX Live or MiKTeX installation containing article, lmodern, AMS math, mathtools, booktabs, longtable, geometry, microtype, enumitem, fancyhdr, hyperref and xurl, run:

    python build_report.py --output ../round13-render

This does not alter the release. PDF byte equality is not claimed across different TeX distributions; mathematical graph rebuilds are byte-exact.
