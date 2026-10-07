# Report 201

Harmonic perturbations of power-weighted Dyck moments

Absolute amplitudes and polynomial-weight asymptotics

4 October 2026

## Main results

The article derives the full absolute amplitude of Z_n(h^p) for every fixed real p>0, with a relative O_p((log n)^(-2)) remainder. The proof combines a uniform endpoint occupation estimate with the fixed Freud-weight leading-coefficient theorem, directly inspected in Claeys-Krasovsky-Minakov equation (2.3), which explicitly restates Kriecherbauer-McLaughlin Theorem 1.5. The original 1999 theorem text was not directly inspected. Moment indeterminacy does not affect the finite Jacobi identity for the chosen comparison measure.

Separately, the article proves a relative amplitude theorem for harmonic and parity-harmonic logarithmic changes. A direct interpolated limit-shape argument controls the singular harmonic occupation; Gamma products give absolute amplitudes for every real polynomial of positive degree that is positive at the positive integers. A generalized stability lemma handles an ordinarily convergent residual series with r_h=o(1/h), without assuming absolute convergence. The cubic Dixon and quartic Berg-Valent routes remain independent special-case checks.

Kotěšovec already posted the cubic formulas and the general-p absolute formula on OEIS. This article gives a rigorous route to those known formulas, with the precise source access boundary stated. No first-proof or novelty claim is made. No effective onset, uniformity in p, all-orders raw expansion, or unproved first correction is claimed.

The generic inverse retains a finite-prefix check and inclusive two-ceiling uncertainty o(1/log t). Pure unscaled powers h^p have a separately proved O_p((log t)^(-3)) radius. That logarithmic rate is not transferred to general harmonic/polynomial families, and neither radius gives a computable finite-threshold certificate.

## Files

- `Report201.pdf`: complete article
- `Report201.tex`: self-contained LaTeX source, with bibliography
- `build.py`: deterministic validation, full replay, PDF build, and ZIP creation
- `test_guards.py`: finite package/path/input rejection and bytecode-regression suite
- `requirements.txt`: numerical diagnostic dependency
- `repro/check.py`: exact Dyck/application checks plus optional high-precision diagnostics
- `repro/freud_check.py`: exact Freud normalization/product checks and separate logarithmic diagnostics
- `repro/README.md`: detailed mathematical conventions, finite ranges, and data documentation
- `repro/data/oeis_displayed_terms.json`: inspected displayed OEIS term fields and provenance
- `repro/generated/`: exact check receipt, all moment arrays, separate diagnostics, and hashes
- `repro/freud_generated/`: exact Freud checks, optional numerical diagnostics, and hashes
- `repro/FREUD_REPRODUCTION_RECEIPT.json`: Freud companion replay receipt
- `repro/REPRODUCTION_RECEIPT.json`: finite companion-code replay receipt
- `manifests/source_manifest.json`: source hashes and PDF engine banner
- `manifests/package_manifest.json`: every public member other than this manifest itself

No downloaded third-party paper PDF, private research/audit report, credential, or private filesystem path is included. Public source links are in the article and term fixtures. No network is needed for any reproduction command once dependencies are installed.

## Dependencies and reproducibility scope

- Full build: Python 3.9+ and mpmath 1.3.0; release checked with Python 3.12.14
- Exact data-only mode: Python standard library only
- PDF: pdfLaTeX with T1/lmodern, microtype, geometry, AMS packages, mathtools, booktabs, array, xcolor, enumitem, fancyhdr, and hyperref, with their installed font maps
- The source manifest records the release's exact pdfTeX first-line version banner

Install the optional diagnostic dependency using your normal package manager, for example `python -m pip install -r requirements.txt`. The builder does not install anything. It requires installed `pdflatex`, `kpsewhich`, and, if a private format must be initialized, `pdftex`.

Byte-for-byte PDF replay requires the matching TeX distribution, package versions, and font files. Matching the engine banner is a necessary guard, not a guarantee across arbitrary installations with different package trees. The build itself compares the regenerated PDF bytes and rejects a mismatch. Exact integer/rational checks are independent of TeX. The optional decimal diagnostics are deterministic in the documented mpmath/Python environment but are not interval certificates.

## Full release replay from an actual extracted ZIP

Extract `Report201.zip` into a fresh directory. It contains one `Report201/` root. From that root, use fresh, nonexisting output paths outside the package:

```sh
python build.py --validate-only
python build.py --output ../replay-normal --archive ../replay-normal.zip
python -O build.py --output ../replay-optimized --archive ../replay-optimized.zip
cmp ../replay-normal.zip ../replay-optimized.zip
```

Also compare the regenerated ZIP with the delivered ZIP, using its actual relative location:

```sh
cmp /path/to/Report201.zip ../replay-normal.zip
```

The absolute path above is a placeholder chosen by the reader, not a package dependency. Each normal build validates the source package before work, runs all exact checks and diagnostics, runs the finite guard suite, compiles the PDF in fresh isolated TeX work directories until its bytes stabilize, regenerates both manifests, and compares every public member byte-for-byte against the source release. It then creates an uncompressed ZIP with fixed metadata, ordering, timestamps, and permissions. Byte identity of the archive follows from identical members and this fixed container layout. The generated ZIP has no self-referential hash inside itself; its external release SHA-256 is supplied with delivery.

For maintainers only, `--initialize` creates a new release and manifests from the explicit source allowlist. It intentionally does not claim identity with an earlier release. Ordinary readers should not use it for replay.

Existing destinations are never overwritten by the builder. Source and output directories must be distinct and non-nested; the archive must be outside both. Dangling destination symlinks are rejected as well. The builder does not turn an unsafe output request into permission to modify an existing package.

## Data-only commands

These commands leave the source package unchanged when their output is placed outside it:

```sh
python -S repro/check.py --out ../exact-data
python repro/check.py --diagnostics --out ../all-data
python -O repro/check.py --diagnostics --out ../all-data-optimized
python -S repro/freud_check.py --out ../freud-exact
python repro/freud_check.py --diagnostics --out ../freud-all
python test_guards.py
```

Both companions default to n=256; `--max-n` accepts 48 through 512. The Freud companion also accepts `--norm-degree` from 8 through 24 (default 16). `--dps` sets the optional numerical precision (default 65, at least 45). Exact JSON does not depend on that precision. To recreate the supplied numeric outputs, retain the defaults and mpmath 1.3.0.

All code checks use explicit exceptions, not removable Python assertions. The scripts disable local bytecode generation before loading local modules. The release is also tested with `PYTHONDONTWRITEBYTECODE` and `PYTHONPYCACHEPREFIX` unset, in ordinary and optimized Python modes. The direct standard-library-only regression copies only the checker and its fixture to a temporary location and verifies that the source remains byte-for-byte unchanged.

## Finite exact check scope

The default replay stores 16 arrays through n=256, including all principal cubic/quartic laws, classical comparison families, signed-Dixon normalized moments, and the separate A338634 free-cumulant transform.

It checks 252 displayed moment/source values across 16 entries and 36 displayed A187756 weight values. The fixture records source offsets and signs. No unexamined b-file is claimed as checked.

Other checks include 375 independent walk/first-return/S-fraction comparisons, 27,448 conditional-pair identities, 49 Dixon ODE/Dyck identities through semilength 48, varied-law occupation and primitive-excursion identities, classical Gaussian/secant coefficients, finite rising products, Gamma reductions, and cubic normalization algebra. See `repro/generated/exact_checks.json` and `repro/README.md` for the exact ranges and categories. A test count records finite instances, not distinct theorems.

The separate Freud companion records 760 exact finite instances at its defaults: rational Gamma moments and Hankel norms for integer p=1,...,6 through norm degree 16; positive pivots, S-fraction moment reconstruction, unscaled/normalized telescoping, exact rational rescalings, Gaussian recurrence and classical checks, seven symbolic prefactor/smooth-part identities, and 60 exact first-inclusive crossings. Five integer pure-power arrays are generated through n=256; their hashes are recorded. The optional output has 40 pure-power rows across eight fixed exponents, including p=1/4,1/2,3/2, and 60 inverse diagnostic rows. See the companion README and machine-readable check counts for the finite ranges. These are not proofs of the published Freud asymptotic or effective constants.

## Numerical scope and inverse caution

`repro/generated/numerical_diagnostics.json` is labeled `DIAGNOSTICS_ONLY`. It evaluates profiles, occupation constants, finite products, relative and absolute amplitudes, positive polynomial examples with complex/negative shifts, and Lambert-W centers. These are not interval-certified errors, proofs of convergence, or effective asymptotic onsets.

An exact inclusive crossing is checked separately against all earlier generated values. In particular, at Y=A218221(128), the displayed center is slightly above 128 and its unguarded ceiling would be 129, while the exact first inclusive crossing is 128. The general-family radius is unspecified o(1/log t); the pure-power O_p((log t)^(-3)) radius also has unspecified constants and onset. The code does not invent a computable finite-Y radius. Nearly equal logarithms may round at finite precision, so exact integer comparisons decide the crossing.

## Manifest and guard coverage

Manifests use canonical JSON with explicit path, byte count, and SHA-256 records. The public allowlist excludes undeclared files and directories. Validation rejects duplicate JSON keys, nonfinite JSON values, noncanonical/traversing/absolute paths, bad schemas/types/hash formats, missing/duplicate/reordered records, changed bytes, special files, symlinks, oversized members, and undeclared content. Rejection tests exercise representative cases, deterministic ZIP metadata, existing/nested destinations, and dangling destination symlinks.

The per-file size limit is 16 MiB, sufficient for this finite package. This finite guard suite is not a comprehensive security audit or a guarantee for arbitrary malicious files. It does not replace review of a modified source program before running it.
