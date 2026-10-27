# Asymptotic improvement analysis for the October 2026 3 SAT preprint

**Outcome: no stronger unrestricted 3-SAT bound has been established.**
**This archive contains no faster 3-SAT solver, no full implementation of Appendix D, and no new formal certificate.** The original scripts check finite algebra/combinatorics and artifact/source integrity only.

The target is to beat the paper's strongest Appendix D guarantee, not merely
replace the reviewed older Lean loglog-squared endpoint with the paper algorithm.

Start with `report/report.pdf`; editable sources are `report/report.tex` and its
included TeX fragments. The report distinguishes published claims, elementary
proved restricted barriers, unproved compression interfaces, and finite tests.
It does not certify the paper's ETH conclusion or all Lean dependencies.

## Mathematical contents

* The pinned paper claims general bit time
  `poly(n,m) * 2^{O(n loglog(n) / sqrt(log(n)))}` and polynomial space.
* For fixed density it already claims
  `poly(n,m) * 2^{O(n / sqrt(log(n)))}`.
* Exact scoped proofs explain why bare weighted-budget tightening, taper retuning,
  or Newton modes do not automatically improve the existing exponent.
* A **missing** degree-preserving recursive interface would imply the intermediate
  general exponent `O(n sqrt(loglog(n)/log(n)))`.
* A **missing** uniform linear-wire compression interface would imply the stronger
  general exponent `O(n/sqrt(log(n)))`.
* Neither interface has been constructed. Neither conditional consequence is
  advertised as a new SAT algorithm. The support-entropy construction in
  `research_decision/findings.md` is an existence/barrier example, not a solver.

## Provenance and evidence

Source pin: `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` of `openai/math`.
The report contains immutable source links. `source/manifest.json` and
`audit/lean_selected/manifest.json` identify fetched files and fingerprints.
The full 16 MB Lean tree listing and the full Lean repository are intentionally
not included. There was no Lean build, transitive axiom audit, benchmark of the
paper algorithm, or execution of upstream repository programs.

The original paper source, PDF, README and repository license are preserved in
`source/`. See `source/REPOSITORY_LICENSE` for the repository's Apache 2.0 terms.
Research notes, checks and report files outside `source/` are newly authored for
this analysis; selected Lean files are identified separately by their manifest.

## Rebuild and finite checks

Dependencies: Python 3; Bash; pdfTeX/pdfLaTeX; Latin Modern and AMS fonts;
`amsmath`, `amsthm`, `mathtools`, `geometry`, `microtype`, `enumitem`, `hyperref`;
Poppler `pdftotext`, `pdftoppm`, `pdfinfo`. The build script explicitly uses the
installed Debian-style system TeX paths; adapt those paths for other systems.
It constructs a local font map and format, disables shell escape, and never
executes or compiles the preserved upstream source. It uses no network and does
not install dependencies. Pixel equivalence is expected in the documented local
toolchain, not guaranteed across arbitrary TeX/Poppler versions.

From an unpacked bundle:

```
bash scripts/build_report.sh
python3 audit/check_taper_newton.py
python3 -O audit/check_taper_newton.py
python3 scripts/check_report_lemmas.py
python3 -O scripts/check_report_lemmas.py
python3 research_runtime/validate_toy_claims.py
python3 -O research_runtime/validate_toy_claims.py
```

The PDF rebuild is written under `build-report/`; it does not overwrite the
sealed `report/report.pdf`. The tests use exact integer/rational arithmetic and
explicit exception guards, not removable `assert` statements. They are finite
algebra checks, not a proof assistant or full SAT implementation.

## Sealed archive verification

Keep the downloaded ZIP intact. From an unpacked copy:

```
python3 scripts/verify_bundle.py /path/to/downloaded.zip
python3 scripts/replay_archive.py /path/to/downloaded.zip
python3 scripts/negative_integrity_controls.py /path/to/downloaded.zip
```

Verification checks the exact file inventory, sizes and SHA-256 digests before
extraction. Replay rebuilds the report, compares extracted text and every rendered
page pixel, and reruns finite checks in normal and optimized Python. Negative
controls require rejection of corruption, removal, unexpected files, duplicate
paths, and path traversal. The manifest establishes internal consistency only;
it is not a digital signature. Use the separately supplied complete ZIP hash to
identify the intended release. Generated replay files are not original evidence.

To recreate a deterministic ZIP from unmodified payload files:

```
python3 scripts/build_bundle.py rebuilt.zip --validation-summary
```

The report and bundle are intended to record a useful research result honestly:
what was established, what failed within a specified method, and exactly which
new lemma would be needed to complete a genuine stronger-bound claim.
