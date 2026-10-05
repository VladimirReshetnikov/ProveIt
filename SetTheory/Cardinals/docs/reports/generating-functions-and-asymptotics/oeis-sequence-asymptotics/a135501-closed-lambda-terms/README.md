# Report 110 — All logarithmic orders for closed lambda terms

This local, self-contained research package proves every fixed inverse-logarithmic order in the logarithms of unrestricted closed lambda-term counts OEIS A135501 and A220894, with a controlled threshold inverse. It does not prove a multiplicative equivalent, an amplitude, or a full multiplicative transseries. The proofs are ordinary analytic proofs, not Lean formalizations or external peer review. No priority claim is made.

## Main files

- `report110.pdf`: final report
- `report110.tex`: complete, standalone mathematical source
- `check.py`: exact, standard-library finite checker, independent of floating-point diagnostics
- `data/`: four exact JSON fixtures, covering total counts through size 30, reduced-height counts, coefficients, and check coverage
- `validation/`: reader-facing checker, independent implementation review, and corruption records
- `manifest.json`: strict SHA-256 inventory, including the final PDF and all distributable files except the manifest itself
- `build.py`, `integrity.py`, `corruption_test.py`, `seal.py`, `replay.py`: reproducible package tools

The report gives the explicit first six forward polynomials and a recurrence for every fixed order. The exact checker generates forward coefficients through order 8 and inverse coefficients through order 6 via independent logarithmic and exponential formal-series identities. It verifies integer recurrences, both size conventions and parity, reduced shape counts and depths, rational radical bounds, exact spine convolution inequalities and moments. All guards remain active with `python3 -O`.

The analytic theorem is not inferred from these finite checks. All packaged mathematical checks use exact integer/rational arithmetic and require neither SymPy nor floating-point diagnostics.

## Reproduce locally

Python 3.9 or newer is required. The checker uses only the standard library.

```
python3 integrity.py
python3 -O integrity.py
python3 check.py
python3 -O check.py
python3 corruption_test.py
python3 build.py
python3 integrity.py
```

The build requires pdfTeX/pdfLaTeX plus the TeX packages listed in `report110.tex`. It performs two clean builds under fixed metadata and requires byte-identical PDFs. It never installs software or accesses the network. Overfull boxes, unresolved citations, and unresolved references fail the build.

The archive can be replayed from a fresh directory, including the final PDF:

```
python3 replay.py --archive report110_source_checks.zip --out /tmp/report110-fresh
```

The destination must not exist. Replay validates the exact archive inventory, extracts, runs normal/optimized integrity and exact mathematical checks, runs the corruption campaign, rebuilds the PDF, and verifies its bytes against the archived PDF. The output directory receives a structured replay result and step logs. Its mutation campaign uses disposable copies; mathematical mutants bypass the manifest deliberately, ensuring failures are real mathematical guards rather than hash mismatches.

`python3 check.py --write-data` is an explicit maintainer command to replace fixtures; the normal command only verifies them. `python3 integrity.py --generate` explicitly regenerates the manifest. `python3 seal.py` creates the deterministic source/checks ZIP after verification. Do not regenerate a received manifest to make a verification failure disappear: retain the original archive and investigate.

## Provenance and limits

The article contains the complete proof, including the coarse localization majorant. The exact bound is

M_r(N) - O(log N) <= log A_s(n) <= M_r(N) + O(R_r(N)),

where r=s+1, N=n+1, t=W(4eN exp(-r/2)), M_r=N/r*(t-2+1/t)+N/2, and R_r=N^(1-1/(3r))*(log N)^(-2/3+1/(3r)).

All theorem constants and onset thresholds are asymptotic, not explicit certified numerical bounds. The bibliography credits the located primary sources, including Bodini–Gardy–Gittenberger–Jacquot (2013), David et al. (2013), and fixed-parameter 2015/2018 work. The checked literature comparison is bounded. No downloaded literature PDFs or third-party author code are redistributed. No earlier report was modified and no artifact was published or uploaded.

The checksum manifest is an integrity inventory, not a signed authenticity certificate. Generated build/QA directories, local research-input storage, Python caches, the ZIP container, and its external final checksum file are intentionally outside the payload inventory. Every payload file actually included in the ZIP is manifested except `manifest.json` itself; the external final hash list includes the manifest and archive.
