# Report 131: Leafless loopless multigraphs by edges

This package contains the self-contained article, its TeX source, and exact finite checks for OEIS A307316 and A307317. The main results are a polynomial counting sandwich, a refined logarithmic asymptotic, a connected/total ratio, and an implicit threshold inverse with additive O(1) error. A separate elementary theorem gives a relative minimum-degree probability in a labelled exact-total model.

The article explicitly states its classical Wright input and the primary-source verification limitation. It does not prove a relative equivalent A_m ~ H_m and makes no historical priority claim. Finite checks are not certification of an asymptotic theorem.

## Files

- `report131.pdf`: reader article
- `report131.tex`: complete editable source
- `checks/`: standard-library exact verifier, public OEIS table snapshots, fixtures, provenance, and reference results
- `build.py` and `build.sh`: reproducible TeX build with explicit quality gates
- `output_guard.py`: external-only, exclusive-create output guards
- `integrity.py` and `CHECKSUMS.sha256`: closed package inventory
- `test_integrity.py`: selected adversarial tests of the inventory verifier
- `test_output_guard.py`: selected output-rejection tests for build, replay and ZIP utilities
- `repack.py`: deterministic ZIP creation
- `reproduce.py`: immutable replay, fresh extraction, rebuild, and repack checks
- `build-environment.txt`: toolchain versions used for the supplied PDF

The inventory covers every regular file except itself and rejects missing, changed, extra, symlinked, malformed, or unsafely named entries. It also rejects unexpected directories. Hashes establish integrity against an independently retained package hash; they are not a signature or a protection against an attacker replacing the entire verifier and all expected hashes.

## Offline replay

Use Python 3.10 or newer. The finite checks use only the standard library. From this package directory:

```
python3 -B integrity.py
python3 -B checks/verify.py --output /tmp/report131-checks.json
python3 -B -O checks/verify.py --output /tmp/report131-checks-optimized.json
python3 -B test_integrity.py
python3 -B reproduce.py --output /tmp/report131-replay.json
```

The full replay checks normal and optimized execution, validates the reference bytes, tests selected corruptions, builds the PDF twice in separate clean temporary directories, extracts a fresh deterministic ZIP, repeats the checks and builds there, verifies unchanged package contents, and requires byte-identical repacking. Outputs must be outside the package and must not already exist; symlink destinations and ancestors are rejected. Use a fresh filename when rerunning. Temporary work is discarded automatically. Runtime guards use explicit exceptions and remain effective under `python -O`.

To run without a TeX installation, add `--skip-pdf` to `reproduce.py`. Its output explicitly records that PDF reconstruction was skipped. This does not replace the full replay used for the delivered package.

## PDF dependencies and build

The supplied PDF uses pdfTeX and the packages named in the TeX preamble: the standard LaTeX article class, geometry, fontenc, Latin Modern, AMS mathematics/theorems/symbols, mathtools, booktabs, microtype, hyperref, enumitem, fancyhdr, and xcolor. The build also requires the standard Computer Modern and Latin Modern font maps. No dependency is downloaded or installed by these scripts.

```
python3 -B build.py --output /tmp/report131-rebuilt.pdf
```

The script fixes the source date, locale, timezone, PDF date fields and trailer identifiers; generates a clean format; runs three TeX passes in each of two clean directories; rejects overfull boxes and unresolved references; and requires byte equality. Bit-for-bit reconstruction requires the same compatible TeX/font versions as the supplied build. Different toolchain versions can give a mathematically identical article with different PDF bytes; the strict comparison will correctly report that difference.

The original authoring validation rendered and inspected all 18 pages. Page rendering is not repeated by `reproduce.py`; render the rebuilt PDF with Poppler or another viewer to inspect typography independently.

## ZIP reconstruction

```
python3 -B repack.py /tmp/report131-source.zip
```

ZIP members have fixed timestamps, ordering, and permissions. Byte equality also depends on a compatible zlib compression implementation. The archive contains this entire reader package, including the PDF, and no private research notes or audits. No network access, upload, or publication is performed by any replay command.
