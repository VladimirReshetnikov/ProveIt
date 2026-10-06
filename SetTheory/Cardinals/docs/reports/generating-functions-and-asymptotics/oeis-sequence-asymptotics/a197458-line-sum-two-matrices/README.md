# Report 168 Sparse binary matrices with line sums at most two

This standalone report concerns OEIS A197458: the number a_n of n by n binary matrices with every row and column sum at most two. It includes the labeled bivariate EGF, a Bessel diagonal and exact differential recurrence, and the leading equivalent

    a_n ~ (n!)^2 exp(2 sqrt(2n)) / (2^(5/4) pi n^(3/4)).

Every fixed order in n^(-1/2) has a proved remainder. Four explicit corrections, a finite Gaussian-moment calculator, a logarithmic expansion, constructive further real-inverse orders, an explicit Lambert-W inverse through the bounded correction, and an existential two-ceiling integer threshold enclosure are included. Four carefully posed research directions describe possible extensions without claiming them as results.

General bounded-degree enumeration and configuration-model methods are prior work. The retrieved direct sources do not state this scalar expansion, but historical priority is not certified. The Goulden-Jackson textbook exercise cited by companion OEIS entries was not directly inspected. No complete beyond-all-orders transseries, effective remainder constant, or universal rounding rule is claimed.

## Files

- `Report168.pdf`: standalone mathematical report
- `Report168.tex`: complete editable LaTeX source
- `companion/USAGE.md`: bounded commands and exact coverage
- `companion/exact_matrix.py`: exact ODE, compressed-state DP, labeled tuple DP, bitmask, and rational-GF checks
- `companion/symbolic_coefficients.py`: standard-library exact Gaussian-moment and independent discrete-ODE correction calculations
- `companion/test_*.py`: positive and negative regression tests
- `data/`: small numeric fixtures, source provenance, and recorded computations
- `SOURCE_PROVENANCE.json`: source coverage and claim boundaries
- `verification_receipt.json`: completed release checks and hashes
- `build_pdf.py`, `make_zip.py`, `release_tools.py`, `test_release.py`: deterministic release tools and safety tests
- `SHA256SUMS`: sorted frozen allowlist checksums; the manifest is itself inside the ZIP

The archive excludes third-party papers, the full OEIS entry, temporary builds, screenshots, and private working materials. `data/oeis_term_records.txt` contains only the three numeric term lines needed to cross-check the JSON fixture.

## Exact replay

Use Python 3.10 or newer. All delivered computation scripts use only the standard library; there is no network dependency or optional CAS requirement. From the extracted package directory:

    python companion/exact_matrix.py verify
    python -O companion/exact_matrix.py verify
    python companion/symbolic_coefficients.py --order 4
    python -O companion/symbolic_coefficients.py --order 4
    python -m unittest discover -s companion -p 'test_*.py' -v
    python -O -m unittest discover -s companion -p 'test_*.py' -v
    python -m unittest -v test_release
    python -O -m unittest -v test_release

The exact verification defaults cover all 17 OEIS terms, the ODE through n=200, compressed DP through n=40, rational GF through n=30, labeled tuple DP through n=8, and literal masks through n=4. The symbolic executable is explicitly bounded to orders 0 through 8. The mathematical rule itself applies at every fixed order. The usage guide gives all other resource bounds. Invalid inputs fail explicitly, and verification checks remain active under `-O`.

Exact finite agreement checks implementations and identities. It is not a proof of the asymptotic theorem, which is supplied in the report. No decimal diagnostic is a certified error bound.

## Rebuild the PDF

The PDF builder requires Linux/POSIX descriptor operations and `/proc/self/fd`, Python, `pdftex`, `pdflatex`, and the LaTeX packages used in the source (including Latin Modern, AMS math, geometry, microtype, and hyperref). The tested engine is pdfTeX 1.40.26. From the package directory, choose a path that does not already exist:

    python build_pdf.py --output-dir rebuilt_pdf

The parent directory must already exist and must contain no symbolic-link path components. The builder creates a fresh private directory exclusively, builds a clean format with restricted fixed TEXMF trees, disables shell escape, pins locale/time and PDF metadata, waits for cross-references to stabilize, and rejects settled warnings or layout defects. It refuses an existing target, including files, directories, and symlinks. A failed build may leave its new diagnostic directory behind; choose a new path for a retry. It does not overwrite the packaged PDF.

Two fresh builds in the tested TeX environment produced byte-identical PDFs. The same bytes are not promised across different TeX/font versions. The packaged PDF was rendered and every page visually inspected.

## Verify and reproduce the ZIP

From the extracted package directory:

    sha256sum -c SHA256SUMS
    python make_zip.py --output ../Report168_Source_rebuilt.zip

The requested output must not exist, and its parent directory must already exist without symlink components. The ZIP builder reads only the fixed allowlist, requires a matching sorted checksum manifest, rejects nonregular inputs and symlink paths, and uses sorted entries, a fixed timestamp, permissions, and uncompressed storage. It validates the resulting ZIP before exclusively creating the output. Extra files in the working directory are excluded rather than included accidentally.

The release tests cover existing targets, parent and destination symlinks, dangling links, FIFOs, path traversal, descriptor-pinned parent-swap races, manifest mutation, payload tampering, fixed ZIP metadata, and deterministic archive bytes. They run normally and under optimization. The PDF and ZIP builders never publish, upload, contact an author, or edit an external repository.
