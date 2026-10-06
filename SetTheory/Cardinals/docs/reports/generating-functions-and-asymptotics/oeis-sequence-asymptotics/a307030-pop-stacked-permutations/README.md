# Report164 exact generating function for pop stacked permutations

Report164 is a standalone mathematical report on OEIS A307030. It derives an
explicit exponential generating function, its meromorphic continuation,
simple-pole residues, infinitely many positive poles, non-D-finiteness and
non-P-recursiveness. An exact Riccati equation provides a quadratic-arithmetic
counting recurrence. A polynomial resultant proves differential algebraicity.
The dominant-pole proof, rational enclosures for rho and C, finite-radius pole
expansions, fixed-order Stirling expansions and safe inverse rounding are included.

The report preserves the distinction between new exact formulas/proofs and the
published numerical pole estimates. Its source search is bounded, not a claim of
worldwide priority. It does not certify an effective numerical complex gap or
asymptotic error constant, order the nonreal poles, assert a convergent infinite
pole sum, claim bit complexity or optimality, or solve run-refined enumeration.
The previously delivered Report161 is unchanged.

## Contents

- `Report164.pdf` is the 15-page report
- `Report164.tex` is the editable LaTeX source
- `companion/pop_egf.py` is the bounded standard-library exact companion
- `companion/README.md` documents its API, commands, bounds and proofs used
- `companion/test_pop_egf.py` tests the public contract and mathematical checks
- `data/counts_p0_p70.json` records the frozen count fixture and provenance
- `data/verification_n70.json` records the two independent exact series checks
- `data/constant_certificate.json` records the exact rational interval certificate
- `SOURCE_PROVENANCE.json` records primary sources and verification scope
- `author_review_receipt.json` summarizes completed release checks
- `build_pdf.py`, `make_zip.py`, `release_tools.py` and `test_release.py` reproduce
  and test the local release
- `SHA256SUMS` fixes the payload contents

Only the fixed allowlist in `make_zip.py` enters the ZIP. Audit work files,
rendered page images, build logs, caches and replay archives are not payload.

## Exact computation

From the package root, with Python 3:

```sh
python -B companion/pop_egf.py counts --n 400
python -B companion/pop_egf.py verify --n 70
python -B companion/pop_egf.py certify
python -B -m unittest discover -s companion -v
python -B -O -m unittest discover -s companion -v
python -B -m unittest test_release -v
python -B -O -m unittest test_release -v
```

All computation CLI results are deterministic JSON on stdout. The CLI has no
file, URL, upload or output-path options. The module performs no application
file reads or writes and emits nothing on import. Use `-B` to suppress Python's
own bytecode-cache writes. Tests read their fixed local fixture and start local
Python subprocesses. Mathematical checks use explicit exceptions, so Python
`-O` does not disable them.

The recurrence is bounded at N=400 and the independent quotient at N=70.
Booleans, non-integers and out-of-range API inputs are rejected before large
allocation. The O(N²) arithmetic / O(N) scalar-storage claim applies to the
recurrence, not the slower independent quotient check. It is not a bit-cost
claim. The interval certificate uses rational Taylor bounds and integer square
roots, with no floating-point arithmetic or external numerical package.

The certificate's real denominator sign test is identified with the first pole
by the report's monotonic-phase proof. It does not independently certify complex
pole locations. The fixture's p₁…p₂₅ are posted OEIS terms checked previously;
p₂₆…p₇₀ are endpoint-recurrence computations, not extra posted OEIS terms.

## Rebuild the PDF

The original reproducibility environment is Linux with Python 3 and system
TeX Live providing pdfTeX/pdfLaTeX, Latin Modern, AMS packages, geometry,
microtype and hyperref. A TeX installation must include the standard source
format `pdflatex.ini`; the builder initializes its own format in its fresh output
directory. It disables shell escape and isolates writable TeX cache/config paths.

Choose an existing trusted parent directory and a destination name that does
not exist:

```sh
python -B build_pdf.py --output-dir /absolute/trusted/parent/pdf_replay_one
python -B build_pdf.py --output-dir /absolute/trusted/parent/pdf_replay_two
cmp /absolute/trusted/parent/pdf_replay_one/Report164.pdf /absolute/trusted/parent/pdf_replay_two/Report164.pdf
```

The output directory is created exclusively; existing files/directories and
symbolic-link path components are rejected. Builds use fixed PDF metadata,
source date and font maps, a bounded stabilization loop, and reject settled TeX
warnings, missing glyphs, overfull or underfull boxes. Exact bytes are verified in
the stated environment; other TeX/font versions may produce different bytes.

## Verify and rebuild the ZIP

```sh
sha256sum -c SHA256SUMS
python -B make_zip.py --output /absolute/trusted/parent/Report164_replay_one.zip
python -B make_zip.py --output /absolute/trusted/parent/Report164_replay_two.zip
cmp /absolute/trusted/parent/Report164_replay_one.zip /absolute/trusted/parent/Report164_replay_two.zip
```

The packager verifies the exact sorted fixed allowlist against `SHA256SUMS`,
refuses mismatches, fixes ZIP timestamps/permissions and stores uncompressed
members in sorted order. It creates the output with exclusive no-clobber flags.
Unlisted files cannot enter the archive. Existing destinations, symbolic links,
FIFOs, parent traversal, and symlinked parent components are rejected. Parent
file descriptors are held to prevent a later pathname swap from redirecting a
write. The release tests cover these cases, parent-swap behavior, archive
reproduction and manifest tampering.

These helpers assume trusted payload sources and trusted output parent
directories. They are not a general malicious-TeX sandbox or a defense against
an adversary allowed to replace files inside an already-opened directory. The
scripts require Linux/POSIX descriptor facilities and do not claim portability
to operating systems lacking them.
