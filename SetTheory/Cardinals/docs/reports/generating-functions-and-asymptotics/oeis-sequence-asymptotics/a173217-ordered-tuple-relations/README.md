Report220: Exact pole sectors and integer recovery for ordered tuple relations
4 October 2026

RESULT AND BOUNDARIES
For d >= 2, H_d(n) counts sets of distinct ordered d-tuples on an active
ordered vertex set. Repeated entries within a tuple are allowed. It is not
the ordinary d-element-set-edge hypergraph model. The first three cases
are OEIS A173217, A301466, and A301468.

The article proves a post-Stirling-transform pole-tail bound with exact
polynomial amplitudes, an all-fixed-order compact-complex collision kernel,
and eventual shrinking two-ceiling inverse enclosures. The no-logarithm
recovery cutoff M = ceil[(d/6)(2*n^(d-1))^(1/d)] for n >= 2 has absolute
error < 13/(18*n^(d-1)) <= 13/36. A finite-sum interval of width <= 1/4
therefore gives the exact integer by rounding its midpoint. A separate
harmonic cutoff gives a smaller error constant with more poles.

The older coarse normalized growing-cutoff bound alone does not certify
rounding. Growing poles retain exact amplitudes; fixed-pole asymptotics
cannot be substituted over the entire lattice. Pole count is not a bit-cost
or fixed-precision stability claim. Inverse constants and onsets are
existential; no universal single-ceiling or effective inverse algorithm is
claimed. Known leading equivalents, the enumeration/Stirling transform,
Fubini pole identity, and prior collision methods are explicitly credited.
There is no global priority or famous-conjecture claim.

READING AND CONTENTS
Report220.pdf is the 18-page article; Report220.tex is its editable source.
Appendix A gives three source-specific corrections with immutable links,
commit, blob and SHA-256 pins. SOURCES.txt summarizes attribution boundaries.
code/README.md documents exact finite ranges, scripts, guards and commands.
code/results/ contains freshly regenerated outputs and their deterministic
reproduction receipt. MANIFEST.json pins all listed public files except
itself to avoid self-reference. SOURCE_FILES.txt defines the public inventory.
No network access, repository checkout, external source-paper PDF or private
review document is needed for reproduction or included in the package.

FULL REPRODUCTION
Extract the archive and, in the extracted Report220 directory, run:
  python3 -B reproduce.py --out /absolute/new/output-directory \
    --reference-zip /absolute/path/Report220-reproducibility.zip
The output directory must not exist, must have an existing parent, and must
be outside the input tree. The reference-zip option compares against the
actual delivered archive bytes. It is optional when that file is unavailable;
without it every actual generated member is still checked, but no original
whole-archive comparison is claimed.

Repeat using python3 -B -O and a different output directory. The outer driver
first checks the baseline manifest, regenerates every finite result, builds
the PDF to byte stability with a private format and explicit installed font
maps, writes fixed-metadata uncompressed ZIP members, and compares every
actual member against the built files. Normal and optimized runs must produce
identical JSON, PDF, manifest, member bytes and whole ZIP with the same
stated toolchain. The external reproduction.json receipt records hashes and
which baseline/archive checks actually ran. It is intentionally outside the
archive, since run mode and reference-archive availability can differ.

The finite driver itself runs every finite computation twice normally and
twice under -O from unrelated temporary working directories. Source and
reference checks are not disabled by optimization. The PDF driver rejects
overfull boxes, undefined citations/references and a non-stable PDF.

FINITE REPRODUCTION ONLY
  python3 -B code/reproduce.py --output-dir /absolute/result-directory
This runs exact and symbolic calculations, decimal diagnostics, certified
rational recovery and negative controls, but does not build a PDF or ZIP.
The integer recovery module alone requires only Python's standard library:
  python3 -B code/rational_checks.py recover 2 100
  python3 -B code/rational_checks.py recover 2 100 --cutoff harmonic
The standalone recovery never reads an exact-count oracle for n >= 2.
Computed arbitrary-size integer and rational outputs use chunked decimal
conversion, without changing Python's interpreter-wide input digit limit.
Ordinary CLI integer parsing retains that safety guard. Output size and
runtime remain bounded by practical memory and computation resources.

The combined reproduction and decimal mpmath diagnostic layer require Python's
standard 4300-digit integer conversion limit or higher (an explicitly unlimited
caller setting also works). The full drivers reject a lower limit before
starting calculations. They never change that setting. This condition is due
to internal formatting in mpmath 1.3.0 and does not apply to the standalone
certified rational recovery module, which is tested at the strict 640 limit.

DEPENDENCIES AND PORTABILITY
See requirements.txt. The tested interpreter is CPython 3.12.14, with
SymPy 1.14.0 and mpmath 1.3.0 for the combined finite driver. Certified
recovery itself needs neither package. The tested PDF toolchain is
pdfTeX 1.40.26, TeX Live 2025/dev/Debian, kpathsea 6.4.0/dev, with Latin
Modern fonts and the listed LaTeX packages. The driver discovers the installed
TEXMFDIST via kpsewhich, adds its sibling texmf font tree when present, and
builds a private pdflatex format; it does not depend on a user format cache.
The installed map files must be discoverable as documented. PDF byte identity
is a same-toolchain promise, not a promise across arbitrary TeX/font versions.
The mathematical exact/rational outputs have no such TeX dependency.

GUARDS
All guards use explicit exceptions rather than assert. An intentional root
pre-write failure is available via --self-test-failure and must exit nonzero
without creating the output directory. Mutating an inventoried source without
updating its manifest must likewise fail before writing outputs. The authoring
option --initialize permits establishing an absent PDF/manifest baseline;
do not use it for ordinary reproduction or as a way to bypass verification.
Finite checks establish their finite claims only; the universal asymptotic
and recovery claims depend on the proofs in the article.
