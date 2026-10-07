Report214 Fixed collision orders and smooth inverse centers for A094149
4 October 2026

RESULT AND SCOPE
The article gives a finite Bell-transform expansion at every fixed collision
order p, with relative remainder O_p(log^(10p+6)(k)/k^(p+1)). Each transform has
leading scale W(k)^(3j)/(2^j j! k^j). Exact lower transforms must be retained
before interpreting a smaller residual scale. The first two transforms are
written explicitly. Coefficients require finite child-return rows, not only
scalar moments.

A finite real Poisson interpolation supplies smooth inverse centers. For fixed
p>=1 the integer threshold is between two ceilings at radius
C_p log^(10p+5)(x)/x^(p+1). Center displacements and successive-center leading
shifts are proved. The constants/onsets are existential; this is not a certified
finite-threshold numerical inversion algorithm. There is no growing-order
expansion, exponential resummation, or historical priority claim.

The complement theorem is inherited from Report213. A complete proof of the
required complement estimate is recalled in Appendix B, with explicit credit
for the Bauer-Golinelli coefficientwise comparison as its external theorem.
No previous report or private source file is required to read or reproduce
Report214. SOURCES.txt distinguishes inspected primary results from remaining
full-text gaps and contains no third-party full texts.

READING
Report214.pdf is the article; Report214.tex is editable source. Small exact
child-return rows and rounded correction diagnostics are in the article.
code/results/ contains their exact compact data and finite-check counts.

FULL REPRODUCTION
Extract the ZIP. In the extracted Report214 directory run:
  python3 -B reproduce.py --out /absolute/new/output-directory \
    --reference-zip /absolute/path/Report214-reproducibility.zip
Use a new output directory outside the source tree, with an existing parent.
The reference ZIP option compares the complete rebuilt archive bytes with the
actual original file. It is optional if the original archive is unavailable;
without it, every actual rebuilt member and archive inventory are still checked,
but no original whole-ZIP comparison is claimed.

The outer driver verifies the source manifest before writing outputs, freshly
regenerates all finite data, rebuilds the PDF to byte stability using a private
TeX format and explicit installed font maps, and creates a ZIP with fixed
metadata. The finite harness separately exercises both normal and -O Python.
SOURCE_FILES.txt lists the public source and data inventory. MANIFEST.json
pins its bytes and the PDF; it excludes itself to avoid self-reference.

Run the same full command with python3 -B -O and a distinct output directory
to check the outer driver under optimization as well. Same-toolchain replay
must produce identical PDF, manifest, actual member bytes, and entire ZIP.
No internet access or neighboring project files are needed. See requirements.txt
for the expected TeX/font toolchain.

FINITE REPRODUCTION ONLY
  python3 -B code/reproduce.py --out /absolute/new/finite-output-directory
This requires only the Python standard library. See code/README.md for exact
ranges, algorithmic independence, command options and negative-test scope.
The finite program recomputes all results; shipped rows are not used as an
input to the recurrence or independent walk enumeration.

GUARDS AND LIMITATIONS
All correctness guards use explicit exceptions, retained under -O. A root
pre-write guard can be exercised with --self-test-failure: the process must
exit nonzero and create no output directory. Mutating an inventoried source
without updating the manifest must also fail before output creation. Do not
use --initialize for ordinary reproduction; it is an authoring option for
establishing an absent PDF/manifest baseline, not a validation shortcut.

Finite checks validate the stated formulas only at their enumerated indices.
Recurrence generation at higher indices is not an independent algorithm there.
The asymptotic theorems rest on the all-index mathematical proofs. PDF byte
identity depends on the same installed TeX/font versions; exact integer and
rational data need no third-party Python library. No large row arrays, private
reviews, source PDFs from third parties, or executable binaries are included.
