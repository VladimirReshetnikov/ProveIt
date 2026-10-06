# Report 150

Leading asymptotics of unlabeled circle graphs

For connected and all unlabeled circle graphs (OEIS A156808 and A156809), this report proves

c_n ~ g_n ~ exp(-3/2) (2n-1)!! / (4n).

A reciprocal-representation-fiber upper bound matches an injective construction from asymmetric split-prime cores with leaf/true-twin/false-twin decorations. A self-contained local-pattern forcing coupling sharpens both individual count estimates to relative O(1/n). The report also proves the connected fraction 1 - 1/(2n) + O(1/n^2), independent limiting Poisson(1/2) decoration counts, core deficit Poisson(3/2), graph asymmetry probability exp(-1), and a qualified Lambert-W inverse with ceiling-safe least-index brackets. A bounded reciprocal-automorphism argument supplies an optional labeled consequence.

The source review is bounded: the complete texts inspected include arXiv:2402.06394v1 and an additional author-hosted 2024 copy. The 2026 journal metadata was identified, but the final journal text was not inspected. No exhaustive priority claim is made. The quantitative theorem gives an O(1/n) remainder, but no individual first correction coefficient, all-orders expansion, or effective finite-input inverse certificate. The explicit bound min(1,200/n) concerns only local matching-pattern total variation, not the graph-count constant or onset.

## Contents

- `Report150.pdf` and `Report150.tex`: the complete report and editable source
- `companion/`: fresh standard-library Python finite verification, deterministic evidence, and mutation tests
- `SOURCE_PROVENANCE.json`: inspected source versions, theorem locations, source hashes, and limitations
- `build_pdf.py`: clean, deterministic PDF builder with shell escape disabled and settled-log validation
- `make_zip.py`: fixed-allowlist archive builder which checks the frozen checksum manifest
- `release_tools.py` and `test_release.py`: descriptor-pinned exclusive output primitives and adversarial tests
- `SHA256SUMS`: hashes of every other archive member

No downloaded papers, previous reports, private working notes, or build intermediates enter the archive. Only bounded factual count snapshots are included as companion test data. Nothing has been submitted to OEIS, sent to authors, or written to a public repository.

## Requirements

The companion and archive builder use Python3.10+ and only the standard library. Safe outputs require POSIX O_NOFOLLOW and O_DIRECTORY. The PDF builder additionally needs Linux /proc/self/fd, pdftex and pdflatex, and TeX Live packages for Latin Modern, amsmath/amsthm/mathtools, geometry, booktabs/longtable/array, microtype and hyperref. It uses the Debian-style system trees /usr/share/texlive/texmf-dist and /usr/share/texmf. No network access or software installation is required on the tested environment.

PDF bytes are reproducible with the tested pdfTeX1.40.26 / TeX Live2025-dev Debian toolchain. Other TeX versions may produce different bytes with equivalent mathematical contents. The source ZIP uses stored members with fixed metadata and sorted names, avoiding compression-version differences.

## Verification

Run from the extracted package root. All output parents must already exist. Output destinations must be new: existing files, symlink components and parent traversal are refused. A failed PDF build can leave its newly created diagnostic directory; the scripts never silently overwrite it.

```sh
mkdir validation
sha256sum -c SHA256SUMS
python3 companion/circle_companion.py --output validation/evidence.json
python3 companion/verify.py validation/evidence.json
python3 -O companion/circle_companion.py --output validation/evidence-optimized.json
python3 -O companion/verify.py validation/evidence-optimized.json
cmp companion/evidence.json validation/evidence.json
cmp validation/evidence.json validation/evidence-optimized.json
python3 -m unittest discover -s companion -v
python3 -O -m unittest discover -s companion -v
python3 -m unittest test_release -v
python3 -O -m unittest test_release -v
```

The companion README records its finite ranges and additional semantic-evidence validation command. Those checks test finite formulas, graph classes, representation fibers, geometric versus abstract symmetry, source counts, atomic forcing witnesses and inverse algebra. Euler inversion derives c13=21,593,488,017 from the sourced all-graph count, explicitly distinguished from a source-table entry. They do not establish the infinite asymptotic theorem or its input Poisson limits.

## Rebuild the PDF and ZIP

```sh
python3 build_pdf.py --output-dir validation/pdf-a
python3 build_pdf.py --output-dir validation/pdf-b
cmp Report150.pdf validation/pdf-a/Report150.pdf
cmp validation/pdf-a/Report150.pdf validation/pdf-b/Report150.pdf
python3 make_zip.py --output validation/source-a.zip
python3 make_zip.py --output validation/source-b.zip
cmp validation/source-a.zip validation/source-b.zip
```

The PDF builder creates its own clean format, isolated home and TeX state, and explicit font-map set. It runs until auxiliary references, bookmarks and contents stabilize, and rejects warnings, overfull/underfull boxes, or missing characters in the settled log.

The ZIP builder validates every allowlisted file against the fixed sorted checksum manifest before creating a new output. Unlisted files are excluded, and altered payloads fail rather than being silently rehashed. SHA256SUMS provides package consistency, not cryptographic authenticity if an adversary can replace both the payload and its manifest.

## Inverse interpretation

The inverse uses the exact gamma interpolation of the leading equivalent. A tail supremum of the actual sequence-to-model log error defines a shrinking existence envelope. The least index lies between the ceilings of the displayed Lambert-W approximation plus or minus O(1/(u log u)), where u=log(x)/W(2 log(x)/e). Eventually there are at most two adjacent candidates; near an integer boundary, the asymptotic equivalent alone cannot choose between them. No universal rounding rule or effective numerical onset is claimed.
