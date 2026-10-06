# Report 153 All orders refinement for unlabeled permutation graphs

This standalone release contains the complete proof, editable LaTeX, rendered
PDF, and exact computational companion for OEIS A123448. If a_n counts unlabeled
permutation graphs, the result is, for each fixed R >= 1,

    a_n = (1/4) sum_{k=0}^{R-1} h_k (n-k)! + O_R((n-R)!)

The eight independently reproduced coefficients are

    1, -4, -1, -94/3, -769/6, -19969/15, -531812/45, -40114096/315.

The proof uses interval exclusion, canonical strong modules, a connected and
coconnected insertion lemma, bounded vertex-rooted contexts, weighted
four-realizer counts, and Borinsky's established finite-polynomial factorial
transfer. It does not assume asymptotics for the unknown graph series.

The report also proves:

- k! h_k is an integer at every order
- arbitrary fixed-order threshold windows with explicit floor/ceiling bounds
- a second Lambert-W inverse shift with O(1/(u^2 log u)) rounding-window width
- an all-orders expansion for exactly-four-realizer graph classes
- a sharp all-orders total variation expansion for uniform permutations versus
  uniform unlabeled graph classes, beginning

    4/n - 15/n^2 + 169/(3n^3) + 215/(2n^4) + O(n^-5).

Seven total-variation coefficients and seven four-realizer factorial
coefficients are given in the report and companion. The marked context count
is t(L,v)=f(L) times the size of the root's automorphism orbit. Nontrivial
contexts with t=1 occur already at size seven; this factor cannot be omitted.

## Scope and source boundary

Every truncation order is fixed. No remainder uniform in a growing order,
convergence, Borel summability, identification of all exponentially small
sectors, or optimal-truncation estimate is claimed. Inverse coefficients are
computable, but remainder constants and onset are not numerically certified.
The exact integer threshold can be ambiguous between neighboring integers near
a shrinking boundary window. Total variation controls additive event errors
and uniformly bounded observables, not arbitrary unbounded statistics.

Bayoumi--El-Zahar--Khamis (1990) already supplies an exact recurrence and a table
through n=20. El-Zahar--Sauer (1988) and Winkler (1990/91) are close classical
poset-asymptotic and sampling precedents. The final 2026 intersection-graph
article and the full older subscription texts were not inspected. This is an
all-orders refinement with a bounded source review, not a first-ever claim for
the leading equivalent. Source versions, URLs, and review limitations are in
SOURCE_PROVENANCE.json and the report bibliography.

The input graph counts a1..9 and rooted counts r1..9 were exhaustively
recomputed by two implementations. All needed one-realizer and marked-context
inputs through n=8 are also replayable. The high n=15..20 values quoted from
the 1990 table are prior art and are not independently certified by this
companion; the authors' stated double-precision computation is disclosed.
They do not enter the asymptotic coefficients or proof.

No downloaded paper, private review document, unrelated earlier report, or
research working note is bundled. No external publication, author contact,
OEIS submission, or public repository edit is part of this release.

## Contents

- Report153.tex and Report153.pdf: complete mathematical argument and rendering
- companion/: standard-library exact checks, expected claims, graph enumeration
  routes, tests, provenance, and recorded normal/optimized results
- build_pdf.py: deterministic isolated PDF builder
- make_zip.py: fixed-allowlist, checksum-verifying deterministic archive builder
- release_tools.py: descriptor-pinned exclusive local output helpers
- test_release.py: output-safety, manifest-mutation and archive tests
- SHA256SUMS: checksums for the frozen release payload

The FILES tuple in make_zip.py is the authoritative packaged allowlist. The
ZIP contains that payload plus SHA256SUMS, and never recursively includes the
working directory. The ZIP itself is intentionally not a manifest member.

## Reproduce exact calculations

Requirements: Python 3.10 or newer on POSIX with O_DIRECTORY and O_NOFOLLOW.
No external Python packages are required. From the extracted release root:

```sh
python3 -B companion/verify.py
python3 -B -O companion/verify.py
python3 -B companion/test_companion.py
python3 -B -O companion/test_companion.py
python3 -B -m unittest -v test_release
python3 -B -O -m unittest -v test_release
```

The default checker includes light exhaustive graph replay. For the full
finite-input replay using both enumerators through n=9:

```sh
python3 -B companion/verify.py --enumerate-through 9
python3 -B -O companion/verify.py --enumerate-through 9
```

A full replay is substantially slower than the default. See companion/README.md
for its exact finite ranges, result schema, and safe optional JSON-output
syntax. Checks remain active under Python -O and mutation tests require altered
claims to fail. Finite calculations check exact algebra and enumerated input
data; they do not prove structural or analytic theorems.

Use the program's --output option with a fresh permitted filename for a saved
result. Existing outputs, symbolic links, traversal and disallowed destinations
are refused. Shell redirection is outside these safety guarantees.

## Rebuild the PDF

The tested toolchain is Python 3.12.14 and pdfTeX 1.40.26 (TeX Live 2025), with
LaTeX, Latin Modern, AMS, mathtools, geometry, booktabs, longtable, array,
microtype, and hyperref. The builder uses the Linux trees
/usr/share/texlive/texmf-dist and /usr/share/texmf, POSIX /proc/self/fd, and
installed font maps. It is not a cross-platform TeX wrapper.

Choose a new output directory whose parent already exists:

```sh
python3 -B build_pdf.py --output-dir /tmp/report153-pdf-replay
cmp Report153.pdf /tmp/report153-pdf-replay/Report153.pdf
```

The builder creates a fresh private directory, initializes an isolated TeX
format, disables shell escape, pins the font maps, fixes locale/timezone/source
date, suppresses PDF dates and trailer identifiers, and iterates until the
reference files stabilize. It rejects settled warnings, overfull or underfull
boxes, and missing glyphs. All intermediates stay in the new directory. The
source needs no network connection or shell-escape command.

PDF byte identity is qualified to the recorded toolchain. Different TeX or font
versions may produce the same typesetting with different PDF bytes.

## Rebuild the archive

```sh
sha256sum -c SHA256SUMS
python3 -B make_zip.py --output /tmp/Report153_Source_replay.zip
```

The archive builder verifies every payload checksum and the exact allowlist
before producing a stored ZIP with sorted members, timestamp 2026-10-03
00:00:00, and fixed regular-file permissions. It then reads back the in-memory
archive and checks every member. Rebuilding the same payload gives identical
ZIP bytes. Existing destinations and symlink path components are refused.

If verification fails, investigate the changed payload rather than replacing
the manifest to silence the failure. The manifest proves internal consistency,
not authenticity against simultaneous replacement of payload and checksums.
