# Sparse edge cancellation in unknot recognition

Research continuation for Vladimir Reshetnikov's ProveIt project, 12 October 2026.

**The package proves a parameterized discovery theorem and provides working
performance improvements. It does not establish a general quasi-polynomial
unknot-recognition algorithm.** The article identifies the exact additional
geometric coverage theorem that would imply that bound.

Source revision:

`90e16db798c8d976bbe0c062e07cf20565e0b63a`

[Pinned project source](https://github.com/VladimirReshetnikov/ProveIt/tree/90e16db798c8d976bbe0c062e07cf20565e0b63a/Topology/UnknotRecognition)

## Read the article

- `article/unknot_cancellation.pdf`: complete research article.
- `article/unknot_cancellation.tex`: main LaTeX source.
- `article/theory.tex`: local metric reconstruction, cancellation, vertex
  discovery, polynomial rank gate, sparse incidence and sign chambers.
- `article/examples.tex`: explicit new disc, infinite layered family, and
  the multivertex Whitehead obstruction.
- `article/interfaces.tex`: ordered parallelity interfaces and correct
  relative-handle descriptions for disc products.
- `article/implementation.tex`: implementation, comparisons and validation.
- `article/research.tex`: prioritized open questions and research programme.

The article has complete proofs, explicit assumptions, primary references,
finite experimental results, and a distinction between proved algorithms,
implemented modes and open structural hypotheses. Reviews and exact
certificates are included; no proof-assistant formalization or journal peer
review is claimed.

## Main results

For a one-vertex source with first Betti number one, a standard vertex
meridian with cancellation on at most `k` edges lies in
`span(|c|, unit_e : e in F)`, of dimension at most `k+1`. The algorithm
retains this space throughout discovery. It does not need a quadrilateral
sector supplied in advance. The sparse determining equations have at most
four edge variables each; a determinant-matching argument gives the sharper
system count stated in the article. Multiple vertices introduce the cocycle
dimension `p`, giving a complete `t^O(p+k)` search.

An independent polynomial verification mode checks a supported matching
minor, primitive coordinates, Euler characteristic one and a nonzero
boundary cohomology class over F2. It requires no component-orbit routine.

On the maintained eight-tetrahedron coherent obstruction, the new method
finds a 47-piece standard vertex disc, changing only interior edge 30 from
weight 1 to 5. The coherent primitive surface has genus two. Boundary
layering gives infinitely many examples with the same one-edge cancellation
and quadrilaterals in `t-2` tetrahedra. The 72-tetrahedron example represents
308,061,521,170,163 normal pieces in binary coordinates.

The existing seeded-sector solver finds the same disc. The optimized global
one-edge method is approximately 1.39, 4.69, 27.9 and 90.6 times faster on
the four measured layered sources. These are controlled observations on one
structured family, with full preparation and positive checking included.
The elementary new all-subspace method is slower on small sources; its
unfavorable timings are retained.

The Whitehead construction proves that arbitrary multivertex triangulations
can force linearly many cancellation edges for every meridian. It is a
representation obstruction, not a complexity lower bound for unknot
recognition and not a one-vertex counterexample.

## Reproduce without changing a checkout

Python 3.12 was used. The core tests and certificate replay use the standard
library only. The optional external audit needs Regina; rendering the figure
needs Matplotlib; compiling the article needs a standard LaTeX installation
with `latexmk` and `pdflatex`.

From this archive's root:

```bash
python reproduce.py test
python reproduce.py replay
python reproduce.py enumeration
python reproduce.py family
python reproduce.py benchmark --rounds 7
```

The first command runs the 31 focused tests: 13 discovery, 7 rank-gate and
11 interface tests. The second independently replays representative saved
certificates with discovery producers disabled. New experiment output goes
to `reproduced/`, preserving the supplied measurement record.

Optional tasks:

```bash
python reproduce.py regina
python reproduce.py figure
python reproduce.py pdf
```

The external audit intentionally omits topology routines above 10,000
expanded normal pieces because the relevant Regina methods expand discs or
arcs. Large examples retain independently replayed native certificates and
exact rank checks. The saved JSON explains each omission.

`repro/Topology/UnknotRecognition/` contains the pinned Python dependencies,
the three additions, selected test helpers and the three required source
datasets. It is sufficient for these focused commands. It is not a full
ProveIt checkout or a complete copy of all historical reports, so use the
actual repository for the entire maintained test suite.

## Integrate into ProveIt

`integration/edge-cancellation.patch` contains three additive files:

```text
Topology/UnknotRecognition/fast/fastunknot/normal_weight_defect.py
Topology/UnknotRecognition/fast/normal_orbit_research/weight_defect.py
Topology/UnknotRecognition/fast/tests/test_normal_weight_defect.py
```

From the root of a clean checkout at the pinned revision:

```bash
git apply --check /path/to/integration/edge-cancellation.patch
git apply /path/to/integration/edge-cancellation.patch
cd Topology/UnknotRecognition/fast
python -m unittest tests.test_normal_weight_defect -v
```

The exact same files are under `integration/tree/` for direct inspection.
The patch was applied to an empty validation checkout and all output bytes
were compared with the overlay. Existing recognizer defaults are unchanged.
The article and supplementary prototypes can be placed in the next report
directory or integrated into the synthesis at the maintainer's discretion;
no historical report number is assumed or overwritten.

The general-`k` elementary arrangement algorithm is implemented. The faster
row-first determinant-matching algorithm is implemented only for `k=1`.
The multivertex sign-chamber discovery extension is proved but is not
implemented in the supplied search module. The complete polynomial rank
gate is a separate supplement in
`artifacts/edge_discovery/vertex_gate.py`. The timed search still uses the
richer existing component observer, whose current accounting depends on its
realized traces. The article proves its abstract bit bound using the rank
gate, without attributing that bound to the current richer observer.

The interface prototype is in `artifacts/parallelity/`, with its own README,
producer, independent checker, literal oracle, tests and complete examples.
It outputs local relative-handle plans; it does not perform surgery or
construct an admissible hierarchy.

## Evidence and provenance

`artifacts/verification-summary.json` summarizes successful coverage of all
1,627 maintained tests across the original broad run and a targeted rerun.
The initial sparse checkout lacked historical dependencies; 20 exact pinned
files were restored and all affected tests passed. There are no unresolved
assertion failures. Both logs and the full test identifiers are retained.
The 13 discovery tests are included in that count; the 18 supplementary tests
are additional.

`artifacts/edge_discovery/` contains raw paired timings, exact counters,
enumerations, all retained witnesses, independent Regina audit results,
polynomial rank certificates and focused logs. `artifacts/parallelity/results/`
contains the 184-comparison audit, including 54 authenticated source cases,
and both full-circle and partial-collar certificates.

`artifacts/benchmark_summary.csv`, `benchmark_plot.pdf`, `benchmark_plot.png`
and `plot_benchmarks.py` provide exact exported figures. `MANIFEST.json`
records file sizes and SHA-256 hashes for the delivered contents, excluding
the manifest itself. Intermediate LaTeX files, caches and rendered QA pages
are excluded from the archive.

## Remaining theorem obligation

To obtain a general quasi-polynomial recognizer by this route, construct and
verify a suitably small family of polynomial-size exterior triangulations
in quasi-polynomial time, and prove that some member has a **standard vertex
meridian** with `p+k <= C log(n+2)` whenever the input is an unknot. Search
only sources and radii within that fixed budget. No such general source
coverage theorem is proved here. Restricted exhaustion and budget exhaustion
must continue to return appropriately limited or inconclusive results.
