# Independent Regina topology audit

The complete frozen audit passed: **664 cases, 1,395 producer calls, 1,395
exact matches to Regina, and 1,395 accepted certificates**. No case failed,
timed out, or returned an inconclusive result. All runtime Python source
hashes remained unchanged during the audit.

## Files and reproduction

- Script: `topology_research/regina_audit.py` under the `fast` repository root.
- Frozen corpus: `topology_research/data/regina_corpus.json`.
- Final report: `regina_audit.json` in the research results directory.
- Console log: `regina_audit_console.txt` in the research results directory.

From the `fast` root, substituting the report path as needed:

```sh
python topology_research/regina_audit.py audit \
  --corpus topology_research/data/regina_corpus.json \
  --output regina_audit_replay.json

python topology_research/regina_audit.py audit \
  --corpus topology_research/data/regina_corpus.json \
  --output regina_audit_fresh.json --recheck-oracle
```

The first command replays all frozen oracle answers and requires no Regina
installation. The second additionally reconstructs every supplied face
pairing in Regina and freshly recomputes every oracle answer. The recorded
complete run used Regina 7.4 and the second mode. The `generate` command
rebuilds the corpus; `run` combines generation and audit. The generators seed
both Python and Regina, but Regina explicitly allows its random sequence to
vary with release, operating system, architecture and compiler. Frozen face
pairings and normal vectors are therefore the portable reproduction source.

## Exact coverage

| Quantity | Observed |
|---|---:|
| Total cases | 664 |
| Empty surfaces | 34 |
| Nonempty surfaces | 630 |
| Labeled triangulations | 34 |
| Triangulation isomorphism classes | 26 |
| Tetrahedra | 1–10 |
| Maximum normal-disc count | 1,528 |
| Maximum individual coordinate | 85 |
| Direct calls | 664 |
| Quadrilateral-core calls | 664 |
| Additional classical-AHT controls | 67 |
| Distinct connected topological types | 49 |
| Largest orientable genus | 9 |
| Largest nonorientable crosscap count | 10 |
| Most boundary circles on one component | 15 |
| Largest retained certificate byte length | 52,404 |
| Largest total orbit-cycle count in one call | 77 |

The 26 isomorphism classes comprise fifteen layered solid tori, two boundary
cap variants, a solid torus with an interior vertex, the projective-plane
fixture, the Klein-bottle fixture, the trefoil exterior, the figure-eight
exterior, and the torus-knot exteriors T(2,5), T(2,7), T(3,4), T(3,5).
Eight simplicial relabelings supply the remaining labeled triangulations.
Every ambient triangulation is independently checked by Regina to be valid,
connected, finite, orientable, and to have exactly one boundary component of
Euler characteristic zero. The projective-plane and Klein-bottle fixtures
exercise the general torus-boundary manifold contract; they are not claimed
to be knot exteriors in the three-sphere.

Input provenance comprises 187 selected Regina vertex vectors, six supplied
fixture vectors, 208 scales, 173 compatible random sums, 26 original empty
vectors, and 64 relabeled cases. Some relabeled cases are empty, giving 34
empty cases in total. The arbitrary Python randomness has seed 20261009.

The corpus includes connected spheres, discs, projective planes, Möbius
bands, annuli, tori, Klein bottles, closed orientable surfaces of larger
genus, and surfaces with more boundary components. Scaled Klein-bottle
vectors produce both Klein-bottle and torus components at the identical
weight type (Euler characteristic, boundary count) = (0,0), directly testing
the zero-type inversion. For example, cases 0440 and 0442 have respectively
one Klein bottle plus one torus, and one Klein bottle plus two tori.

## Independence and checks

Oracle generation does not import the producer geometry, orbit algorithm,
core extraction, or topology reconstruction. The existing pure input fixture
constructor and two fixture JSON files are reused only as source data.

For each bounded input, the oracle uses Regina's standard matching matrix
to verify all matching equations, separately checks the quadrilateral
constraints, and asks Regina for the explicit connected components. For
each component it obtains `eulerChar()`, `countBoundaries()` and
`isOrientable()`. It also checks that Regina reports each piece connected,
that its classification data have valid genus or crosscap values, that
the component normal vectors add exactly to the original vector, and that
Euler characteristics and boundary counts add to Regina's totals. Empty
surfaces use the empty component list, regardless of the convention in
Regina's `isConnected()` predicate.

Each frozen oracle histogram is compared with both the direct and the
quadrilateral-core production result using an exact multiplicity counter.
Every tenth case additionally runs the direct algorithm with the classical
AHT periodic rule. Every produced certificate is passed to the independent
source-bound verifier with the original input. The report retains each
certificate's canonical SHA-256 and byte length; full certificates are
regenerated from the frozen inputs rather than duplicated in the package.

## Scope

This is finite regression evidence for the topology of supplied embedded
normal surfaces. It does not establish an asymptotic time bound, exhaust
all normal vectors, test huge binary multiplicities, determine boundary
essentiality, or recognize an unknot. Regina's explicit routines are
deliberately confined to the small-coordinate corpus. All 664 cases were
retained, and there were no discarded or omitted failing cases.

The final audit took approximately 6.0 seconds on the recorded environment;
generation took approximately 0.3 seconds. These times are reproducibility
metadata, not an independently controlled performance comparison.

## Canonical content hashes

The following are hashes of canonical sorted compact JSON content, as
specified by the script, not hashes of the indented JSON file bytes:

- Corpus: `0a67910d79eef8fdf6d4860f592f515e6f77883a27b984d8ab27529e239ad03e`.
- Results: `5087aca237e410d5f7d560eccf1aef17d3f7e89f6c17a4c8d6dc77e59a59fdea`.
- Runtime source-hash map: `312d9094832fd5fd6cedbcf89c8307be8aea18364fecdd469678c2abc783be66`.

The report and corpus separately retain all actual source-file hashes,
case-input hashes, oracle hashes and certificate hashes needed to identify
the checked objects.

### Pinned-source provenance correction

After corpus generation, the repository materialization was corrected by
removing one extra terminal newline from each inherited file, bringing all
401 downloaded files into byte-for-byte agreement with their pinned Git
blob hashes. This changed file hashes but no Python semantics or fixture
data. The complete fresh-Regina audit was then rerun against the corrected
runtime; the results and runtime hashes above identify this final run.

The corpus was preserved unchanged because it already embeds the exact face
pairings, coordinates and oracle answers. Its `fixture_hashes` remain the
historical hashes of the files read at generation time, before the terminal
newline correction; they should not be mistaken for hashes of the corrected
on-disk fixture files. Its own corpus hash and every embedded input/oracle
hash remain valid. The final audit independently recomputed all 664 Regina
answers from those embedded inputs and verified all 1,395 certificates using
the corrected runtime sources.
