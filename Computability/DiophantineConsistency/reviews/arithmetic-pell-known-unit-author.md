# ArithmeticPellKnownUnit: author validation

27 October 2026. The complemented47 agent authored and fully read the new
206-line main and50-line Checks, then compiled them privately against the
exact ROOT-authorized Classification inventory. The final pair is **PASS**,
with an empty main log and four standard-only axiom reports. All three
attempts are preserved; no accepted prerequisite source or object changed.

The only main import is `DiophantineConsistency.ArithmeticPellClassification`.
The public `known_unit_classification` theorem works in every
`[ORingStructure V]` model of IΣ1. Given `D>0`, `A>1`, `S>0` and the actual
norm equation `A*A=1+D*S*S`, it derives one `b,v` with `v>0`, `b+2≤A`,
`v≤S`, `(b+2)^2=1+D*v^2`, and, simultaneously for every norm solution
`x*x=1+D*y*y`, an internal index `n≤y` satisfying
`x=xcoord n b` and `y=v*ycoord n b`.

No minimality, classification, standard-index or fundamental-unit premise is
supplied at this endpoint. The bounded predicate is exactly
`0<v ∧ v≤S ∧ ∃F≤A, F*F=1+D*v*v`. Its witness is the supplied seed, and
`ISigma0.least_number` produces the least ordinate. If any positive solution
had a smaller ordinate, square comparison would also put its abscissa inside
the seed box, contradicting that bounded minimum. Thus the derived unit is
minimal among all positive solutions, not merely those initially in the box.

The descent helper keeps explicit minimality only as an internal interface;
the public theorem derives it. The norm equations prove `v*x≤F*y` and
`D*v*y<F*x`, so both natural subtractions are justified. The additional
strict square comparison proves `F*y-v*x<y`. The new coordinates satisfy
the same norm, and exact cancellation identities recover the original
coordinates as their next recurrence step. The discriminant identity
`delta b=D*v*v` preserves the ordinate scale. Classification uses actual
Sigma1 order induction at internal `y`, with bounded universal abscissa
`x≤(D+1)*y+1` and internal existential index `n≤y`. The zero-ordinate branch
returns index0. No Nat-only recursion or external Pell classification is
used. The intentionally retained seed assumption `A>1` is redundant given
the other positive seed assumptions; it is not used to strengthen a result.

Focused checks retain the exact public theorem, two arbitrary norm solutions
with the same derived base/scale, the zero-ordinate case, and minimality for
a query not assumed inside the seed box. The four audited public theorems
are `least_unit`, `minimal_unit_descent`, `minimal_unit_classification`, and
`known_unit_classification`. Each reports only propext, Classical.choice,
and Quot.sound.

| Module | Source SHA256 | Object SHA256 |
| --- | --- | --- |
| ArithmeticPellKnownUnit | c676e7c29719fbedf87aea549cefd57bee1df8844ef443a72a9d87467a9e3cb9 | efbe7eed7d2ec64cbcfbbce9e65812a489886be7ceed6f05c34aacb018c60cf8 |
| ArithmeticPellKnownUnitChecks | 9fd672d63abffe7011298c5d2323d2fdb82a204e5709a21ac9eaaba64ea0f12d | fe839490ea6ceaa6d3712212661996b981dd65f8c478a295d0e534e294d6260d |

The immutable cache plan is
`research/arithmetic-pell-congruences-cache-plan.json`, SHA256
`a5182706264e4a28a0ff58f2a97cf32a2860e7246ff3c04d76a163a9e83f8f99`.
It selects97 custom modules,95 Foundation,382 custom artifacts,38 external
boundary names, and zero prerequisite refreshes. Its historical field
`external_companions=114` actually counts **all114 recorded boundary
artifacts:38 primaries plus76 companions**, each boundary having an olean,
private and server artifact. This receipt corrects the terminology without
changing that frozen inventory or the100-line scope supplement
`research/arithmetic-pell-known-unit-next-plan.md`, SHA256
`224e82cecc69aa3a2fccd64bb7a14862485ee454306b458da1f85e06f05d3a8b`.

The executed driver rehashes all selected source/object/provider records,
re-reads import headers, verifies exact reachable closure and all496 actual
first-provider artifacts, and retains only the private custom overlay plus
explicit package/toolchain paths. Source-authenticated cached prerequisites
retain their accepted provenance; this is not a new Foundation or package
build. The two non-Foundation providers remain the accepted Recurrence and
Classification objects identified in the frozen scope supplement.

Every source, Checks and executed driver was fully read before each relevant
compile. Each compiler command uses pinned Lean4.32 with
`-M6000 -j1 -DElab.async=false`, one thread, and a512MiB reserve. New output
objects are fresh regular files; cached inputs are private links. The final
provider is `/tmp/arithmetic-pell-known-unit-author-henm3tkg/lib`.

| Attempt | Main result / seconds | Checks result / seconds |
| --- | --- | --- |
| 1 | failed /21.073 | not run; input snapshot preserved |
| 2 | failed /20.396 | not run; input snapshot preserved |
| 3 | PASS /19.589 | PASS /1.880 |

Attempt1 found only three inequality-helper addition-side mismatches and an
explicit `1+1=2` numeral normalization. Attempt2 qualified the same helpers
but retained their addition-side mismatches. Attempt3 adds explicit
commutativity normalization. No theorem statement, import, memory cap or
mathematical scope changed. Final main/check peak RSS is1,862,904/1,794,788KiB.
There are no final warnings, errors or sorry axioms. Final free space was
1,422,159,872 bytes.

All source/driver/input snapshots, failures, logs, timings and commands are
in the [replay packet](arithmetic-pell-known-unit-replay.json), SHA256
`faf3ab49a1a56710f95cfac4e8a317012d96c2f0c48984719911dcdda8716c87`, and
[33-file evidence manifest](arithmetic-pell-known-unit-author-replay/FILES.json),
SHA256 `8d445ad61576c3097c30c15eb96c75bdcaeb48f8d88a2f7fcbfdda6ae2aa5e24`.
The final freeze independently rehashed3,146 observations across1,846 paths,
rebinding historical draft-source pins only to their exact preserved input
snapshots. The executed author driver SHA256 is
`8f02dd0745afbfc517f916b6d7043b038b123eb2c24e4b8ca2146900871db823`.

This is author validation, pending ROOT's independent review/replay. Internal
gcd normalization, common-discriminant construction, sequence divisibility,
Jones relaxed-integrality, Qh, cofinal witnesses and the final HA equation
remain outside this packet. No shared document, frozen source, display or
Git state was changed.
