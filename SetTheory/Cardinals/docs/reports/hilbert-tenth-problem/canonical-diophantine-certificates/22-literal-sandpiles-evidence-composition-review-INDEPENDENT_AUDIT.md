# Independent binary-prism certificate audit

## Verdict

The binary specialization is sound and canonically unique **over natural witnesses at a fixed nonempty rectangular prism**, under the stated undirected threshold-six sink-graph hypotheses and exterior initial stability. It is precisely the existing compact compiler restricted to `u=k+c` and `alpha=0`; the simplex makes this a binary odometer restriction. The collar condition is an exact global-closure test. The mathematical statement does not assert uniqueness across differently padded prisms.

No remaining substantive defect was found in the reviewed certificate, streaming compiler or adapter. Four implementation/accounting issues were corrected during review: the reference stabilizer now re-enqueues a site that remains unstable after its toppling; raw coefficient generation now omits unit multiplications to match its ledger; huge prism iterators now use nested range loops because itertools.product eagerly cached billion-length input ranges; and the adapter now disregards foreign cached dependency modules while importing its verified files, then restores the caller’s import state. The huge-iterator failure was caught by the primary author’s actual45-record literal coefficient-prefix test, not by the initial small-instance audit.

## Mathematical checks

- Naturality and `f+k+c=1` make the three rank categories disjoint. The beta product fixes beta=0 in ranks zero/one. The derived support `u=k+c` is exactly the positive-rank support.
- Five-way edge comparison has a unique selector and gap for every integer rank difference. Both orientations' greater-or-equal and one-earlier comparisons are correct.
- Success plus failure one round earlier force exactly the parallel support-burning ranks. Inactive `g` and `h` are forced to zero. Thus no delayed-rank or inactive-gap freedom survives.
- The existing undirected support-burning criterion removes stable but nonlegal borrowed-firing proposals. Test example: on a two-site line with eta=(5,5), u=(1,1), z=(0,0) passes binary balance and a zero-background collar, but cannot satisfy burning.
- Empty support is allowed and unique. At eta identically zero, f=1, all rank/support variables vanish, each edge's equality selector is1, and all interior/exterior stability gaps are5.
- Each exterior L1-halo point of a rectangular prism has exactly one internal neighbor, even when one or more side lengths equal1. The halo cannot contain duplicate face points.
- For side lengths a,b,c>=1: V=abc; E=3abc-ab-ac-bc; H=2(ab+ac+bc). Witness count=26abc-4(ab+ac+bc), summand count=29abc-5(ab+ac+bc). Singleton:14 witnesses and14 summands.
- No result extends to nonnegative real witnesses. For singleton eta=1 and zero exterior background, the fractional tuple z=0, ell=5, f=5/6, k=1/6, c=beta=g=h=0, with halo gaps29/6, is a spurious real zero. The true natural certificate has empty support.

## Polynomial and operation ledgers

Let d be internal vertex degree, I=[eta_v>0], A=#nonzero interior initial heights, and L=#halo initial heights<5. Raw means expanded records before inter-summand collection; each template summand itself has distinct monomials.

- Per vertex raw records: binom(4+2d+I,2)+21+(2+3d)(3+3d)+binom(4d+4,2)
- Per edge raw records:173
- Per halo point raw records:6+4[eta_x<5]
- Evaluation additions:21V+63E+3H+A+L-1
- Evaluation multiplications:33V+76E+4H
- Expansion coefficient multiplications:sum_v[(3+2d+I)^2+(2+3d)^2+(4d+3)^2+30]+301E+sum_h(3+[eta_x<5])^2
- Per-vertex bounds:955 raw records and1415 expansion multiplications
- Every raw coefficient has magnitude at most K=max(72,12M,M^2), M=max interior eta. Therefore collected coefficient magnitude is at most K times total raw records. For eta<=6, K=72.

Evaluation counts refer to a specified straight-line affine algorithm, excluding constant-times-one products and initial additions to zero. They are not literal counts of Python `sum` internals. Input-oracle lookup/index costs are separate; `PeriodicInput.height` scans the additions list.

The exact local collection scheme is valid: give each vertex variable its vertex as owner, each edge variable the lower endpoint, and each halo variable its internal neighbor. Every variable owner appearing in a summand lies at its anchor or a nearest neighbor. Hence a nonconstant monomial's minimum-owner bucket needs only those local anchors. No nonconstant monomial is emitted twice. The global constant is exactly26V+E+sum_v eta_v^2+sum_h(eta_h-5)^2. The conservative local bound10738=7(955+3*173+6*10) raw entries is valid.

## Independent executable evidence

Only newly authored local programs were executed. The adapter provenance regression imports verified loader module definitions but builds no Circuit and runs no background evaluation, edge scans or universal computation. No upstream code was executed.

1. `audit_independent.py`: 2,240 initial configurations on prisms with1–4 vertices; all2,335 stable binary balance candidates checked with rank ranges through |V|+2; all2,168 feasible candidates have exactly one canonical rank vector and equal independent legal sink stabilization. Also checks21 signed rank differences and9 geometries.
2. `audit_polynomial.py`: a separate sparse-algebra implementation, used as an independent exact coefficient oracle.
3. `audit_crosscheck.py`:8 full exact polynomial comparisons;80 random off-zero evaluations;15 translated/degenerate geometry checks;2,240 constructor acceptance/rejection and odometer checks.
4. `audit_streaming.py`:16 random periodic/addition inputs through3x3x3 and4x3x2, including translations; exact local collection equals full global collection with no duplicates; all edge/halo inverse indices and closed versus enumerated operation ledgers agree.
5. `audit_adapter.py`: altered manifest/file rejection before import, cached foreign-module isolation, verified dependency paths, restored caller import state including explicit None cache entries, three huge iterator-prefix checks, and2,197 candidate halt-bound cases. All reviewer scripts use explicit exception guards rather than removable assert statements; all five suites pass normal and optimized Python with identical output.

Representative raw/collected counts:

| Prism; eta; exterior background | Raw | Collected |
|---|---:|---:|
| 1x1x1;0;0 |99|55|
| 1x1x1;6;0 |103|55|
| 1x1x1;6;5 |79|49|
| 2x1x1;(6,5);0 |473|345|
| 2x2x1;(6,5,4,0);0 |1624|1269|
| 2x2x2;(6,5,4,3,2,1,0,0);0 |4920|3913|

## Scope caveats

`PeriodicInput` implements nonnegative additions to a stable periodic background. The abstract proof also covers arbitrary finite modifications whose resulting heights are natural and whose support lies in the prism, but that wider interface is not implemented by this dataclass. The loader's global one-shotness and its quantitative support enclosure are separate hypotheses; these tests establish neither. The compiled family has variable arity as prism volume grows, and does not by itself compress the construction into one fixed Diophantine polynomial.

## Final proof review

The final `PROOF.md` was read in full. Its direct binary soundness argument is valid: fire support sites in nondecreasing rank, in any order within a tied layer. Before v fires its height is z_v+6 minus the number of its still-unfired support neighbors. That count is at most A_v, so success implies a legal firing. The previous-round inequalities independently force the unique canonical rank vector. This supplies an elementary no-borrowed-firing argument for the binary specialization.

All certificate-section constants were checked: raw bound1534V, expansion bound2414V, evaluation multiplication bound285V, addition bound235V-1, constant coefficient bound215V, nonconstant coefficient bound773136, and local record bound10738. The dimensional volume calculation also checks: with N=|ell|+|right|+T+1, the displayed prism has horizontal length at most16BN and time-axis length at most5BN, so V<=80B^2(Zmax+1)N^2. A hypothetical supplied T,p does not certify that exact halting time; the proof correctly distinguishes that from spatial closure.

The U15 simulation, one-shotness theorem, routing details, and claimed literal background query-operation counts were not independently re-audited here. Frozen-manifest and file integrity were checked by the adapter regression. Those remain the separately audited loader dependency. The adapter’s verified module definitions were imported solely for provenance checks; no loader computation or upstream code was executed by this independent audit. Final local replay covers both normal Python and Python -O, with explicit guards active in both modes.


## Adapter and primary test review

The complete final adapter and primary test source were read. The portable default is composition/../loader and an explicit --loader-root override is available. The default dimension command does not instantiate the loader. Source validation checks the pinned manifest hash and every one of its24 listed file hashes before import, isolates the two loader dependency module names, verifies their source paths and restores caller state. The primary tests use explicit require guards that remain active under -O. Their45-record literal coefficient-prefix check is a streaming regression, not a full giant-polynomial validation. The README correctly warns that even a --take limit cannot bypass the fully collected generator’s global constant scan. These tests and the adapter do not assert that hypothetical T,p are true halt data.


The final matching-work corollary also passes its algebra check. For s=n+T+1, the bounds |p|<=T and -L,R>=3 give D_L,D_R>=3. Since R-L>=n+2, their sum is at least s. Therefore each D(D-1)/2>=D^2/3 and the two-square inequality give A_CA>=s^2/6. The exact A_CA formula agrees with the separately audited loader’s `ca/SEMANTICS_AND_BOUNDS.md`, section5. Combining its distinct-active-root semantics with one-shotness and V<=Cs^2 gives the stated conditional halting-work order Θ(s^2), with no n-only computable stopping bound.
