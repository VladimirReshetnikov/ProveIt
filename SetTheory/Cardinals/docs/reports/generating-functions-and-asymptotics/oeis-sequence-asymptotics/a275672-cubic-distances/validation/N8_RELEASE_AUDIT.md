# Independent focused audit of the side-eight exact result

## Conclusion and scope

The frozen source, run inputs, complete case list, summary, and lower-bound witness are internally consistent. Independent Python enumeration confirms that the recorded target-thirteen run covers every possible unique-diameter orbit in the side-eight lattice. No logical error or omitted diameter case was found. Together with the previously reviewed exhaustive-search algorithm, the recorded result and twelve-point witness support the computational claim **a_8 = 12**.

This audit did not rerun the 38,430,195-node impossibility search. It verifies source identity, complete outer case coverage, recorded execution consistency, storage and arithmetic ranges, and the constructive lower bound. Individual UNSAT cases rely on the reviewed C++ implementation and recorded execution; the package does not supply separate DRAT or theorem-prover certificates for them.

## Frozen source and execution records

The released `rainbow_edge_prefix.cpp` has SHA-256

```text
321fd408db85b0e91543dbac68838d784fd8ee16032aabfc52d4d6b2939ca64d
```

It is byte-identical to `sources/rainbow_edge_prefix6.cpp` in this audit bundle. Its prefix recursion was independently reviewed; the difference from the small-case-tested top-four source is the single CLI change admitting `top5` and `top6`. The induction proving completeness for a general processed edge prefix is in `SEARCH_AUDIT.md`.

All 36 files listed in the release manifest matched their recorded hashes at the time of the focused audit. Relevant SHA-256 values are preserved in `recorded/n8_release_audit.json`.

The complete run's inputs and output are:

| Parameter | Recorded value |
|---|---:|
| Side length | 8 |
| Target number of points | 13 |
| Edge prefix length | 6 |
| Scope | All diameter cases |
| First and last case index | 0 and 22 |
| Number of cases | 23 |
| Result of every case | UNSAT |
| Total inner-search nodes | 38,430,195 |
| Recorded elapsed seconds | 445.028 |

Every log row has the independently expected endpoint identifiers and squared diameter. The cumulative node counts and times are nondecreasing, and the final row agrees with the JSON summary. There is no missing row, UNKNOWN result, or single-case restriction in the complete run.

## Independent diameter coverage

The point identifiers are the lexicographic enumeration of `(x,y,z)` in `{0,...,7}^3`, equivalently `64*x + 8*y + z`. The independent audit constructs all points and the exact palette directly from integer sums of three coordinate-difference squares. The palette has **87** positive members.

A thirteen-point configuration has 78 pairwise distances. Its longest squared distance is therefore at least the 78th palette member, **101**. There are **660** unordered grid edges whose squared lengths meet this threshold.

The audit independently constructs all 48 coordinate-permutation/reflection maps as permutations of the 512 integer point identifiers. It takes the smallest sorted identifier pair in each orbit. The 660 eligible edges form exactly **23** orbits, whose sorted representatives match all logged cases. This calculation uses a representation different from the C++ source's coordinate-sextuple canonicalization.

Every valid configuration has a unique longest edge because every pairwise distance is distinct. Applying a cube isometry places that edge at one of these representatives. It is therefore enough to exclude completions of every recorded representative.

The stronger modulo-four check below raises the necessary diameter to 102. The search's weaker threshold 101 consequently includes some unnecessary cases, but omits none.

## Radial, parity, and storage checks

For diameter endpoints p and q at squared distance D, every other selected point v must satisfy

```text
0 < |v-p|^2 < D,   0 < |v-q|^2 < D,   |v-p|^2 != |v-q|^2.
```

These are exactly the initial candidate conditions. The independently computed initial candidate counts range from 445 to 510; every case's count and parity split are retained in the JSON audit output. These counts are recorded for transparency, not asserted to be sufficient for a completion.

At a recursive state with s chosen vertices and `need = 13-s`, the `s*need` selected-to-new edges of any valid completion must have distinct squared lengths. Thus the union of candidate radial colors must contain at least that many elements. Any valid completion's full set of 78 colors lies in the source's `available` union. These are necessary conditions and justify the radial and palette-count pruning.

Squared-distance parity equals the parity difference of the coordinate sums. If the final two parity classes have populations x and 13-x, exactly `x*(13-x)` selected distances are odd. The dynamic parity test enumerates every possible number of new vertices in either class allowed by the candidate pool, and checks their required odd and even distances against available capacities. It cannot discard a valid completion.

Modulo four, the squared length between two points is the Hamming distance between their three coordinate-parity bits. Within one of the eight classes it is 0 modulo four. The source's occupancy requirements and dynamic residue capacities therefore give necessary conditions, including all possible class populations compatible with the selected set and remaining candidates. Each class in the side-eight grid contains exactly 64 points.

There are 512 vertices, within the 1024-bit vertex capacity. Squared distances are at most 147, within the distance-mask indices 0 through 255. All target pair counts, class populations, degrees, palette indices, and distance arithmetic fit the declared integer ranges. Before thirteen vertices are selected, at most six prefix ranks are processed; their palette indices are nonnegative and within the 87-element palette. The node total is stored in an unsigned 64-bit integer.

## Independent lower-bound witness

The audit verifies that `n8_k12_verified.json` contains exactly twelve different integer points inside `{0,...,7}^3`. It recomputes all 66 unordered squared distances, checks their uniqueness, and compares the sorted result against the recorded list. All checks pass.

## Modulo-four minimum-diameter certificates

Let z_i be the number of selected points in parity class i, for i = 0,...,7 in binary order. For a target of k points, enumerate every nonnegative vector z with sum k. The required counts of squared-distance residues are

```text
R_0(z) = sum_i binom(z_i,2),
R_r(z) = sum_{i<j, Hamming(i,j)=r} z_i*z_j,    r=1,2,3.
```

Let L_r be the increasing list of members of the exact cube distance palette that are r modulo four. A vector z can pass the residue-capacity condition for diameter at most D only if `R_r(z) <= # {d in L_r: d <= D}` for every r. Its least possible capacity-feasible diameter is therefore the maximum, over nonzero R_r(z), of the R_r(z)-th element of L_r. An occupancy whose requirement exceeds a full palette class is globally infeasible and is discarded.

`verify_mod4_diameter.py` evaluates this expression with integer arithmetic for every weak composition. Taking its minimum over all occupancies proves infeasibility for every smaller squared diameter. Its defaults give:

| n | k | Occupancies enumerated | Distance-count threshold | Modulo-four threshold |
|---:|---:|---:|---:|---:|
| 8 | 13 | 77,520 | 101 | **102** |
| 9 | 15 | 170,544 | 136 | **149** |
| 10 | 17 | 346,104 | 181 | **209** |

For example, at squared diameter 101 in side eight the four palette capacities are `(17,25,24,12)`, and none of the 77,520 occupancies fits. At diameter 102 they become `(17,25,25,12)`. The occupancy `(0,1,1,2,2,1,6,0)` has requirements `(17,25,25,11)` and fits those capacities. It certifies that 102 is the precise threshold of this residue relaxation, while saying nothing about the geometric realizability of that occupancy. The analogous attaining vectors and capacities for the other two instances are retained in the JSON certificate.

## Reproduction

Both focused audit scripts use Python 3.9 or later and only the standard library. They accept output paths, and the release checker accepts a configurable release directory. No scratch-workspace paths are embedded.

```bash
python audit_n8_release.py --release-dir ../exact_search/release --output n8_audit.json
python verify_mod4_diameter.py --output mod4_diameters.json
```

Adjust the release path to the package layout. The first command checks the run records and witness without executing the C++ solver. The second independently recomputes the finite residue-relaxation minima.
