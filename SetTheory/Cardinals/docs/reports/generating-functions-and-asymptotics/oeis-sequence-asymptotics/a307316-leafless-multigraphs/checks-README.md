# Report131 finite verification suite

This directory is a portable, standard-library-only exact check suite. **Passing these checks does not certify an analytic asymptotic theorem, a source quotation, an error bound at infinity, or a novelty claim.**

## Replay

From the package root, with Python 3.10 or newer on a POSIX system supporting `O_DIRECTORY` and `O_NOFOLLOW` (such as Linux or macOS):

```
replay_dir="$(mktemp -d)"
python checks/verify.py --output "$replay_dir/results-normal.json"
python -O checks/verify.py --output "$replay_dir/results-optimized.json"
cmp "$replay_dir/results-normal.json" "$replay_dir/results-optimized.json"
```

The optional output file is the only requested persistent write; the replay commands above leave the package unchanged. Output must be a new file strictly outside the entire package. Existing files, symlink targets or ancestors, parent-traversal components, and missing parent directories are rejected before the mathematical checks start. Final creation rechecks the target and uses exclusive, no-follow creation via directory file descriptors, so an existing file is never overwritten. Omit `--output` for stdout-only operation. All adversarial mutations take place in disposable temporary directories. The verifier does not access the network or the original source directory. JSON is also written to standard output. A rejected check exits nonzero and writes `VERIFICATION FAILED` to standard error.

All runtime guards call an explicit exception-raising function; none uses Python's `assert` statement. The normal and optimized runs execute the same thirty intentional rejection cases. The checked-in outputs are byte-identical. `replay-evidence.json` records an additional replay from an isolated copy and an AST check for assertion statements, preservation of the copied package, and fail-fast output rejection even when the fixture in a disposable copy is corrupt.

## Exactly what is checked

1. **Exhaustive unlabelled graph counts, 0–6 edges.** For each positive edge count `m` and `2 <= n <= m`, enumerate every weak composition into the `binom(n,2)` unordered vertex-pair multiplicities. Filter by minimum degree at least two. Take the lexicographically smallest adjacency-multiplicity vector over *all* `n!` vertex permutations as the exact canonical key. Connectedness is tested by traversal of the positive-multiplicity support. The bound `n <= m` follows from the degree sum and makes this enumeration exhaustive. There are 46,686 candidate compositions in this graph-count check. The resulting A307316 counts are `1,0,1,2,5,11,34`; A307317 counts are `1,0,1,2,4,9,26`. Their initial `1` is the supplied exceptional OEIS convention. The actual empty-graph connectedness predicate returns false. Vertex-count breakdowns are in the output.
2. **Euler relation and inverse, 0–50 edges.** Direct finite multiplication of `prod_(k>=1) (1-x^k)^(-C_k)` recovers all supplied A coefficients. A separate logarithmic-derivative/divisor recurrence recovers all C coefficients from A, with explicit integrality and nonnegativity checks. `C_0` never enters the product. Beyond six edges this is a consistency check of the supplied two tables, not an independent graph enumeration.
3. **Composition factorial moments.** By enumeration, check `E[binom(X,r)] = binom(m,r) K^(rising r)/M^(rising r)` for `1 <= M <= 6`, `0 <= m <= 7`, `0 <= K <= M`, `0 <= r <= 5`: 1,296 rational identities, including empty subsets and orders larger than the total. Separately check 28 exact empty-cut count/product identities for `4 <= n <= 6`, `0 <= m <= 6`, `2 <= s <= floor(n/2)`.
4. **Monotone Pólya coupling.** For `1 <= N <= 5` and `0 <= k <= 6`, verify all 791 transition rows with probabilities `(a_i+1)/(N+k)`, all 3,465 coordinatewise-increasing transitions, and all 1,281 uniform target probabilities. These are uniform **vertex-labelled composition** checks. Independently, exact fixed-vertex probabilities of minimum degree two, with and without connectedness, satisfy 70 adjacent-total monotonicity comparisons in the graph enumeration range.
5. **Formal expansions.** Exact rational polynomial arithmetic implements addition, multiplication, reciprocal, and logarithm of truncated series. Forward and inverse coefficient recurrences have zero residual through order six, the displayed coefficients through order three match the independent constants in the verifier, and a second direct substitution checks each expansion. All coefficients through six are in the output. This finite extraction complements, rather than replaces, the analytic argument for an expansion at every fixed order.
6. **Source integrity and adversarial cases.** A SHA-256-pinned fixture and a closed two-file public-source inventory are checked before and after the run. The thirty expected rejections include eighteen cases exercising false guards, invalid composition/graph inputs, malformed b-files, invalid formal-series domains, byte corruption, missing/extra inventory members, an altered OEIS term, and substitution of a symlink. The other twelve cases cover output confinement for the whole package, the verifier and source files, existing external targets, symbolic targets/ancestors, dangling links, parent traversal, missing parents, and attempts to replace files after an initial check. The inputs must remain unchanged throughout.

## Provenance and limitations

`sources/` contains only the two supplied public OEIS b-file snapshots. Their public URLs and SHA-256 digests are recorded in `fixtures.json` and `source-provenance.json`. These are the supplied table snapshots, **not a fresh online retrieval**.

The snapshots are read-only for ordinary use. Read-only permissions alone are not an immutability guarantee: the digest checks detect changes. The verifier's fixture digest is pinned in `verify.py`; the outer package inventory protects the verifier and its other files. A party deliberately changing both a verifier and its pinned expected hashes can of course manufacture a different test package. The final report's closed inventory and independently retained package hash identify this package.

Hash verification identifies the public snapshot bytes. Finite graph agreement, a finite Euler transform, and finite formal-series identities are not sufficient to justify an asymptotic connected/total ratio, a relative equivalent, or a novelty claim. Those require the separate mathematical argument and primary-source audit discussed in the report.
