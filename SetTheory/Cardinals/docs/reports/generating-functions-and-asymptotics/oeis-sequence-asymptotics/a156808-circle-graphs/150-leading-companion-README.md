# Report150 exact computational companion

Fresh Python 3.10+ standard-library code. No network access, downloads, optional
packages, floating-point approximations, or prior companion code are required.
The exact finite checks support review of the mathematical argument. They are
**not a proof of an asymptotic theorem, a convergence-rate certificate, a
uniform numerical threshold, or a priority/novelty certificate**.

## Run

From this directory:

```sh
python verify.py
python -O verify.py
python -m unittest -v
python -O -m unittest -v
```

Each verification/test command took about two seconds in the preparation
environment. The verifier recomputes the full evidence and compares every
field, including types, rather than trusting a saved success flag or hash.
Normal and optimized Python execute the same explicit mathematical guards.
The test suite contains 24 targeted semantic mutations, structural mutations,
JSON duplicate-key/nonfinite-value rejection, and integer-type substitution
checks. `bool` and `float` are not accepted as integer evidence.

To create a new independent evidence file, give a **fresh**, nonexistent path
whose parent directories already exist:

```sh
python circle_companion.py --output /tmp/report150-new-evidence.json
python verify.py /tmp/report150-new-evidence.json
```

The output writer never replaces an existing file. Its POSIX descriptor-pinned
I/O uses `O_EXCL` and `O_NOFOLLOW`, rejects symlink components and `..`, and
requires regular files on reads. POSIX `O_DIRECTORY`/`O_NOFOLLOW` support is
required (Linux and macOS). These protections are tested under `-O` too.
Generating without `--output` targets `evidence.json` and therefore refuses to
overwrite the included reference file. No parent-package helper is needed.

## Exactly what is checked

- Perfect matchings and graph-isomorphism classes are exhaustively enumerated
  for orders 1–6. The recovered connected counts are 1, 1, 2, 6, 21, 110, and
  the all-graph counts are 1, 2, 4, 11, 34, 154. Exact reciprocal graph-fiber
  sums recover the graph counts
- Every rotation and reflection fixed-count formula is checked against all
  indexed matchings for orders 1–6. Full dihedral actions, including both
  orientations, are used; small-order nonfaithfulness is handled by the actual
  stabilizer and orbit-stabilizer identity
- For every admissible nonshort fixed chord at orders 4–7, direct enumeration
  checks both forms of the long-leaf count. Exact convolution ratios and the
  stated endpoint-sum upper bound are checked at 8, 16, 32, 64, and 128
- A six-chord asymmetric split-prime core is checked for connectivity, minimum
  degree, absence of nontrivial splits, and trivial graph/geometric
  automorphisms. Independent moves of 1, 2, or 3 leaves give respectively
  2, 4, or 8 distinct full dihedral orbits, all with trivial stabilizer
- For the one-leaf example, all 135,135 seven-chord indexed matchings are
  examined. Its entire graph-representation fiber contains exactly 56
  matchings in two dihedral orbits of size 28. This finite equality is not
  substituted for a general fiber-equality theorem: the proof needs only its
  stated lower bound on representation-fiber size
- Chord-level L/T/F insertions are checked independently against graph-level
  operations. Deleting leaves, recovering twin classes, and contracting
  them recovers the exact original core and each decoration's vertex/type.
  Disjoint twin swaps are tested directly; complete automorphism enumeration
  gives the predicted elementary-abelian group orders 1, 2, 4, or 8
- A different six-chord diagram has geometric stabilizer order 1 but graph
  automorphism order 4. This explicitly distinguishes representation symmetry
  from graph automorphisms outside the split-prime uniqueness setting
- At order 6, all 10,395 indexed matchings are used to verify the exact
  X/Y/Z means `12/11`, and the 108 generated Z patterns are distinct.
  Three explicit forcing witnesses (two singleton edges and one two-edge
  pattern) have equal preimage counts: 11 for each singleton target and 99
  for each two-edge target. Every original edge outside the forced support
  survives. This is finite conditional-law evidence, not a computational
  certificate for the report's asymptotic Palm/Stein bound
- Exact rational multinomial identities check deficit coefficients through 6.
  Finite decoration weights are evaluated at orders 20, 50, and 100 for
  deficits 0–4. These are algebraic checks, not convergence estimates
- Exact Laurent-polynomial algebra in `D=log(2u)` and `c=log(2)` checks the
  smooth inverse displacement, including the forced `+1` and
  `(3+log 2)/(2 log(2u))`. Shifted-gamma Stirling terms through degree 4 are
  recovered rationally. These calculations do not imply a quantitative
  remainder for either graph sequence
- An exact threshold example on the integer gamma-model values demonstrates
  why a sequence asymptotic to that model may have a least-index inverse one
  larger than the unqualified ceiling of its smooth inverse. Multiplicative
  envelope ceilings bracket the two adjacent possibilities

## Source counts and provenance

`sources/oeis_snapshot.json` contains the captured A156808/A156809 entries;
`sources/danielsen_parker_table3.txt` contains the local text extraction of
Danielsen–Parker Table 3. Their connected and all counts agree through 12.
The all-count OEIS snapshot also gives order 13. The original local source
file hashes and source links appear in `sources/provenance.json`; all included
snapshot hashes are recorded in the evidence.

The connected-to-all Euler product is independently checked through 12.
Inverting the logarithmic derivative of the all-count Euler product recovers
the connected source counts through 12 and derives
`c_13 = 21,593,488,017`. This order-13 connected value is **derived**, not a
Danielsen–Parker Table 3 entry or a value in the captured A156808 snapshot.
The finite identity “graphs with an isolate = all graphs one order smaller”
and the component-product upper bound for the remaining disconnected graphs
are checked through order 12.

Sources:
- https://oeis.org/A156808
- https://oeis.org/A156809
- https://arxiv.org/abs/0804.2576, Table 3, printed page 8

## Files

- `circle_companion.py`: exact constructions, enumerations, algebra, and JSON generator
- `verify.py`: fresh semantic recomputation and strict comparison
- `safe_io.py`: standalone safe file I/O
- `test_companion.py`: unit and adversarial tests
- `evidence.json`: deterministic exact results; fractions have integer numerator/denominator fields
- `sources/`: bounded factual snapshots and provenance
The reference evidence is deterministic. Runtime transcripts and exploratory
files are excluded from the source archive.
