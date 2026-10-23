# Sign recovery and centered norms for explicit ZFC consistency equations

Start with **`report.pdf`**. Its editable LaTeX source is `report.tex`, with
component sections included from the directories below. This package
was prepared for incorporation into ProveIt; it does not modify or publish
anything in the upstream repository.

## Results

Every displayed equation is an ordinary polynomial with fixed integer
coefficients. All auxiliary arithmetic registers are abbreviations, not
quantified variables. The ordinary mathematical proofs establish, in ZFC,
that existence of a zero on the stated domain is equivalent to a finite
refutation in the fixed ZFC calculus. Negating gives equivalence of absence
of zeros and `Con(ZFC)`.

| Domain | Unknowns | Exact degree | Live binary operations | Definition |
|---|---:|---:|---:|---|
| Strictly positive integers | **13** | **114** | **83** | `positive13/polynomial.json` |
| Unrestricted integers | **42** | **4** | Not optimized | `quartic42/quartic42.json` |
| Unrestricted integers | **35** | **6** | Not optimized | `quartic42/companions/sextic35.json` |
| Unrestricted integers | **30** | **8** | Not optimized | `quartic42/companions/octic30.json` |
| Strictly positive integers | **9** | **1,834,516** | **453** | `nine/generated/split_116_positive_global.json` |
| Nonnegative integers | 9 | 1,834,516 | 460 | `nine/generated/split_116_natural_global.json` |

Operation counts charge binary additions, subtractions and multiplications,
including multiplication by fixed scalars and every squaring. Constants
are leaves and reuse is free. This is not a bit-complexity measure.

The comparison revision is
`beb0192cb8dc36f78c369c080f2adfbc1887a486`, including packages 54–59.
The thirteen-positive result improves both named late alternatives:
degree 126/91 operations and degree 132/83 operations. The quartic reduces
45 unrestricted variables to 42. The historical sextic 42 and octic 36
become 35 and 30. The nine-positive companion improves degree 1,910,404/473
operations to1,834,516/453. Domains and tradeoffs are kept separate.

These are concrete local improvements. A globally simplest equation or a
major breakthrough in universal Diophantine representation has not been
established. The fifteen-positive degree 24 and twelve-positive degree 242
points are not improved here.

## New mathematical mechanisms

1. **Center a root before taking its norm.** The thirteen-variable equation
   replaces two root witnesses by one `t`, with `x=t+ell`. The identity
   `(d(x²-A)-e)²-4dAe=(d(x²+A)-e)²-4d²x²A` recovers an integer root
   directly; subtracting the known part `ell` cancels the highest terms.
   The full diagonal leading coefficient is `2^19*beta^67`, proving exact
   degree 114 on the actual fixed-coefficient instance.
2. **Recover a common sign after recovering the Pell rank.** The quartic
   replaces two ternary positive forms for `eta,zeta` by one for their
   product. Strengthening the existing scale to `w=4u²` lets the index
   congruence rule out a negative common sign. This saves three integer
   witnesses at degree 4.
3. **Move a square guard to an existing coordinate.** The sextic and octic
   first exchange `q=2qroot²` for `X=8rho²`. Since `X=wq` and `w=4u²`,
   the recovered equation `q u²=2rho²` implies `u|rho`. The exchange is
   proved before subsequent monic coordinate eliminations.
4. **Reorder sparse targets and share powers.** The nine-variable companion
   lowers convolution height 2161→2068, uses the coherent compact native
   tuple, and replaces 102 pure-base multiplications by an 88-gate shared
   addition chain. All 22,544 target interactions are checked exactly.

## Fixed coefficients and proof boundary

No coefficient placeholder remains. The complete compact44 tuple is used
by the thirteen- and nine-variable forms; the complete source34 tuple is
used by the quartic and its companions. Their four raw numeral encodings
occupy 295,388 and 532,479 bytes, respectively. The high mask is already
shifted. Ports from different tuples must not be mixed. Exact payloads, bindings, builders, transition tables, source pins and licenses are supplied.

The new reductions are ordinary mathematics formalizable in ZFC. They
retain the identified native compiler and K215/refutation calibration;
the nine-variable companion also retains its Jones ratio interface. The
other new forms do not use a Jones/Sun variable-reduction theorem.

This package does **not** supply a fresh end-to-end Lean/Rocq certificate or
an exported object-language ZFC derivation. The inherited K215 endpoint
statement is included, but its full transitive formal development is not
rebuilt. The included internal reviews and exact finite checks are labeled
by scope. They do not substitute for the unbounded mathematical proofs.
No consistency assumption is made in either direction of the equivalence.

The authenticated predecessor quartic has an off-by-one transcription in
its transport prose. Its literal equation uses
`(K0+w)C=F+z(q-1)`, and the correct restored guard is `z>0`. The original
source is retained unchanged; the correction and its proof are explicit
in the new article. The thirteen-variable circuit uses the old product
coordinate, which is one greater than this shifted coordinate.

## Offline verification

Requirements: **Python 3.10+**, standard library only. From this directory:

```sh
python3 verify_all.py
```

The root driver authenticates the delivered files, copies the three
components into a temporary directory, and runs every active finite replay
there. It leaves the sealed polynomial definitions and coefficient data
unchanged. A successful receipt and complete stage logs are written under
`verification/`. It checks actual coefficient reconstruction, sparse
identities, monic restoration maps, exact-degree certificates, and circuit
rewrites. It does not attempt a search for a refutation or a polynomial zero.

Optional optimized replay:

```sh
python3 -O verify_all.py
```

The optimization flag propagates to subprocesses. Both modes were checked
during preparation. No new acceptance condition relies on removable
`assert` statements. Historical scripts requiring SymPy are retained only
as inert provenance; the root replay does not execute them.

To rebuild the article with a normal TeX Live installation:

```sh
python3 build_report.py
```

The script runs three LaTeX passes to settle the table of contents and
cross-references. PDF byte identity is not promised across TeX versions.
The delivered PDF was rendered and visually checked.

## File map

- `positive13/`: literal 83-operation circuit, complete norm proof, actual
  compact tuple, two separate algebra/degree checkers, independent review.
- `quartic42/`: all 27 quadratic residuals, exact sum-of-squares expansion,
  common-sign proof, two sparse algebra implementations and reviews.
- `quartic42/companions/`: all sextic/octic residuals, the exchanged guard,
  all 19 monic elimination steps and 54 complete parent-row restorations.
- `quartic42/dependencies/`: authenticated Pell/native/compiler proofs,
  source34 coefficient construction and its independent decoder.
- `nine/`: exact sparse kernels and code, global arithmetic circuits,
  compact coefficient tuple and all 12 final fixed leaves, source proofs.
- `RESULTS.json`: machine-readable domain and complexity ledger.
- `SOURCE_SNAPSHOT.json`: immutable comparison revision and source links.
- `RESEARCH_NOTES.md`: unproved directions and rejected shortcuts.
- `MANIFEST.json`: SHA256 manifest; generated replay logs are excluded.
- `NOTICE.md`, `LICENSE`: authorship/review scope and license information.

Within `nine/`, `generated/LEDGER.json` describes the intermediate 467-gate
Horner evaluator. The final 453-gate object is the explicitly named
`split_116_positive_global.json`, with its own certificate. This distinction
is intentional.
