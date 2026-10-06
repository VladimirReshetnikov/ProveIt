# Report153 exact computational companion

This self-contained, standard-library-only Python companion verifies the finite
inputs and rational coefficient identities for the fixed-order factorial
expansions of unlabeled permutation graphs and exact-four-realizer graphs.
It also verifies the resulting logarithmic, formal inverse, and total-variation
series. No original research file, external package, network access, or private
path is needed at run time.

**Scope:** finite computation is not a proof of an all-orders asymptotic
remainder, large-core transfer, exact-fiber multiplicativity, an eventual
rounding threshold, or novelty. Those are mathematical obligations in the
report. All asymptotic interpretations are at fixed order. The companion
neither estimates an onset nor supports a growing truncation index.

## Reproduce

Requirements: Python 3.10 or later, on a POSIX system supporting `O_NOFOLLOW`,
`O_DIRECTORY`, directory file descriptors, and same-filesystem hard links.
The recorded runs use Python 3.12 on Linux. Run these commands from this
`companion/` directory; no installation is necessary:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B test_companion.py
python3 -B -O test_companion.py
```

The default checker reconstructs every rational coefficient and exhaustively
replays **both graph enumeration methods through order 6**. The 33-test suite
also compares both sampling enumerations through order 7, including the first
nontrivial marked-context count. Default runs take seconds on a typical modern
machine; exact graph enumeration has rapidly increasing cost.

Replay all sampling inputs through order 8, or all full-graph inputs through
order 9:

```sh
python3 -B verify.py --enumerate-through 8
python3 -B verify.py --enumerate-through 9
python3 -B -O verify.py --enumerate-through 9
```

The full order-9 run checks both `a_n,r_n` sequences through 9 and both `b_n,c_n`
sequences through 8. It does **not** claim a value of `g_7`. Full runs can take
minutes. To isolate a route, use `--enumerator degree` or `--enumerator refined`.
`--enumerate-through 0` performs algebra only and explicitly labels that scope
in its output.

Every successful checker invocation prints a complete, deterministic JSON
record to standard output and exits 0. Mathematical or I/O failure exits 1;
invalid CLI syntax exits 2. The test runner writes progress to standard error
and a JSON summary to standard output. It exits nonzero if any test fails.

To retain a result using the program's publication safeguards, choose an unused
filename:

```sh
python3 -B verify.py --output results/my-default-replay.json
python3 -B verify.py --enumerate-through 9 --output results/my-full-replay.json
python3 -B -O test_companion.py --output results/my-optimized-tests.json
```

## Fixed exact inputs and independent enumeration

`inputs.json` contains these exact, finite counts:

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `a_n`, unlabeled classes | 1 | 2 | 4 | 11 | 33 | 142 | 776 | 5699 | 50723 |
| `r_n`, vertex-rooted classes | 1 | 2 | 6 | 20 | 89 | 504 | 3776 | 34620 | 368683 |

Each entry through order 9 was already exhaustively enumerated by two original
implementations. This release additionally replays both adapted implementations
through 9. Counts are of graph isomorphism classes and vertex **orbits**, not
labeled graphs or arbitrary marked vertices.

The independent routes in `enumeration.py` retain separate graph construction,
canonicalization, and root-counting code:

1. **Degree route.** Adapted from the research `compute_rooted.py`. It enumerates
   all labelings inside degree classes, minimizes triangular edge masks, and
   separately canonicalizes root-colored graphs to distinguish rooted classes
2. **Refined route.** Adapted from the independently authored
   `independent_enumeration.py`. It iteratively refines vertex colors, minimizes
   bit-adjacency encodings within color cells, and recovers root orbits from
   minimizing labelings and their automorphisms

Every permutation of each requested order is visited, and the visitation count
is checked against `n!`. Neither route uses precomputed answers in its search.
Exact caching reuses only graphs identified by a complete adjacency encoding
under an explicit relabeling. Twin-vertex reductions discard only permutations
already proved to be automorphisms; the refined route restores their exact
multiplicity and joins their orbits. The test suite compares these reductions
with brute-force automorphism enumeration for every labeled graph through
order 4. Source-file SHA256 digests and adaptation details are recorded in
`enumeration.py` and `provenance.json`.

### One-realizer graphs and marked contexts

For a graph class `G`, let `f(G)` be its full fiber of normalized permutation
realizers. For a rooted class `(G,v)`, the marked-realizer count is

`t(G,v) = f(G) * |Aut(G) v|`.

Thus `b_n` counts graph classes with `f=1`; `c_n` counts singleton vertex orbits
of those classes. Having one unmarked realizer does not make every rooted
version a one-marked-realizer context.

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `b_n` | 1 | 2 | 2 | 4 | 2 | 8 | 4 | 22 |
| `c_n` | 1 | 0 | 0 | 0 | 0 | 0 | 2 | 0 |

Both companion enumeration routes collect complete fiber histograms. The
degree route identifies singleton root orbits by grouping root-colored keys;
the refined route obtains orbit sizes from minimizing labelings. Each retained
one-realizer witness lists its normalized permutation and singleton-orbit
positions, both one-based. At order 7, the two nontrivial witnesses are
`[3,6,1,4,7,2,5]` and `[5,2,7,4,1,6,3]`, with singleton position 4 in each.

The original sampling calculation reused the earlier refined-route primitives;
it is not represented as a third independently authored graph method. The
fresh two-route replay here supplies an independent check of all `b,c` inputs.

## Exact coefficient construction

All arithmetic uses Python integers and `fractions.Fraction`. Put

`F(x) = sum_{n>=1} n! x^n`, `T = F^{-1}` under composition,
`A(x) = sum a_n x^n`, and `C(x) = sum r_{d+1} x^d`.

The direct route solves `F(Q)=A` recursively and constructs

`H = C * Q' / ((Q/x) A') * exp((1 - 1/(Q/x))/x)`.

It checks the reversion residual, `Q=x+O(x^3)`, integrality of the prefactor and
exponent, and integrality of `k! h_k` at every computed order. It obtains

`h_0,...,h_7 = 1, -4, -1, -94/3, -769/6, -19969/15, -531812/45, -40114096/315`.

The second route uses Lagrange inversion

`t_n = (1/n) [z^(n-1)] (z/F(z))^n`

to construct `T`, builds the normalized known simple-permutation asymptotic
series, and applies the finite-polynomial transfer separately for `R=1,...,8`.
It checks stabilization and agreement with every coefficient from the direct
route. The two mathematical constructions share rational-series primitives,
but the second route does not call or import the recursive-Q constructor.

The normalization is

`a_n ~ (1/4) sum_{k>=0} h_k (n-k)!`.

Only `a_1,...,a_9` and `r_1,...,r_8` enter `h_0,...,h_7`; `r_9` is retained as
an additional exact enumeration check. Mutation tests confirm that changing
`a_9` or `r_8` changes `h_7` and leaves earlier coefficients unchanged.

### Logarithm and inverse residuals

The checker converts falling-factorial terms into ordinary powers, computes
`log U` both by logarithmic differentiation and by the finite `log(1+v)` power
sum, and adds the exact Bernoulli/Stirling correction. It recovers

`log a_n = n(log n-1) + (1/2)log n + C - 47/(12n) - 9/n^2 + ...`,

where `C=(1/2)log(2*pi)-log 4`. In a rational Laurent-polynomial ring with
formal variables `D=log u` and `C`, it verifies the constant and `1/u` residuals
for

`delta_0 = -1/2 - C/D`,

`delta_1 = 97/(24D) - C^2/(2D^3)`.

The first-shift `1/u` residual is `-97/24+C^2/(2D^2)`; the second shift cancels
it exactly. The nonzero `1/u^2` residual is reported explicitly. These formal
identities provide no effective numerical error constant, threshold onset, or
unconditional rounding rule.

### Exact-four fibers and total variation

Substituting `J=sum b_j x^j` and `K=sum c_{d+1}x^d` for `A,C` gives `H4`.
Both the direct and finite-polynomial routes agree through degree 6:

`g_0,...,g_6 = 1, -8, 22, -230/3, 382/3, -22468/15, -283418/45`.

Let `U,V` denote the ordinary inverse-power transforms of `H,H4`. The checker
forms `V*(1/U-1)` and independently solves `U*TV=V*(1-U)` by coefficient
recurrence. Its coefficients of degrees 1 through 7 are

`4, -15, 169/3, 215/2, 26449/15, 232253/10, 101570743/315`.

Because `1/U-1` has constant term zero, only `g_0,...,g_6` are needed for degree
7. The checker explicitly varies the unknown degree-7 coefficient of `V` and
verifies that the reported result is unchanged. No value of `g_7` is inferred.
A mutation test sets `c_7=0` and confirms the resulting changes of 2 in `g_6`
and 8 in the seventh TV coefficient. This guards against incorrectly discarding
the outer marked-context factor.

The asymptotic interpretation uses total variation as `sup_E |P(E)-U(E)|` and
the report's separate proof that fibers below four contribute only a
superpolynomial error. The companion does not reprove that statement or the
large-core exact multiplicativity lemma.

## Claims, output safety, and release evidence

`claims.json` is an explicit list of exact rational regression targets, separate
from construction code. The program checks its entire key set and every value.
`--claims` and `--inputs` permit controlled alternate inputs. There is no command
that silently updates expected claims. Input reads are descriptor-pinned,
nonblocking, size-limited to one MiB, and reject duplicate keys, nonfinite JSON
constants, special files, symlinks, symlink parents, and `..` traversal. Rational
claim strings must be reduced canonical fractions; input counts must be actual
integers rather than booleans.

`--output` accepts only a **new `.json` file strictly inside this companion's
existing `results/` directory**. It refuses existing files, directories, FIFOs,
symlinks, dangling symlinks, symlink parents, paths outside the allowed root,
and `..` traversal. It never creates parent directories. Every parent component
is opened using a no-follow directory descriptor. A temporary file is fully
written and fsynced before an exclusive hard link publishes the final filename;
this is atomic and cannot clobber a racing existing destination. Temporary files
are removed on ordinary failure. Confinement is checked lexically before the
parent is pinned: if an already-open parent is renamed, publication follows
that directory and may no longer be reachable under the original `results/`
pathname. If directory fsync fails after publication, the command can report
failure with a complete destination present; no partial JSON is exposed.
Shell redirection is outside these safeguards.

The 33 tests cover normal and `-O` subprocess equality; altered main, inverse,
sampling, and TV claims; fixed-input mutations; formal coefficient dependencies;
finite graph reductions; and I/O safeguards, including FIFO rejection, parent
symlink swaps, simulated write failure, and competing publication. Checks use
explicit exceptions, never removable `assert` statements.

Current release results:

- `results/check-release-normal.json` and `check-release-optimized.json`: default
  two-route replay through 6; checker payloads are byte-identical
- `results/check-full-release-normal.json` and
  `check-full-release-optimized.json`: both full-graph routes through 9 and both
  sampling routes through 8; checker payloads are byte-identical
- `results/tests-release-normal.json` and `tests-release-optimized.json`:
  all 33 tests pass; runner optimization level is recorded

`provenance.json` contains source digests, precise independence limits, executed
commands, and a release `package_files` allowlist. Only those files belong in
the user-facing release. Earlier intermediate result files may remain in the
working directory but are excluded. No private audit, unrelated report, or
original external research script is bundled or imported. Provenance records
hashes of all allowlisted files except itself; the enclosing release manifest
can hash `provenance.json` without a self-reference.
