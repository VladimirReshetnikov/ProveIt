# Finite algebra and stable selection in iPRA

Research report prepared for Vladimir Reshetnikov, 19 November 2026.

## Read first

- `paper/report.pdf` is the complete human-readable report.
- `paper/report.tex`, `paper/sections/`, and `paper/references.tex` are its complete LaTeX sources.
- `lean/` contains proposed proof code, explicit targets and a detailed formalization roadmap.
- `code/` contains executable exact-arithmetic reference implementations.
- `validation/` contains the results of checks actually executed.
- `research/` contains the source audit, selected pinned upstream snapshots and independent mathematical reviews.

The ProveIt source snapshot is
`3ee850b4c2d650cf01263823fd5415963747c5d0`.

## Main results

### Automatic nonzero polynomial norms

For a nonconstant squarefree rational polynomial `f`, any positive integer `m`,
and any nonzero reduced polynomial `G = sum A_j(X) Y^j` with `j < m`, the
multiplication norm modulo `Y^m - f(X)` is nonzero and has degree at most

`W = max_j (m deg A_j + j deg f)`.

The proof uses actual repeated polynomial division. Write
`A_j = f^(a_j) B_j`, with `B_j mod f != 0`. The weights `m a_j + j` have
a unique minimum `s`, at `k`. The actual determinant satisfies

`N(G) = f^s ( (-1)^(k(m-1)) B_k^m + f Q )`.

A factorization-free Bezout argument proves that `Q[X]/(f)` has no nonzero
nilpotents, so the bracket has nonzero residue. No root or irreducible
factor is selected, and `gcd(m, deg f) = 1` is unnecessary.

The more general certificate `f = g^e h`, `gcd(m,e)=1`, a reduced quotient
by `g`, and a Bezout witness for `g,h` also works. A separate local Newton
certificate extends the argument to mixed monic equations. An inherited
initial-form determinant test is credited to the previous work; this report
adds its compression from size `m` to `gcd(m,deg f)` in the superelliptic case.

### Finite common-zero and subspace bounds

The report develops the full fiber-multiplicity argument: a fiber containing
`r` distinct common zeros contributes `(X-a)^r` to the norm. Thus any supplied
finite list of distinct common zeros has length at most the norm degree.
Bounded row elimination supplies nonzero annihilators for proper subspaces,
giving a weighted subspace-fiber cap `L` and a finite-cover cap `C L`.

The norm/fiber mechanism is inherited and restated in full. The automatic
nonvanishing hypotheses are strengthened here. These cardinality statements
do not provide a general height bound or a global Diophantine cover.

### Canonical points from convex finite approximations

Finite Hausdorff-coherent rational clouds with a certified midpoint defect
admit an explicit canonical point selector. The selector minimizes squared
distance to a supplied anchor. Its proof cancels two objective values at a
common midpoint, so neither an exact infimum nor an objective-gap program is
required. Sampling stage `2k+c`, where `2^c >= 24dB`, gives a fast Cauchy name.

A concrete cloud producer for convex hulls of named vertices works through
coincident vertices and affine rank collapse. Counterexamples show why the
input representation and midpoint condition are substantive.

## Proof status

| Layer | Status |
|---|---|
| Main mathematical arguments | Fully developed human proofs with explicit finite algorithms and induction obligations |
| Exact reference computations | Executed successfully; see `validation/` |
| New midpoint object-iPRA proof | Complete proposed source, **not elaborated** |
| New norm and selection object endpoints | Detailed targets/blueprints, **not kernel-checked** |
| `SemanticSquarefreeTargets.lean` | Definitions of ordinary Lean specifications; **not proofs** and not object-iPRA exports |
| Existing ProveIt components | Status reported from pinned source and inspected declarations; no fresh full repository build |

There was no Lean executable or compiled Lean dependency cache available.
The source does not claim that the main new theorems have already been checked
by Lean. A definition of a target proposition is not a proof of that target.

## Reproduce the finite computations

Use Python 3.10 or later and SymPy (the exact version used is recorded in
`validation/environment.json`):

```bash
python3 -m pip install -r requirements.txt
bash run_exact_checks.sh
```

The checks cover 54 mixed local-Newton cases, 41 compressed leading tests,
80 squarefree quotient-algebra cases, 29 separate polynomial-division-order
certificates over rational and finite fields, and explicit edge cases.
The convex suite checks 4,474 cloud/anchor combinations, 3,101 rounding cases,
3,101 midpoint certificates and 1,127 transfer certificates.

The optional figure uses Matplotlib:

```bash
python3 code/make_projection_figure.py
```

Exact fractions determine the plotted selections. Floating point is used
only to render coordinates, not in the arithmetic validation.

## Build the PDF

On a configured TeX Live installation:

```bash
bash build_report.sh
```

The figure is already included; it need not be regenerated. The report uses
ordinary LaTeX packages including AMS mathematics, Latin Modern, geometry,
microtype, longtable, hyperref and xurl. The preparation environment needed
a local format/font-map bootstrap; the exact recipe is in
`validation/BUILD_ENVIRONMENT.md`.

## Continue the Lean formalization

Use a ProveIt checkout at the exact pinned commit and its declared dependencies:

```bash
bash lean/check_against_proveit.sh /absolute/path/to/ProveIt
```

The script refuses a different revision, builds the selected upstream
providers, and attempts elaboration of the candidate files. It is a replay
command, not a record of a successful run. The selected source snapshots in
`research/` are for inspection and are not a complete transitive dependency
closure. `lean/FORMALIZATION.md` and `lean/SQUAREFREE_FORMALIZATION.md` give
the exact remaining work and distinguish semantic from object-theory targets.

The principal next modules are runtime polynomial division/Bezout,
polynomial-division orders and determinant carries, fiber multiplicity,
runtime annihilators, rational midpoint comparison and the actual cloud
selector. These extend the current arithmetic library rather than replacing
its existing bounded-syntax or finite-demand compilers.
