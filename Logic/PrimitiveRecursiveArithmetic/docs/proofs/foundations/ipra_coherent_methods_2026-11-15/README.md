# Coherent finite methods for intuitionistic primitive recursive arithmetic

Research report and executable companion prepared for Vladimir Reshetnikov,
15 November 2026.

## Start here

- Read `paper/ipra_coherent_methods.pdf` for the complete human-readable arguments.
- The full LaTeX source begins at `paper/ipra_coherent_methods.tex`.
- Read `lean/FORMALIZATION.md` for the exact definitions, checked lemmas,
  remaining theorem targets, and ordered path to complete Lean formalization.
- Consult `PROOF_STATUS.json` before interpreting any build or test result.
- `provenance/source_manifest.json` records the inspected repository sources.

The source review is pinned to ProveIt commit
`052fbaebfc955294b4c02f6532ab7e7a3f760f7a`. It covers the proof-packet index,
three existing embedding frameworks, the necessary ConciseIPRA interfaces,
and selected application reports. It is not a verification of all 54 packets.
Existing finite-demand, bounded-loop, scalar Hensel, analytic-chart, and
hyperelliptic-norm work is explicitly credited. No claim of historical
priority is made for the underlying algebraic ideas.

## Main mathematical results

### Coherent finite presentations

An object is presented by a specified primitive recursive producer of finite
observations, with bounded validity and equality tests and explicit restriction
maps. Correctness, preservation under restriction, and finite uniqueness imply
coherence. This is a finite proof transformation. It does not use countable
choice, a universal evaluator for all primitive recursive programs, or
reflection from proof checking to arithmetic truth.

Operations state their precision demand. Multiplication reads the requested
jet prefix; differentiation reads one additional coefficient. A formal
identity, an analytic error estimate, and a compatible modular root have
different specifications, and conversion between them needs its own proof.

### Filtered lifting with a frozen inverse

Let B be a fixed primitively recursively presented commutative ring with a
decreasing multiplicative filtration F^0=B and F^N=0, where N>0. Let P be a
finite polynomial system, a a seed with P(a) in F^1, and U a matrix satisfying
both J(a)U=I and UJ(a)=I modulo F^1. Define

    b_0 = a,
    b_(r+1) = b_r - U P(b_r).

The residual at stage r is in F^(r+1). After N-1 updates the result is an
exact root, unique in the seed class modulo F^1. Finite uniqueness proves
compatibility under restriction. The report proves the finite Taylor
identity, residual improvement, uniqueness, independence from higher-order
choices, and the fixed iteration bound. No division is needed during the
iteration, and the generally linear gain in precision is sharp.

Applications include simultaneous formal implicit equations, inverse series,
and roots modulo q^N for every integer q>=2, including composite q. The input
must supply a root and inverse Jacobian modulo q. A modular tower alone does
not yield a rational or integer solution.

### Hurwitz coefficients

Use the binomial product

    (a * b)_n = sum_{j=0}^n binom(n,j) a_j b_(n-j).

Then differentiation is a shift, with the necessary extra input coefficient.
Polynomial differential equations admit a triangular primitive recurrence
over an arbitrary presented commutative ring, without dividing by factorials.
The human proof covers finite systems and time-dependent polynomial data.
The supplied Lean target and producer cover the scalar rational
constant-coefficient polynomial case. Bell numbers and the factorial solution
of Y'=Y^2 illustrate the construction; their known identities are not claimed
as new results.

### Weighted determinant norms and sharp point counts

Let

    F(X,Y) = Y^m - c X^d + lower-weight terms,
    wt(X)=m, wt(Y)=d,

where m>=2, d>=1, gcd(m,d)=1, c is a nonzero rational, and every lower term
has weight strictly below md. For nonzero G of Y-degree below m, let W be its
largest monomial weight. Form the multiplication matrix of G in the free
Q[X]-module Q[X,Y]/(F). If a X^k Y^j is the unique leading-weight term of G,
the report proves

    degree_X det(M_G) = W = mk+dj,
    leading coefficient = a^m ((-1)^(m-1)c)^j.

Weighted rescaling reduces the leading-coefficient calculation to a cyclic
matrix. An explicit Vandermonde row argument proves that r distinct common
zeros over one x-coordinate contribute r factors to the determinant.
Consequently every supplied finite list of distinct common rational zeros of
F and G has length at most W. The argument includes lower-weight mixed terms
and singular fibers; it does not assume smoothness.

The monomials X^i Y^j with j<m and mi+dj<=L form an explicit space of
functions. Its dimension is the finite residue count in the report, and for
L>=max(0,md-m-d) it equals

    L+1 - (m-1)(d-1)/2.

Every proper subspace of the corresponding evaluation space contains at most
L evaluation vectors from distinct curve points. A supplied cover by M proper
subspaces therefore gives the bound ML. An adjugate argument also supplies
an exact function-field presentation. A nonzero initial norm certificate
extends the individual zero-count argument to some noncoprime cases.

This settles a broader family of the geometric zero-count obligations in the
inspected Siegel route than the existing odd-degree hyperelliptic repair.
It does not produce the separate approximation cover, a global height bound,
or a complete rational-point list.

## What is and is not formalized

Ten standalone Lean modules compile with Lean 4.32.0 and `Std`:

| Layer | Supplied status |
| --- | --- |
| Scoped arithmetic syntax and intuitionistic deduction | Reused pinned upstream foundations, with original source and license retained |
| Ranked descent and coherent towers | Proved host Lean theorems |
| Contract composition, specialization, a QF-induction interface, and identity iteration | Actual constructions of embedded `Prf PRAAx` derivations |
| Arithmetic descent compiler | Exact PR syntax and object formula; general compiler target unproved |
| Polynomial systems, jets, residues, weighted norms, and Hurwitz coefficients | Executable definitions and fully stated general target propositions |
| Universal application target propositions | Unproved in Lean; complete human proofs and explicit completion plans are supplied |
| Two finite examples | Kernel-checked modular output and finite monomial count |
| Rational jet, norm, and ODE examples | Exact executable diagnostics, not universal theorems |

The audited declarations contain no `sorryAx` or `Classical.choice`
dependencies. Some host metatheorems use `propext` and `Quot.sound`; these do
not add axioms to the embedded arithmetic theory. No new axiom or opaque
placeholder asserts an unfinished application theorem.

The source includes the actual repository proof relation rather than an
invented surrogate. A host theorem about naturals is not automatically an
iPRA derivation. The full object derivations for lifting and weighted norms
remain formalization work, as requested by the distinction between complete
human arguments and a Lean formalization outline.

## Reproduce the builds and checks

### Lean

Install Lean 4.32.0, then run from this directory:

```bash
bash lean/build.sh
```

If the compiler is outside `PATH`, supply its executable explicitly:

```bash
LEAN_BIN=/absolute/path/to/lean bash lean/build.sh
```

The script compiles all ten modules in dependency order and prints the axiom
audit. No Mathlib checkout or project-specific package download is needed.
Generated object files go in `lean/.build/`.

### Exact arithmetic diagnostics

Use Python 3.12 and SymPy 1.14.0 (the tested versions):

```bash
python3 -m pip install -r requirements.txt
python3 verify.py
```

The filtered-ring examples use only Python's standard library. SymPy is used
for independent polynomial determinant calculations in the norm checks.
The validation files record 1,254 modular lifting instances, 13,114 candidate
residues, coherent simultaneous rational jets through precision 12, 18 exact
weighted-norm cases, and 600 dimension identities, along with worked examples.
All are finite regression evidence; the universal mathematical proofs are
in the report.

### PDF

With a TeX Live installation containing the packages listed in the main
source, run:

```bash
bash build_pdf.sh
```

The script runs pdfLaTeX three times and rejects unresolved references or
citations. It includes a local fallback for Debian-style TeX installations
whose precompiled format or font map is absent. `pdfinfo` and `rg` are used
for build reporting. The delivered PDF does not depend on rebuilding.

## Archive contents

| Path | Purpose |
| --- | --- |
| `paper/` | Complete LaTeX source, references, and rendered PDF |
| `lean/` | Ten modules, formalization roadmap, build script, pinned upstream sources and license |
| `code/` and `verify.py` | Exact-arithmetic examples and regression runner |
| `validation/` | Build records, finite check results, and final review notes |
| `provenance/` | Pinned source audit and packet catalog |
| `PROOF_STATUS.json` | Machine-readable claim and formalization status |
| `MANIFEST.sha256` | SHA-256 inventory of the distributed files |

No modification or publication to the upstream repository is part of this
archive. For integration, follow `lean/FORMALIZATION.md`: replace the
standalone kernel import with the actual `ConciseIPRA.PR` import, complete
the numerical local contracts and object proofs, and only then transport
them through the repository's native equivalence.

