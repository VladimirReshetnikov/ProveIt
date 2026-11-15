# Brun's theorem in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 15 November 2026.

## Main result

The article gives a complete human-readable finite proof of Brun's theorem,
with a primitive-recursive Cauchy modulus. With

\[
B(N)=\sum_{\substack{p<N\\p,p+2\text{ prime}}}
\left(\frac1p+\frac1{p+2}\right),
\]

it proves

\[
M,L\ge N(q):=2^{2^{q+13}}
\quad\Longrightarrow\quad |B(M)-B(L)|\le2^{-q}.
\]

The counting estimate is

\[
k^2 T(2^k)\le1400\,2^k\le2048\,2^k,
\]

and the finite reciprocal tail with smaller prime at least \(2^m\) is at
most \(8192/m\). The proof uses explicit rational Selberg weights, a finite
harmonic-square comparison, and finite dyadic telescoping. No prime number
theorem, Mertens asymptotic, infinite Euler product, or monotone convergence
principle is needed.

## Exact iPRA meaning

Let \(D(V)=(V+1)!\) and

\[
R(U,V)=\sum_{U\le p<V}\chi_{\rm twin}(p)
\bigl(D(V)\mathbin{\rm div}p+D(V)\mathbin{\rm div}(p+2)\bigr).
\]

The internal theorem is the universal closure of the quantifier-free
primitive-recursive matrix

\[
N(q)\le U\le V\quad\Longrightarrow\quad2^q R(U,V)\le D(V).
\]

Every contributing denominator divides \(D(V)\). The paper explains the
bounded algorithms, Boolean induction invariants, and integer/rational
encoding needed to carry the proof out with quantifier-free induction.

## Read first

- `brun_ipra.pdf`: the complete article.
- `brun_ipra.tex` and `sections/`: all LaTeX sources.
- `lean/FORMALIZATION_PLAN.md`: the route to a complete Lean proof,
  including a derivation in the deeply embedded `PRAAx` theory.
- `lean/SOURCE_LEDGER.md`: the inspected ProveIt snapshot and exact paths.

## Formalization status

The human proof is complete. A full Lean proof is **not** claimed.
`lean/BrunSpecification.lean` contains bounded definitions, the precise
integer target, and candidate conditional assembly proofs, **uncompiled**.
It has no added axioms or `sorry` declarations, but explicitly assumes the
finite tail theorem as a hypothesis in its assembly result. The finite
sieve library and the object-theory derivation still need implementation.

The inspected ProveIt commit is
`8c135f6f2a9d041cde785a1a632c44ad98065b20`, with Lean and Mathlib v4.32.0.
The existing ConciseIPRA faithful interpretations can transfer a completed
`PRAAx` derivation to its scalar/native presentations. Ordinary semantic
Lean truth alone does not establish the required iPRA derivability.

## Executable diagnostics

Run from this directory:

```sh
python3 -m unittest discover -s tests -v
python3 artifacts/finite_sieve.py --json artifacts/verification.json
```

The ten unit tests pass. The JSON report records 1,730 exact integer and
rational assertions. These test finite examples of the CRT counts, Mobius
transform, coefficient bounds, quadratic identity, prime-support grouping,
sieve inequalities, and factorial coding. They are diagnostic checks,
not proofs of universal theorems.

The Python implementation uses only the standard library. It deliberately
prints the double-exponential cutoff symbolically. Finite sample sums
are not presented as practical certified approximations to Brun's constant.

## Building the article

With a standard LaTeX installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error brun_ipra.tex
```

The preamble lists the required packages. `make pdf`, `make test`, and
`make diagnostics` provide the corresponding commands. In an existing
workspace with the pinned Mathlib dependency, the candidate Lean source
can be checked with `lake env lean /absolute/path/to/BrunSpecification.lean`.
That Lean command has not been run successfully in this authoring environment.

## Conventions and limitations

- `T(X)` counts smaller primes `p <= X`, without requiring `p+2 <= X`.
- `B(N)` uses `p < N` and includes both reciprocals in each pair.
  Thus the prime 5 occurs twice, and `B(6)=92/105`.
- The constants favor a short arithmetic proof, not an efficient numerical
  approximation algorithm. Already `N(0)=2^8192`.
- The proof does not assume or decide that infinitely many twin primes exist.
- The repository was inspected as a source; no upstream commit or PR was made.

## Reproduction and provenance

`artifacts/verification.json` records exact diagnostic outputs;
`artifacts/test_run.txt` records the test invocation;
`artifacts/build_summary.json` records PDF and source validation.
`SHA256SUMS` lists the packaged files for integrity checking.
The article includes its bibliography, and the source ledger supplies
permanent repository links and inspection limitations.
