# Computation-normal iPRA and a smaller validated checker

This package contains a written mathematical reduction, an independently
reviewed completeness argument, complete Python proof checkers, reproducible
measurements, and explicit limits on the simplification claim.

**The overall requested minimum has not been established.** The directly
measured improvement is an 860-byte checker for the unchanged native calculus,
versus an 870-byte baseline with the same public Eq/Q/D contract. The new
six-rule full-normal calculus is bi-interpretable with iPRA by the written
argument, but does not robustly reduce matched complete-checker size.

## Start here

- report.pdf: compiled research report.
- report.tex: its complete LaTeX source.
- code/scope_lexical.py: recommended 860-byte complete checker.
- code/full_normal.py: readable new six-rule full-normal calculus.
- code/full_normal_fuel.py: explicitly bounded normalization interface.
- certificates/full_normal_case.json: a nontrivial recovery of atomic
  case introduction at witness zero, using its case hypothesis.
- evidence/checker_metrics.json: whole-source metrics including gzip level 9.
- evidence/reproduction.json: test outcomes and the exact runtime.

## Mathematical result

Normalize both iterator equations in syntax and substitution. Keep Hyp,
Refl, one-term crossed Tr, QE, DE, and the single witness-selected DI.
Full normalization destroys every closed nonliteral zero alias. The proof
repairs the single-introduction completeness argument by deriving

    D_(x,y) (I(y,0;u.x) = 0).

Eliminating this formula gives a fresh variable b and a closure from which
QE proves b=0. Case introduction can then use b as a syntactically nonzero
witness and discharge it afterward.

The proof proceeds through a stable seven-rule normalized calculus,
establishes equivalence with the pinned raw native kernel, proves both
normalization round trips, and composes them with the existing native/iPRA
bi-interpretation. Both numerical domains are whole and the composite graph
is x=y. This is a written mathematical proof, not a new Lean formalization.

Uniform full normalization is total recursive but not primitive recursive.
The fuelled implementation makes its additional bound explicit and measured.
The report does not claim iPRA-internal uniform normalization.

## Measured implementation result

The practical change preserves the exact arithmetic proof kernel. It combines
the existing whole-certificate integer/list gate with reuse of the existing
initial scope traversal. The public validator consequently needs only a
Boolean term/formula mode.

| Complete module | Normalized bytes | Significant tokens | AST nodes | Gzip 9 |
|---|---:|---:|---:|---:|
| Matched public Eq/Q/D baseline | 870 | 383 | 442 | 507 |
| Scope reuse | 860 | 377 | 433 | 508 |

The 516-byte arity-envelope checker in the repository has a different
validation contract and is included as an honest reference. No new absolute
size record is claimed.

The fair full-normal comparison is 3044 bytes / 992 tokens / 1046 AST nodes
versus 3029 / 991 / 1049 for the equally optimized zero-normal control.
Full normalization trades costs rather than uniformly improving them.

## Reproduce

Python 3.12 or later is recommended; exact reported source normalization used
CPython 3.12.14 and zlib 1.3.2. No third-party Python packages or network are
needed.

    python3 reproduce.py

This reruns 272 complete old/new scope-checker process checks, 9000 independent
scope/grammar comparisons, the full-normal mathematical certificates and
normalizer tests, goal-directed controls, and explicit-fuel boundary tests.
It regenerates metrics, normalized complete programs and deterministic gzip
files. Resource limits of physical Python execution remain applicable.

Build the report with a conventional TeX installation:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

Run the complete compact checker on a JSON certificate:

    python3 code/scope_lexical.py < certificate.json

Acceptance requires exit code zero and the exact output ACCEPT.
This arity-coded format differs from the tagged format of full_normal.py;
the report and scope_composition/README.md describe their contracts.

## Provenance and status

All comparisons use ProveIt commit
d9383325b18d349b8bfdc54ef564c5784cc029ec, specifically
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA.
The scope_composition subdirectory is a portable subpackage containing
baseline sources, inherited fixtures, the preservation proof, provenance
and its own reproduction script. Source copies and derivatives are
distinguished in provenance files.

The inherited theory and baseline checker are credited to ProveIt
contributors. Their MIT No Attribution license is included. New proof notes,
checker modifications and reproduction scripts in this package may be reused
under the same license.

See CLAIMS.json for machine-readable claim boundaries and MANIFEST.sha256
for hashes of delivered files.
