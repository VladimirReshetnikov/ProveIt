# Direct C222 quartic with normalized power certificates

This is a complete, explicitly expanded equation obtained by simplifying the
direct proof-rule compiler delivered in `ConZFC_Direct_Centered_Round12_2026-10-24.zip`.
It does not encode a Turing-machine run or use a Jones universal polynomial.
It inherits the twelve numerical C222 rules, finite proof-flow certificate,
CRT bounded-family compiler, and finite Pell arithmetic certificates.

The new step is a proved elimination inside all 108 power certificates. The
finite branch already implies that its auxiliary Pell root `a` exceeds both
`w` and the power base `n`. Thus its separately encoded truncated difference
`d=max(a-n,0)` is just `a-n`. Moving `y*n` across one congruence removes `d`
and its sign slack without introducing a new condition.

| Quantity | Incoming fixed-base equation | This equation |
|---|---:|---:|
| Nonnegative integer variables | 16,036 | **14,956** |
| Unrestricted integer variables | 27,916 | **26,188** |
| Total degree, either domain | 4 | **4** |
| Semantic natural inputs | 3,960 | **3,744** |
| Retained nonlinear wires | 12,076 | **11,212** |
| Quadratic residuals before sign conversion | 12,366 | **11,502** |
| Expanded natural monomials | 700,865 | **670,455** |
| Expanded integer monomials | 758,275 | **724,768** |
| Largest absolute integer coefficient | 320,307,372,009,918 | **320,307,372,009,864** |

The saved `equation_integer.json` is the literal polynomial in 26,188
unrestricted integer unknowns. `equation_affine.json` is its 14,956-natural
counterpart. Each `terms` entry is `[coefficient, monomial]`; a monomial is a
sorted list of zero-based variable indices, with repetitions denoting powers
and the empty list denoting the constant. There are no symbolic coefficient
ports, variable exponentiation operations, unexpanded factorials, or hidden
compiler calls in those two polynomial files.

## The theorem and its scope

Ordinary mathematical proofs formalizable in ZFC show that either equation
has a solution exactly when C222 derives its target, equivalently when ZFC
has a syntactic refutation. Negating gives the requested biconditional.
The new proof is in `normalization.tex`; the inherited proof-flow, CRT,
arithmetic and natural-to-integer arguments are reproduced in
`UPSTREAM_MATHEMATICAL_AUDIT.md`. Exact source files and their SHA256 hashes
are supplied. This is a mathematical proof plus complete finite exact
artifact checks. It is not a new end-to-end Lean or Rocq certificate.

These counts improve this particular completed direct construction. They
do not beat the repository's low-variable native/Pell equations, and no
global minimality or historical novelty of the elementary algebra is claimed.
The useful distinction is a smaller complete direct proof-rule equation with
ordinary explicit coefficients and an auditably local change.

## Reproduce

Run `python3 replay.py` from any directory. Only the Python standard library
is used. The script rebuilds the complete polynomials, checks the sole source
change and pinned theorem files, checks every arithmetic interface and C222
rule, checks the bounded-CRT source instantiations, and verifies every
quadratic row and the full sparse expansions over the integers. The affine
audit also checks all sign guards and topological nonnegativity of internal
wires. The symbolic interface checker does not import the builder.

The reference Lean files are supplied for provenance and inspection; this
package does not claim that they form a standalone Lean project or that a
kernel build was run here. Their original commit is
`9a33342a03d19cf5b061b2083c6b5d3f27f752ed`. The incoming compiled construction
was inspected at ProveIt commit `43ac596e36c105a0e8b07c2d1f5ae200cae9c056`.

`upstream/` contains the exact original two builders and summary files.
`audit/check_normalization.py` checks that the current compiler differs from
the original by exactly the single proved fragment. Attribution and the
inherited project license are retained in `licenses/`.
