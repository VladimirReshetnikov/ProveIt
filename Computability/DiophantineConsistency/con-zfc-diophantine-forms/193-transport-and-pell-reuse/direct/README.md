# A direct 83-integer equation for Con(ZFC)

The principal equation, P83/circuit.json, is an ordinary integer-coefficient
polynomial in **83 independently quantified unrestricted integers**, of
**exact total degree 624**. It is the sum of 31 explicit residual squares.
Composing the supplied ordinary arithmetic proof with the identified inherited
C222/ZF/ZFC refutation calibration gives, in ZFC,

    (there is no integer zero of P83) <=> Con(ZFC).

The polynomial has no variable exponent, factorial primitive, unspecified
coefficient tuple, or hidden existential predicate. It uses neither a K215
simulation nor Jones's universal polynomial. Its direct proof calculus and
logical calibration remain credited dependencies.

The preferred evaluator of this same polynomial is now
**factored83/circuit.json**: it uses **1,789 operations** and integer literals
of absolute value at most **64**. The canonical P83 graph below remains the
reference for source projection; both graphs agree at every integer tuple.
See factored83/README.md for the exact two-factorization proof and replay.

## What changed

The new arithmetic identifies the free Pell-center slack with the existing
odd quotient of a lower Pell frame. A local permutation theorem for Pell
indices permits this reuse while satisfying the same common modular-root
condition. The signed-frame variant gives a 227-variable sextic source.
An acyclic orientation of literal unit pivots then removes 144 coordinates,
giving the principal equation. The ordinary proof is in
RECYCLED_QUOTIENT_CENTER.md.

The 83/624 endpoint improves both dimension and degree relative to the
inspected package-175 direct 92/692 equation. Its preferred factored evaluator uses 1,789 live binary arithmetic
gates, below that equation's 2,428. The canonical graph uses 2,939 gates and
integer scalars of absolute value at most 324; the factored graph lowers the
latter bound to 64. The expanded coefficient height is
proved strictly smaller than 2^1568 by P83/TIGHT_HEIGHT.json; its exact value
and expanded monomial count were not computed. A literal scalar bound is not
an expanded height. The older coarse graph bound 2^3618 in METRICS.json is
also valid; the tight certificate preserves the exact propagated norm bound.

## Alternatives

| Integer variables | Exact degree | Residual squares | Canonical binary gates |
|---:|---:|---:|---:|
| 79 | 8,388,620 | 27 | 2,926 |
| 81 | 2,048 | 29 | 2,932 |
| 82 | 764 | 30 | 2,935 |
| **83** | **624** | **31** | **2,939** |
| 84 | 512 | 32 | 2,943 |
| 85 | 444 | 33 | 2,946 |
| 86 | 424 | 34 | 2,949 |
| 87 | 268 | 35 | 2,953 |
| 88 | 176 | 36 | 2,941 |
| 89 | 128 | 37 | 2,945 |
| 91 | 80 | 39 | 2,952 |

The 79-variable form improves the coordinate count of the inspected
package-177 87-variable direct equation, whose degree is 8,388,612. This is
a measured comparison within the direct-calculus family, not a global
minimality or literature-priority claim. Other repository equations have
fewer variables with different coefficient and encoding costs.

## Complete finite definition

- source227.json contains all 175 source residuals and 227 coordinate names.
- Each PN/projection.json partitions the source rows into retained rows and
  unit definitions, with an exact integer polynomial for every removed
  coordinate. The definition dependency graph is acyclic.
- Each PN/circuit.json contains the complete resulting polynomial using
  integer literals, inputs, binary addition and binary multiplication only.
- P83_definition.tex prints all free assignments, acyclic definitions and
  retained residuals of the principal equation.
- PN/certificates.json supplies an exact-degree witness modulo 1,000,003,
  a modular gradient proving actual occurrence of every input, and a
  deterministic coefficient-norm height bound.

The sparse term [c,[i,j,...]] means c*z_i*z_j*...; an empty index list is a
constant and repeated indices mean powers. All indices are zero based.
In a circuit, ['const',c] is literal integer c, ['input',i] is free input i,
and ['add',a,b] or ['mul',a,b] combines earlier node IDs. Restoration roots
are intermediate expressions, not additional quantified unknowns.

## Verify and rebuild offline

Python 3.10 or later and its standard library suffice:

    python3 -B verify.py
    python3 -B -O verify.py
    python3 -B rebuild.py
    python3 -B check_lemma.py
    python3 -B factored83/check_factored.py --rebuild

The independent verifier imports no producer or search program. It replays
the retained source's 208 unit eliminations and affine changes, checks the
new two-row mutation, and checks every final acyclic projection and circuit.
A nonzero leading residual coefficient on a specified integer ray proves
exact degree; highest real homogeneous squares cannot cancel. Every modular
input derivative and coefficient-norm bound is checked. Four deliberate
corruptions are rejected. The separate producer rebuild.py reconstructs all
eleven circuits byte for byte from their literal source and certificates.

For one profile or to save a fresh receipt outside the release:

    python3 -B verify.py --profile 83 --receipt /tmp/direct83-replay.json

These finite checks do not replace the unbounded number-theoretic proof or
the inherited consistency calibration, find a root, or prove Con(ZFC).

## Evaluate a supplied tuple

Write a JSON array of exactly N integers to tuple.json, then run:

    python3 -B evaluate.py 83 tuple.json --factored
    python3 -B evaluate.py 83 tuple.json --modulus 1000003 --residuals --restore227

The optional modulus permits fast arithmetic with large-degree profiles.
The exact evaluator uses ordinary arbitrary-precision integers.

## Provenance and proof boundary

The comparison commit is cdfea7d90176775d74c1c30afbe49fa78ade9897 of
VladimirReshetnikov/ProveIt. PROVENANCE.json gives exact parent paths and
hashes. parent166/ retains the literal source, Horn-factorization data, all
unit/affine certificates used here, relevant ordinary proofs and notices.
It is a scoped dependency subset, not a fresh rebuild of the parent's full
transitive proof development. Horn factoring, older Pell/CRT facts and the
logical calibration remain identified inherited proof dependencies.

The recycled-center change preserves zero existence by a cofinal completeness
construction. Subsequent unit elimination has the exact identity
P227(restore227(x)) = PN(x) and induces a bijection on integer zero sets.
The proof uses internal ZFC arithmetic and finite CRT/Hensel lifting. It
assumes no external standardness, transitivity, or omega-model.

This work was AI-assisted. Independent review means a separately assigned
mathematical and code audit in that workflow, not external human peer review.
The root report explains the full logical boundary. Original MIT No
Attribution license and notices are retained under parent166/.
