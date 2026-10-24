# Literal equation and coordinate schema

The final equation is the ordinary polynomial in
`equations/equation_integer.json`. It has exactly **7,617 unrestricted
integer unknowns**, degree **4**, and **148,220 nonzero monomials**.
The polynomial is supplied in full, not as an MRDP oracle or an unspecified
universal-polynomial parameter. Its largest coefficient magnitude is
8,974,652,400,619,654,748,160 (73 bits).

## Sparse polynomial format

The `terms` array contains records `[coefficient, monomial]`. A monomial
is a sorted list of zero-based variable indices, with repetition denoting
exponentiation. Thus `[7,[2,2,5]]` represents `7*x_2^2*x_5`, while
`[-3,[]]` is the constant `-3`. There are no zero coefficients, duplicate
monomials, unbound coefficient ports, variable exponents or hidden
quantified parameters. All indices lie between 0 and 7616 inclusive, and
every index occurs in a nonzero term.

Equivalently, write

    P(x_0,...,x_7616) = sum_(row in residuals_integer.json) row(x)^2.

All 4,379 residuals are explicitly listed, using the same sparse-term
convention. They have degree at most two. The standalone polynomial file
is exactly their expanded sum of squares; `check_exact.py` independently
checks this identity term for term.

## Coordinate accounting

| Role | Number |
|---|---:|
| Semantic inputs that retain nonnegativity guards | 1,040 |
| Signed congruence quotients | 201 |
| Euclidean quotients whose nonnegativity is inferred | 27 |
| Nonlinear arithmetic wires | 3,198 |
| Retained affine wires | 31 |
| Three-square nonnegativity witnesses | 3,120 |
| **Total unrestricted integer coordinates** | **7,617** |

The first 1,268 coordinates are the semantic inputs, in exactly the order
of `circuit_integer.json`'s `variable_names` array. The next 3,229 are
retained arithmetic wires, in topological order. Finally, each guarded
semantic input gets three coordinates `(A,B,C)` for its equation

    x = A^2+B^2+C(C+1).

`variable_map.json` names every one of the 7,617 coordinates. The semantic
descriptions explain their role; every unknown in the final polynomial
still ranges over all integers. The nonnegativity conditions are enforced
by the polynomial, not by an external restriction of its domain.

## Arithmetic DAGs

`circuit_integer.json` uses nodes `c` (integer constant), `v` (semantic
input), `a` (addition), `s` (subtraction), and `m` (multiplication).
All operation operands are earlier node indices. Its equalities are
triples `[left_node,right_node,label]`. Its domain lists state which
semantic inputs receive guards. The remaining arithmetic wires are
unrestricted and have explicit defining equations.

The affine support budget is 16: an affine expression with more than
16 nonzero terms is retained as a wire. This small, fixed choice adds
31 linear equations and prevents unnecessary expansion of large affine
sums inside products. It changes neither the represented relation nor
the quartic degree.

`source_circuit_before_pruning.json` also retains the arithmetic-graph
call ledger and all source-binding node indices. It is for independent
checking of the 40 power/Pell calls, 27 divisions, two factorials and
11 binomials. The final polynomial contains none of those functions as
primitive operations: all have already been replaced by ordinary
polynomial graphs and flattened.

## Source relation

The natural local row has eight coordinates

    (a,b,c,d,S,q,S_next,q_next)

bounded by `(N,N,N,N,y,U,y,U)`. Its proof is in
`source/PREPROCESSING_PROOF.md`. The original twelve-rule Horn source is
retained in `source/horn_shared_source.json`. Its supplied literal
constructors and the C222-to-ZFC-refutation calibration are inherited
source data and theorems, not new assertions of formal certification.

The backend proof is `proofs/SIGNED_COMPILER.md`. Exact artifact audits,
ordinary unbounded proofs, and the inherited logical calibration are
separate obligations throughout the package.
