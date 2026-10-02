# A literal simplification of the bounded FRACTRAN certificate

This packet transfers two reductions to the actual compiler shipped with
[Canonical Diophantine certificates](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/README.md),
Part VII. Both preserve the **complete natural zero set on the same witness
coordinates**. They delete two residuals per fraction per step; an optional
second stage also makes one retained quadratic residual linear. The original
report and compiler remain frozen.

This is a family indexed by an externally fixed program and horizon. It does
not lower the operation bound for one fixed-arity universal polynomial. The
counts below use an explicitly charged, unoptimized sparse-polynomial circuit;
they are not claims about minimal circuits.

## The imported certificate and its exact rewrite

The source is
[the report's actual FRACTRAN compiler](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/04-witness-faithful-diophantine_compiler.py).
Its complete SHA-256 is
`23c0c0ce8859a7a70eec4b8327607bf0ce18badd096a1afa8a3bed1c2981f767`.
The new [checker](fractran_divisibility_residual_projection.py) loads that file
by path. It calls `compile_fractran(..., witness=False)`, serializes every
actual residual and witness name, and requires complete equality with a
fresh canonical parent before any rewrite, comparing both values and exact
Python types so floats and Booleans cannot impersonate integer coefficients. Thus its source is neither a
handpicked gadget nor a replacement interpretation of FRACTRAN.

A program consists of `r >= 1` fixed positive rational fractions, reduced
before compilation, and a horizon `T >= 0`. The source and target integers
are fixed and positive. Every quantified coordinate is a **nonnegative
integer**, with zero included. For each fraction at each time, the imported
compiler contains the following six divisibility residuals:

\[
 n-bq-\rho,\qquad \rho+s-(b-1),\qquad
 B=z(z-1),\qquad J=z\rho,\qquad
 R=\rho-(1-z)(u+1),\qquad Z=zu.
\]

The imported `prefix`, `first_applicable`, nonterminal, output, endpoint and
optional first-halting rows are retained literally. In particular, this
reduction retains the source's first-applicable-fraction priority semantics.
All witness names and their order remain unchanged.

The `delete` stage removes exactly `zero_bit_t_j` and `zero_test_t_j`, namely
`B` and `J`. The `linearize` stage additionally replaces the actual
`positive_test_t_j` row `R` by

\[
 L=\rho-u+z-1.
\]

It retains `inactive_zero_t_j`, namely `Z`, in both stages. The script checks
all four named source polynomials against their exact expected sparse forms
at every fraction-step before altering any row. It also validates the full
metadata, parameters, variable list and residual list on its public output
and accounting APIs. Unreduced input fractions are normalized by the imported
compiler; this normalization is reflected in the packet's displayed spec.

## Equality of the full natural zero sets

Suppose the retained equations vanish at a natural assignment. Since
`u+1 > 0` and `rho >= 0`, `R=0` implies `1-z >= 0`. The natural variable `z`
therefore equals either zero or one. Consequently `B=0`; also `J=0`, because
`z=0` makes the product zero and `z=1` forces `rho=0`.

Thus every zero of the deletion stage satisfies the two removed rows at
every fraction-step. The converse is immediate. All other rows are identical,
so this is equality of the entire natural zero sets, including on inputs
with no valid execution. It is not merely agreement on canonical runs.

For the second stage the exact polynomial relation is

\[
 R=L+Z.
\]

The separately retained equation `Z=0` therefore makes `R=0` and `L=0`
equivalent. This implication holds over all integers; the preceding deletion
step still needs the natural domain. In the divisible case, `z=1` and `Z=0`
force `u=0`. Removing that normalization row would lose the source's unique
witness property. All quotient, remainder, priority and configuration
coordinates keep their original values.

The imported source proves that its natural zeros are precisely the bounded
FRACTRAN runs, with one witness for a successful instance. Since the complete
zero sets are equal, both reduced sources inherit this exact contract. The
optional terminal gadget remains untouched, including the impossible
first-halting case when a denominator is one. For `T=0`, no rows are changed.

## Residual and circuit accounting

Without terminality the source uses

\[
 V=T(7r+2)+1,\qquad E_{\rm parent}=T(8r+3)+2.
\]

Both reduced stages keep `V` and have

\[
 E_{\rm reduced}=T(6r+3)+2.
\]

Terminality adds exactly `3r` witnesses and `2r` residuals in every stage.
The sum-of-squares polynomial still has degree at most four. No witness is
projected away despite this packet's filename: the mathematical map on the
whole witness tuple is the identity.

To make an arithmetic comparison reviewable, the script exports a complete
straight-line program for every displayed form. It evaluates each expanded
sparse residual independently, takes positive-coefficient terms before
negative-coefficient terms, preserves the source's lexicographic monomial
order within each sign, multiplies the variables in each monomial, and charges
all coefficient multiplications except magnitude one. It then squares every
residual and adds the squares. Literals and variable references are free;
every `+`, `-`, and `*` gate costs one, including multiplication by nonunit
fixed constants. It performs no common-subexpression elimination across rows
and no optimization of the finalizer. An initial negative term is represented
by the charged subtraction from zero. `A` counts additions and subtractions;
`M` counts multiplications. The output is the polynomial itself, tested equal
to zero without a further arithmetic gate.

Under this declared schedule the per-fraction-step savings are exact:

| Stage | Removed residuals | Saved M | Saved A | Saved operations |
| --- | ---: | ---: | ---: | ---: |
| Delete `B,J` | 2 | 4 | 3 | 7 |
| Delete `B,J` and replace `R` by `L` | 2 | 5 | 4 | 9 |

Indeed, `B` needs `1M+1A`, `J` needs `1M`, their two squares need `2M`, and
their removal saves two additions in the final sum. The original expanded
`R` needs `1M+4A`, while `L` needs `3A`. Every other source row and its order
are unchanged. There are always at least two endpoint residuals, so the
left-associated sum's count changes by exactly the number of deleted rows.

For the actual six-step run of `(3/2,5/3)` from `8` to `125`:

| Requirement | Stage | Witnesses | Residuals | M | A | Operations |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Specified endpoint | Parent | 97 | 116 | 224 | 291 | 515 |
| Specified endpoint | Delete | 97 | 92 | 176 | 255 | 431 |
| Specified endpoint | Linearize | 97 | 92 | 164 | 243 | 407 |
| First halt | Parent | 103 | 120 | 230 | 304 | 534 |
| First halt | Delete | 103 | 96 | 182 | 268 | 450 |
| First halt | Linearize | 103 | 96 | 170 | 256 | 426 |

The comparisons keep the same natural witness convention. Replacing every
natural coordinate by a positive variable minus one would require a newly
charged source; these figures do not silently include that conversion.

## Off-zero correction and domain boundary

Let `P0`, `Pd`, and `Pl` denote the three literal sum-of-squares polynomials.
On every integer assignment, with sums over all fraction-steps,

\[
 P_0-P_d=\sum(B^2+J^2),\qquad
 P_d-P_l=\sum(2LZ+Z^2).
\]

These are the checked off-zero corrections. Neither reduction claims an
identity of the full output polynomials. The second correction can have
either sign away from zeros.

Natural integrality is essential to the deletion theorem. The receipt contains
a **full actual compiler** signed counterexample for program `(1/2,1/1)`,
source and target `1`, and horizon `1`. At its first fraction choose
`q=1, rho=-1, s=2, u=0, z=2`; at its second use `q=1, rho=s=u=0, z=1`.
The prefix coordinates are `(1,-1,0)` and selection coordinates `(2,-1)`;
both configurations equal one. All retained rows vanish, while the deleted
rows are `2` and `-2`. The output energies are therefore `(8,0,0)`.
The natural-domain evaluator rejects this assignment explicitly.

Nonnegative reals would also be too broad. Already the local values
`rho=1/2, u=0, z=1/2` satisfy `R=Z=L=0` but have
`B=-1/4` and `J=1/4`. The theorem concerns natural integer zeros, not a real
algebraic relaxation. The semantic evaluator also rejects noninteger and
Boolean coordinate values.

## Reproduction and limits

The [receipt](fractran_divisibility_residual_projection.json) records all
18 complete sources for six parameter/interface cases, their literal gate
counts, liveness checks, degree bounds, source hashes and the signed
counterexample. The author replay passed:

- 2,197 local natural candidates and 845 canonical divisions, including zero
  dividend and denominator one;
- 4,092 natural-zero evaluations from actual imported compiler runs;
- 720 independent residual-versus-SLP output comparisons;
- 240 complete-compiler off-zero corrections, including 120 signed maps;
- 105 rejected malformed callers and three rejected signed semantic inputs.

Run the checker without arguments for a fresh deterministic receipt replay;
`--write` regenerates the receipt. The source contains no dependency on a
LaTeX installation, external theorem prover, or optional numerical package.
Finite checks supplement the algebraic proof above. They do not prove the
report's universality claim or instantiate a variable-horizon fixed-arity
compiler. Neither the current universal operation frontier nor any
optimality assertion changes here.

Author provenance, 2 October 2026: the receipt writer and a separate fresh
read-only replay both passed with the deterministic seed `20261002`. The
receipt's author-file hash matches the saved checker. A separate static check
validated every local Markdown link, all 18 exported source hashes, Python
syntax and Markdown trailing whitespace. The original report's nine test
entry points had also passed in restored delivery copies under `/tmp`; no
tracked report or original receipt was rewritten. Independent review results
are recorded separately by the coordinating agent.

The independent reviewer identified and the author repaired an input-guard
issue before publication: ordinary Python equality could accept floating
coefficients numerically equal to canonical integers. Exact recursive type
comparison now guards both parent rewrites and output packets. The regression
uses endpoints `2^100`, where rounding could otherwise turn an endpoint error
of one into a false zero; float constants, float unit coefficients and Boolean
unit coefficients are rejected by all relevant public APIs. The revised
writer and a fresh receipt replay passed. This guard repair changes neither
the residual transformation nor any arithmetic count above.

Independent review, 2 October 2026: the final proof, source, domain boundaries
and arithmetic ledger passed after that repair. A separate evaluator checked
144 complete source forms, 48 ledgers and 2,304 outputs, including 1,152 signed
assignments and their correction identities. It accepted 477 actual compiler
witnesses and rejected 477 wrong endpoints. Separate checks covered 9,261
natural local triples, 729 signed triples and all 39 float/Boolean coefficient
mutations. Both the independent reviewer and the coordinating root ran the
final deterministic receipt replay successfully. No unresolved finding remains;
these checks have the bounded scope described above.
