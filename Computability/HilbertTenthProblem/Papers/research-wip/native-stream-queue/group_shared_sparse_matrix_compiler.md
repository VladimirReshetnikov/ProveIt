# Shared typing and sparse flow in the complete matrix compiler

Combining the [shared typing kernel](group_shared_typing_matrix_compiler.md)
with [sparse macro flow](group_sparse_macro_flow.md), then sharing the
duplicated geometric registers, gives a complete fixed-table certificate
with the exact literal cost

    3m+3h+p+222+f_flow-3min(h,3).                       (1)

It has **47 equations** and **m+67 strictly positive existential
witnesses**. Its single sum-of-squares polynomial costs

    3m+3h+p+362+f_flow-3min(h,3)                        (2)

and has exact degree **12m+112**. Every one of its47 residuals is the
same integer polynomial as in the shared-typing parent, even on arbitrary
signed assignments. Thus its complete ordinary-input theorem and
positive witness domains are unchanged.

Here m=2^h>=2 is the padded edge count, p the unchanged physical port
cost, and f_flow the exact sparse-flow cost. For total nonempty macro
length L, f_flow<=2L. The numerically instantiated universal subgroup
alphabet remains unspecified; (1)--(2) are exact formulas for a supplied
fixed table, not a numerical improvement on75 or88 operations.

## 1. The two reviewed rewrites compose without new hypotheses

Start with the actual shared-typing source. It has already replaced the
separate controller subset kernel by upper binary lanes in the retained
selected-source AND kernel. It uses two independent native cores: the
joined typing core and the linked-duration geometry core. Keep both
unchanged.

Replace only the controller's edge-checksum addition tree and dense
state-flow block by the sparse-flow source. This is exactly the local
rewrite proved in the sparse packet: its groups and weighted sums use
the same supplied edge hats and fixed vertex coefficients. It preserves
the checksum and flow residuals on all integer assignments, regardless
of which native kernel proves that the edge fields are typed.

In particular the shared-typing soundness proof still establishes the
low-mask bound before invoking any Boolean semantics. Its scalar port
equations and checksum are unchanged polynomials. The subsequent binary
region split, edge typing, chronological path, exact selected digits,
history induction and matrix endpoint proof all apply verbatim. No
assumption about correct cell digits is introduced by moving the
controller's group sums earlier in its arithmetic schedule.

The supplied coordinates and fixed compiler data are unchanged. The
ordinary positive input remains x and the paid loader remains
`r=alpha*x+beta`. Every old positive witness tuple is a new positive
witness tuple with the same values, and conversely. Thus this combination
has the identity map on its complete positive solution set.

## 2. Exact common-register sharing

The controller already computes the successive powers

    P,P^2,...,P^(m/2),

their plus-one factors, and their cumulative products. The selector
separately computes P^2,P^4,P^8 and the three repunits of lengths2,4,8.
Both sources compute B-1. The joint source also squares P^(m/2) to
obtain P^m, which duplicates one selector power when m<=8.

These are literal common expressions. The new source performs exact
structural sharing only within this named set of registers, after
resolving earlier aliases. A gate is deleted only when its operation
and both resolved operands match an earlier retained gate. Every use,
including comparison operands, is redirected to that earlier register.
This is a topologically ordered identity transformation; no equation
from the represented relation is needed.

The exact deletion counts are

| h | m | Deleted M | Deleted A | Total |
|---|---|---:|---:|---:|
| 1 |2|1|2|3|
| 2 |4|3|3|6|
| at least3 |at least8|5|4|9|

For h=1, the reused registers are P+1, B-1 and P^m=P^2. For h=2,
the shared P^2, its plus-one factor and the length-four repunit add
three savings, while P^m now reuses P^4. For h=3, the shared P^4,
its plus-one factor and the length-eight repunit add another three;
P^m reuses P^8. For h>=4, the controller already has P^8, so its
reuse replaces the earlier saving on P^m, leaving the same total.

Write these multiplication and addition savings as delta_M,delta_A.
Then delta_M+delta_A=3min(h,3). The implementation deliberately excludes
all other core or algebraic expression sharing from this count. Every
retained numeral multiplication and square is still charged.

## 3. Table-dependent flow and exact totals

For clarity, the inherited sparse-flow data are fixed by the actual
macro table. Let n=sum_codes(length-1), b be the number of codes of
length at least two, and k=n-b. The weighted-group flags epsilon count
consecutive least coefficients, precisely as in the sparse-flow proof.
The exact flow multiplication/addition counts are

| Case | f_M | f_A | f_flow |
|---|---:|---:|---:|
| n=0 |0|0|0|
| n=1 |1|1|2|
| n>=2,k=0 |2n-3|2n|4n-3|
| k>0 |n+b-1-epsilon|n+b+1|2(n+b)-epsilon|

Thus f_flow=f_M+f_A<=2n+2b<=2L. The shared-typing parent's dense
flow had `(2m+1)M+2mA`. Replacing it and making exactly the common
register deletions of Section2 gives

    certificate_M=m+2h+101+f_M-delta_M,
    certificate_A=2m+h+p+121+f_A-delta_A.              (3)

There are still47 comparisons, including an identically zero flow
comparison if n=0. The explicit SOS adds47 residual subtractions,
47 squares and46 summation additions. Consequently

    polynomial_M=m+2h+148+f_M-delta_M,
    polynomial_A=2m+h+p+214+f_A-delta_A.               (4)

Equations(3)--(4) give (1)--(2). The same m+67 positive existential
coordinates remain; no computed register alias is counted as a new
witness and no positive slack is discarded.

The saved receipt contains these illustrative nonuniversal fixed tables:

| Code lengths | m | h | p | f_flow | Certificate | Polynomial | Degree |
|---|---:|---:|---:|---:|---:|---:|---:|
| none |2|1|0|0|228|368|136|
| 2 |4|2|0|2|236|376|160|
| 2,2 |8|3|0|5|251|391|208|
| 10 |16|4|4|19|296|436|304|
| 2,3,4 |16|4|2|17|292|432|304|

For example the ten-letter fixture originally cost401 operations before
SOS and580 after it in the separate-kernel dense compiler. Shared typing
saves50 and89 respectively; sparse flow saves46 in either schedule;
the common geometric registers save9 more. The resulting296/436 totals
have the explicitly larger degree304 instead of208. These costs are
not an optimality claim for the fixture or for a universal alphabet.

## 4. Polynomial identity, degree and complete scope

Sparse flow preserves all comparison residuals. Structural register
sharing preserves the value of every retained register and comparison
by induction through the instruction list. Therefore the complete new
SOS polynomial is identically equal to the shared-typing parent's SOS
polynomial over the integers, with the same supplied variables and
fixed numerals. This is stronger than merely asserting equality of
their accepted positive inputs.

The exact degree is consequently unchanged at12m+112. Its unique
highest residual remains the joined kernel's first norm, of degree
6m+56 and highest form

    w_selection^2*s_selection^4*k_selection^2
      *(16P^(m+8))^6.

Squaring gives the nonzero highest form of the complete output. Every
supplied coordinate has degree one; compiler numerals have degree zero.
No relation such as P=B^t or a native packing equality is substituted
into the polynomial for this degree calculation.

All ordinary-input, positivity and universality conclusions are exactly
those of the complete shared-typing parent. For any supplied fixed list
of nonempty physical macro codes, the new system is solvable exactly
when a word in its hub macro language has product diag(L_r,L_r). If
the list contains each fixed subgroup generator and its inverse, this
is the corresponding subgroup-membership predicate. The effective
fixed-universal-subgroup construction can be compiled by this source
once its finite table is supplied. No extra geometry, selection,
controller or endpoint obligation is left unpaid, but this artifact
does not numerically instantiate that universal table.

## 5. Literal source and reproducible evidence

The [source](group_shared_sparse_matrix_compiler.py) starts from the
actual shared-typing parent and imports the reviewed sparse-flow
instructions. It does not rebuild either native core. Its
[receipt](group_shared_sparse_matrix_compiler.json) contains the full
DAG, all47 comparisons, the unchanged positive coordinate list, flow
groups, exact deleted common gates, aliases and ledgers for each table.

On1,280 assignments, including320 signed off-zero cases, the checker
compares every residual with both the parent DAG and independent
shared-typing formulas. It also checks the complete SOS and every
deleted common register against its retained alias. Weighted offset
polynomial evaluations at m=2,4,8,16 verify the stated degree and
highest coefficient in all sharing regimes. These checks establish
arithmetic identities; the unbounded positive equivalence is the
parametric proof above, not a conclusion from sampled Pell solutions.

Default execution compares the saved receipt; `--write` regenerates it.
Both parent trios remain unchanged.

Two independent full proof/source/default reviews passed without findings.
They checked every flow case, the unchanged comparison polynomials,
restricted topological register sharing in all four h regimes, positive
domain preservation, exact operation and witness ledgers, and inherited
ordinary-input and degree statements. One review independently compared
all 47 residuals and every register alias on 512 signed assignments
across 128 separately generated macro tables with h=1 through7. Empty
code lists and length-one macro cases were included. Both reviews kept
the generic compiler theorem separate from numerical universal-alphabet
instantiation.
