# Bounded factor-partition search around the direct14 equation

Eliminating the direct14 square witness by substituting the signed ordinate
square recovers the already documented 13-variable, degree-36, 87-operation
sum-of-squares equation `../../equation36.pdf`. Its equivalence to the
original four-factor equation is supported by the existing factor-unit and
signed-pair theorems; it is not a new 13-variable candidate.

This bounded survey tries all 15 set partitions of the four existing factor
unit conditions. For each nonsingleton group it enumerates a direct product
minus one and recursive uses of
`(1+a)(1+b)-1 = a+b+ab`; for multiple groups it sums the squares of their
group residuals, and for one group it uses the product-minus-one directly.
It retains the existing 13-variable prefix, performs exact syntactic common
subexpression reuse and removes dead gates. The search records the cheapest
enumerated construction for each partition, not a global operation minimum or
a search over arbitrary Diophantine encodings.

At an original zero, the existing factor-unit theorem makes every original
factor one, so every group residual is zero. Conversely, a sum of group
squares equal to zero makes each group product one; multiplying the groups
gives the original product equal to one. The one-group case is the original
product condition. This is ordinary integer reasoning using the separately
proved factor-unit theorem; no Lean transport theorem is newly claimed here.

The [results](results.json) contain all partitions and choices. Exact
factor-residual degrees 15, 13, 18 and 10 are checked by the two preexisting
finite certificate programs, which this survey reruns. At the actual fixed
ports their leading forms are nonzero; multiplying factors adds degrees, and
the leading homogeneous part of a sum of real squares cannot cancel. Thus
the degree of a multi-group equation is twice the greatest sum of degrees in
a group. Positive shifts preserve these degrees.

The only nondominated points **within this family** are the two existing
13-variable constructions:

| Degree | Unshifted binary operations | Partition |
| ---: | ---: | --- |
| 36 | 87 | four singleton factors |
| 56 | 86 | all four factors in one group |

The survey therefore found no new improvement in this bounded family. It
also checks each generated group identity on all 81 choices from
`{-2,0,1}^4`, rejects an altered multiplication sign, and pins both input
graphs. The identity for all integers follows structurally from the displayed
two-factor identity, not from the finite grid. Run in ordinary Python with
`python3 Computability/DiophantineConsistency/research/direct14-factor-partition-survey/survey.py`;
the script rejects optimized mode and refuses to overwrite different results.
