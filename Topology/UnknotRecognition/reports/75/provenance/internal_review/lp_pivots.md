# Exact Bland pivot counts for the synthetic screening family

This is a proof for the exact all-slack implementation in
`work/fast/fastunknot/exact_lp.py` and the algebraic models in
`work/fast/lp_cache_research/synthetic_family.py`. No claim is made that
the models are normal-matching systems of genuine triangulations.
Pivot budgets must be absent or sufficient for both complete runs.

## Abstract chain lemma

There are m equations, in this exact order:

    X_i - z = 0,             0 <= i < m,

where each X_i is a sum of a disjoint group G_i of original nonnegative
variables. Any G_i can contain one or more duplicate columns; it may also
be empty. All other original variables, collectively y, have zero
coefficients in these equations. The objective is z. Normalize by

    z + sum_i X_i + sum y <= 1.

The solver forms the inequalities Cx<=0, then -Cx<=0, then the
normalization inequality, in that order, with all-slack initial basis.
Write a_i for the slack of C row i, b_i for the slack of -C row i, and
s for the normalization slack. Every original variable has an index
smaller than every slack, and slack indices follow the listed row order.

The original tableau equations are therefore

    a_i + X_i - z = 0,
    b_i - X_i + z = 0,
    s + z + sum_i X_i + sum y = 1.

The exact solver selects the least-index column with strictly positive
reduced objective coefficient; among minimum-ratio rows it chooses the
least-index current basic variable. It never pivots on a zero reduced
coefficient. It returns immediately after attaining positive objective,
or after all reduced coefficients become nonpositive.

**Lemma.** If every G_i is nonempty, the solver returns POSITIVE after
exactly m+1 pivots. If h is the first index with G_h empty, it returns
NONPOSITIVE after exactly h+1 pivots. This holds independently of the
number and ordering of irrelevant y variables and of the number of
available twins in each nonempty group.

### First pivot

Initially z is the only positive reduced-cost variable. Its coefficients
are -1 in every C row, +1 in every -C row, and +1 in the normalization
row. The -C rows have ratio zero, whereas normalization has ratio one.
Bland's leaving rule therefore chooses b_0. The pivot coefficient is 1,
the objective remains zero, and the dictionary expresses

    z = X_0 - b_0.

If G_0 is empty, every reduced coefficient is already nonpositive and
the solver terminates after this one pivot, as claimed.

### Full tableau invariant

Suppose h>=0, the solver has made h+1 pivots, and groups G_0,...,G_(h-1)
were nonempty. Let x_i be the least-index available variable in G_i that
entered the basis, and let Y_i=X_i-x_i for i<h.

The basic original variables are z and x_0,...,x_(h-1). All a_i remain
basic, all b_j with j>h remain basic, and s remains basic. The nonbasic
slacks are b_0,...,b_h. In the original row positions, the dictionary has
the following exact equations:

    z - X_h + b_h = 0;

    x_i + Y_i - X_h + b_h - b_i = 0,       i<h;

    a_i + b_i = 0,                        i<=h;

    a_j + X_j - X_h + b_h = 0,            j>h;

    b_j - X_j + X_h - b_h = 0,            j>h;

    s + (h+2)X_h - (h+1)b_h
      + sum_(i<h) b_i + sum_(j>h) X_j + sum y = 1.

The reduced objective is exactly

    z = X_h - b_h,

and its current value is zero. All right-hand sides except that of the
normalization row are zero. These formulas hold for h=0 after the first
pivot. They also exhibit every possible positive entering coefficient:
only the variables of G_h have positive reduced coefficient, each equal
to 1; b_h has coefficient -1, and all other nonbasic variables have
coefficient zero.

If G_h is empty, there is no entering column, so the solver terminates
NONPOSITIVE after h+1 pivots.

Otherwise Bland selects x_h=min G_h. Its tableau coefficient is -1
in the z and earlier x_i rows, zero in a_i rows for i<=h, -1 in later
a_j rows, +1 in later b_j rows, and h+2 in the normalization row.
Consequently the only eligible leaving rows are the later b_j rows,
which have ratio zero, and the normalization row, which has ratio
1/(h+2).

If h<m-1, the minimum ratio is zero. Among the b_j with j>h, the
smallest current basic-variable index is b_(h+1), because they retain
their original slack labels. The pivot coefficient is 1 and the row
has right-hand side zero. The entering variable x_h replaces b_(h+1).
Substitution using

    X_h = X_(h+1) - b_(h+1) + b_h

gives every displayed invariant formula with h replaced by h+1.
This completes the induction, including the exact entering and leaving
tie rules.

If h=m-1, there is no later b_j. The only positive pivot-row coefficient
is m+1 in the normalization row. This final pivot makes
x_(m-1)=1/(m+1), makes the objective 1/(m+1)>0, and the solver returns
POSITIVE immediately. The number of pivots is the initial z pivot plus
m entering-group pivots, namely m+1.

Irrelevant variables y never enter because their reduced coefficients
are zero throughout the zero-objective stages. Duplicate columns in a
group are harmless because they have identical reduced coefficient 1
when that group is current and Bland selects their least index. Once a
group's earliest variable is basic, the other twins have reduced
coefficient zero. If the earlier twin was removed before this LP call,
the remaining twin is simply the least member of the available group.

### Separate zero-objective case

If the column z is absent, the restricted objective is identically zero.
Every initial reduced coefficient is zero, so the solver returns
NONPOSITIVE before making any pivot. This case is not an application
of the nonempty-z chain lemma.

## Apply the lemma to the r-block family

For the synthetic family let m=2r-1. The row groups, in the exact order
used by the model builder, are

    G_0       = {q[0,1], p[0]},
    G_(2j-1) = {q[j,0]},              1<=j<r,
    G_(2j)   = {q[j,1], p[j]},        1<=j<r,

and z=q[0,0]. Each p[j] is a triangle variable in an auxiliary block.
Its original index is greater than that of q[j,1]. The model has no
triangle-anchor restrictions. Every other variable, including all
three quadrilateral variables in every irrelevant prefix block, is an
irrelevant y variable in the chain lemma.

At propagation stage j, all earlier mandatory blocks ell<j have been
forced to quadrilateral type 0, so q[ell,1] has been removed while
p[ell] remains available. This replaces G_(2ell) by its nonempty
singleton {p[ell]}. Other row groups are unchanged. In particular,
every current-node LP has all groups nonempty and therefore uses
exactly m+1=2r pivots.

Deleting any tested irrelevant prefix coordinate changes only the
number of y variables. It neither empties a row group nor changes the
objective, so every such positive deletion query also takes 2r pivots.
Deleting a column changes the absolute slack indices by a common
offset, but preserves their row order. Thus the stated Bland leaving
tie choice is unchanged.

The first mandatory query at stage j deletes q[j,0]:

- For j=0 this deletes z itself. The restricted objective is zero, so
  the query terminates after zero pivots.
- For j>0 this makes G_(2j-1) empty, while all earlier row groups remain
  nonempty. The chain lemma gives exactly (2j-1)+1=2j pivots.

After all r forced choices, the returned positive current-node witness
is admissible and the propagation procedure terminates without another
deletion scan. Hence there are exactly r+1 current-node LPs, each using
2r pivots, and r mandatory deletion LPs with costs 0,2,...,2(r-1).

The baseline additionally executes 3r irrelevant-prefix deletion LPs
at each of r stages, namely 3r^2 positive deletion queries, each with
2r pivots. The screened producer skips precisely these queries using
the zero coordinates of its current exact positive witness.

## Exact total pivot theorem

The baseline total is

    (r+1)(2r) + (3r^2)(2r) + sum_(j=0)^(r-1) 2j
      = 6r^3 + 3r^2 + r.

The screened total is

    (r+1)(2r) + sum_(j=0)^(r-1) 2j
      = 3r^2 + r.

The pivot savings is exactly 6r^3. Both formulas apply even if global
cache capacity is zero, because the screening responsible for this
family uses only the current-node witness retained during its scan.

These are exact pivot counts for the specified solver, row ordering,
column ordering, and algebraic family. They strengthen the oracle-call
separation. They do not establish a polynomial bound for Bland simplex
on other inputs, a general wall-clock factor, or a geometric family of
3-manifold triangulations with these counts.
