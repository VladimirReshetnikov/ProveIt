# Source161 discriminant deletion is already subsumed

## Conclusion

The discriminant contraction in newly placed source161 gives **no further
variable reduction** of this submission's Balanced218 or Centered216.
Its target coordinate was already removed by the earlier strict-horizon
semantic reduction. It is not an additional 218-to-217 or 216-to-215 move.

This is a comparison and redundancy check, not a new equation or theorem
of minimality. The supplied equations and their coefficients are unchanged.

## Newly inspected repository source

Repository snapshot: `fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb`.

Source161 describes its exact algebraic contraction in
[QUADRATIC_ELIMINATION.md](https://github.com/VladimirReshetnikov/ProveIt/blob/fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb/Computability/DiophantineConsistency/con-zfc-diophantine-forms/161-affine-certificates/proofs/QUADRATIC_ELIMINATION.md).
The construction is also summarized in its
[README](https://github.com/VladimirReshetnikov/ProveIt/blob/fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb/Computability/DiophantineConsistency/con-zfc-diophantine-forms/161-affine-certificates/README.md).

With stored Pell-base coordinate `a`, the contraction uses

    Z-(a+1)Y=0,   D-a^2-2a=0,
    aZ-(a^2+2a)Y-a(Z-aY-Y)=-aY.

Consequently one may substitute `D=a^2+2a` and use a reversible polynomial
row operation to cancel the resulting cubic term. Source161 also handles
an additional linear occurrence of D in its chosen residual basis.

## Exact correspondence with our retained parent

Our source157 242-variable parent has the same target under the literal
name `index_addition.D`, at zero-based coordinate **170**. Its defining
residual is row **123**:

    index_addition.D - shared.A^2 - 2*shared.A = 0.

Its only other occurrence is in row **124**, the redundant power request
for `pow6.output`, which represented `q^(t+1)`. Coordinate170 occurs in
exactly rows123 and124 in this parent.

The construction's first stage, `composition/composed/strict238`, already
deletes the following parent coordinates and rows:

| Parent coordinate | Name |
|---:|---|
|112|pow6.output|
|170|index_addition.D|
|171|pow6.quotient|
|233|remainder_budget.ratio1|

Deleted parent rows are **123,124,173**. The stage also deletes the
`-pow6.output^2` term from the square frame and redirects the five applicable
range rows to the retained ratio. These are precisely the already proved
cofinal strict-horizon edits, not a new deletion justified by a local search.

The discriminant is therefore absent from strict238, basis235, pooled223,
differences223, Balanced218 and Centered216. Its original output is not
retained under an alternative name: the coordinate-retention certificate
explicitly excludes coordinate170.

## The last-norm occurrence has already been resolved

In our parent and both final equations, the residual labeled
`shared.last_norm` is already

    shared.A^2 + 2*shared.A + mul.450^2 - mul.451^2.

Its row numbers are105 in the parent,96 in Balanced218, and94 in
Centered216. Thus it contains the explicit quadratic expression `a^2+2a`,
with no independent discriminant coordinate to remove. Source161's warning
about its additional linear D occurrence creates no missed obligation here.

## Reproducible finite check

Run the accompanying standard-library checker with the final package path:

    python3 check_redundancy.py /path/to/ConZFC_Pooled_Projection_2026-10-25

It checks the exact parent discriminant definition and its complete use list,
the strict-stage certificate and retention map, absence from every subsequent
stage and endpoint, and the three literal last-norm residuals. The normal
and optimized runs passed. It does not modify the package and does not
establish the inherited unbounded strict-horizon theorem; that proof is
already part of `composition/COMPOSITION_PROOF.md`.
