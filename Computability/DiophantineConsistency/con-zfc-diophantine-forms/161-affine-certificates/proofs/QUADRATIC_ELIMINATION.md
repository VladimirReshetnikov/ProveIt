# Removing the Pell discriminant gate

This is an unconditional algebraic reduction on the literal systems emitted
by the affine-radix construction. It applies to every integer zero, without
using binomial, factorial, sign, cofinality, or consistency assumptions.

## General contraction lemma

Let an integer polynomial system contain the residual `c*x+f(z)`, where
`c=1` or `c=-1` and `f` does not involve `x`. Substitute `x=-c*f(z)` in every
other residual and delete that one row and variable. Projection and the
polynomial restoration `x=-c*f(z)` are inverse bijections of the integer zero
sets. No denominators and no divisibility conditions are introduced.

After substitution one may perform elementary polynomial row operations
`R_i := R_i - h(z)*R_j`, where the unchanged row `R_j` is retained. Their
inverses add the same multiple. The simultaneous zero set is unchanged even
if the multiplier is not constant. Such operations can cancel cubic terms
created by the substitution, which an affine-only elimination misses.

## The actual identity

Write `a` for the stored coordinate called `shared.A`; the semantic Pell base
is `a+1`. Three existing algebraic quantities satisfy

```
Z - (a+1)*Y = 0,
D - a*a - 2*a = 0,
R = T + a*Z - D*Y = 0,
```

where `T` is the rest of the affected residual and is quadratic. The
discriminant's only nonlinear occurrence is the product `D*Y`. There is
also a linear occurrence in the residual labeled `shared.last_norm` after
the inherited row operations. Replacing that occurrence by `a*a+2*a`
keeps its degree at most two, and the exact certificate transforms that
row as well. Substitute
`D=a*a+2*a`, and subtract `a` times the first row from the third. The result
is simply

```
R_new = T - a*Y = 0.
```

Indeed `a*Z-(a*a+2*a)*Y - a*(Z-a*Y-Y) = -a*Y` identically.
Thus the entire transformed system remains quadratic. The deleted
discriminant is uniquely restored as `D=a*a+2*a`.

For the incoming principal240 source the pivot row is 121, its variable is
167, the row requiring a polynomial residual operation is 122, and the
retained product row is 105. Its additional linear occurrence is in row104.
For its companion239 source the corresponding numbers are120,166,121,104,
with the additional linear occurrence in row103.
These are zero-based indices in the archived source equations. The supplied
certificates record the full coordinate renumbering and restoration maps.

## Exact finite result

`principal_D` has 239 unrestricted integer variables, 175 quadratic residuals,
degree 4, 5,044 collected monomials, and coefficient height 7,968.

`companion_D` has 238 unrestricted integer variables, 174 quadratic residuals,
degree 4, 12,789 collected monomials, and coefficient height 7,968.

The same exact contraction applies to the separately proved horizon-free
arithmetic variants. `horizon_principal_D` has 238 variables, 174 rows and
5,042 terms; `horizon_companion_D` has 237 variables, 173 rows and 12,787
terms. Both remain quartic and have coefficient height
1,298,074,204,962,300,530,359,575,779,475,468. The larger height is the cost
of inserting the fixed multiplier `2^26` in the arithmetic growth base.

The final polynomial is the sum of squares of its complete retained residuals.
Over the integers it vanishes exactly when all residuals vanish. Consequently
each final polynomial has an integer zero if and only if the corresponding
source polynomial does. Composing with the separately proved source theorem
gives the same refutation/consistency equivalence, formalizable in ZFC.

The larger source theorem is not established by these finite checks. The
statement here is the algebraic bijection and the literal equation data.
No global minimum or literature-wide priority is asserted.

## Reproduction

The standalone builder and search use only integer arithmetic and the Python
standard library. `verify_projection.py DIRECTORY` is separately written,
imports neither builder nor search, verifies the source digest, every
substitution, every reversible polynomial row operation, every restoration
coordinate, every collected coefficient, and every stated metric. It also
rejects changed replacement, changed residual, and changed expansion inputs.

An exhaustive scan of the same restricted rule after the D deletion found
no further contraction on the 238-variable source. This is a statement about
the implemented local search only, not a mathematical lower bound.
