# An explicit equation over unrestricted integers

The literal recipe in `recipe.json` replaces each of the 261 natural
variables of the principal quartic by

`H(u,v,w) = u^2 + v^2 + w(w+1)`.

It therefore defines a fixed polynomial in 783 integer variables of
exact degree 8. The file specifies every substitution and pins the base
polynomial by SHA-256; no variable coefficient, program parameter or
nonpolynomial operation occurs in its definition.

For any integer `w`, `w(w+1)>=0`. Conversely, for any `n>=0`, Legendre's
three-square theorem represents `4n+1` as three squares. Exactly one is
odd and the other two are even (by reduction modulo 4), so rearranging
and dividing by four gives `n=u^2+v^2+w(w+1)`. The substitution is thus
surjective onto the natural numbers. This proves, in ZFC, equivalence of
solvability with the base equation.

Degree 8 is exact: set all `v_i,w_i` to zero, leaving the injective
monomial substitution `z_i -> u_i^2`, which cannot annihilate the nonzero
degree-four homogeneous part of the base polynomial.

This is a domain companion, not a claimed new size record over integers.
