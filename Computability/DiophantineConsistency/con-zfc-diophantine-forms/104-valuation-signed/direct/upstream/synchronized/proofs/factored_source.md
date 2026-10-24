# Factoring the C222 axiom disjunction

For real numbers p,q,v, code values c_1,...,c_s,b and guard value g, write

    C=p^2+q^2,
    A=v product_{j=1}^s(v-c_j),
    B=(v-b)^2+g^2.

Then

    (C+v^2) product_j(C+(v-c_j)^2) (C+B)=0

if and only if

    C+A^2 B=0.                                      (L)

Every factor of the left side is nonnegative. A factor vanishes exactly
when p=q=0 and its remaining square(s) vanish. The right side is a sum of
two nonnegative terms; it vanishes exactly when p=q=0 and either A=0 or
B=0. Since a product over the reals vanishes precisely when a factor does,
these are the same alternatives. The result is valid in particular for
integer and natural assignments.

In the concrete C222 source s=8. The free truth code is zero, the eight
unconditional axiom codes are the first eight entries of the unchanged
`codes` list, and the guarded bundle code is its final entry. Its guard is

    g=((c-a)(c-b))^2-(d+1)^2.

Multiply both sides' zero conditions by the same nonnegative modus-ponens
and generalization factors. Add the same nonnegative squares enforcing
the accumulator update and the two beta-reading equations. Vanishing of
the resulting old and new source expressions is therefore equivalent.
This is zero-set equivalence, not a claim that the polynomial values agree.

`direct_source_factored.py` retains the exact constructor code prefix and
the exact eleven-coordinate local-row suffix from `direct_source.py`.
Only the block from the definition of `pq` to the definition of `carrier`
changes. Its pair representation uses

    (a,b)+(c,d)=(a+c,b+d),
    (a,b)*(c,d)=(ac+bd,ad+bc),
    (a,b)^2=(a^2+b^2,2ab),

so each pair represents its first component minus its second exactly, and
both components remain polynomials with nonnegative coefficients. This
preserves the coefficientwise monotonicity used in the shared CRT majorant.

The ordinary proof of (L) is a short ordered-ring argument. Finite controls
check the implementation and source boundaries; they are not substitutes
for this proof over all inputs.
