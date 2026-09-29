# Input-sum reuse: two obstructions and an exact spill example

This note records a bounded search for reusing the instruction `b=x+beta`
to remove the separate coordinate-code addition `C=x+g`. It does not claim
a lower bound for arbitrary encodings.

## Direct reuse is incompatible with the radix

In the current system `B=Hb^2`, with `H>16` and `b>=2`. The decoded unit
coordinate `delta=1` is at weight 1, so every intended coordinate code
satisfies `C>=B` (in fact `C>B`, because its unit input is positive).

Reusing the already computed input sum as the code would give

    C=x+beta=b<B,

which contradicts that condition. Reusing `beta` as the complete code
also fails, since `0<beta=b-x<b<B`. These are failures of necessity,
not merely weaknesses in the soundness proof.

Taking `C=b+g` or `C=beta+g` still costs one addition. To recover the
original input from `b-beta`, both numbers must then be tied to decoded
coordinates. A decoded coordinate for beta cannot simply be assumed
equal to the external positive variable beta. A new equality or a
proved mask identity would be needed; none has been obtained at lower
arithmetic cost.

If the variable `b=x+beta` is repurposed as the complete code while a
different variable bounds the radix digits, the construction again
requires a relation making the actual input smaller than that new
digit bound. Merely renaming the variables does not remove that cost.

## Why the input bound cannot simply be omitted

There is an explicit spill into an ignored dummy coordinate if the
relation `b=x+beta` is dropped while `C=x+g` is retained.

Consider the valid fixed quadratic encoding for the set `{1}`. One may
start with the residual `x-1` and pad to the prescribed number of rows.
Its homogeneous residual is `x delta-delta^2`. The unit guard and
special row are as in the published construction.

Fix an admissible index and a power of two `b>=2`, and put `B=Hb^2`.
Choose one dummy target position `t`. Let `v_59` be the position of the
guard coordinate `u`. The intended digit polynomial

    C_0=1+B+B^(v_59)+B^t

has input 1, delta 1, u 1, and one dummy coordinate 1. It satisfies the
homogeneous original residual, `u delta-x^2=0`, and the special test.
Every digit is smaller than `b`.

Now supply the different positive external input and code integer

    x_ext=1+B^t,      g_ext=B+B^(v_59).

Then `C=x_ext+g_ext=C_0` exactly. The first mask accepts `g_ext`: it has
only allowed coordinate positions and digits smaller than `b`. The
third mask sees the same legitimate digit polynomial `C_0`, whose
input digit is 1. The external value `B^t` has entered an ignored dummy
coordinate, not the input digit.

Use the canonical fixed e and ell codes. The packed congruence, all
coefficient bounds, positive Omega and sigma, and the normalized block
ranges hold exactly as for legitimate small digit values. Both changed
no-carry blocks hold: the first checks the allowed g_ext, and the third
checks C_0. The central-binomial divisibility condition therefore holds
for the r computed from these data. Nevertheless `x_ext` is not in
`{1}`.

This explicitly disproves the attempted inference that the first mask,
the polynomial target tests, and the positivity bounds would recover
`x<b` after that input equation was deleted. The surviving coding and
binomial conditions do not distinguish this example from a legitimate
digit code for input 1. A full auxiliary-Pell instantiation is not
claimed here; it is unnecessary for this stated failure of the proposed
range argument.

## Scope

The examples exclude direct reuse of b or beta as the entire current
code, and exclude deleting the input bound without a replacement
argument. They leave open broader constructions that encode an external
radix bound inside the homogeneous coordinates with a proved relation
and a lower total arithmetic cost.
