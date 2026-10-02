# The coefficientwise boundary assertion fails at four cores

This is an obstruction to extending the new three-core coefficientwise result. It is not a counterexample to scalar Rayleigh nonnegativity, real-rootedness, or rank-ULC.

Take four tail vertices 0,1,2,3 and five distinct head vertices a,b,c,d,e. Include exactly the one-way arcs given by

    N(0)={c,d,e}, N(1)={a,b,e}, N(2)={b,d}, N(3)={e}.

Give the tails unit activities and give the heads activities a,b,c,d,e. Let B_J count feasible head supports matchable to the tail set J, once per support.

The relation has a role cover of two tails {0,1} and three heads {b,d,e}. Thus it lies within the general two-tail/three-head class being investigated. The physical graph is bipartite and its matching degree is four.

Direct Boolean matching tests give

    B_012 = abc+abd+abe+acd+ade+bcd+bce+bde+cde,
    B_013 = ace+ade+bce+bde,
    B_01 = ac+ad+ae+bc+bd+be+ce+de,
    B_0123 = abce+abde+acde+bcde.

Their boundary gap is

    B_012 B_013 - B_01 B_0123
      = e^2 (a^2 d^2 - abcd + abd^2 + b^2 c^2 + b^2 cd + b^2 d^2).

The coefficient of abcde^2 is −1. Restoring tail activities simply multiplies the entire gap by u_0^2 u_1^2 u_2 u_3, so it remains a negative coefficient in the full role-activity ring.

Nevertheless the exact identity

    B_012 B_013 - B_01 B_0123
      = e^2 [(ad+b(d-c)/2)^2 + 3b^2(c+d)^2/4]

proves that this gap is nonnegative at every real head-activity assignment. It therefore does not disprove scalar Rayleigh nonnegativity; its purpose is to show that coefficientwise positivity is a genuinely stronger property which cannot be assumed beyond three cores.

The standalone standard-library verifier `check_four_core_obstruction.py` reconstructs the four B polynomials from endpoint-support feasibility, checks the negative coefficient, and expands the rational two-square identity exactly. No numerical optimization or floating-point roots are involved.

No minimality or literature-priority assertion is made.
