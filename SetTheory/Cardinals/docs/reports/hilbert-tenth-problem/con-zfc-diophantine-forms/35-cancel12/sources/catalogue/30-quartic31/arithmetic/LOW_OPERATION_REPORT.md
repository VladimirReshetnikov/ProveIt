# Retained-root auxiliary gap: a modest system tradeoff

The pinned package-22 source really has 16 positive witnesses, 7 equations,
59 binary gates (33 multiplications, 26 additions/subtractions), and residual
degrees 22,18,24,7,2,22,6. Its stated degree 24 is correct.

Replace its positive auxiliary root y by V+e, where V=of-c and e is a new
positive coordinate in place of y. Every other formula and equation is left
unchanged. Computing V+e costs one addition and its square reuses the original
y-square gate. The emitted `retained16_gap_system60.json` has 60 gates,
33 multiplications and 27 additions/subtractions, and exact residual degrees
22,18,20,7,2,22,6. Its maximum degree is 22.

For soundness, restore y=V+e. The strong equation makes A0=(ic^2)^2>1.
The auxiliary norm A0 V^2-(A0-1)y^2=1 excludes y=0. Replacing y by |y|
therefore gives a positive source root while leaving every equation intact;
no positivity of V is required for this direction. For canonical positive
source witnesses, V>1 and y>0, and

    (A0-1)(y^2-V^2)=V^2-1>0.

Consequently y>V and e=y-V is positive, proving completeness. This is an
existence equivalence, not a claim that all original positive tuples have
positive gap. The exact auxiliary leading degree drops from 24 to 20 through

    A0[V^2-(V+e)^2]+(V+e)^2
      = (V+e)^2-A0 e(2V+e).

The system's degree22 is still attained by the unchanged first norm and
ordinary strong equation.

Comparison must use the actual existing data: package12 already has a
15-positive-variable, 6-equation, 61-gate, degree22 system
`ordinary_gap_system61.json`. Thus our 16-variable 60/22 point saves just one
gate in exchange for one additional variable and equation. The main result of
this lane is the separate 31-variable quartic, not a claimed new <59-gate
frontier.

## Explored but not promoted

- No rigorously equivalent system with fewer than 59 gates was established.
  Simple factorization and affine shears mostly redistribute, rather than
  remove, charged operations.
- A first-root gap tau=L+t costs one more addition and lowers that residual
  to degree12, but the strong equation remains degree22. It offers no better
  maximum-degree/operation point here.
- Eliminating alpha through G=q(q-F)-C can keep certain transport expressions
  quadratic using X=wq, but discards a required positivity restriction. It was
  rejected rather than treating inferred bounds as automatic.
- Weakening c^2 divisibility to c in the strong Pell equation does not preserve
  the needed conclusion c|m from the available rank proof. It was not used.
- Direct coordinate elimination can miss useful relations between remaining
  equations. The successful G deletion instead uses N=q(L+1) to reduce the
  apparent cubic product GL to two quadratic products.

These are scoped research observations, not lower bounds or minimality claims.
