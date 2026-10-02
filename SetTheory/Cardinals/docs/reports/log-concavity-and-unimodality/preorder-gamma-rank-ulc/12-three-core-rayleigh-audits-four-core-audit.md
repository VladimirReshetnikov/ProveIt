# Independent audit of the four-core coefficient obstruction

Date: October 1, 2026. Verdict: **APPROVED**.

The example proves that the three-core coefficientwise boundary assertion
cannot be extended without qualification to four physical core vertices. It
does not exhibit failure of scalar Rayleigh nonnegativity, real-rootedness, or
rank-ULC.

## Exact graph and support counts

The four physical tails `0,1,2,3` and five physical heads `a,b,c,d,e` are
disjoint, and all arcs point from tails to heads. Their neighborhoods are

    N(0)={c,d,e}, N(1)={a,b,e}, N(2)={b,d}, N(3)={e}.

The role cover `{0,1}` on the tail side and `{b,d,e}` on the head side covers
every arc. The matching `0→c,1→a,2→b,3→e` has size four, and no matching can
be larger because there are only four tails. Thus the matching degree is four
and this is an example within the stated two-tail/three-head role-cover class.

The independent verifier uses Hall conditions for each selected head subset,
rather than the producer's permutation-based witness predicate. It recovers
exactly the displayed support families:

    B_012: abc, abd, abe, acd, ade, bcd, bce, bde, cde
    B_013: ace, ade, bce, bde
    B_01:  ac, ad, ae, bc, bd, be, ce, de
    B_0123: abce, abde, acde, bcde.

Their sizes are `9,4,8,4`, respectively. Every listed monomial has coefficient
one because a head subset, with the tail subset fixed, specifies one ordered
endpoint support. Matching witnesses are not counted. For example, the only
missing three-head subset in `B_012` is `ace`, which supplies no neighbor for
tail 2.

## Negative coefficient and sum of squares

Exact sparse polynomial multiplication gives

    G=B_012 B_013−B_01 B_0123
     =e²(a²d²−abcd+abd²+b²c²+b²cd+b²d²).

Thus the coefficient of `abcde²` is exactly `−1`. Restoring the four tail
activities multiplies both products by the same monomial
`u_0²u_1²u_2u_3`; it shifts rather than removes the negative coefficient.
This is therefore a genuine obstruction in the original role-activity ring.

The independent checker verifies the denominator-cleared integer identity

    4G=e²[(2ad−bc+bd)²+3(bc+bd)²].

Dividing by four gives exactly the producer's rational two-square formula.
In particular `G≥0` at every real head-activity assignment when the tails have
unit activities. With arbitrary nonnegative tail activities the restored
monomial factor is also nonnegative. Coefficientwise negativity consequently
does not furnish a negative scalar value of this gap.

For the four-core unused-monomer polynomial, `G` is the Rayleigh difference
in the core monomers indexed by 2 and 3, evaluated at all core monomers zero:
the derivatives at zero are `B_013,B_012,B_01`, and the constant term is
`B_0123`. Thus the expression is the appropriate four-core boundary analogue.

## Additional unit-activity check

Independently enumerating all tail subsets gives the full univariate support
polynomial at unit activities:

    Γ(t)=1+9t+24t²+19t³+4t⁴.

Exact rational evaluation gives opposite signs at the endpoints of each of
the four disjoint negative intervals

    (−3,−2), (−2,−1), (−1/3,−1/4), (−1/4,0).

The intermediate value theorem supplies one root in each interval; degree
four leaves no other roots. Thus this unit specialization is real-rooted and
rank-ULC. This supplementary observation is not a claim of real-rootedness
under every possible role-weight assignment.

## Reproducibility and scope

`independent_check.py` uses only the Python standard library. It verifies the
Boolean support sets, exact gap coefficients, integer-cleared SOS, role cover,
degree-four matching, unit support polynomial, and rational sign-change
intervals. `independent_receipt.json` records the results. The producer's
standard-library checker was also inspected; its Boolean existence tests and
exact rational operations agree with this reconstruction.

The approved obstruction concerns **coefficientwise extension only**. The SOS
addresses this particular boundary gap, not every scalar Rayleigh difference
of the graph. No failure of scalar Rayleigh inequalities, real-rootedness, ULC,
or the general two-tail/three-head conjecture is inferred. No minimality or
literature-priority claim is approved.

Earlier approval records and the delivered structural archive were untouched.
