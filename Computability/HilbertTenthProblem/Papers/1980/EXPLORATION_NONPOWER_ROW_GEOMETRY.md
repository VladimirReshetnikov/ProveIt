# Open search for redundancy of the row square-root divisibility

This note concerns a possible deletion of q=v*quot from the proved
82-operation finite-history component system. Deleting that multiplication,
equation and positive quotient would cost 81 operations if the remaining
equations still had the required meaning. That implication is unresolved;
there is no proved 81-operation component result here.

The separate direct-length reparameterization in
`EXPLORATION_DIRECT_HISTORY_LENGTH.md` now proves an 81-operation
component while retaining this geometry equation. It does not resolve
the deletion considered in this note.

Keep Q=q^2 a power of four after the unchanged Pell decoding, W=v^2,
Q-1=H*(W-1), and the gapped five-field Boolean packing. The known proof
needs q=v*quot to infer that v is a power of two. Without that equation,
nonpower possibilities genuinely satisfy the isolated geometry: for
example Q=4^12,v=118,H=1205. The question is whether the full local,
temporal and strengthened input equations eliminate all such cases.

## 1. Correct finite search interface

For Q=4^N, enumerate v>=2 with v^2-1 dividing Q-1 and v not a power
of two. For each Boolean word T<Q, set B=T-H and require B>0 and
B divisible by four. Put C=B/4. Split the normalized digits of B+C
uniquely into X+2D with Boolean X,D, and the digits of 4B+D into
Z+2E with Boolean Z,E. The latter splitting includes the possible
extra digit above Q. Then set Y=X+D-E and require all supplied local
variables positive.

The input parameter must be recovered by

    I = (C-W*Y) mod Q, 0<I<v,
    F = (I+W*Y-C)/Q > 0.

It is incorrect to assume I=C mod W in this experiment. After the
proposed deletion, Q need not be divisible by W; that inference would
silently reinstate part of the missing geometry. The test above is
exactly the remaining temporal equation and the strengthened input bound.

The bound-free mask proof still gives B<Q/3 and D,X,E<Q,Z<2Q,Y<Q
before the missing row geometry is used. Thus these splittings describe
every possible positive tuple with the decoded five fields. They do
not assume B Boolean or a row decomposition of Q into powers of W.

## 2. A finite digit automaton for longer tests

The checker also processes T from low base-four digits upward. It tracks
the previous and current B digit, the borrow in T-H, the carries in
B+C and 4B+D, the signed carry in Y=X+D-E, the carry in W*Y+I,
and flags ensuring that every required local plane is positive. Equal
states can be merged because the remaining H digits and every future
arithmetic transition then agree.

At position i, choose the next Boolean T digit and compute b_(i+1)
by subtraction. With incoming carries c1,c2,c3, calculate

    s1=b_i+b_(i+1)+c1,
    x_i=s1 mod 2, d_i=floor((s1 mod 4)/2),
    s2=b_(i-1)+d_i+c2,
    z_i=s2 mod 2, e_i=floor((s2 mod 4)/2),
    s3=x_i+d_i-e_i+c3, y_i=s3 mod 4.

The next carries are the respective floors after division by four.
The temporal step requires

    (W*y_i+c_time) mod 4=b_(i+1),

starting with c_time=I and finishing with c_time=F. The exterior
b_N is zero. The terminal check retains Z's possible additional
digit from b_(N-1) and the second addition carry, requires no
overflow of E or the other bounded planes, and verifies positivity.
Every recovered path is rechecked against the full integer equations.
The search includes every I in 1,...,v-1 and both parities of P.

## 3. Reproducible finite evidence

`../verification/explore_nonpower_row_geometry.py` and its JSON receipt
record the following exact checks:

* All 45,696 Boolean words across every nonpower radical v for N<=16.
  The cases are v=6,14 at N=6; v=20 at N=9; v=6,14,118 at N=12;
  and v=10 at N=15. No full outer tuple survives.
* Fifty longer digit-automaton searches: v=6,14 through N=60;
  v=20 through N=90; v=118 through N=120; and v=10 through N=150,
  in the appropriate multiples of the geometric periods. No tuple
  survives. The saved state counts show where each prefix closes.
* Four power-of-two positive controls recover actual tuples, exercising
  the endpoint reconstruction rather than only empty search results.
* On every small exhaustive case, the brute-force search and the digit
  automaton agree on whether a witness exists.

This is bounded evidence for a possible redundancy theorem, not that
theorem. In particular, it does not cover arbitrary even v or prove a
uniform obstruction from its low-digit carries. The published
82-operation finite-history system retains q=v*quot, and the proved
universal bound remains 90.
