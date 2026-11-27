# Dividing out q³ saves one operation and raises degree to572

The proposed positive substitution Y=q³y is valid for the accepted
zero-offset98/360 equation: every positive zero has q³|Y, and q>=32.
The complete numerator and carrier admit the universal identities

    M_old=q³ M_new, Z_old=q³ Z_new,
    M_new=(q-1)mu²H,
    Z_new=(q-1)mu²[H(n+V-L*Bt)+Kpos]
          +H[mu²((q-1)y-Bt)-(q-1)e].

All unchanged upstream definitions use the derived Y=q³y. The four norm
arguments consequently acquire a common q^6 factor, and the whole old
output equals q^24 times the new output. Soundness maps a new positive
y to the old positive Y; completeness takes the positive integer
quotient y=Y/q³ at any old zero. This is a whole source equivalence via
an input substitution and a positive output factor, not equality of the
two polynomials at identical input coordinates.

The literal complete graph has97 live operations:57 multiplications,
22 additions and18 subtractions. The net saving is only one: inserting
Y=q³y adds one multiplication; removing P1=q³(q-1) and q³Bt removes two.
Existing q² and q³ gates move before the first use of derived Y. Every
remaining arithmetic row is retained or explicitly rebound, and all ten
inputs remain strictly positive. The entire four-coefficient tuple is
pinned to the accepted original compact44 parent and is carried together.
This packet makes no claim about replacing its K by a different tuple.

The degree cost is substantial. Under the new input weights,

    deg c=5, I=11, H=8, Df=38, Q=54, b=6, V=44,
    deg M_new=13, Z_new=57, u=110, v=118, h=168.

The leading term of b is now c(T+alpha), rather than the old rank R.
Thus simply reweighting the old total-degree leading monomials misses
new dominant terms. Write Z0=Z_new-M_new V and omega=s-h. The actual
center cut gives deg Z0<=27, hence deg omega<=138. In the universal
centered norm

    E=omega²-2(u+v)(2h+omega)+(u-v)²,
    N=E²-64uvh(h+omega),

the unique top of E is -4vh, of degree286. Its square gives the unique
degree572 leading part16v0²h0²; the final product has degree at most564.
Over q0=beta*J, X0=wq0 and k0=eta+zeta, that full leading form is

    2^20 q0^352 X0^36 i^20 y^80 k0^44(T+alpha)^4
    =2^20 q0^388 w^36 i^20 y^80 k0^44(T+alpha)^4.

In particular the coefficient of J^388 w^36 i^20 y^80 eta^44 T^4 is
2^20 beta^388>0, so572 is exact. The naive graph bound672
is only an upper bound before the centered cancellation.

This97/572 tradeoff is dominated by the separately sealed97/368
I²-weight equation, which also saves one operation. It gives no new
operation/degree frontier and is retained as a negative research result.
There is no canonical, common-report, PDF or Lean change and no promotion
of this candidate. A fresh complete page was not rendered because the
measured arithmetic tradeoff already loses to an existing complete one.

check.py independently reconstructs and compares every row of
normalized97.json, authenticates the complete immutable parent inventory
and whole four coefficient files, checks topology/liveness/counts, all35
norm coefficients and q^24 homogeneity, the full numerator/carrier cuts,
the centered cancellation, actual leading components and the nonzero
selected coefficient. CHECK{,_OPTIMIZED}.json retain normal and optimized
replays. The controls reject wrong source rebindings and degree/factor
claims; the unbounded proof above supplies ordinary equivalence.

```sh
python check.py --output /tmp/qcube-normalization.json
python -O check.py --output /tmp/qcube-normalization-optimized.json
```

The closed MANIFEST.json pins all packet files except itself. This
negative packet imports no parent code, runs no incoming code and does
not edit a sealed parent.
