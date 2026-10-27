# Independent review: heterogeneous cached contraction below 38

This is the final cached schedule reviewed for the report. It supersedes
the earlier eight-group candidate. The conclusions below are conditional
on the same imported contraction identities, full-block Cauchy separation,
and asymmetric balancing theorem as the other new constructions. The
schedule and its composition have been independently checked; the full
upstream theorem has not been formally rebuilt.

## 1. Schedule and final coefficients

Use `lambda=ceil(log2 s)`, `H=ceil(s/lambda)`,
`Delta=ceil(s^(9/10))`, and `B=ceil(6 log2 lambda)`. Let

    r0=7,            rd=9 for d>=1,
    eta0=89/5000,
    eta1=1233/125000,
    delta=7/25,
    ud=floor(eta1 lambda delta^(d-1)) for d>=1,
    u0=floor(eta0 lambda),
    ad=sum_{j<=d} uj+(d+1)B,
    Ld=2^ad,         Qd=rd^ad.

The total tail range is `eta1/(1-delta)=137/10000`, and the complete
leading packet-exponent budget is

    A=eta0+137/10000=63/2000=.0315.

Partition the root's seven groups into blocks of sizes 2,2,3. At all later
calls partition nine groups into blocks of sizes 3,3,3. Cache individual
group functions, construct the three block tables, and contract the triangle
by the existing division-free rectangular Strassen algorithm.

Put `kappa=pi sqrt(2)/ln2`, `omega=log2 7`, and `beta=omega-2`. Define

    a7=sqrt(12)/7,
    aB7=sqrt(30)/7,
    b7=sqrt(24+8 beta^2)/7,
    j7=sqrt(24)/7,

    a9=4/9,
    aB9=sqrt(42)/9,
    b9=sqrt(4+2 beta^2)/3,
    j9=2/3.

The final coefficients are

    C_time = kappa [a7/sqrt(eta0)+(2/7)b9/sqrt(eta1)]
           =37.930109082884556... <38,
    C_space=kappa j7/sqrt(eta0)
           =33.623040921657754... <34.

The time is bounded by `poly(s+description) 2^((C_time+o(1))s/sqrt(log2 s))`,
and space by the same form with C_space. Space is subexponential rather than
polynomial. These are normalized wire-level upper-bound coefficients.

## 2. Important root table correction

The root Strassen coefficient is

    b7=.7721501355724768...,

whereas its block-table construction coefficient is

    aB7=.7824607964359516... .

Thus `b7<aB7`, not the reverse. The root recurrence must retain aB7.
This does not change the final coefficient: the three competing root costs
on the normalized leading scale are

    matrix multiplication: 37.0963482859143...,
    block-table construction:37.59170255554196...,
    cached group children: 37.930109082884556... .

The last term dominates all three. This correction must be reflected in
the report and its verification script; it should not be hidden by using
the numerically correct final coefficient alone.

## 3. Packing and changing alphabets

Each call's labels and packets are freshly constructed. No deformation or
factorization identity requires that its alphabet agree with an ancestor's.
Changing seven groups to nine preserves all old entries and their fixed
canonical representatives. Below the root, all retained tensors occupy the
row side and fresh packet tensors the column side, so

    R_d<=Delta, C_d<=2 L_{d-1}.

The asymmetric packing gates are `Q R/M=o(1)`,
`Q^2 C (log s)^2/M=o(1)`, and `L Q^2/M=o(1)`.
At the root the leading power condition is

    9/10+2 eta0 log2 7<1,

which is certified exactly by `7^89<2^250`. Below the root,

    9/10+A log2 9<1,

certified by `9^63<2^200`. The numerical gaps are approximately
`0.0000581647747493` and `0.0001473624545672`; they are strictly positive
fixed constants, although far too small to suggest practical crossover
sizes.

The remaining below-root exponents satisfy

    Q_d^2 C_d : 2 A log2 9+A < .2+.0315=.2315<1,
    L_d Q_d^2 : A(1+2log2 9)<.2315<1.

At the root the rounding exponent is smaller still. New packet tensors
have degree at most `2 L_d=s^(.0315+o(1))<Delta`. The additive buffers are
only `O((log lambda)^2)=o(lambda)` at logarithmic depth. Consequently all
packing and maximum-degree conditions hold with strict power gaps.

## 4. Noncircular depth and uniform errors

Initially verify the gates at every hypothetical active depth

    d<=1+ceil(log_4 lambda)+O(1).

At the root, near-unit padding eventually gives a child bound below M/3.
At tail depths, its sharper ratio is `2/9+o(1)<1/4`, so the coarse tail
bound M/4 holds. It follows that an active path has at most the displayed
number of levels; the hypothetical range is therefore justified.

Within that range,

    u_d>=lambda^(1-ln(25/7)/ln4+o(1)) -> infinity,

because `25/7<4`. All floors are uniformly relatively negligible. The
explicit padding error is `O(1/lambda)+s^(-c+o(1))` for some fixed c>0,
so multiplying it over `O(log lambda)` levels yields `1+o(1)`. In particular

    M0<=s,
    M_d<=(1+o(1))(2/7)s(2/9)^(d-1), d>=1.

A mere unspecified o(1) error at each depth would not itself establish the
last uniform statement; the explicit error bound is what makes it valid.

## 5. Precision, entropy, and per-pair multiplicity

The additive gap and exact taper give, as in the reviewed asymmetric packet,

    p<=O(s lambda^2 2^(a_{d-1})),
    D_i>=2^(a_{d-1}+B+1),
    p_t<=(6+o(1)) M D_i/u_d.

Indeed the ratio of inherited precision to `M D_i/u_d` is at most
`O(lambda^4 2^(-B))=O(lambda^(-2))`, uniformly. All relevant precisions,
interpolation degrees, and ring dimensions remain polynomial in s.

Common padding implies that one directed unequal group pair has at most

    (2+o(1)) M/(r_d^2 D_i)

modes of each slope-four index. The full-block weights may conservatively
be replaced by `1+4q-2 popcount(q)`. Their generating function has leading
term `pi^2/(24 theta)`. Thus for fixed pair coefficients z_e and pair-list
logarithms h_e,

    sum_e z_e h_e
      <=(sqrt(sum_e z_e^2/r_d^2)+o(1))K_d,
    K_d=kappa M_d/sqrt(u_d).

The finite alphabet set {7,9} permits uniform error bounds. Exact directed
pair-weight enumeration is polynomial, with fixed exponents. The entropy
proof uses the global total weight and one tilted parameter, so individual
pair budgets are not incorrectly assumed large.

## 6. Combinatorial counts and recurrence

At the root, a group has 12 incident directed pairs. A block of size k has
`2rk-k^2-k` incident pairs, giving maxima 30 for the 2,2,3 partition. Boundary
pair counts are `2k(r-k)`, with maximum 24. The three crossing classes have
sizes 8,12,12. Rectangular Strassen discounts the smallest class by
`1-beta^2`, producing b7 above.

At a tail call a group has 16 incident pairs. Blocks 3,3,3 have incident
count 42 and boundary count 36. Crossing class sizes are 18,18,18. These
give a9, aB9, b9, j9 as displayed.

The tail ratio of successive entropy scales is

    gamma=(2/9)/sqrt(7/25)=10/(9sqrt7)=.41996052556580804... .

Therefore the tail's entire recursive coefficient relative to its own K1 is

    max(b9,aB9,a9/(1-gamma))=b9.

Here `a9/(1-gamma)=.7662313756800506...<b9=.7676547213096726...`,
and `aB9=.7200822998230956...<b9`. All recursive child calls are explicitly
paid; group functions are not free oracles.

The complete root bound is consequently

    max(kappa b7/sqrt(eta0),
        kappa aB7/sqrt(eta0),
        kappa a7/sqrt(eta0)+(2/7)kappa b9/sqrt(eta1)),

equal to the last term by the strict inequalities proved below. Leaf cost
`2^{O(s/lambda)}`, old-entry cost `exp(O(s^.9))`, and new packet-entry cost
`exp(s^(.0315+o(1)))` are lower order. Fixed-polynomial factors across
logarithmic depth add only `O(lambda log lambda)` to the logarithm of time.

Stored tables at root and at the first tail call have leading coefficients

    kappa j7/sqrt(eta0)=33.623040921657754...,
    (2/7)kappa j9/sqrt(eta1)=12.292878078413612... .

Later scales decrease. Stored tables at different levels add in size, so
their leading exponents take a maximum rather than a sum. Root group caches
are smaller than root boundary tables. The stated space coefficient follows.

## 7. Rational proofs of the recurrence comparisons

Let beta=log2(7/4). Exact integer inequalities give

    25/31<beta<13/16,
    because 7^31>2^87 and 7^16<2^45.

Also `gamma<21/50`, since its squared form is the integer inequality
`250000<250047`. Hence

    a9/(1-gamma)<200/261 < sqrt(566)/31 < b9.

The middle comparison follows by squaring:
`566*261^2-40000*31^2=116486>0`; the final one follows from
`b9^2>(4+2(25/31)^2)/9=566/961`.

Because beta<13/16, `24+8beta^2<30`, proving `b7<aB7`.
To prove the cached-child root term exceeds the table term, it is enough to
show

    2 b9 sqrt(eta0/eta1)>sqrt30-sqrt12.

The simple bounds `b9>153/200`, `sqrt(eta0/eta1)>67/50`,
`sqrt30<11/2`, and `sqrt12>69/20` give

    left side > 10251/5000=2.0502,
    right side <41/20=2.05.

The first bound follows already from beta>4/5, certified by `7^5>2^14`.
The second follows by squaring `eta0/eta1=2225/1233>4489/2500`.
Thus the leading-time formula is certified without relying on rounded
decimal output.

## 8. Simple rational headline certificates

Use `pi<22/7` and `ln2>69314/100000`. The latter follows from the first five
positive terms of

    ln2=2 sum_{j>=0} 1/((2j+1)3^(2j+1)),

whose partial sum is `4297606/6200145>.69314`. Squaring gives
`kappa<6413/1000`.

The upper bound beta<13/16 gives `b9^2<227/384`. Also

    a7/sqrt(eta0)=sqrt(60000/4361)<371/100,
    (2/7)b9/sqrt(eta1)<sqrt(3546875/725004)<2213/1000.

Therefore

    C_time < (6413/1000)(371/100+2213/1000)
           =37984199/1000000=37.984199<38.

Similarly

    j7/sqrt(eta0)=sqrt(120000/4361)<21/4,
    C_space<(6413/1000)(21/4)=33.66825<34.

The tail space coefficient is smaller by direct comparison of the exact
squared scales `2000000/543753<120000/4361`. These headline certificates
are deliberately simple; tighter interval arithmetic supplies the decimal
coefficients quoted in Section 1.

## 9. Scope of the improvement

The strict time coefficient 37.930109... improves the 38.167745... limiting
certificate identified for the stronger prior compatible fixed-family
composition, as well as the larger explicit coefficients. The proof uses
depth-dependent group counts and a separately allocated root/tail range;
it is more than merely multiplying the old headline constants.

This is still an improvement to the leading coefficient of the
`s/sqrt(log s)` exponent. It does not improve its logarithmic order, does
not supply an end-to-end practical SAT solver, does not imply an observed
SAT speed ratio, and does not dominate missing conditional `s/log s`
interfaces. Polynomial-space improvements should be presented separately.
