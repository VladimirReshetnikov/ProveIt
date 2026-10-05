# A paid integral-plane factorization for each relator and its inverse

For any fixed P in SL2(Z), the relator pair acting on the existing eight
raw selected-source ports can be appended to the current(d,e,f) increment
accumulators with

    21M+19A=40 operations.                                  (1)

The uniform three-by-four coefficient schedule in the frozen sparse
action uses24M+24A=48 per relator pair, so(1) saves eight operations
per presentation relator. This is an explicit integral factorization
with every runtime product and accumulator update charged. A rank bound
alone would not establish the count or permit runtime division.

Root requested a paid generic relator continuation after the optimized
eight paired letters. The present handwritten result changes none of
their inputs, outputs, native lanes or positive witnesses. The numeral
recipe below is finite fixed compiler preparation; the universal relator
list remains numerically unmaterialized.

## 1. Exact raw-word cut and fixed difference matrix

Write P=[p,q;s,t], with pt-qs=1, and use the established representation

    S(P)=[p^2,-2pq,q^2;
          -ps,pt+qs,-qt;
          s^2,-2st,t^2].                                   (2)

For either sign the four retained raw ports are Z4,Z5,Z6,Z7. The three
signed decoded coordinates are

    C Z=(Z4-Z7, Z4+Z5-2Z7, 2Z4+Z6-4Z7)^T,
    C=[1,0,0,-1;1,1,0,-2;2,0,1,-4].                       (3)

Let z be the eight-vector of positive-slot raw words followed by the
negative-slot raw words, each in the coordinate order4,5,6,7. The exact
three-coordinate pair increment is Wz, where the fixed integer matrix is

    W=[(S(P)-I3)C | (S(P^-1)-I3)C].                        (4)

The existing accumulated coordinates(d0,e0,f0) must be updated by Wz.
They are computed signed intermediates, not new existential witnesses.
All equalities below hold for arbitrary integer z and accumulator values;
the proof does not require one-hot selectors or positivity at this cut.
The raw-word producers and native selected-product proof remain outside
the local ledger and unchanged.

## 2. A common integral left normal, including the central cases

Put n0=(s,p-t,-q). Direct multiplication gives

    n0 S(P)=n0.                                            (5)

Indeed its first component is s[p^2-p(p-t)-qs]=s(pt-qs)=s;
the second is(p-t)(pt+qs)-2qs(p-t)=(p-t)(pt-qs)=p-t;
the third is q[qs-t(p-t)-t^2]=q(qs-pt)=-q.
The inverse is[t,-q;-s,p], whose corresponding normal is -n0.
Thus n0 also fixes S(P^-1), and n0 W=0.

If n0 is nonzero, divide its three entries by their positive gcd to
obtain a primitive integer normal n. Fixed preparation chooses an
output-coordinate permutation so that n1 is nonzero. Apply the same
permutation to the rows of W. Denote the resulting matrix by W' and
normal again by(n1,n2,n3), so

    gcd(n1,n2,n3)=1, n1!=0, (n1,n2,n3)W'=0.               (6)

If n0=0, then s=q=0 and p=t with p^2=1, so P=I2 or -I2.
In either case S(P)=S(P^-1)=I3 and W=0. For the uniform recipe simply
take n=(1,0,0), W'=W, and the identity output permutation. Conditions(6)
then hold as well. One could instead omit the identically zero increment,
but that optimization is not required for the bound(1).

## 3. Explicit integer basis and precompiled coefficient forms

Let g=gcd(n1,n2)>0, and choose fixed integers a,b with

    a n1+b n2=g.                                           (7)

Primitivity implies gcd(g,n3)=1. For each column j of W', write its
entries as(x_j,y_j,z_j). Define fixed coefficients

    alpha_j=b*x_j-a*y_j,
    beta_j=z_j/g.                                         (8)

Every beta_j is an integer: equation(6) says
g divides n3*z_j, and gcd(g,n3)=1 therefore gives g divides z_j.
This is a divisibility proof about fixed integer columns, not a
divisibility condition later imposed on runtime witnesses.

Set the two fixed integer basis columns

    u=(n2/g,-n1/g,0)^T,
    v=(-n3*a,-n3*b,g)^T.                                  (9)

Then each column of W' satisfies exactly

    (x_j,y_j,z_j)^T=u*alpha_j+v*beta_j.                    (10)

For example its first reconstructed entry is

    [n2(b*x_j-a*y_j)-a*n3*z_j]/g
      =[b*n2*x_j+a*n1*x_j]/g=x_j,

using n1*x_j+n2*y_j+n3*z_j=0 and(7). The second entry follows in the
same way, and the third is g*beta_j=z_j. Consequently the entire
fixed matrix factors as W'=[u v] times the two-by-eight coefficient
matrix with rows alpha and beta.

This construction handles n2=0, n3=0, negative normal entries and all
noncentral trace values without a separate division by a matrix entry.
For the central default normal one may take g=1,a=1,b=0; both coefficient
rows are zero. All gcd computations, Bezout choices, coordinate
permutations and exact divisions in(6)--(9) belong to the preparation of
fixed integer numerals. The runtime arithmetic below contains no division,
gcd, search, variable choice, norm certificate or additional witness.

## 4. The complete appended runtime schedule

Write z1,...,z8 for the raw selected words at this cut. Compute two
ordinary eight-term dot products

    A=sum_(j=1..8) alpha_j*zj,
    B=sum_(j=1..8) beta_j*zj.                              (11)

For each dot product emit eight coefficient multiplications and seven
additions. This is16M+14A, including unit, negative or zero fixed
coefficients. Such redundant products are permitted in a uniform upper
schedule; no minimality is claimed.

Next compute the five products

    X1=(n2/g)*A; X2=(-n3*a)*B;
    Y1=(-n1/g)*A; Y2=(-n3*b)*B;
    Z=g*B,                                                (12)

and the two sums X=X1+X2, Y=Y1+Y2. The quotients and products appearing
as coefficients in(12) are already fixed integer numerals from(9);
their displayed preparation is not runtime arithmetic. The five
variable multiplications in(12) are all charged:5M+2A.

Finally add X,Y,Z to the three existing accumulators in the inverse
of the fixed coordinate permutation used in Section2. This is exactly
three additions. A coordinate permutation itself is a static register
alias, not an arithmetic gate. The total is

    16M+14A +5M+2A +3A =21M+19A.                          (13)

Equations(10)--(11) prove that the appended values are precisely Wz in
the original(d,e,f) order. No missing chart, sum of inverse slots or
accumulator addition lies outside(13). The recipe consumes the same
eight raw ports as the old per-relator difference table.

## 5. Comparisons and exact scope of the saving

The preceding uniform schedule evaluates all24 entries of the two
three-by-four matrices in(4). Since the accumulators already exist,
each of its24 products is added once to its target accumulator, giving
24M+24A. Compared with that schedule,(13) saves3M+5A per relator pair.

**Remark 1 (retained missing-append correction).** Root's preliminary
suggestion was that decoding both triples first might cost18M+25A
per relator append. That count omitted the three final additions to
the existing accumulators. The explicit decoded alternative uses10A
to obtain both triples in(3),18M+12A for the two three-by-three actions,
3A for the three inverse-pair sums, and3A for accumulation:18M+28A=46.
Without the last three additions it computes three separate outputs,
not the requested updated accumulators. Thus the initial18M+25A
append count was false; the corrected alternative saves only two
operations against48. The new integral-plane schedule(13) saves eight.

Keeping the frozen paired-letter optimization30M+168A and appending
each of r relator pairs by(13) gives the six-increment cut

    (30+21r)M+(168+19r)A.                                 (14)

The already paid postprocessor then gives

    unscaled selected action: (40+21r)M+(189+19r)A,
    fused recurrence action: (42+21r)M+(189+19r)A.           (15)

The latter totals231+40r, eight per relator below231+48r. The fixed
raw alphabet still has8+2r slots,52+8r selected-source interfaces and
62+10r native lanes. No raw field or lane has been deleted by(13).
Special relators, zero entries or unit coefficients may admit cheaper
schedules; these formulas are uniform upper schedules, not lower bounds.

This is exact fixed-coefficient algebra for P in SL2(Z). It is not an
identity for independent arbitrary assignments to the old matrix
coefficient ports: those coefficients must be the valid recipe(2)--(4).
The reconstructed numerals(8)--(9) likewise must use that same fixed P.
On the supplied integer coordinates, the six boundary polynomials remain
identical after each relator replacement. Native domains and history
soundness do not need to be reproved solely because of this local algebra.

**Open question 1 (complete source composition).** Emit this local
fixed-coefficient recipe in a full sparse compiler, inspect its actual
row/consumer mapping and fixed-numeral roles, and charge the complete
native, packing and finalizer arithmetic. No such successor, source
degree, numerical universal presentation or whole-source bound is
certified by this handwritten note alone.

## 6. Evidence and execution boundary

The frozen paid sparse-action and inverse-pair notes were read inertly.
This proof uses only handwritten integer matrix identities and explicit
instruction ledgers. No supplied, archived, committed, predecessor or
frozen helper is executed/imported; no saved scientific source or
coefficient array is evaluated or degree-propagated. No numerical
sampling or scientific code is used. The companion metadata binds only
the proof bytes and exact dependency read spans. Root handchecked the
proposed integral factorization and uniform central convention. Aristotle
subsequently read the full draft and independently checked all normal,
divisibility, permutation, central/sign, ledger and retained-correction
cases, with no correction requested. All new files are in/tmp; repository
files, Git and earlier frozen artifacts are unchanged. The already
published complete source excludes this proposed per-relator saving.
