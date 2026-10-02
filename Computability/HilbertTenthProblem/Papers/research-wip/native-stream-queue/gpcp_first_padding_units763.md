# Two first-padding signs give a 763-operation complete U15,2 compiler

The [literal source](gpcp_first_padding_units763.py) reduces the reviewed
[765-operation upper-transport compiler](gpcp_upper_transport_unit765.md) to
**763=352M+411A**, with719 certificate operations,15 comparisons,125 positive
witnesses, three fixed positive program parameters and ordinary positive input.
Its exact formal-polynomial degree is232964. The supplied-initial interface
costs766 operations with126 witnesses and exact degree9624. The
[receipt](gpcp_first_padding_units763.json) records all eight schedules.

The selected765 parent and this source have the **same full supplied positive
zero set for every positive program parameter**, with all supplied coordinates
unchanged. Two first-padding signs and both native checksum signs are forced
positive together, before any history typing. Existing global and native-bound
signs may remain negative. No off-zero polynomial identity is asserted.
The separate75-certificate/87-polynomial universal bound is unchanged.

## 1. Fold a constant into each first padding row

In each of the recoder and history AND cores, the parent has the paid comparison

    input_A=F1+F3=16H+12=padded_A.                    (1)

The actual padded_A row has no source consumer and is exported only through
this comparison. Change its constant from12 to13, append

    Aunit=padded_A_new−input_A=16H+13−F1−F3,          (2)

multiply Aunit into the complete product, and delete comparison(1). The new
constant costs the same single addition as the old one. Each conversion adds
one subtraction and one multiplication and deletes three finalizer gates,
so it saves one addition. The two conversions save exactly two additions.
All numerical multiplications, including multiplication by16, remain charged.

The active first-padding interfaces record the new constant13 and its relation
to the parent's constant12. Every old register except the two padded_A values
has precisely its old value on every integer input. Historical parent and
history records remain provenance; the current source and interface describe
both changes explicitly. Full canonical-parent guards check the private rows,
the retained second paddings, checksum factors and actual computed F3 rows.

|Enabled bound pairs|Computed operations|Comparisons|Exact degree|Supplied operations|Comparisons|Exact degree|
|---|---:|---:|---:|---:|---:|---:|
|none|767|19|214407|770|20|8812|
|geometry only|765|17|214473|768|18|8878|
|AND only|765|17|232898|768|18|9558|
|both, default|763|15|232964|766|16|9624|

Computed sources use352 multiplications and125 witnesses; supplied sources
use353 multiplications and126 witnesses. Default certificates have337M+382A
=719 operations. The unchanged fixed U15,2 machine,57 literal tiles, program
frame, ordinary-input recoder and padding convention are inherited from765.

## 2. Establish strict local bounds before choosing either sign

At a zero of the complete anchored finalizer, every remaining ordinary residual
vanishes and each factor in its complete product is an integer unit. All12
native norm factors are+1 by the separate modulo4 arguments in
[the checksum proof, Section2](gpcp_checksum_global_units771.md#2-positive-native-quantities-before-any-checksum-or-global-sign).
This needs neither a padding sign nor a checksum sign. In a fixed AND core write

    C=q−(F0+F1+F2+F3)=epsilon, Aunit=sigma,
    epsilon,sigma in{+1,−1}.                         (3)

The supplied F0,F1,F2 are positive. The actual computed F3 is positive and
at least8 before any binary interpretation: it is16*Ahat−8 in the recoder
and16*Z+8 in the history, whose decoded-selector expression gives Z>=0.
The positive scalar cones and both positive-multiple-of16 scales q are the
same as in771 and765. They do not depend on either changed padded_A value.

The retained second padding gives F2=2 modulo16, and the computed F3 gives
F3=8 modulo16. Equation(2) gives F1=5−sigma modulo16. Since q=0 modulo16,
(3) then gives exactly these low residues:

|epsilon|sigma|(F0,F1,F2,F3) modulo16|Low sum|Low population|
|---:|---:|---|---:|---:|
|+1|+1|(1,4,2,8)|15|4|
|−1|+1|(3,4,2,8)|17|5|
|+1|−1|(15,6,2,8)|31|8|
|−1|−1|(1,6,2,8)|17|5|

In every case the packed index

    r=F0+q*F1+q²*F2+q³*F3

is odd and nonzero modulo16, with r>q and r>=9. Meanwhile X=wq is divisible
by16. If its native bound is still an ordinary comparison it gives X>r.
If enabled as a unit H_X, then positive beta and H_X=±1 give

    X−r=beta+H_X>=0.

The residues exclude equality, hence **X>r** in all four sign cases.
This residue argument needs only X−r>=1; no earlier13/15 margin is used
at this stage. The complete source also has X divisible by q, which can
strengthen the gap. Existing global, bound and upper-transport signs remain free.

## 3. Recover the raw population equation independently of both signs

The exact first-index and auxiliary-linear comparisons, positive ratio slacks
and complete normalized strong factors have not changed. The local argument
in [771 Section3](gpcp_checksum_global_units771.md#3-exact-local-indices-and-population-without-a-checksum)
requires only positive fields, r>q, r>=9, X>r and
Y=q*(2*odd_half+1)>=3q; it does not use the exact first padding or field
upper bounds. Here are its relevant strict inequalities with the weaker gap1.

Put E=XY, P0=2XY²+1, a=Y(X+1), A=a+2 and Delta=A²−1.
Then E>2r+1, a>2r+1 and P0>A. The first norm and exact comparison give
n=r+1 modulo E, so n>=r+1. The main norm and ratio give p>n and

    c>A*Delta², c>2p, c>Yk>2(2r+1).                 (4)

The full normalized strong equation gives pc dividing its index m and the
strict window f>2chi_A(2p)>2c. The exact auxiliary-linear comparison now
has the same positive value V=of−c=jc−(2r+1)>0. Strict step-down at the
auxiliary norm gives p=2r+1, then n=r+1 exactly. None of these comparisons
mentions padded_A, C, Aunit, a history transport or a global bound sign.

The raw scalar ratio and root-congruence proof then gives

    X=2^(2r+1),
    Y=binom(2r,r)+sum_(j=1..r)binom(2r,r+j)*X^j.

Since q divides X, q=2^t. Since r>q, 2q divides X. The retained odd quotient
Y/q forces t=popcount(r). This obtains

    q=2^popcount(r)                                  (5)

without assuming field disjointness, either checksum sign or either new
padding sign. The proof is the scalar kernel, not its wrapper with a separate
geometry lower-bound interface. The geometry core itself is untouched.

## 4. The three unwanted sign pairs contradict population

From(3), sum F_i=q−epsilon. Since all four fields are strictly positive,
every field is strictly below q in both checksum cases. Now(5) makes q dyadic,
so the four base-q blocks in r are disjoint and

    popcount(r)=sum_i popcount(F_i).                  (6)

Write q=16Q and F_i=16a_i+l_i with the low residues in the table. Each a_i
is nonnegative. Population subadditivity gives

    sum_i popcount(a_i)>=popcount(sum_i a_i).         (7)

For epsilon=−1, in either padding-sign case, sum a_i=Q−1 and the low
population is5. Since Q=2^(t−4), (6)–(7) imply

    popcount(r)>=popcount(Q−1)+5=t+1,

contrary to(5). For epsilon=+1,sigma=−1, sum a_i=Q−2 and the low population
is8. Q=1 is impossible because the high sum would be negative. For Q>=2,

    popcount(r)>=popcount(Q−2)+8=t+3,

again contradicting(5). Thus independently in each AND core,

    C=+1 and Aunit=+1.                               (8)

The argument does not need the product of old factors to have been+1 before
this conclusion. In particular it permits all sign patterns of the inherited
G and native H factors that the parent permits.

Now both deleted comparisons(1) are restored, and the two new factors are1.
Removing them from the new complete product restores the complete old product
as1. Every old ordinary comparison and every other old register is unchanged.
This is exactly a positive zero of the selected765 parent on the same supplied
tuple. Conversely, a positive parent zero has both equations(1), so the changed
padded_A values make both new factors1 and satisfy the new complete finalizer.
This proves full same-coordinate positive-zero equality for all positive program
parameters, before restricting to the parent's universal program slices.

The same population argument does **not** justify changing the second padding
as well. At q=64, the scalar fields(1,20,36,8) have sum65, packed population6,
F1+F3=16*1+12 and F2+F3=16*2+12. A shifted second-padding unit could be−1
alongside a negative checksum without a population contradiction. This is a
component obstruction to that proposed proof, not a complete compiled Pell zero
and not an impossibility result for another second-padding method.

## 5. Complete output correction and exact formal degree

Let W be the old complete product, A1,A2 the new factors, S the sum of the
remaining ordinary residual squares, and R=(A1−1)²+(A2−1)². On arbitrary
integer inputs the full outputs are

    F_old=W*(1+S+R)−1,
    F_new=W*A1*A2*(1+S)−1,
    F_new−F_old=W*((A1*A2−1)*(1+S)−R).               (9)

The source checker executes both full circuits and every old register, checking
the two changed registers differ by exactly1 and all others agree. Equation(9)
is an explicit correction, not an identity between the two outputs.

Every old propagated degree entry is unchanged by changing a constant.
The recoder A1 has strict highest term16*copies, degree2, while its input_A
has degree1. The history A2 has the strict highest term16*leading(joined_H).
Its reserved top region has leader16*B_h*P_h^67; this has degree4555 for
the computed-initial interface or135 for the supplied interface. The competing
input_A has degree4423 or133, respectively. These strict leaders are nonzero;
the modular leading-form certificates evaluate each new factor and the complete
output at two primes, retaining the guarded three main-norm cancellations.

The retained history first-index residual still has degree18292 or547, strictly
larger than either removed first-padding residual. Its nonzero highest form
makes the top degree of the surviving real sum of squares unchanged. The old
unit product has its previously proved nonzero highest form. Therefore the
complete polynomial has **exact** degree increased by2+4555=4557, or by
2+135=137, giving232964 or9624 in the default forms. These are formal total
degrees including the program parameters before specialization. A fixed program
can lower them. No zero-set relation is substituted into a formal degree.

## 6. Canonical checks and finite evidence

The APIs support exactly both initial interfaces and the two paired-bound
switches of765. Strict Boolean validation precedes caching. The rewrite accepts
only the full canonical parent; finalizer, degree and ledger APIs require the
full current canonical packet. Every emitted gate reaches the full output and
all original positive domains are retained. Returned packets have isolated copies.

Author writer90410 passed192 complete register/output corrections(96 signed),
including32 zero-selector contexts, all eight literal ledgers and16 nonzero
leading certificates. The independent component routine checks6218 four-field
cases, including4617 unwanted-sign population contradictions,11021 positive
signed-bound cases and the impossible smallest-scale corner. It rejects145
malformed callers. These are finite algebraic and component fixtures; no full
compiled Pell witness is claimed. The general sign and zero-set theorems are
proved above. Author fresh52409 also passed. Native full proof/source review found one prose precision issue: a relaxed
modulo16 cone allows gap1, while the complete source also requires X to be
a multiple of q. The note and test comment now distinguish those scopes;
no circuit, receipt or proof conclusion changed. Its independent final-source
checker passed160 full register/output corrections(80 signed), all eight
ledgers,16 exact leading certificates,192 malformed callers and cache
isolation checks. Its separate mathematical audit covers208026 exhaustive
field cases,3744 raw bootstrap cones,1040 strict-gap residue cones and96
large population-bound fixtures. Root reran that final-source checker in
session18464 successfully. All five local proof links resolve.
