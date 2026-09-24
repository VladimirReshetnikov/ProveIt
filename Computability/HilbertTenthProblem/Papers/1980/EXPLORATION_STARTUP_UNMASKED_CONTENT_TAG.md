# First-zero startup does not replace the tag content guard

Deleting GN from the complete
[91-operation product-coordinate source](EXPLORATION_PRODUCT_COORDINATE_TAG.md)
gives a rejected **86-operation source: 47 multiplications and
39 additions/subtractions, with 29 positive unknowns and 18 equations**.
There are complete positive false halts in both leading-symbol branches,
even with all the existing startup promises: the actual input begins with
zero, its initial deleted prefix has a nonzero symbol beyond the head,
and its genuine computation reads a one. All eight remaining masks,
both transports, true radix geometry, and the compiled numerical bounds
hold. The endpoint is the single zero symbol.

The zero-leading example uses u=0100 and input011000. The one-leading
example uses u=10 and input011. Both genuine computations are explicitly
periodic. Neither example is asserted to be a Neary compiler instance.
This does not improve either the valid91 encoded-instance bound or the
established90 bound for the fixed universal/raw-input construction.

The [checker](../verification/explore_startup_unmasked_content_tag.py)
and [receipt](../verification/explore_startup_unmasked_content_tag.json)
contain both complete symbolic sources and exact outer tuples. Author
and two independent complete proof/source/dependency reviews and fresh
verification PASS, with no findings.

## 1. Exact rejected source

Keep all the positive coordinates, constants, and comparisons of91.
Use its definitions

    K=3^beta, k=K/3, B=3^(a-1), U=3Ut+epsilon,
    cc=(k-1)/2, M1=2Q+S1,
    N=3T+S1 for epsilon=0, N=3T-2Q for epsilon=1.

Supply D and Z=AH as positive coordinates, exactly as in91. Remove only
the field GN=N+jZ. The eight remaining fields, in their existing order,
are

    S0=H-S1, S1, Q, G=Q+Z, M0=L-M1, M1, Ebar=ccH-E, E.

Their packing can be written

    TE=ccH+(q-1)E,
    Rest=L+(q-1)M1+q^2 TE,
    P=H+(q-1)S1+q^2[Q+q(Q+Z)]+q^4 Rest.             (1)

The eight outer comparisons are

    kD=R,
    D(T-E+Ut M1)=N-Ninit,
    D[L+(B-1)M1]=L-Linit+3q,
    RH=H+q-1, RH=CZ, Rv=q,
    2r+1=q^8+2P, r+betaP=q^8.                        (2)

Use the unchanged ten fixed-plus43 kernel equations at scale D0=q^8,
with sixteen strictly positive auxiliaries. The retained norm-source
correction remains at zero-based comparison16 and uses the computed
u=pell_j*pell_c+2r+1.

Removing jZ and its addition to N saves1M+1A. Removing the multiplication
q^2 GN and its addition to TE saves1M+1A. Computing q^8 instead of q^9
saves one further multiplication. Thus91 becomes86=47M+39A. The checker
verifies both complete generic sources, rather than relying only on this
subtraction. Products by constants remain counted even when a particular
example's constant equals zero or one. No coordinate is removed.

## 2. Constructing the unmasked content

Both examples have beta=2, hence K=9,k=3,cc=1. Choose positive powers
of three C,A and put R=CA, b=R/9, D=R/3=3b. For a finite selector
sequence s_i and its exact scalar length markers l_i, define

    S1=sum s_i R^i,
    Q=sum s_i(l_i-1)/2 R^i,
    M1=2Q+S1, L=sum l_i R^i,
    E=sum e_i R^i, e_i in {0,1},
    q=R^h, H=(q-1)/(R-1), Z=AH, v=q/R.

Let offset=S1 in the zero-leading branch and offset=-2Q in the
one-leading branch. Define the supplied content coordinate by

    T=[b(E-Ut M1)+(offset-Ninit)/3]/(b-1),
    N=3T+offset.                                    (3)

The tables below make both divisions exact and T positive. Equation(3)
is precisely the content comparison in(2), since D=3b. The mathematical
division defines a witness; the proposed straight-line source supplies
T as a coordinate and contains no unpaid division instruction.

The prefix bits were found by finite modular subset sum: modulo b-1,
one has R=9. The maintained checker verifies the fixed resulting lists
and exact divisions directly; its result does not depend on a search
cutoff or on finding a tuple again.

## 3. A zero-leading counterexample

Use the rules0->0,1->0100 and input011000. Its genuine computation is

    011000 -> 10000 -> 0000100 -> 001000 -> 10000 -> ... .

Thus it does not halt. Its first deleted prefix is01 and its second
genuine step reads a one. The encoded initial values are
Ninit=12,Linit=729. Take

    C=3^11=177147, A=3^6=729, R=3^17=129140163,
    b=3^15=14348907, h=32.

Choose the selector list

    00 (100)^9 000.

The initial length is6. A zero decreases length by1; a one increases
it by2. The first two steps therefore reach length4; each100 block
returns to length4; the last000 reaches length1. All source lengths
are at least2, so these exact length transitions prove the full length
comparison in(2).

Choose the prefix list

    1,0,1,1,1,1,1,1,0,1,1,1,1,1,1,1,
    0,1,0,0,1,1,0,0,0,0,1,0,0,1,0,1.

Here Ut=1. Modulo b-1=14348906, the exact residues are

    E=9361532, Ut M1=9933849, (S1-Ninit)/3=572317.

The signed sum9361532-9933849+572317 is zero, proving the second
division in(3). The first division is integral because S1 and Ninit
are divisible by3. The final prefix bit is1 while the last selected
row is earlier, so E>M1 and the resulting T is strictly positive
(also checked directly with its exact integer numerator).

All selected rows have length4, so Q has row value40, whose four
low ternary digits are1. Adding A=729 has disjoint ternary support.
Thus G=Q+AH is Boolean, including the unselected rows. All eight
remaining fields are Boolean and strictly below q. The checker also
verifies all positive outer coordinates and all eight comparisons
directly.

The fixed constants satisfy every width and initial-domain condition:

    C>max(K^3,3K*3^a,2KU+3,K^2 Linit), a=4,U=3.

In particular the example does not drop the strict compiled input bound.

## 4. A one-leading counterexample

Use0->0,1->10 and input011. Its genuine computation is

    011 -> 10 -> 10 -> ... .

The same startup promises hold. Here Ninit=12,Linit=27 and Ut=0.
Take

    C=3^8=6561, A=9, R=3^10=59049,
    b=3^8=6561, h=34.

The selector list is0, followed by32 ones, followed by0. The initial
length3 drops to2, remains2 on every selected step, and finally drops
to1. Hence Q=4S1, M1=9S1, and

    L=27+9(R+R^2+...+R^33).

Use the prefix list

    1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,0,
    1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1.

Modulo b-1=6560 its residues are

    E=4, Ut M1=0, (-2Q-Ninit)/3=6556.

Their sum is6560, making(3) integral. Its exact numerator is positive.
The reconstruction here is N=3T-2Q, not the zero-leading formula.
On selected rows Q=4 has ternary digits11 and A=9 has disjoint support;
on unselected rows G has just A. Thus all eight masks pass. The
numerical C thresholds and K^2 Linit<C hold strictly, and every outer
coordinate and source comparison is checked directly.

## 5. The first content row is correct but the next row is false

Both tuples even satisfy0<N<q and N mod R=Ninit=12. Their first
supplied selector is0 and their first prefix bit is1, matching the
actual initial prefix01. Neither example relies on corrupting the
initial content residue. Their first five ordinary base-R residues are

    epsilon0: 12,14348908,73338858,79893323,123668291;
    epsilon1: 12,39367,37179,36936,36909.

The genuine second content is1 in both cases. The unmasked second
residue is instead b+1 or6b+1. No claim of rowwise content validity is
made: equation(3) enforces the whole integer transport, and missing
content bounds permit these spurious carries. The omitted GN=N+jAH
is non-Boolean in both tuples, as verified directly.

## 6. Complete positive Pell extension

For each eight-field packing in(1), define

    D0=q^8, r=P+(D0-1)/2, betaP=D0-r.

The fields are Boolean, the unit trit of S0 is1, and every field lies
below q. The resulting r has native ternary digits1 or2 with unit2.
Its exact central-binomial valuations are4352=8*17*32 and2720=8*10*34.
Both indices are even and satisfy

    D0>=81, r>=27, r<D0, D0<r^2.

These statements are checked by exact integer arithmetic. For parity,
the sum of the eight fields is, modulo2,

    H+Q+(Q+AH)+L+ccH = (A+2)H+L = H+L.

Here A is odd and cc=1. Every length marker is odd, so H and L have
the same parity. Hence P is even. The exponent of D0 is even, making
(D0-1)/2 even too. The fixed-plus43 converse in
[the general-scale kernel proof](EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md)
therefore supplies sixteen fresh strictly positive auxiliaries. It
completes all18 equations in each rejected86 source. The enormous Pell
auxiliary integers are specified by that proved construction rather
than materialized.

Fresh verification covers all36 generic source comparisons, both exact
operation counts, every supplied outer coordinate, all16 individual
mask checks across the two examples, all16 numerical outer comparisons,
the exact startup and nonhalting traces, compiled bounds, quotient
integrality, even indices and full positive-kernel hypotheses. These
are complete false solutions on the current source's startup domain.
They do not establish a false solution on the narrower full Neary
compiler family and make no lower-bound claim about other encodings.
