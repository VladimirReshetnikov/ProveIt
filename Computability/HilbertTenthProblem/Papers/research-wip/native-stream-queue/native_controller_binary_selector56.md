# Four exact binary selectors in 56 operations

The retained fixed-minus binary Pell kernel can certify **four one-hot
binary streams in56=29M+27A**. The new ingredient is an odd quotient: it
forces an exact binary population count, which a checksum turns into a
partition. A single paid bound on the Pell base permits four packed fields
at scale q; no large scale q^4 is needed.

This is a complete typing component, with14 equations and19 positive
auxiliary coordinates apart from its five positive parameters q,F0,F1,F2,F3.
Its exact projection is:

- q=2^t;
- F0,F1,F2,F3 are strictly positive length-t Boolean binary words;
- at every bit position exactly one field has bit1;
- the units bit of F0 is1.

In particular t>=4: all four labels must occur. Zero fields are not allowed
by this interface. No universal controller, input bridge, wiring geometry,
or acceptance condition is included. The complete universal bound remains76.

## 1. Source and paid schedule

Take the unchanged43-operation fixed-minus core of the
[complete78 source](../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md), with scale
alias n2=q. Its17 positive coordinates are

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y_aux.

Here h is the first Pell-index quotient, not a controller offset. Also
supply positive odd_half and bound_beta. Define

    X=wq, Y=sq, E=XY, Delta=a^2+4a+3,
    J=2r+1, U=jc-J.

The unchanged ten kernel equations are

    (E^2+X)*(Yk)^2=tau*(tau+1),
    c=Yk+eta, k=eta+zeta, k=r+1+hE,
    a=Y*(X+1), d=X+ac+ga*(4a+3),
    d^2=1+Delta*c^2,
    (i*c^2)^2=Delta*(f^2-1),
    (i*c^2)^2*(U^2-y_aux^2)=1-y_aux^2,
    U=of-c.                                             (1)

The four outer equations are

    r=F0+qF1+q^2F2+q^3F3,
    F0+F1+F2+F3+1=q,
    s=2*odd_half+1,
    r+bound_beta=X.                                     (2)

Horner packing uses3M+3A. The checksum uses4A and exposes its intermediate
Q=F0+F1+F2+F3=q-1. The odd quotient uses1M+1A. The last bound uses1A;
X is already computed by the core. Hence

    43+(3M+3A)+4A+(1M+1A)+1A = 56 = 29M+27A.

The [literal checker](native_controller_binary_selector56.py) audits all
14 independent residuals against the acyclic source, including the standard
auxiliary-norm substitution correction. The scale alias is register reuse,
not an uncharged power computation.

## 2. Preliminary inequalities before power or digit recovery

Positivity and the checksum give q>=5 and 0<Fi<q. Thus, without assuming
that q is a power or that the fields are disjoint,

    q^3+q^2+q+1 <= r < q^4, r>=156,
    X>r, Y>=q>=5, E>r+1,
    a=Y*(X+1)>2r+1.                                    (3)

The first Pell parameter P=2XY^2+1 exceeds the main parameter A=a+2.
Classifying the first norm in(1) yields k=psi_P(n). Reduction modulo E
and k=r+1+hE give n=r+1 modulo E, so n>=r+1. The positive interval
Yk<c<(Y+1)k and P>A imply that the main index p>=r+2>=158.
Consequently

    c=psi_A(p)>A^(p-1)>A*(A^2-1)^2,
    c>Yk>Y(r+1)>J, c>2p.                               (4)

These are stronger than the hypotheses of the retained relaxed auxiliary
rank and half-parameter arguments. They give

    p=J=2r+1, c=psi_A(J), d=chi_A(J),
    f=chi_A(m), c divides m, m>=c>2p,
    R=i*c^2=Delta*psi_A(m)>1.                            (5)

No field decoding or parity assumption has been used. Also n=r+1 exactly:
any larger n congruent to r+1 modulo E would exceed2r+1=p; P>A and c>k
then give a contradiction.

The generic signed-parity theorem in Section4 of the
[fixed-minus parity proof](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md)
now applies to the minus signs in(1). In particular U=jc-J>0, c>2p,
m>=c>2p, and f>2c by Pell growth. It proves **r odd** for every positive
solution, including noncanonical auxiliary indices.

## 3. Lower ratio first, then the direct binary exponent

Put xi=(X+1)^(2r)/X^r. Elementary Pell bounds give

    c/k > xi*(1+3/(2a))^(2r)*(1+1/(2XY^2))^(-r) > xi.   (6)

For the last inequality,6XY^2>a is already immediate from a=Y(X+1)
and X,Y>=5. This lower estimate requires no preliminary small upper-error
bound. Since c/k<Y+1 and xi>X^r, with Y and X^r integers, it follows that

    Y>=X^r, a>X^(r+1).                                  (7)

Now6r/a<6r/(r+1)^(r+1)<1/2. The usual upper estimate, even using the
larger constants from the ternary proof, gives

    c/k < xi*(1+12r/a),
    0<c/k-xi<24r/(X+1).                                 (8)

The direct Pell recurrence gives

    chi_(a+2)(J)-a*psi_(a+2)(J) = 2^J modulo4a+3.

Indeed both sequences satisfy the main recurrence and agree at indices0,1
modulo4a+3, since2 is a root of its characteristic polynomial modulo that
number. Comparing with the source exponent equation yields X=2^J modulo
4a+3. Both representatives are positive and below that modulus: X<a and

    2^J=2*4^r < X^(r+1) < a                             (9)

because X>r>=156. Therefore X=2^(2r+1). Since q divides X and q>=5,
we recover q=2^t for t>=3.

After this recovery, the error in(8) is below1/2. In the binomial expansion
of xi the fractional part is

    sum_{j=1}^r binom(2r,r-j)*X^(-j) < 4^r/(2X)=1/4.

The positive unit interval Y<c/k<Y+1 together with(6)–(8) therefore forces

    Y=floor(xi)
     =binom(2r,r)+sum_{j=1}^r binom(2r,r+j)*X^j.         (10)

The integer sum in(10) has no factor2. Its coefficients are the upper
half of a single binomial expansion.

## 4. Exact population count and one-hot decoding

Since t<q<r<2r+1, the recovered X=2^(2r+1) is divisible by2q. Equation(10)
then implies that q divides the central binomial coefficient and

    (binom(2r,r)/q) = (Y/q)=s modulo2.

The paid equation s=2*odd_half+1 makes this quotient odd. Thus

    v2 binom(2r,r)=t.

The elementary factorial-valuation identity

    v2 binom(2r,r)=popcount(r)

gives popcount(r)=t. The already proved bounds0<Fi<q imply that Horner
packing has no base-q field carries, so

    sum_i popcount(Fi)=popcount(r)=t
                     =popcount(q-1)=popcount(sum_i Fi). (11)

Adding binary words decreases the total number of set bits by exactly
one for each elementary carry. Equality in(11) therefore excludes every
carry. Their sum is the all-ones length-t word, so exactly one field is1
at every position. Finally q is even and r is odd, hence F0 is odd.
All four fields are positive, so each label occurs and t>=4.

This establishes the full forward projection. In particular the exact
valuation is essential: divisibility alone would permit extra populations
and overlapping fields.

## 5. Strictly positive converse

Conversely, take any four positive binary words partitioning the length-t
repunit, with F0 odd. Set q=2^t and pack r as in(2). Then t>=4, r is odd,
q<r<q^4, and popcount(r)=t. Set

    X=2^(2r+1), Y=floor((X+1)^(2r)/X^r),
    w=X/q, s=Y/q,
    bound_beta=X-r, odd_half=(s-1)/2.                   (12)

The exact valuation and(10) show that s is an odd positive integer.
Moreover Y>=X^r makes s>1, so odd_half is strictly positive. The other
new coordinate bound_beta is strictly positive by construction.

Use the retained positive odd-index kernel map at this actual r and
scale q. Explicitly set a=Y(X+1), P=2XY^2+1, A=a+2,
k=psi_P(r+1), c=psi_A(2r+1), d=chi_A(2r+1), and use the retained
positive auxiliary construction for the fixed-minus branch. The first
index quotient is positive and integral; the ratio interval makes
eta=c-Yk and zeta=k-eta positive; the direct exponent congruence supplies
the positive integral ga. The standard auxiliary construction supplies
positive f,i,j,o,y_aux, including its norm and both minus congruences.
These are precisely the retained17 coordinates, not inherited numerical
values from a different packed index.

The lower and upper bounds in Sections2–3 verify the rank, exponent,
rounding and ratio hypotheses needed by that map. Therefore all fourteen
equations hold with strictly positive supplied coordinates. This proves
the converse, rather than only a sound typing test.

## 6. Gate interface and evidence boundary

One possible interpretation is to let labels0,1,2,3 stand respectively for
input pairs00,10,01,11. Then

    input_A=F1+F3, input_B=F2+F3,
    output_D=F0+F1+F2

are exact native binary NAND streams. The output is already the computed
checksum prefix bs_sum012, so the two input additions give a **58-operation
typing-and-NAND component**. This charges no wiring or rotations because
none are claimed. The compulsory first label makes both input units bits0
and the output units bit1; all four gate cases must occur somewhere.

The [receipt](native_controller_binary_selector56.json) records all14
symbolic source checks,23,751 pre-power field tuples, the complete positive
checksum scan through q=64, and2,556 positive one-hot partitions through
t=7. It also computes actual central binomial valuations for three packed
indices, including r=532611, and verifies their odd quotients. It does not
materialize the vastly larger full Pell tuples; their existence is the
positive-map argument above. Run the checker without `--write` for a fresh
comparison. Independent full proof, source, and default-replay review passed.
