# Excluding gap nine by exact residue cutoffs and one wrap test

Every positive zero of the [unchanged86 candidate](complete75_weakened_bound86_candidate.md)
with **R<0 and mu>0** satisfies

    p odd, n<p<=2n-11.

The [gap-seven theorem](complete75_weakened86_gap_seven.md) left
n<p<=2n-9. This note excludes p=2n-9. Exact main-root growth separates
176 finite power-of-two-X cases from82 low-X compiler lanes. A uniform
residue-size induction bounds the index in each low-X lane, leaving39
more finite cases. Exact monotonicity certificates exclude every ratio
window except one. That last window fails a retained wrap congruence.

The [source](complete75_weakened86_gap_nine.py) and
[receipt](complete75_weakened86_gap_nine.json) do not change the candidate's
86=48M+38A gates,19 positive witnesses or exact degree203. Odd gaps at
least11 and mu<0 remain unresolved. No universal86 theorem or complete
false-input zero is claimed; the established75/87 bounds are unchanged.

## 1. Actual complete-source conditions

Assume a complete positive candidate zero with R<0, mu>0 and p=2n-9.
Retain the [index-gap theorem](complete75_weakened86_index_gap.md) and
all the actual compiler hypotheses used in the gap-seven proof:

    B=2^d, d>=4, J>=1, q=(B-1)J+1>=16,
    X=wq^3, Y=sq^3, w,s>=1,
    a=Y(X+1), A=a+2, Delta=A^2-1, H=4a+3,
    P=2XY^2+1, k=2*psi_P(n), c=psi_A(p),
    kY<c<k(Y+1), p odd>=13, n=(p+9)/2.

Here A is the mathematical Pell parameter, not the source's register
holding Delta. The main root and full normalized strong norm remain
unchanged. In particular none of the index or input classifications
below comes from deleting a full strong equation or either ratio.

Write b_p=psi_2(p), M=q^2-1. The inherited scale/growth bounds are

    Y<=U=(2q^2-3)b_p+3p-1,
    U+1<=2q^2*b_p,
    (X+1)^((p-9)/2)<512Y^8(Y+1).                   (1)

The second inequality uses b_p>=p. The third is equation(6) of the
index-gap proof with dgap=9, derived from the actual upper ratio.
The computed main root gives

    X=2^p modulo H, 0<X<H, X<=2^p.                 (2)

For the positive input root, the unchanged literal equations give

    kappa=psi_A(v), mu=chi_A(v), 0<v<p,
    kappa=u+delta*Delta, u=2d*x+b, 0<b<B,
    C=q-F-alpha-2d*x>=0, 0<=C<q,
    W=C-Z=E_A(v)-rho*H,
    E_A(t)=chi_A(t)-(A-2)psi_A(t).                  (3)

F,alpha,x,delta,rho are positive. The fixed compiler input offset b is
not the Pell number b_p. Let K be the unchanged positive packing term
from the preceding proof. The full source supplies

    0<K<q^4, R=K-MZ,
    R+epsilon-lambda=omega*p-j*c,
    epsilon,lambda,omega in{1,-1}, 0<=j<=2q^2-3,    (4)
    j*b_p+2n-omega*p-lambda=0 modulo Y.             (5)

The wrap count j is distinct from the supplied auxiliary coordinate with
the same name. Equation(5) comes from the first-index congruence and
c=b_p modulo Y. Every displayed condition is necessary for the complete
candidate zero, not a claim that an isolated ratio or wrap is sufficient.

## 2. The power branch is finite; the other branch has82 compiler lanes

If X<2^p, (2) implies H<=2^p-X<2^p, hence
Y<2^(p-2)/(X+1). Substitution into(1), using Y+1<2Y, gives

    (X+1)^((p+9)/2)<2^(9p-8).                      (6)

If X+1>=2^18 the left side is at least2^(9p+81), a contradiction.
Thus every putative zero belongs to

    X=2^p; or X+1<2^18.                            (7)

In the first branch q=2^t,4<=t<=floor(p/3), w=2^(p-3t).
Using(1) and b_p<=4^(p-1),

    2^(p(p-9)/2)<2^18*q^18*b_p^9<=2^(24p).

Since p>0 this implies p<57. Consequently all power-branch cases are

    p in{13,15,...,55}, q=2^t,
    4<=t<=floor(p/3), w=2^(p-3t).                  (8)

There are exactly176 triples. This enumeration includes every compiler
representation of a given q because the ensuing ratio test depends only
on q,p,w.

In the other branch X=wq^3<=2^18-2, so q<=63 and B is16 or32. The
actual relation q=(B-1)J+1 leaves precisely the following82 lanes:

| B | J | q | Allowed w |
|---:|---:|---:|---:|
|16|1|16|1 through63|
|16|2|31|1 through8|
|16|3|46|1 through2|
|16|4|61|1|
|32|1|32|1 through7|
|32|2|63|1|

Here X is fixed as wq^3 in each lane. These are the actual compiler
scales; arbitrary small Pell parameters are not substituted for them.

## 3. Every low-X lane has a proved large-index cutoff

Fix one of these lanes. The positive input bound in(3) yields

    u_min=2d+1 <= u <= u_max,
    u_max=2d*floor((q-2)/(2d))+B-1.                 (9)

Every lane has2^u_min>q. Define the following fixed integers for that
lane:

    T=q^4+M*2^u_max+2,
    A0=3X*T+2(2q^2-3)(X^2-1), A1=3X,
    h=floor(log_2(X+1)),
    e(p)=floor((h(p-9)-20)/18).                    (10)

The h notation means the exact bit-length predecessor; no approximate
logarithm is used. In every lane12<=h<=17. Equation(1) and Y+1<2Y imply

    Y^9>(X+1)^((p-9)/2)/1024,
    Y>2^e(p).                                     (11)

The checker records the smallest odd p0>=13 for which

    2^e(p0)>max(A0+A1*p0,p0,u_max).                 (12)

All82 such p0 lie between65 and141. Their existence is also immediate
from the following strict induction, whose starting inequalities are
checked as integers in the receipt. Since2h>=24>18,

    e(p+2)>=e(p)+1.

Also A0+A1*p>2A1 for p>=p0, so doubling A0+A1*p exceeds
A0+A1*(p+2). Doubling p exceeds p+2, and doubling the positive u_max
exceeds itself. Therefore(12) persists for every odd p>=p0. With(11),

    H>Y>max(A0+A1*p,p,u_max).                      (13)

This is an all-index proof, not extrapolation from a bounded replay.

We now show that(13) is impossible at a complete candidate zero.
From(3), v<p<Y<A and u<=u_max<Y<A. The exact discriminant congruence is

    psi_A(v)=v modulo Delta for odd v,
    psi_A(v)=v*A modulo Delta for even v.

Because0<v<A, both displayed representatives are in(0,Delta).
The even representative is at least2A>u, whereas an odd representative
forces v=u. Hence v=u is odd. As E_A(u)=2^u modulo H, equation(3)
implies Z=C-2^u modulo H. Define

    Theta=K-MC+M*2^u+epsilon-lambda.

The bounds(4),(9) give

    0<1-M(q-1)+M*2^u_min-2 <= Theta < T.           (14)

For the first inequality, every lane has2^u_min>q. From(4),
Theta=omega*p-j*c modulo H.

As in the preceding packet, expansion of the actual main norm, whose
root is X+a*c+gamma*H, uses Delta=a^2+H and4a=H-3 to give

    3Xc=2(X^2-1) modulo H.

No inverse of3 is assumed. It follows that H divides

    L=3X*(Theta-omega*p)+2j*(X^2-1).               (15)

But(10),(13),(14) show |L|<A0+A1*p<H, hence L=0. Reducing this equality
modulo X gives X divides2j. In every lane

    0<=2j<=4q^2-6<q^3<=X,

so j=0. Equation(15) then gives Theta=omega*p; positivity makes omega=1.
The original wrap equation(4) implies R>=p-2>0, contradicting R<0.
Thus every low-X zero must have p<p0 in its lane.

## 4. Exact necessary filters leave39 low-X triples

The large-index argument has reduced each low-X lane to finitely many
odd p. Three further exact necessary tests suffice to leave a short list.
First retain X<2^p. Write X=2^ell*o with o odd. Since H is odd,
equation(2) gives

    H divides N=2^(p-ell)-o>0.

Consequently

    N>=4q^3(X+1)+3,                                (16)
    H<2^(p-ell), Y<2^(p-ell-2)/(X+1).

Substituting the latter strict inequality into(1) gives

    (X+1)^((p+9)/2)<2^(9(p-ell)-8).                (17)

The checker enumerates every odd13<=p<p0 in all82 lanes and applies
X<2^p, (16), (17), using integer powers and comparisons only. The entire
surviving list is:

| q | w | X | p0 | Remaining odd p |
|---:|---:|---:|---:|---|
|16|1|4096|79|57 through77 (11 cases)|
|31|1|29791|97|49 through95 (24 cases)|
|31|2|59582|91|83 through89 (4 cases)|

These39 necessary triples are not asserted to have any complete positive
extension. All other low-X lanes or indices fail a proved necessary test.

## 5. Exact monotone ratio certificates and the sole exception

For each of the176 power triples and39 low triples, set n=(p+9)/2 and

    F(Y)=2Y*psi_(1+2XY^2)(n)-psi_(2+(X+1)Y)(p),
    G(Y)=2(Y+1)*psi_(1+2XY^2)(n)-psi_(2+(X+1)Y)(p).

The two strict ratios require F<0<G at Y=sq^3, with
1<=s<=floor(U/q^3). Both polynomials have degree p+8. Their exact
shifted Pell recurrence arrays, for every listed triple, satisfy

    all coefficients below degree p are strictly negative;
    all coefficients at or above p are nonnegative;
    the leading coefficient is positive.                          (18)

Therefore F(Y)/Y^p and G(Y)/Y^p are strictly increasing on Y>0. An
exact binary boundary search finds the last admissible s with F<0.
If it exists and G there is positive, a second boundary search finds
the first s with G>0. Exact endpoint inequalities and(18) prove that
these are the entire ratio intervals; scales between checked endpoints
are not being sampled without justification.

Of all215 domains,214 have no ratio solution. The sole surviving scale
is

    q=16, p=21, n=15, w=512, s=2,
    X=2097152, Y=8192.                             (19)

In particular G at s=1 is nonpositive, both ratios hold at s=2, and
F at s=3 is nonnegative. This is a genuine ratio fixture, not a full
candidate zero, and we do not discard it by an inaccurate strict bound.

For(19), equation(5) uses

    psi_2(21)=296011017105=2961 modulo8192,
    j in{0,...,509}, omega,lambda in{1,-1}.

None of the2,040 integers

    2961*j+30-21*omega-lambda                       (20)

is0 modulo8192. Explicitly2961*5489=1 modulo8192, so the four least
nonnegative solutions for j, in sign order(-1,-1),(-1,1),(1,-1),(1,1),
are1292,4078,2454,5240. Every one exceeds509. The receipt additionally
checks the complete finite range; its least nonzero residue is8.
Thus the last ratio fixture fails a retained
full-source congruence. Gap nine is excluded. Since the preceding theorem
already makes2n-p an odd integer at least9, it is now at least11.

## 6. Literal-source, algebraic and recurrence audits

The source imports the unchanged complete86 hash and full strong/source
checks, including the fourteen actual input rows guarded in the gap-seven
packet. It changes no gate, supplied coordinate, mask or compiler input.
For arbitrary off-zero assignments put

    rmain=(X+ac+gamma*H)^2-Delta*c^2-1,
    Qcorr=Xc-2c^2+4gamma*(X+ac)+2gamma^2*H,
    rwrap=R+epsilon-lambda-omega*p+jc.

The two exact correction identities are

    3Xc-2(X^2-1)=-2*rmain+H*Qcorr,
    3X*rwrap-L=j*(-2*rmain+H*Qcorr)+3X*M*(W-2^u).

The checker verifies640 assignments,320 signed, with M from all six
possible low-q values. It also records430 per-triple coefficient checks
(122 distinct arrays),17,073 exact ratio recurrence evaluations and379
boundary checks against independent Horner evaluation of those arrays.

Another10,578 growth-envelope instances supplement the uniform induction
in Section3. There are4,719 individual Pell roots and391,677 discriminant
classification comparisons over A=128 through160 and u=9 through91.
These are component identities and necessary-domain certificates. None
is advertised as a complete positive Pell extension or false-input zero.

```sh
python3 complete75_weakened86_gap_nine.py
```

Author receipt generation and a fresh default replay pass. All five
local links resolve. Root and another independent reviewer completed
full proof/source reviews and fresh default replays without findings.
Root independently rebuilt all215 domains,430 per-domain coefficient
arrays (122 distinct) and379 boundary evaluations using a closed
Chebyshev-binomial formula and binary Pell oracle. Its separate lane
audit checked all82 cutoffs,2,553 finite-index filters, the176 power and39
low triples, every induction base, the Theta and X>2j bounds, and the four
inverse wrap classes. The other reviewer independently reconstructed all
82 lanes and cutoffs, all122 coefficient arrays and430 sign checks by a
direct polynomial Pell recurrence,579 endpoint inequalities across215
domains, and all2,040 exceptional wrap cases. These remain necessary-domain
and component audits, not constructions of full positive zeros. Larger
odd gaps and the mu<0 branch remain open.
