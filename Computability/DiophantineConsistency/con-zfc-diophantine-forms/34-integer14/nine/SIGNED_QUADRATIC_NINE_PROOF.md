# Nine unknowns: signed quadratic majorants and a zero-margin-safe finalizer

## 1. Result, scope, and credits

Set L=5^32. There is an explicitly specified fixed polynomial with nine
nonnegative integer unknowns, exact total degree

92324 L + 296 = 2149585634469985961914062796,

and a division-free circuit with 1,559 binary operations (692 additions,
22 subtractions, 845 multiplications). An equivalent polynomial over nine
strictly positive integer unknowns has 1,554 operations. Both have 80
nonliteral fixed leaves: the two index integers and 78 distinct nonliteral
coefficient recipes. The 402 original weighted coefficient records remain
the canonical coefficient specification.

These combine package 30's quartic31, package 27's multivariate Horner and
coefficient-recipe folding, and package 28's signed-divisor finalizer.
The new mathematical reductions are the signed quadratic majorants below,
which cause a provable leading cancellation and lower the degree, and
replacing u(2m−1) by um in the finalizer. Sources are pinned at
8c6eec9d19ef80538c8e61ff6e0180040583446a.

The claimed equivalence is a mathematical theorem formalizable in ZFC:
no solution in the stated domain if and only if Con(ZFC). It does not
prove consistency, decide existence, assert global minimality, or provide
a new proof-assistant certificate. It imports the explicit quartic/Pell
compiler interface, the coherent coefficient adapter, K215 calibration,
and the constructive parameterized Jones reduction. The new arithmetic
steps are proved below without assuming any radicand is a square.

## 2. Fixed coefficient instance

The parent is the 31-positive-variable, 22-quadratic system in
quartic31.json. Its sum of squared residuals after replacing each positive
coordinate by n_i+1 is P31(x,n), with unused dummy input x. It has degree
four (coefficient of n_tau^4 is one) and P31(x,0)≥1 (the residual EX+E−aX
is one at the all-ones tuple). The register-elimination proof from package
30 is retained as QUARTIC31_PROOF.md. All four coefficient ports are
replaced together by ../coefficients/payloads/COEFFICIENT_BINDING.json:

beta=2^1064921−1, K=Kconstant, MC, and MF=MF_source.

The fourth is the shifted mask, never the native high mask. The complete coefficient adapter, not individual modular identities, establishes
that this tuple implements the ordinary positive compiler interface.

For each alpha=(alpha_0,...,alpha_31) of weight at most four, set
c_alpha=(4−|alpha|)! product_j alpha_j! times the coefficient of
x^alpha_0 n_1^alpha_1 ... n_31^alpha_31 in P31. Set
expo(alpha)=sum_j alpha_j 5^j. All 402 nonzero symbolic coefficients in the
four ports are listed in INDEX_CONSTANTS.json. The other coefficients
are zero. There are binomial(36,4)=58,905 eligible alpha.

Let s=4,259,933 and z=2^s. INDEX_BOUND.json records a direct finite bound:
if c_alpha=sum_t a_t kappa^e_t and the four port bit lengths are b_j,
then |c_alpha| ≤ sum_t |a_t| 2^(sum_j b_j e_tj), and this last integer
plus one is strictly smaller than 2^s for every record. Here the bit
lengths are (1,064,921; 1,065,043; 1,064,921; 1,064,922). Thus

|c_alpha|+1 < z.

Define e(T)=sum_{|alpha|≤4} (z+c_alpha) T^(L−expo(alpha)),
y=e(2z), and the proof-interface constant u_index=sum_{j=1}^31 (2z)^(5^j).
All exponents are positive integers, since expo(alpha)≤4*5^31<L.
Base-5 uniqueness gives distinct digit positions. Each digit z+c_alpha
lies strictly between one and 2z. Consequently

2(2z)^L ≤ y < (2z)^(L+1).

The left inequality uses c_0=24 P31(0)≥24. These facts are the explicit
Jones index hypotheses. The auxiliary u_index does not occur in the
polynomial. z is materialized as a 532,492-byte little-endian integer;
All 78 distinct nonliteral weighted coefficient leaves are also materialized
as signed-magnitude gzip files: 22,496,535 raw magnitude bytes compress to
2,427,559 bytes. Only y remains an explicit bounded recipe rather than a
materialized integer. The 402 canonical coefficient recipes remain available
for verification and aliases. No uncomputed recursively enumerable index
or unspecified integer is hidden in a coefficient.

## 3. Complete polynomial description

The nine unknowns are epsilon,g0,h0,s0,w0,phi,i0,j0,n in N={0,1,...}.
Set g=g0+1,h=h0+1,s=s0+1,w=w0+1,i=i0+1,j=j0+1, and

b=y+1+epsilon, B=b^5, q=B^L,
ell=sum_{k=1}^31 B^(5^k), lambda=sum_{k=0}^{4L−1}B^k,
N=q^16, Gcap=32 b B^(5^31).

Define the packed polynomial

R=[g+e(B)q^3+ell q^5+
 (2(e(B)−z lambda)(1+B+g)^4+lambda B+lambda B q^4)q^7](N^2−N)
 +[q^3−b ell+ell+(B−2z)lambda q^3+(B−2)q^8](N^2−1).

Continue with

U=N^2 w, Y=N^2 s, M=RY,
P=2M^2 U, K=R+1+h(P−1), A=M(U+1),
B1=2R+1, W1=bw, C=B1+W1+phi,
J=4A−5, Q=3W1 C−2(W1^2−1),
D=(A^2−1)C^2+1, E=i J D C^2,
F=(A^2−1)E^2+1, G=A+F(CD+1−A),
H=B1+jC, I=(G^2−1)H^2+1,
a0=(P^2−1)K^2+1, a1=DFI,
u=JF, v=QF+J(H−C),
m=K^2 Gcap−4(C−KY)^2 Gcap−8gK^2.

Every symbol is a polynomial abbreviation, not an additional unknown.
The letter u here is the signed divisor and is distinct from u_index.
Now put

r=W1+phi, sigma=Y(U+1),
MD=sigma(RC+r^2), TC=CH+r^2,
MF=AE+1,
MI=F(D TC+2H^2+A^2)−A^2+1,
V0=PK+1, V1=MD MF MI+1,
Mdiv=Q^2+(H−C)^2+1,
Omega=u m,
Theta=u(n+Mdiv)+v−Omega(2Mdiv+V0 V1).

The requested polynomial is

F9=(Theta^2−Omega^2(a0+V0^2 a1))^2
       −4 Omega^4 V0^2 a0 a1.

All powers have fixed nonnegative exponents. The JSON circuit expands each
power into binary multiplication gates. Its natural-domain filename is
nine31_signed_quadratic.json. For strictly positive unknowns substitute
each supplied variable by its value minus one; the optimized translated
circuit is nine31_signed_quadratic_positive.json.

## 4. The packed integer cannot vanish

The index gives b≥2. Reduction modulo q gives

R ≡ (b−1)ell (mod q).

Indeed q divides N, and every term of the second bracket except
(1−b)ell is divisible by q. Moreover

0 < (b−1)ell ≤ (B−1)ell
 ≤ (B−1)sum_{k=0}^{L−1}B^k =q−1.

Hence R≠0 for every nonnegative assignment, before imposing F9=0.
Since U,Y≥1, sigma≥2 and A=R sigma imply |A|≥2.
Also P≥2R^2≥2 and
K≥R+P≥2R^2+R≥1. Thus J≠0, D≥1, AJ=A(4A−5)>0,
AE=iAJDC^2≥0, and F≥1. In particular u=JF≠0.

## 5. Signed quadratic majorants

Here r=bw+phi≥2, C=2R+1+r, and H=(j+1)C−r.
The elementary identity

2RC+r^2=4(R+(r+1)/4)^2+r^2−(r+1)^2/4

is strictly positive when r≥2. It follows that RC+r^2>|RC|:
if RC≥0 its excess is r^2, and if RC<0 the excess is 2RC+r^2.
Since the quantities are integers, the excess is at least one. Therefore

MD=sigma(RC+r^2) ≥ |AC|+sigma ≥ |AC|+2 ≥ sqrt(D).

In particular MD≥1. This statement permits either sign of R and C,
and C=0. No assumed sign of m or square condition was used.

Likewise

2CH+r^2=2(j+1)C^2−2rC+r^2≥0

by completing the square (j≥1). Thus TC=CH+r^2≥|CH|.
The coefficient j+1 is why this bound remains valid for negative C and
for H=0. Since AE≥0,

MF=AE+1≥1,   F=(AE)^2−E^2+1≤MF^2.

Using G=FDC+F−A(F−1), integer inequalities |H|≤H^2 and
|AH|≤A^2+H^2 yield

|GH| ≤ FD TC+F H^2+(F−1)(A^2+H^2).

Adding |H|+1 and using |H|≤H^2 proves

MI=FD TC+2F H^2+(F−1)A^2+1 ≥ |GH|+|H|+1.

Consequently MI≥1 and
sqrt(|I|)≤sqrt(G^2H^2+H^2+1)≤|GH|+|H|+1≤MI.
This includes negative I and both zero edge cases. Hence

V0,V1≥2,  sqrt(|a0|)≤V0−1,  sqrt(|a1|)≤V1−1.

For a0 use 1≤a0=(PK)^2−K^2+1≤(PK)^2. For a1 multiply
D≤MD^2, F≤MF^2, |I|≤MI^2. These inequalities are unconditional
on the natural outer domain.

## 6. A zero-margin-safe signed-divisor finalizer

Lemma. Suppose a0,a1,u,v,m,M,V0,V1 are integers with u≠0,
V0,V1≥2, sqrt(|at|)≤Vt−1, M≥1, and |v/u|≤M−1.
For n≥0 set Omega=um and
Theta=u(n+M)+v−Omega(2M+V0V1). Then the polynomial in Section3
has a nonnegative integer n making it zero if and only if a0,a1
are integer squares, u divides v, and m>0.

Proof. If m=0, Omega=0 and Theta/u=n+M+v/u≥n+1>0.
Thus the polynomial is Theta^4≠0. Otherwise Omega≠0. Choose complex
square roots r0^2=a0, r1^2=a1. The polynomial factors exactly as
product_{epsilon,delta in {−1,1}}[Theta−Omega(epsilon r0+delta V0r1)].
A zero allows signs to be absorbed so that s=r0+V0r1=Theta/Omega
is rational. If s≠0 then 2s r0=s^2+a0−V0^2a1 makes both roots
rational and hence integers (their squares are integers). If s=0,
|r1|=|r0|/V0≤(V0−1)/V0<1 forces the integer a1 to have absolute
value below one, so a1=a0=0. This avoids any independence assumption
on quadratic fields and handles negative radicands.

Let Z=2M+V0V1+r0+V0r1. The root bounds give Z≥2M+1>0.
The vanishing factor becomes n+M+v/u=mZ. Its left side is positive,
so m>0. Its right side is integral, so v/u is integral and u divides v.
Conversely choose integer roots and let n=mZ−M−v/u. Then n is an
integer and n≥2M+1−M−|v/u|≥2. Its factor vanishes. QED.

For the Jones application, |v/u|=|Q/J+(H−C)/F|
≤|Q|+|H−C|≤Q^2+(H−C)^2=Mdiv−1. The lemma therefore applies.
The choice Omega=um saves one multiplication and one subtraction relative
to u(2m−1); the extra m=0 case above is essential.

## 7. Equivalence to consistency

For each fixed eight-coordinate outer assignment, the last lemma identifies
existence of n with exactly the inherited four Jones ratio conditions:
a0 and a1 squares, JF dividing QF+J(H−C), and m>0.
The constructive parameterized Jones packing and ratio theorems then
identify existence of all nine coordinates with a zero of P31(1,·).
This uses nu=31, not the separate public existence theorem normalized
at nu=58. The explicit index in Section2 satisfies the former theorem's
hypotheses. The quartic31 algebraic reduction and complete coefficient
adapter identify those zeros with a finite blank K215 halting computation;
the K215 calibration identifies this with a finite ZFC refutation.
All transformations concern finite arithmetic objects and are provable
in ZFC. Negating their existence equivalence gives precisely

ZFC proves: [no N^9 solution to F9=0] iff Con(ZFC).

The positive-domain translated circuit has the same conclusion by the
bijection between N and positive integers. Neither statement is valid
merely by reading the same nine-variable formula over unrestricted Z.

## 8. Exact degree despite a top cancellation

Degree counts the nine unknowns, with fixed coefficients of degree zero.
On the diagonal where every unknown is t, relevant degrees and leaders
are as follows (all leaders are independent of fixed coefficients):

R:235L,1; A:555L+2,1; C:235L,2;
D:1580L+4,4; E:2605L+7,2^6; F:6320L+18,2^12;
G:8135L+22,2^15; H:235L+1,2; I:16740L+46,2^32;
MD:790L+2,2; MF:3160L+9,2^6; MI:8370L+23,2^16;
V0:1900L+7,4; V1:12320L+34,2^23;
Omega:9096L+31,−2^23; Theta:23316L+72,2^48.

The naive top terms in Theta^2−Omega^2 V0^2 a1 cancel exactly.
To prove the true degree, use the following polynomial identities:

DeltaD=MD^2−D=2AC sigma r^2+sigma^2 r^4+C^2−1;
DeltaF=MF^2−F=E^2+2AE;
DeltaIRoot=MI−GH=FD r^2+2FH^2+(F−1)A^2+1−FH+A(F−1)H;
DeltaI=MI^2−I=DeltaIRoot(MI+GH)+H^2−1;
Delta=V1^2−a1=DeltaD MF^2 MI^2+D DeltaF MI^2+DF DeltaI+2MD MF MI+1.

The leading term of DeltaD has degree1110L+8 and coefficient4.
The first summand in Delta therefore strictly dominates, giving
Delta degree24170L+72 and coefficient2^46. Let
E0=u(n+Mdiv)+v−2Omega Mdiv. Then the exact rewritten inner expression is

E0^2−2E0 Omega V0 V1+Omega^2 V0^2 Delta−Omega^2 a0.

Its unique leading summand has degree46162L+148 and coefficient2^96.
After squaring, the final subtractand 4Omega^4 V0^2 a0 a1 has smaller
degree. Thus the exact degree is92324L+296 and uniform leading coefficient
2^192≠0. This also proves exact total degree: these formulas give matching
multivariate upper bounds and nonzero diagonal leading terms.
The same degree and leader survive shifts to the strictly positive domain.

## 9. Circuit identities and accounting

Set t_j=B^(5^j), v_j=B^(5^31−5^j), with v_31=1 and
v_j=t_j^4 v_{j+1}. With weights w=(t_31,v_0,...,v_31),

e(B)=t_31[z h4(w)+sum_alpha c_alpha t_31^(4−|alpha|) product_j v_j^alpha_j].

The complete homogeneous polynomial h4 is evaluated by the ascending
recurrence h_k←h_k+w h_{k−1}, k=1,...,4. The correction is evaluated
by recursive multivariate Horner, selecting a variable and splitting each
term into one divisible by that variable and one not. Every step is exact
distributivity. The deterministic heuristic chooses maximum incidence,
then exponent mass, then a fixed permuted tie-break. A finite search of
100 such heuristics selected8; no optimality is claimed.

Lambda is evaluated without division as
product_{j=0}^31[1+t_j(1+t_j)(1+t_j^2)](1+q)(1+q^2).
Identical coefficient recipes become one leaf and literal recipes become
literal integers. Each of the402 alias identities is checked exactly as
an identity in the four ports, not numerically guessed. Shared gates and
literal constant folding are allowed; every binary addition, subtraction,
or multiplication, including scaling by a numeral, is charged. Registers,
references, and fixed integer leaves are free. Coefficient height is a
separate metric, and the bitlength of y is not hidden in a gate count.

## 10. Reproducible checks and limitations

build_signed_nine.py regenerates the four supplied structured/new circuits.
check_degree.py checks cancellation-free exact leaders.
check_signed_nine.py compares inherited core named quantities and exact
rewrite identities modulo three primes, verifies all402 coefficient alias
identities, checks three full58,905-term digit sums,6,144 bound assignments
including negativeR,C=0,H=0,86,016 bounded finalizer assignments, and468
explicit finalizer completeness witnesses. These are implementation
regressions, not proofs that the final Diophantine equation has no solution.
check_actual_index.py reads the authentic four coefficient files, verifies
hashes/bitlengths, evaluates every coefficient bound on actual integers,
and checks all 78 stored signed-magnitude coefficient payloads against their
exact recipes, then records actual-instance modular outputs.
materialize_fixed_leaves.py constructs those payloads. bind_index.py constructs the
finite bound and materialized z. All programs are newly authored or carried
forward from our preceding independently authored audit, not executed
copies of received upstream programs.
