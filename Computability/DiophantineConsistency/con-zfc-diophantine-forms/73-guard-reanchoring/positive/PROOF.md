# Adaptive carriers and a twice-centered auxiliary norm

Research scratch contribution, pinned to ProveIt
9cca523d9f27ad39d52993f4065cbd7e58f8bdd4. These are new local algebraic
existence reductions. The native compiler/calibration remains inherited;
no new formal ZFC derivation or proof-assistant certificate is claimed.

## Results

- Thirteen strictly positive variables, degree 30, 92 binary operations.
  Source61 has degree34/93.
- Twelve strictly positive variables, degree110, 105 operations.
  Source61 has degree118/104.
- The twelve-variable SOS companion has degree164, 104 operations
  (versus172/103).

The first is a degree and arithmetic-cost improvement at fixed domain and
variable count; the second exchanges one extra operation for eight degrees.
These are incremental, not a fewest-variable breakthrough.

## Exact inherited binding

Use the entire compact source44/source58 tuple with beta=2^590069-1,
K0=K, MC, MF=MF_source already shifted. No port mixing. Source61's
positive/PROOF13.md, PROOF14.md and AUDIT12.md at the pinned commit state
the native compiler and Pell interfaces. The coefficient data is unchanged.

## Thirteen-variable polynomial

Inputs j,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma are all strictly positive.
All other names are polynomial abbreviations:

J=3j+1; q=beta J+1; C=q-F-alpha;
E=XY; k=eta+zeta; c=kY+eta; a=E+Y;
H=4a+3; Delta=a^2+H=(a+2)^2-1;
ell=EkY; b0=X+ac; I=ic^2;
R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J;
r0=k-R-1; U=q^2Y;
Dstar=U b0+H(U gamma+qXY-r0);
W=(q-1)k+1; M0=q^3(q-1);
Bt=(qK0+X)C-qF;
Z=M0(ell+k+r)+(q-1)Y-q^3 W Bt;
Kaux=Delta(f^2-1); V=f^2(cT-R)-c.

The four residuals are
A0=Z^2-M0^2(ell(ell+k)+1),
A1=Dstar^2-U^2(1+Delta c^2),
Aa=(V+u)^2-Kaux*u*(2V+u)-1,
As=f^2-Delta I^2-1.

P13=A0^2+A1^2+Aa^2+As^2.

This changes exactly the main carrier from source61:
q^5 is replaced by q^2Y and q^4X by qXY.

### Soundness

A0=0 is unchanged. Source61's elementary rational-square-root argument
gives q^3|Y, q-1|Bt, C>0, and 3q<R<q^4-2.
Moreover q=2 mod3 and H=3 modq, so gcd(q,H)=1.

Since U=q^2Y>=q^5, the original positivity estimate
Dstar>Uac-Hk>k(UaY-H)>0 remains valid.
A1=0 gives D=Dstar/U a positive integer main Pell root and
U|H(qXY-r0).

Crucially, no assertion gcd(U,H)=1 is made. Since q^5|U and
q^4|qXY, reduction at the q-adic submodulus and gcd(q,H)=1 imply q^4|r0.

The unchanged first and main Pell equations classify
tau=chi_(2XY^2+1)(n), k=2psi_(2XY^2+1)(n),
D=chi_(a+2)(p), c=psi_(a+2)(p).
The n=1 case is impossible; hence c>8XY^3>=8q^9>2R and n<p.
The normalized strong equation and the signed auxiliary-index lemma
recover p=R exactly as in source61, without assuming q|X.

The first Pell recurrence gives k=2n mod4XY^2.
Since q^4|4XY^2, q^4 divides 2n-R-1.
Now 1<=n<p=R<q^4 implies |2n-R-1|<q^4, so 2n=R+1.

Consequently r0=k-2n is a positive multiple of 4XY^2.
The crucial adaptive divisibility is

  4XY^2/U = 4XY/q^2 in Z,

because q^3|Y. Thus U|r0. From U|HqXY we obtain
q^2Y|HqXY and hence q|HX. As gcd(q,H)=1, q|X.
Put w=X/q>0 and h=r0/E>0. The integer

  gamma_old=gamma+w-r0/U

satisfies D=X+ac+H gamma_old. The source61 estimate D>(a+1)c
and c>X gives gamma_old>0.

The original positive transport coordinate is recovered as source61
because q-1|Bt and Bt>0. The strong and auxiliary reconstruction is unchanged.
Thus every new zero lifts to the inherited normalized compiler kernel.

### Completeness

Take source61's canonical compact witnesses. They have X=qw and Y=sq^3;
r0 is a positive multiple of4XY^2 and gamma_old>0.
Set gamma=gamma_old-w+r0/U. It is integral; moreover
r0/U>=4XY/q^2=4wsq^2>w, so gamma>gamma_old>0.
Thus the new carrier does not need the predecessor estimate gamma_old>w.
Then Dstar=U D. Every other input is the source61 reconstructed input,
including its positive transport gap r and squared-modulus auxiliary pair.
Hence the four residuals vanish.

The source compiler/refutation equivalence therefore composes with the
new reduction in both directions, without a consistency assumption.

### Exact degrees

Let q0=3 beta j, k0=eta+zeta, R0=q0^3(q0-F), and
B0=(K0 q0+X)(q0-F-alpha)-q0F.
Exact expansion gives

[A0]_15=-2 q0^8 k0^2 X Y^2 B0,
[A1]_13=8 q0^2 k0 X^2Y^4(q0^2Y gamma+R0).

The other degrees remain13 and14. Thus degree(P13)=30.
Its leading form is 4q0^16 k0^4X^2Y^4B0^2.
The coefficient of j^16 eta^4 X^4Y^4alpha^2 is
4(3 beta)^16>0 independently of K0,MC,MF.

## Twelve-variable polynomial

Use inputs j,F,alpha,i,T,X,Y,r,eta,zeta,n,gamma>0.
Use the same outer definitions and A0,A1, with J=6j+1.
Define

  I=ic^2,
  D=1+Delta I^2,
  M=Delta I,
  d=M^2-1,
  b=cT-R,
  V=Db-c,
  nu=n+I(b+a+2),
  A=M[d(nu^2+D)+1-V^2]-2d nu,
  B=2d(M nu-1),
  N=A^2-B^2D.

The proposed equation is

  P12=(1+A0)(1+A1)(1+N)-1=0.

All exponents are fixed. There is no division or root in this polynomial.
The register nu is not a new witness.

### Product finalizer

J and beta are odd, so q is even. M0 and U are even.
Consequently A0 and A1 are squares modulo4. N is also a square modulo4
because B is even.

If the product of the three integer factors is1, each factor is ±1.
A factor -1 would make the corresponding residual -2=2 mod4, whereas
each residual is a square modulo4. Therefore every factor is+1 and
A0=A1=N=0. The converse is immediate.

### Soundness of the centered norm

All positive inputs give c>=3, Delta>0, M>1, D>c+1, d>0.
The integer nu need not be positive for this argument.
Since M>1, M nu-1 is never0 for an integer nu, so B is nonzero.

At N=0, f=A/B is rational with f^2=D in Z. Hence f is an integer.
Put t=nu-f and y=Mt-1. Exact polynomial identities under f^2=D give

  A-Bf = Md t^2-2dt+M(1-V^2),
  M(A-Bf)=d(Mt-1)^2-M^2V^2+1.

Thus M^2V^2-(M^2-1)y^2=1.

Because b is an integer and V=Db-c, either b<=0 and V<=-c<-1,
or b>=1 and V>=D-c>1. Therefore |V|>1. The auxiliary norm gives
d(y^2-V^2)=V^2-1>0, so |y|>|V| and u=|y|-V>0.

Take the P13 inputs j13=2j, f13=|f| and u13=u.
Every occurrence of f in P13 outside its own square is through f^2;
the normalized strong and auxiliary residuals vanish. A0 and A1 are
the same polynomials. This supplies a positive P13 zero and proves soundness.

### Completeness and the positive centered coordinate

Start with canonical compact source witnesses. The source61 PROOF14.md
interface gives B_native=2^590069 and
J=1+B_native+...+B_native^(N-1), where N=581197^v>1 is odd
after the allowed padding. This J is odd; as B_native=2 mod3 and N is
odd, J=1 mod3. Hence J=1 mod6 and j=(J-1)/6 is a positive integer.
Equivalently the canonical P13 coordinate j13=(J-1)/3 is even.
Thus the restriction j13=2j used by the product finalizer loses no
canonical refutation witnesses. Choose the canonical auxiliary
pair for R=3 mod4:

  V=chi_M(R)/M>0, y=psi_M(R)>V.

The odd-index Pell recurrence gives y=-1 modM^2. Therefore
t=(y+1)/M is a positive integer. Put f>0 for the strong root and define

  nu=f+t,
  n=nu-I(b+a+2).

This is integral. To prove strict positivity, write lambda=(a+2)I
and u=y-V>0. Since D-1=M I and V=Db-c,

  n=f-lambda+(u+b-c+1)/M.

Now M>lambda, M>c, D<M^2, and M>=3.
The inherited outer bound R>3q>=48 gives R>=7.
Pell growth chi_M(R)>=M^R gives V>=M^(R-1)>=M^6.
As D(M lambda+c)<M^2(M^2+M)<2M^4<M^6,
one obtains b=(V+c)/D>M lambda+c.
Consequently (u+b-c+1)/M>lambda and n>f>0.

Substitution of nu=f+(y+1)/M into the two exact norm identities gives A=Bf,
hence N=0. This proves completeness.

This proof uses a fresh canonical auxiliary witness, not a claim that all
old witnesses have y=-1 modulo M^2 or positive centered coordinate.

### Degree certificate and count

Work first in the independent polynomial ring Z[a,c,i,b,n] with weights
(2,2,1,4,1), and set Delta=a^2+4a+3 as above.
The fully expanded norm N has875 monomials, weighted degree82 and leading form

  [N]_82=4a^12 c^20 i^10 b^2.

The degree86 terms in A^2 and B^2D cancel. This cancellation is certified
by complete exact sparse expansion, rather than by a naive DAG upper bound.

After composing a=XY+Y, c=(eta+zeta)Y+eta,
b=cT-R and the same outer definitions, N has exact degree82 and leader
4 i^10 k0^20 X^12Y^32 R0^2.

For q0=6 beta j, the final degree110 leader is

 -64 q0^10 i^10 k0^23 X^15Y^38 B0
     (q0^2Y gamma+R0)R0^2.

Its coefficient at
j^18 i^10 eta^23 X^16Y^39 gamma alpha F^2
is64(6 beta)^18>0.

The literal graph has105 live binary operations:
58 multiplications,29 additions,18 subtractions.
The thirteen-variable graph has92:
51 multiplications,24 additions,17 subtractions.
Fixed numeral leaves and register reuse are free; multiplication by
numerals and each squaring are charged.

## Why the centering helps

Source61 used an auxiliary divisor M=Delta i c^3 and Caux=Delta i c.
The new norm uses the symmetric divisor M=Caux=Delta i c^2.
The polynomial shift I(b+a+2) subtracts both the polynomial part of
the auxiliary quotient and the leading approximation (a+2)I to the
strong square root. A single shift permits two cancellation mechanisms.
The unshifted symmetric norm has larger degree; the cancellation is
essential, not a relabeling of source61's balanced split.

## Limitations

The new arguments certify local existential equivalences.
They do not certify the entire inherited native compiler and refutation
calibration by finite testing, decide consistency, prove a universal minimum,
or lower the current nine-positive / ten-integer variable counts.

