# A margin-separated nine-variable equation

## Result and exact scope

This package constructs a polynomial with ordinary, fully specified integer
coefficients in nine strictly positive unknowns; a separately translated
polynomial uses nine nonnegative unknowns. Its lack of zeros in the stated
domain is provably equivalent in ZFC to Con(ZFC). This is not an assertion about
unrestricted integer zeros, a proof of consistency, a minimum claim, or a new
end-to-end proof-assistant certificate.

The imported semantic premises are the common 31-positive-variable quadratic
compiler system and its coherent four-port tuple, together with the numerical
Jones ratio theorems `Jones1982.Nine.ratio_sound` and `ratio_complete` from
`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean`.
The source-system SHA256 is
ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48.
The tuple is exactly `wang943-complement67-shared-anchor-length8807-prime581197`
at repository pin 124c07c0b77a9e20e84676514d8b1ff78536ea3f, supplied as a whole
in `../coefficients/COEFFICIENT_BINDING.json`. No ports from the older tuple are
mixed in. The inherited compiler and calibration dependencies remain explicit.

All register names below denote polynomials, not additional quantified unknowns.
The exact circuits and coefficient payloads are authoritative machine-readable
representations. The companion packing certificates specify the source weights,
row offsets and every integer-coefficient recipe.

## 1. Quadratic radix with a fixed coefficient

Let the shifted source rows be p_j(z), j=1,...,22, of degree at most two in
31 nonnegative coordinates. For a monomial alpha, put
c_(j,alpha)=(2-|alpha|)! (product alpha_i!) p_(j,alpha).
The independently checked sparse packing certificate specifies nonnegative integer
weights w_i, a distinct padding position p with 0<=p<=W=max w_i,
row targets h_j, and nonnegative exponents
h_j-(2-|alpha|)p-alpha.w. The principal interior variants use p=81 and W=174.
It verifies that coefficient extraction against
C_z(T)=(T^p+sum_i z_i T^w_i)^2 gives

  coefficient at h_j of C_z(T) Dcode(T) = 2p_j(z),
  Dcode(T)=sum_(j,alpha) c_(j,alpha) T^[h_j-(2-|alpha|)p-alpha.w].

This finite active-support isolation condition replaces full B2 isolation.
The encoding exponents are distinct, and their largest exponent Dmax has
coefficient 2. Put Kcode=Dmax+2W. The certificates also have
max_j h_j<Kcode; targets and encoding positions are different quantities. These conditions are checked for each delivered certificate.

The coherent tuple has port bit lengths (590069,592884,590069,590070).
Direct evaluation and an independent symbolic coefficient-recipe bound establish
|c_(j,alpha)|<M=2^1182955. Put the fixed ordinary integer
lambda=4096M=2^1182967. Initially b,g,h,s,w,i>=1 and phi,j,n>=0 are the nine
coordinates. Define

  B=lambda b^2,
  ell=sum_i B^w_i,
  N0=B^(W+1), N1=4B^(Kcode+1), N=N0 N1,
  Mask=N0-1-(b-1)ell,
  Targets=sum_j B^h_j,
  Tcode=Mask+(B-2)Targets N0,
  Jcode=2(B^p+g)^2 Dcode(B)+B sum_(k=0)^Kcode B^k,
  Scode=g+Jcode N0,
  R=(N-1)[(Scode+Tcode+1)N+Tcode+1],
  Gcap=32b B^W.

There is no enormous additive floor in b. The scale lambda is a coefficient,
not a variable. Since lambda is a fixed power of two, b a power of two implies
B a power of two, exactly as the later carry proof needs.

For all positive b, B-1>M and the leading coefficient 2 dominates the signed
lower coefficients of Dcode. In particular

  Dcode(B)>B^Dmax>0,
  Dcode(B)<M B^(Dmax+1)/(B-1).

Also Mask>0, so all source registers needed by the ratio theorem are positive,
R>=N>=8, and b<=N<=R. These bounds do not assume a final polynomial zero.

On the bounded branch g<4b B^W, the interior padding requires the bound
B^p+g<(4b+1)B^W<=5bB^W, not the old zero-padding estimate. Hence

  2(B^p+g)^2 Dcode(B)
    <50M b^2 B^(Kcode+1)/(B-1)
    <=B^(Kcode+2)/(64(B-1)).

The geometric summand is less than 2B^(Kcode+1), proving 0<Jcode<N1.
Since 4b<B, g<N0; also 0<=Tcode<N. Thus 0<=Scode,Tcode<N.

## 2. The source carry equivalence

When b is a power of two, so are B,N0,N1,N. For 0<=S,T<N=2^r,

  (N-1)[(S+T+1)N+T+1]
   =(S+T)N^2+(N-1-S)N+(N-1-T).

Legendre's factorial formula and binary digit sums imply
N^2 divides binomial(2R,R) exactly when adding Scode and Tcode causes no
binary carries. This in turn splits into the two low/high-block carry tests.
The low one says exactly

  g=sum_i z_i B^w_i, with 0<=z_i<b.

For such g, every coefficient of C_z Dcode has absolute value less than
M(1+sum_i z_i)^2 <= M(32b)^2=B/4. Consequently

  Jcode=2 sum_(k=0)^Kcode a_k B^k,
  a_k=coefficient_k(C_z Dcode)+B/2, 0<a_k<B.

The high carry mask is (B-2)Targets. Divide both operands by 2, a common
binary shift: at every target cell the mask is B/2-1, and carry-freeness forces
a_(h_j)=B/2, equivalently p_j(z)=0. The nontarget cells impose no conditions. The low digit mask allows exactly
the variable positions w_i and excludes the distinct padding position p; thus
the coefficient of T^p in the encoded linear form is fixed at 1.
Thus b power of two, g<4bB^W and the binomial divisibility imply a source zero.

Conversely, from a source zero choose an arbitrarily large power-of-two b
with b>max_i z_i and set g=sum_i z_iB^w_i. The source has no all-zero shifted
solution (the original fifth row has constant 1), so g>0. Both carry tests
hold, and g<bB^W, hence 32g<Gcap. This is the stronger completeness bound
needed by the ratio theorem.

## 3. Eliminate the F-divisibility by a polynomial reparameterization

Define the usual ratio registers, except for the explicitly changed H:

  U=N^2w, Y=N^2s, M0=RY,
  P=2M0^2U, K=R+1+h(P-1),
  A=M0(U+1), B1=2R+1, W1=bw,
  C=B1+W1+phi, J=4A-5,
  Q=3W1 C-2(W1^2-1),
  D=(A^2-1)C^2+1,
  k=iJC, L=kD, E=LC,
  F=(A^2-1)E^2+1,
  G=A+F(CD+1-A),
  H=C+F(B1+jC),
  I=(G^2-1)H^2+1,
  a0=(P^2-1)K^2+1, a1=DFI,
  m=[K^2-4(C-KY)^2]Gcap-8gK^2.

The original ratio theorem instead uses H_old=B1+j_old C, j_old>0, and
requires JF | QF+J(H_old-C). Since E is divisible by both J and C,
F=1 modulo J and modulo C. The old divisibility is therefore equivalent to
J|Q and F|(H_old-C). Put z=(H_old-C)/F. Because j_old>=1, z>0; because
F=1 modulo C, z=B1 modulo C. Since 0<B1<C, necessarily z=B1+jC for a unique
j>=0. This gives precisely our H. Conversely our H has

  j_old=1+[(F-1)/C]B1+Fj>0,

an integer, and has both required divisibilities whenever J|Q. Therefore the
reparameterization is exact in both directions; no cofinal-witness assumption
is used. The ratio conditions are now just

  a0 square, a1 square, J|Q, m>0.

The numerical ratio theorem then gives b a power of two, 8g<Gcap, and the
central-binomial divisibility. Conversely the stronger source bound 32g<Gcap
produces all the requisite ratio witnesses, which translate as above.

## 4. A second-order polynomial Pell majorant

All following bounds hold unconditionally at every mixed-domain assignment.
The usual size estimates give A>=2 and P,K,C,J,D,E,F,G,H>1.
Take V0=PK. Then

  V0^2-a0=K^2-1>0.

The identity E=CL, L=kD gives

  F=(D-1)L^2+1=(D-1)k^2D^2+1.

Define

  T=k(8D^2-4D-1), V1=TGH.

A direct polynomial identity is

  T^2-64DF=(8D+1)k^2-64D
             =8D(k^2-8)+k^2>0,

because k=iJC>=3. In particular

  Delta1=V1^2-64a1
    =[(8D+1)k^2-64D](GH)^2+64DF(H^2-1)>0.

Thus V1 is a strict integer majorant of sqrt(64a1), much sharper than the
naive product of three Pell majorants. Its smaller polynomial defect is the
source of the additional degree saving.

## 5. The margin separates the two radicals

Q>0 and J>=3. Also Q<3C^2 because W1<C; D>C^2 and
T=k(8D^2-4D-1)>3D give V1=TGH>3D>Q. These stronger concrete bounds
allow us to eliminate all auxiliary quotient offsets. Set

  Omega=Jm,
  Theta=Jn+Q-Omega(V0+V1),
  F9=[Theta^2-Omega^2(a0+64a1)]^2-256Omega^4 a0a1.

The equation is F9=0. If m=0, Theta=Jn+Q>0, excluding a zero. Otherwise
the four real linear factors of the norm imply

  n+Q/J=mZ,
  Z=V0+V1+r0+r1,
  r0^2=a0, r1^2=64a1.

At this stage r0,r1 are only real roots. Nevertheless the unconditional strict
majorants give Z>0. The left side is positive, so m>0 is already proved,
before any integrality claim.

From m>0 follows 4(C-KY)^2<K^2; hence C>K(Y-1/2)>K because Y>=64.
Moreover P<A^2, D>C^2, F>=A^2, G>=A and I>=G^2>=A^2. Consequently

  a1=DFI>A^4C^2>P^2C^2>P^2K^2>a0.

Therefore 64a1>a0 and r0+r1 cannot vanish. Its value Theta/Omega is rational.
If x=r0+r1 !=0, then 2xr0=x^2+a0-64a1, so r0 is rational and then r1 is
rational. A rational square root of an integer is an integer. Thus a0 is a
square; r1/8 is a rational square root of a1 and is an integer as well.
Now Z is an integer, and the displayed factor equation implies J|Q.

Conversely, if the four ratio conditions hold, select the positive integer
roots r0,r1, put Z as above and set n=mZ-Q/J. Since m>=1 and
Z>V1>Q>Q/J, this is a positive integer, in particular n>=0. The corresponding linear factor
vanishes. This proves the finalizer equivalence in both directions.

Together with Sections 1--3 and the stated source compiler, the polynomial
has a zero exactly when there is a finite syntactic ZFC refutation. Negating
this equivalence gives the claimed ZFC-provable consistency equivalence.

For the strictly positive domain replace phi,j,n by their coordinates minus 1.
For the nonnegative domain replace b,g,h,s,w,i by their coordinates plus 1.
These are bijections, not restrictions on the underlying mixed-domain zeros.

## 6. Exact degree and arithmetic circuit cost

Let ell0=Kcode+W+2 and t=2ell0=deg N. On the all-variable diagonal, N has
leading coefficient 4lambda^ell0, and R has leading coefficient
16lambda^(3ell0). The positive geometric term uniquely dominates Jcode.
The new ratio-register degrees are

  P:12t+3, K:12t+4, A:7t+2, C:3t, J:7t+2,
  D:20t+4, k:10t+3, L:30t+7, E:33t+7,
  F:80t+18, G:103t+22, H:83t+19,
  I:372t+82, a0:48t+14, a1:472t+104,
  m:28t+2W+11, Omega:35t+2W+13,
  V0:24t+7, V1:236t+52, Delta1:412t+92.

The last error degree follows from its positive decomposition in Section 4;
the first summand uniquely dominates. With
E0=Jn+Q, the exact identity

  Theta^2-Omega^2(a0+64a1)
   =E0^2-2E0 Omega(V0+V1)
     +Omega^2[(K^2-1)+Delta1+2V0V1]

resolves its leading cancellation. Omega^2 Delta1 uniquely dominates, at
degree 482t+4W+118. Its square in F9 dominates the subtracted norm term.
Consequently

  deg F9=964t+8W+236,
  diagonal leading coefficient=2^1730 lambda^(964ell0+4W).

This is nonzero for the actual fixed coefficient, and the same bound is a
full multivariate total-degree upper bound, so equality follows.

The builder compares global sparse Horner, direct sum, per-row Horner and,
when applicable, homogeneous-row and shared-source encodings. For the last,
put u0=B^(W-p), ui=B^(W-w_i). Evaluate the inherited 60-gate quadratic source
homogeneously at its old positive variables ui+u0, aligning additions by
powers of u0 and lifting each residual to degree two. This gives the quadratic
form with unweighted coefficients. Add one further copy of each diagonal
monomial (u0^2 and ui^2) and leave the mixed terms unchanged. A quadratic
factorial weight is exactly 2 on diagonal terms and 1 on mixed terms, so this
is the same weighted row polynomial. Multiply row j by B^(h_j-2W), which is
polynomial whenever h_j>=2W, and share all source gates between rows.

For the compact intermediate variant, translate every target and every
encoding exponent in the interior packed certificate by 186. This changes
neither the isolation differences nor any coefficient; it makes min h_j=2W
and enables the shared evaluator. Its Dmax=4914 and Kcode=5262. The unshifted
interior packed variant remains the lowest-degree form; interior regular is
the fewest-operation form. The direct global-Horner source is used in every
degree-certificate circuit, independently checking shared-source evaluation
against the explicit 136 weighted terms in modular replays. 
The primary builder selects by the live binary
operation count, charging additions, subtractions, all scalar multiplies,
squares and every fixed-exponent multiplication. Aliases are not variables;
dead gates are not counted. The generated certificate form is separate from
the operation-minimized primary circuit.

## 7. Reproduction and limits

Run build_nine.py with one or more packing certificate paths, then
materialize_coefficients.py and verify_nine.py. These authored programs read
mathematical JSON and integer payloads; they do not execute upstream scripts.
The verification receipt contains modular identity/domain replays, actual-tuple
replays, exact symbolic leading-degree checks, finalizer obstruction and
completeness fixtures, and exact Pell-majorant fixtures. Coefficient payloads
are given with raw and compressed hashes.

These finite checks audit the implementation and its transcriptions. They do
not decide consistency or replace the proofs and imported dependencies above.

## Frozen recommended frontier

The positive-domain variants, with nine variables in each case, are:

- `nine_174_interior_regular_positive.json`: 548 operations, degree 15502748.
- `nine_174_interior_shifted_positive.json`: 603 operations, degree 10486092.
- `nine_174_interior_packed_positive.json`: 655 operations, degree 10127484.

The separately translated natural-domain variants cost three more operations
and have the same respective degrees. The two non-interior variants are
retained only as reproducible comparison points and are dominated by this
frontier. These are improvements over the supplied/local baselines, not claims
of global optimality among all Diophantine representations.
