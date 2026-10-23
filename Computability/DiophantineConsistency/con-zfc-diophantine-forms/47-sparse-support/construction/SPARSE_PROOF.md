# Sparse supported monomials and a scaled quadratic base

## Scope and precise claim

This package gives explicit arithmetic circuits for six new presentations of
the fixed 31-variable quadratic parent in ProveIt package 31, at commit
`124c07c0b77a9e20e84676514d8b1ff78536ea3f`. The new theorem is equivalence of
zero existence to that parent, using the numerical Jones ratio theorems for
the nine-variable families and the imported Sun finalizer for the ten-integer
families. Composition with the parent's machine/compiler calibration gives
the stated Con(ZFC) equivalence. That calibration is an inherited dependency;
this package does not supply a new end-to-end kernel certificate or an
exported object-language ZFC derivation.

The contribution is three concrete source transformations:

1. Isolate only monomials which actually occur in the parent residuals.
2. In the nine-variable construction use a fixed large multiplier times a
   variable square, replacing the previous variable cube.
3. Begin the nine-variable target range at 2W rather than 2W+1, removing
   an unnecessary common exponent shift.

The ten-integer branch already used a scaled square in package 40. Its new
ingredient here is sparse supported-monomial coding. The intersective
quintic in that finalizer is also inherited, and is not a new claim.

## Fixed parent and coefficients

`parent_system.json` is the exact package-31 60-operation circuit, with
SHA256 `ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48`.
It defines 22 quadratic residuals in 31 strictly positive variables, with
four fixed ports `(beta,K0,MC,MF)`. All four ports travel together, and the
fourth is the already shifted MF_source. The compressed bytes and their
hashes are included. The two fixed-leaf manifests specify and materialize
every nonliteral coefficient of every delivered circuit.

Replace the 31 positive variables by `z_i+1`, and reorder the residuals as
1,2,3,4,6,7,...,22,5. Denote the reordered residuals by p_j. Their 136 terms
use exactly 71 distinct monomials: the constant, all 31 linear monomials,
and 39 quadratic monomials. The last row has constant coefficient 1.
`verify_source.py` reconstructs all these facts directly from the parent
circuit using an independent sparse polynomial ring, without SymPy.

## Supported-monomial isolation lemma

Let A be any subset of the monomials of degree at most two in n variables.
For positive integer weights w_i, write w(alpha)=sum alpha_i w_i. Suppose
that for each alpha in A and every beta with |beta|<=2,

    w(alpha)=w(beta)  implies  alpha=beta.

The condition need not hold for pairs of monomials both outside A.
Let p_j(z)=sum_(alpha in A) p_(j,alpha) z^alpha be quadratic polynomials,
W=max w_i, h=2W+1 and H_j=jh-1. Define

    c_(j,alpha)=(2-|alpha|)! product_i(alpha_i!) p_(j,alpha),
    D(T)=sum_(j,alpha) c_(j,alpha) T^(H_j-w(alpha)),
    C(T)=(1+sum_i z_i T^w_i)^2.

Then the coefficient of T^H_j in C(T)D(T) is exactly 2p_j(z).

Proof: a source term (k,alpha) and expansion term beta contribute there
only if H_k-H_j=w(alpha)-w(beta). The right side is in [-2W,2W], while a
nonzero left side has absolute value at least 2W+1. Thus k=j, and the
isolation assumption forces alpha=beta. The factorial in D cancels the
multinomial denominator of C, leaving the factor 2. This proves a
polynomial coefficient identity for every assignment, not a finite-witness
test.

The same assumptions show that all coefficient positions in D are distinct:
different rows occupy disjoint blocks, and the supported monomials are
distinct within each row. Thus if |c_(j,alpha)|<M, every coefficient of D
has magnitude <M. Collisions among unused monomials can change coefficients
of C, but their coefficients are nonnegative when z_i>=0. Consequently the
usual convolution bound remains

    |[T^e] C(T)D(T)| <= M(1+sum_i z_i)^2.

No factor counting unused collisions or the 22 rows is required.

## The two explicit weight vectors

The order is exactly the parent variable order recorded in the target files.
Padding weight zero is implicit and is not a source variable.

For W=220:

    24,89,95,146,205,155,147,197,203,78,29,148,47,208,25,
    217,129,169,30,215,220,219,135,166,27,133,32,200,43,204,152.

For W=239:

    237,231,223,221,233,193,195,215,120,190,226,142,125,151,
    148,169,214,134,140,121,126,172,128,196,238,191,239,192,
    197,184,205.

Both vectors satisfy the isolation condition on all 71 supported monomials
against all 528 possible expansion monomials. The W=220 vector has only
308 distinct sums among all 528; the W=239 vector has 249. The additional
collisions are intentionally allowed. The release audit additionally checks
all 136*528=71,808 source-term/expansion pairs for contamination of any of
the 22 output targets. Every source term has exactly one intended hit.

These are explicit certificates, not claims that the weights are globally
minimal. The W=239 vector gives a shorter exponentiation schedule; W=220
gives lower degree. Neither reported point dominates the other on both
measures.

## Scaled quadratic source for the nine-variable branch

Let M=2^2134927 and lambda=2^2134939=4096M. The finite port-bit-length
calculation bounds every c_(j,alpha) strictly by M in magnitude. Let the
mixed source coordinates satisfy epsilon,phi,n>=0 and g,h,s,w,i,j>=1.
Define

    b=epsilon+2, B=lambda*b^2,
    ell=sum_i B^w_i, H=22(2W+1)-1, Kcode=H+2W,
    N0=B^(W+1), N1=4B^(Kcode+1), N=N0*N1,
    Mask=N0-1-(b-1)ell, Targets=sum_(j=1)^22 B^(j(2W+1)-1),
    Tcode=Mask+(B-2)Targets*N0,
    Jcode=2(1+g)^2 D(B)+B sum_(k=0)^Kcode B^k,
    Scode=g+Jcode*N0,
    R=(N-1)((Scode+Tcode+1)N+Tcode+1),
    Gcap=32b B^W.

All displayed powers have fixed exponents. The delivered circuits expand
them into binary multiplication gates. Geometric sums are also evaluated
polynomially; no division, digit extraction, or auxiliary witness occurs
in the final circuits.

The leading coefficient of D is 2 at degree H. Since B-1>M, lower
coefficients cannot cancel it, so D(B)>B^H>0. Since b>=2 and B is very
large compared with b, Mask, Tcode, Jcode and Scode are positive. Hence
R>=N>=8 and R,N>=b on every outer assignment.

On the bounded branch g<4bB^W, integrality gives 1+g<=4bB^W, and
4b<B implies g<N0. The previous bound on D gives

    2(1+g)^2 D(B) < 32M b^2 B^(Kcode+1)/(B-1).

Now 32M b^2=B/128. Adding the geometric term proves 0<Jcode<N1.
The target mask is smaller than N1, so 0<=Scode,Tcode<N.
These bounds need no carry or equation assumption.

If b is a power of two, B, N0, N1 and N are powers of two. Write N=2^r.
The identity

    R=(Scode+Tcode)N^2+(N-1-Scode)N+(N-1-Tcode)

and the binary digit-sum formula for the central binomial coefficient give

    N^2 divides binomial(2R,R) iff adding Scode and Tcode has no binary carry.

The low block forces g=sum z_i B^w_i with 0<=z_i<b. For such g,
every coefficient of C(T)D(T) has magnitude strictly less than
M(32b)^2=B/4. Adding B/2 to each coefficient therefore puts each digit
strictly between 0 and B. Divide the high carry test by 2, a common binary
shift. At each target it tests disjointness from the mask B/2-1, forcing
that target digit to be B/2, equivalently p_j(z)=0. The extraction lemma
makes this the simultaneous conjunction of all 22 residual equations.

Conversely, given a common nonnegative zero, choose an arbitrarily large
power-of-two b exceeding all z_i, put epsilon=b-2 and g=sum z_i B^w_i.
The final row has constant coefficient 1, so the common zero is not the
all-zero vector and g>0. The estimate g<bB^W yields the stronger
32g<Gcap needed by the completeness direction of the numerical Jones
ratio theorem. All carry conditions then hold.

This is exactly the source interface used by package 45. The old choice
B=b^3 with a huge additive lower bound on b is unnecessary: the fixed
multiplier lambda provides the same digit bounds with degree two in b.

## Unchanged Jones bridge and final polynomial

Use the package-45 numerical Jones registers U,Y,P,K,A,C,J,Q,D,E,F,G,H,I,
a0,a1,u,v,m as explicitly evaluated by `build_sparse_nine.py`. The cited
ratio soundness and completeness theorems turn the source into

    a0 and a1 are squares, u divides v, and m>0.

All their numerical hypotheses were proved above. In particular soundness
gives 8g<Gcap, which is precisely g<4bB^W; completeness uses 32g<Gcap.
No circular use of the carry conclusion is made to establish these bounds.

Let V0=PK, V1=(AC)(AE)(GH), Md=Q+H, Omega=um, and

    Theta=u(n+Md)+v-Omega(2Md+V0V1).

The final polynomial is

    F9=(Theta^2-Omega^2(a0+V0^2*a1))^2
       -4*Omega^4*V0^2*a0*a1.

The strict inequalities 0<a0<V0^2 and 0<a1<V1^2, together with
0<v/u<Md-1, are inherited algebraic identities and positive-domain
inequalities from the unchanged tail. They prove both directions of the
four-factor finalizer, including exclusion of m=0. All named quantities
are polynomial registers, not additional unknowns.

For nine strictly positive input coordinates use b=epsilon+1, shift phi
and n down by 1, and leave g,h,s,w,i,j positive. For nine nonnegative
coordinates use b=epsilon+2, leave phi,n nonnegative, and shift
g,h,s,w,i,j up by 1. These are bijective domain translations. The
nine-variable equations are not asserted to have the same zero set over
all integers; the ten-integer branch is separately supplied for that domain.

## Exact degrees and operation counts

For the nine-variable source, deg N=t=94W+46. Resolving the leading
cancellation V1^2-a1 by its exact telescoping expression gives

    deg F9=1152t+8W+280=108296W+53272.

On the diagonal where all nine inputs equal T, the leading coefficient is

    2^2050 * lambda^(54148W+26496),

which is nonzero. The certificate circuits establish the corresponding
multivariate upper bound and the diagonal lower bound, so the degree is
exact. The primary circuits evaluate the same polynomial more cheaply.

| Family | Maximum weight | Unknown domain | Operations | Exact degree |
|---|---:|---|---:|---:|
| Sparse9 | 239 | 9 positive integers | 651 | 25,936,016 |
| Sparse9 | 220 | 9 positive integers | 670 | 23,878,392 |
| Sparse9 | 239 | 9 nonnegative integers | 655 | 25,936,016 |
| Sparse9 | 220 | 9 nonnegative integers | 674 | 23,878,392 |
| Sparse10 | 239 | 10 unrestricted integers | 662 | 71,151,176 |
| Sparse10 | 220 | 10 unrestricted integers | 675 | 65,506,504 |

Each binary +, - or multiplication costs one operation, including scalar
multiplications and squarings. Fixed literal leaves, fixed coefficient
leaves, and reuse are free. The fixed coefficient payloads are separately
specified and are not hidden witness variables.

The ten-integer circuits retain the complete package-40 scaled-square
source shape and Sun finalizer. Only the supported-monomial weights change.
Both branches now use targets beginning at 2W, matching the inherited
ten-integer source.
Exact degree is 297088W+147144, with a nonzero leading coefficient
certified modulo 1,000,000,007 after diagonal specialization. A nonzero
coefficient modulo a prime is an exact nonvanishing certificate over Z;
this step is not a random identity test.

## Verification and limits

`python3 verify.py` uses only the standard library. It checks coefficient
recipes and compressed/raw hashes, complete gate liveness and operation
counts, exact degree certificates, the closed leading coefficient, and
finite arithmetic replays of the primary/certificate/domain identities.
It then rebuilds the delivered files in a temporary copy and requires
byte-for-byte agreement. `python3 -O verify.py` retains all checks.

Finite audits certify finite data, identities, and circuit bounds. They do
not decide whether any equation has a zero, prove consistency, or replace
the imported unbounded compiler and arithmetic theorems. Global optimality
is not claimed. The comparison baseline is package 45's 788-operation,
degree-129,875,980 nine-positive equation and package 40's 782-operation,
degree-237,520,456 ten-integer equation at the pinned repository snapshot.
