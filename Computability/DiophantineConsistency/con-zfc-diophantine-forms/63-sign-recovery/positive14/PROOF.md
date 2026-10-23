# A positive main-root carrier removes the index quotient

## Result

This note gives an ordinary integer polynomial in **14 strictly positive
variables**, of exact degree **34**, evaluated by **87 binary arithmetic
operations**. Its positive solvability is equivalent to the canonical
native-window compiler system, using the complete source-34 coefficient tuple
shared with the main archive (beta=2^1064921-1).
Combining this with the inherited compiler and K215 calibration yields the
ordinary mathematical equivalence with finite syntactic ZFC refutability.
It does not supply a new kernel-checked end-to-end theorem or a global
minimality result. The prior 14-positive frontier at the inspected commit
beb0192cb8 has degree 52 and 79 operations (packages 55 and 59).

The new point trades eight operations for a degree reduction 52 -> 34.
The optional unshifted-transport comparator has 88 operations. Both reuse
f^2-1 in the strong and auxiliary equations.
The four actual integer payloads are under ../coefficients/payloads, with
their exact inherited COEFFICIENT_BINDING.json. The circuit ports map beta
to beta.bin, K0 to K.bin, MC to MC.bin, and MF to MF_source.bin. This proof
is uniform in authentic tuples satisfying the inherited positive compiler
contract; no oddness or extra congruence restriction on a supplied J is
introduced. In particular no port from source 44 is mixed into this instance.

## 1. Literal polynomial

Supply exactly the positive variables

    J,F,alpha,z,f,i,T,w,Y,r,eta,zeta,u,t.

The four fixed ports beta,K0,MC,MF are one complete authentic tuple; MF is
already shifted. Set

    q=beta J+1, C=q-F-alpha,
    X=wq, E=XY, k=eta+zeta, c=kY+eta,
    a=E+Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
    b0=X+ac, ell=EkY,
    R=[(q-1)(q-F)+alpha](q^2-1)+(MC+q MF)J,
    At=(K0+w)C-F-z(q-1),
    M=4q^4, e=k-R-1, Z=Mt-e, W=M b0+HZ,
    I=ic^2, Q=Delta(f^2-1), V=c(Tf-1)-Rf^2.

Take residuals

    A0=[q^3(ell+r)+Y]^2-q^6[ell(ell+k)+1],
    A1=W^2-M^2(1+Delta c^2),
    As=f^2-Delta I^2-1,
    Au=(V+u)^2-Q u(2V+u)-1.

The proposed single equation is

    P14=A0^2+A1^2+At^2+As^2+Au^2=0.

Every abbreviation is a polynomial register, not a quantified variable.
The literal JSON includes all powers as binary multiplication gates.

## 2. Soundness before restoring the deleted quotient

Suppose all fourteen supplied integers are positive and P14=0. Each
residual vanishes. From At=0,

    (K0+w)C=F+z(q-1)>0,

so C>0. Set z_old=z+1>0. The exact identity Nt(z_old)-1=At recovers
the authentic old transport equation. Thus the whole tuple's inherited
outer-interface bounds apply:

    q>=16, 3q<R<q^4-2.

No deleted index quotient is used in these bounds.

By the elementary fact that an integer with integral rational square root
has an integer root, A0=0 gives q^3|Y. Define

    s=Y/q^3>0, tau=ell+r+s>0.

Then tau^2=ell(ell+k)+1. Consequently Y>=q^3, X>=q and E>=q^4.
Set P0=2XY^2+1 and A=a+2. The first Pell classification gives

    tau=chi_P0(n), k=2 psi_P0(n), n>=1.

Here n cannot equal 1: that would give k=2, tau=ell+1, whereas
tau=ell+r+s>=ell+2. Hence n>=2, so

    k>=2 psi_P0(2)=4P0>8XY^2,
    c>kY>8XY^3>=8q^10>2R,
    c>X.

The carrier W is positive. Indeed a>=q^4>=3, so H=4a+3<=5a;
therefore b0/H>=ac/H>=c/5>kY/5>k. Since M>1 and R>0,

    W/H=M b0/H+Mt-k+R+1>0.

The main residual now says (W/M)^2=1+Delta c^2. Thus

    D=W/M

is a positive integer with D^2-Delta c^2=1. In particular

    M divides H e.                                  (1)

We have not canceled H, or assumed e/M or e/E integral.

## 3. Recover the main Pell index without h

The main Pell classification gives

    D=chi_A(p), c=psi_A(p), p>=1.

Since P0>A and c>k, strict monotonicity gives n<p. In particular p>=3,
and elementary Pell growth gives c>2p. We have already established c>2R.

The normalized strong equation As=0, with I=i c^2 and i>0, gives

    f=chi_A(m), I=psi_A(m), m>=1.

Strong divisibility first gives p|m. Write m=pj. Modulo c, the composition
formula says

    psi_A(pj)/c = j chi_A(p)^(j-1) (mod c).

Its left side is divisible by c, and chi_A(p) is coprime to c. Hence c|j,
so pc|m. Thus c|m and m>2p. Unlike the ordinary-strong variant, this step
requires no large-ordinate relaxed-rank bound.

Put rho=Delta I>1. The strong equation gives Q=rho^2. The auxiliary
residual yields

    rho^2 V^2-(rho^2-1)(V+u)^2=1.

Neither V nor V+u can vanish. The same signed auxiliary-index lemma used
in package 57, Sections 3-5, therefore applies with y_old=|V+u|. Its only
congruences are

    V=-c (mod f), V=-R (mod c).

They follow from the literal formula for V and f^2=1 (mod c). For an
explicit trace, Pell classification yields an odd auxiliary index l and
sign sigma with V=sigma Q_((l-1)/2)(rho^2). The odd-index identities

    Q_j(1-A^2)=(-1)^j psi_A(2j+1),
    Q_j(0)=(-1)^j(2j+1)

and signed step-down with 0<2p<m imply l=+p or -p (mod m), hence
p=+R or -R (mod c). Since 0<p,R<c/2, this forces

    p=R.                                            (2)

Neither (1) nor the assertion that h exists has been used in this step.

## 4. Restore the exact first index, h, and gamma

Because Y=sq^3, H=4Y(X+1)+3 is odd and congruent to 3 modulo q.
No prime except 3 can divide both q and H. If 3|q then 27|Y, so
H=3 (mod 27) and v_3(H)=1. Consequently

    gcd(M,H)<=3, mu=M/gcd(M,H)>=4q^4/3>R.

From (1), mu divides e. The first Pell recurrence gives

    k=2n (mod 4XY^2).

Since 4XY^2=4w s^2 q^7 is divisible by M=4q^4, it follows that
mu divides 2n-R-1. But n<p=R, so |2n-R-1|<R<mu. Therefore

    2n=R+1.

It follows from the same recurrence that e=k-2n is divisible by 4XY^2,
hence by both E and M. It is strictly positive because n>=2 and
psi_P0(n)>n. Thus

    h=e/E>0

is an integer and k-hE-R=1, exactly the deleted index condition.
Likewise

    gamma=t-e/M

is an integer and D=b0+gamma H. Because
D=sqrt(Delta c^2+1)>(a+1)c and c>X, we have

    D-b0>c-X>0,

so gamma>0. These divisions occur only in the proof after exact
divisibility has been obtained.

All the positive normalized source witnesses have now been recovered:
J,F,alpha,z_old,f,h,i,T,s,w,tau,eta,zeta,y_old,gamma, with
z_old=z+1 and
y_old=|V+u|>0. Their first, main, strong, auxiliary, index and transport
equations are exactly the inherited normalized compiler system. Its
ordinary soundness theorem supplies a finite syntactic ZFC refutation.

## 5. Completeness and strict positivity of both new carriers

Start with a finite ZFC refutation. Use the canonical positive normalized
compiler witness from the same whole coefficient tuple. It satisfies

    p=R=2n-1, R=3 (mod 4), q>=16, n>=3,
    X=wq, Y=sq^3, k>XY, gamma>0.

The first Pell recurrence gives M|e, where e=k-R-1>0. Set

    t=gamma+e/M>0.

Then W=MD and A1=0. This sign choice is crucial: the opposite carrier
t=gamma-e/M need not be positive.

For the first root use the same positive gap as package 58:

    r=tau-ell-s.

Since tau^2=ell^2+ell k+1, ell>k and tau<ell+k,

    tau-ell=(ell k+1)/(tau+ell)>k/3>XY/3>Y/q^3=s.

Therefore r is a positive integer and A0=0.

Retain the normalized strong f,i, and let rho=Delta I. Choose fresh
auxiliary witnesses

    V*=chi_rho(R)/rho, y*=psi_rho(R).

Odd R makes V* an integer. Since R=3 (mod 4), the odd-index identities
give V*=-c (mod f) and V*=-R (mod c). The strong equation gives
gcd(c,f)=1 and f^2=1 (mod c). Hence

    T=(V*+c+R f^2)/(cf)>0

is an integer. Its literal V equals V*. The Pell identity gives
rho^2 V*^2-(rho^2-1)y*^2=1; since V*>1,

    y*^2-V*^2=(V*^2-1)/(rho^2-1)>0.

Thus u=y*-V*>0 is an integer, and Au=0. The other residuals remain zero.
This proves completeness without assuming every old auxiliary witness has
the required gap or quotient.

The shifted transport coordinate is also positive. The canonical source
has X=2^R and R>3q, hence w=X/q>q>F. Its equation is

    (K0+w)C=F+(z_old-1)(q-1).

Because C>=1 and K0>=0, the left side is greater than F, so z_old>1.
Thus z=z_old-1>0. Conversely At=0 gives the authentic old transport
equation Nt(z+1)=1 identically. This is the established positive transport
shift, included here to charge its one-operation saving explicitly.

## 6. Exact degree and operation count

The exact cancellation identities are

    A0=q^6[r^2+ell(2r-k)-1]+2q^3(ell+r)Y+Y^2,

    A1=M^2[X^2+2acX-Hc^2-1]+2M b0 HZ+H^2 Z^2.

They give residual degrees (12,17,2,16,15) in the listed order. To see
the unique degree-17 part of A1, put q0=beta J, X0=wq0, a0=X0Y,
c0=(eta+zeta)Y, M0=4q0^4, H0=4a0. Since deg(Mt)=5>deg(e)=4,

    in_17(A1)=2M0^2 a0 c0 H0 t
             =128 q0^10 w^2 Y^3 (eta+zeta)t.

Consequently

    in_34(P14)=16384 (beta J)^20 w^4 Y^6 (eta+zeta)^2 t^2.

The coefficient of J^20 w^4 Y^6 eta^2 t^2 is 2^14 beta^20>0. Thus the
degree is exactly 34 for the actual fixed tuple. A separate
cancellation-expanded DAG supplies a transparent degree upper bound.
The primary division-free DAG has 87 live gates: 48 multiplications,
23 additions, 16 subtractions. All 14 variables and all 4 fixed ports
are live. The five-residual system has 78 gates and maximum degree 17.
The input-plus-one translation has fourteen nonnegative inputs, the same
exact degree, and 101 gates. This direct translation is not asserted to
be operation-optimal. It is supplied as pell14_natural_degree34.json.

## 7. Dependencies and remaining formalization boundary

The following exact source files were read at commit beb0192cb8:

* 58-integral-root/report/report.tex: first-root integral carrier,
  canonical positive gap and normalized witness contract. Its local
  coefficient-independent argument is used; its different tuple is not.
* 34-integer14/coefficients/COEFFICIENT_PROOF.md and
  coefficients/payloads/COEFFICIENT_BINDING.json: the whole active tuple's
  native compiler adapter, literal payloads and canonical witness contract.
* 57-separated-degrees/low_degree/PROOF.md: main-root rationality, the
  normalized strong-index argument, first-index modulus 4q^4 and gcd bound.
* 36-small-tuple/coefficients/source_proofs/SIGNED_DOMAIN_29.md:
  signed auxiliary-index proof and exact proof-order conditions.

This note combines those ingredients in a new single-root carrier with the
opposite quotient sign, eliminating h while preserving a positive t without
eliminating or mixing the first root. The proof of the new existence
equivalence is Sections 2-5, not a finite test. Finite code checks establish
literal transcription, degree, counts and elementary polynomial identities.
The native compiler and syntactic calibration remain imported ordinary
mathematical theorems; no kernel-check claim is made for this new polynomial.
