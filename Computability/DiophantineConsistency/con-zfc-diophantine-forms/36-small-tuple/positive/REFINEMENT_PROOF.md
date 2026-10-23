# Smaller evaluators for the twelve-positive-variable forms

## Result

At the comparison pin `8c6eec9d19ef80538c8e61ff6e0180040583446a`,
package 30's best twelve-positive-variable product costs 111 binary arithmetic
operations; package 24's degree-1069 product costs 123. This synthesis gives:

| Template | Positive variables | Equations | Exact degree | Operations |
|---|---:|---:|---:|---:|
| Short product | 12 | 1 | 1081 | 109 |
| Short unshifted system | 12 | 3 | 1072 maximum | 104 |
| Short shifted system | 12 | 3 | 1072 maximum | 103 |
| Tight product | 12 | 1 | 1069 | 120 |
| Tight unshifted system | 12 | 3 | 1060 maximum | 115 |
| Tight shifted system | 12 | 3 | 1060 maximum | 114 |

The products are **identical polynomial templates** to their named predecessors,
with the twelve variables and four coefficient ports held fixed. Their new
evaluators are cheaper. The low-degree version combines package 24's deliberate
leading-term cancellation with package 30's trace/product remainder method.
There is no claim of a new variable-count or degree record. The shifted systems
add the transport-coordinate shift already proved in packages 22 and 29.

All binary additions, subtractions, and multiplications count, including those
by fixed integers. Equalities, references to earlier values, and integer leaves
are free. The complete emitted circuits, including every gate, are in `circuits/`.

The coefficients must be instantiated by **one complete proved compiler tuple**
in `../coefficients/COEFFICIENT_BINDING.json`; from a circuit's directory the
relative location is `../../coefficients/COEFFICIENT_BINDING.json`. The four
ports are beta=B-1, K0, MC, and shifted MF=MF_native+B-1. This directory does
not silently mix or rebind predecessor coefficients. Its arithmetic identities
are universal in the four ports; semantic instantiation uses the containing
package's one selected tuple and its compiler-interface proof.

## 1. Complete polynomial definition

The supplied variables are

    J,F,alpha,z,h,i,T,s,w,eta,zeta,t > 0.

Every other symbol below is a computed polynomial expression, never an
additional unknown. Put

    q=beta J+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H, ell=E kY,
    A=1+ell(ell+k), G=1+Delta c^2, b0=X+ac,
    Cw=q-F-alpha,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nk=k-hE-R,
    Nt=(K0+w)Cw+q-F-z(q-1),
    I=ic^2, D=1+Delta I^2, Q=Delta^2 I^2, d=Q-1,
    b=c+RD, P=QD c^2 T^2, U=Qb^2.

For the short form set

    M=k(I^2+T^2), L=1+HM, W=b0+Ht.

For the tight form set

    Csharp=E+2(X+Y)+s q^2,
    M=I(2T+R Csharp i c), L=1+2HM, W=L b0+Ht.

Both forms use the same following evaluator:

    n=(HM)^2 A, dn=d n,
    HP=H^2 P, HU=H^2 U, He=HP+HU-H^2, j=4 HP HU,
    Trace=2d(W^2+L^2 G), Kroot=d(W^2-L^2 G), Knorm=Kroot^2,
    AA=2(dn+He), constant=(dn-He)^2-j,
    at=Trace-AA, bt=constant-Knorm, coef=16 dn j,
    v=coef-at(at Trace+2bt), u=bt^2-at^2 Knorm,
    NormLeft=u(Trace v-u), NormRight=Knorm v^2,
    N=NormRight-NormLeft.

The product is the literal integer polynomial

    Nk Nt (1+N)-1 = 0.

The unshifted three-equation system is

    Nk=1, Nt=1, NormLeft=NormRight.

The shifted system, still with twelve strictly positive supplied variables, is

    Nk=1, (K0+w)Cw=F+z(q-1), NormLeft=NormRight.

Its supplied z corresponds to z_old-1 in the product. The norm does not use z.

## 2. Polynomial identity proving the evaluator

Define the even degree-eight polynomial in a formal argument x by

    F_H(x) = [ (d x^2)^2-AA(d x^2)+constant ]^2 - coef(d x^2).

If g^2=G, the two quantities x_+=d(W+Lg)^2 and x_-=d(W-Lg)^2
have sum Trace and product Knorm. Consequently they satisfy

    x^2-Trace x+Knorm=0.

Modulo this monic quadratic,

    x^2-AA x+constant = at x+bt,
    (at x+bt)^2-coef x = u-vx.

Taking the product at x_+ and x_- gives exactly

    F_H(W+Lg) F_H(W-Lg)
      = (u-vx_+)(u-vx_-)
      = u^2-Trace u v+Knorm v^2
      = NormRight-NormLeft.

This calculation is a polynomial identity over the integers, valid even when
the radicands are zero, squares, or dependent. It needs no division, sign
choice, field extension hypothesis, or nonsingularity assumption.

To match the predecessor norm, set e=P+U-1, Baux=2Q(cT)b, and m=HM.
The identity j=H^4 D Baux^2 follows from P=QD(cT)^2 and U=Qb^2.
Eliminating the formal tau with tau^2=A in

    [d(x-m tau)^2-H^2 e]^2-H^4 D Baux^2

gives F_H(x). Thus the final N is exactly the product over g=+/-sqrt(G)
and tau=+/-sqrt(A) used by both predecessors. This is the full algebraic
proof of template identity, supplemented by the independent finite checker.

## 3. Where every saved operation comes from

First, replace d^2(W^2-L^2 G)^2 by [d(W^2-L^2 G)]^2. With W^2 and L^2G
already available, this requires subtraction, multiplication, and squaring:
three operations instead of four. The old d^2 value has no other consumer.

Second, take the negative of the old linear remainder coefficient by reversing
the operands of its final subtraction. This has no cost. Evaluate the final
norm as

    Knorm v^2 - u(Trace v-u).

This takes six gates: square v, multiply by Knorm; multiply Trace by v,
subtract u, multiply by u; subtract the two results. The earlier three-term
expansion takes seven. The two complete products therefore save two gates
against the same trace/product evaluator. For a system the final subtraction
is unnecessary: compare its two arguments, saving a third gate.

The degree-1069 form previously used a different pair evaluator. Replacing it
by this trace/product evaluator saves three gates in its product and unshifted
system. This is a combination of separate earlier ideas, not a new root bound.

Finally the transport shift gives the identity

    [(K0+w)Cw+q-F-(z+1)(q-1)]-1
      = (K0+w)Cw-F-z(q-1).

It removes one operation from the comparison system. Every shifted positive
solution is an unshifted one. Conversely, the full inherited compiler theorem
gives Cw>0, X=wq=2^R, R>3q and F<q at a solution. Thus w>q>F and
(K0+w)Cw-F>0. The old transport equation then gives z_old>=2, making
z=z_old-1 positive. This is an existence-preserving change of coordinates.

## 4. Semantic theorem and exact degrees

The local changes establish universal polynomial identities and the specified
transport substitution. The predecessor proofs recover the original positive
blank-machine compiler witnesses from N=0 and the outer equations, using
separating weights and rational Pell saturation. Those proofs are included as
`upstream/POSITIVE12_PROOF.original30.md` and `upstream/positive.original24.tex`.
The signed compiler and transport proof are also included. Composing them with
the containing package's complete coefficient/compiler theorem and the
calibrated K215 endpoint gives the ordinary mathematical theorem

    ZFC proves: no solution in the stated positive domain iff Con(ZFC).

This is not a new proof-assistant certificate, a consistency proof, a claim
about solutions over unrestricted integers, or a proof of global optimality.

Exact degrees are inherited by template equality. For the short form,
He has degree 134, bt has degree 268 with leading form He_top^2, and u
has degree 536 with leading form He_top^4. In N, u^2 has degree 1072;
the other two expanded terms have degrees at most 1064 and 1056. Hence
N_top=He_top^8 is nonzero. The outer degrees 7 and 2 give 1081.

For the tight form, the deliberate cancellation in package 24 gives

    N_top = 9*2^48 i^48 (eta+zeta)^96 w^76 s^176
            (beta J)^648 (beta J-F)^16,

of degree 1060. It is nonzero for every beta>0. Multiplying the outer
leading forms of degrees 7 and 2 gives exact product degree 1069. The
transport shift preserves its leading form. Thus the system maxima are
1072 and 1060 respectively, uniformly for every authentic positive beta.

The finite checker multiplies all eight conjugates in an eight-dimensional
quotient algebra on 48 signed integer fixtures for each weight, compares the
old/new full circuits, tests transport substitutions, verifies every gate and
port is live, counts every operation, and performs full univariate degree
computations over two finite fields. These checks support the identities and
accounting; the mathematical proofs handle arbitrary witness sizes.

## 5. Rejected simplification: deleting the index equation

Deleting Nk=1 and its quotient h would reduce the supplied count to eleven,
but it is not justified by the present proof. The first Pell equation gives
k=2 psi_(2EY+1)(n). The congruence k=R+1 mod E supplied by Nk=1 is used
to derive 2n=R+1 mod E, and then the exact index relation 2n=R+1 after
recovering the main Pell index p=R. The strict ratio alone gives bounds on
n and p, not that needed congruence. It cannot simply replace Nk=1.
No eleven-variable claim is made.

## Reproduction

With Python 3.10 or later, from this directory run:

    python3 build_positive_refinements.py
    python3 check_positive_refinements.py

No network access or third-party Python package is required. Upstream inputs
are inert JSON/proof text, frozen with their hashes in `SOURCE_PINS.json`.
