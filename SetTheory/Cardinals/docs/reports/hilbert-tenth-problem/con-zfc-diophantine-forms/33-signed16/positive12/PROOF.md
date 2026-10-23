# A 108-operation evaluator for the twelve-positive-variable polynomial

## Result and scope

This package gives a division-free arithmetic circuit for **exactly the fixed
polynomial** of `30-quartic31/positive/positive12_product.json` at ProveIt commit
`8c6eec9d19ef80538c8e61ff6e0180040583446a`, with the **same complete coefficient
tuple**, in 108 binary operations instead of 111. It has twelve strictly
positive variables and exact total degree 1081. Its three-equation system uses
104 operations instead of 107. A standard transport-coordinate shift gives an
existentially equivalent system with 103 operations.

These are evaluator and presentation improvements; the 108-operation circuit
and the earlier 111-operation circuit are identical as polynomials. No smaller
variable count or degree is claimed for this part of the package. The new
identities work over every commutative ring and are independent of the huge
coefficient values. The logical conclusion still uses the inherited blank-run
compiler and K215/refutation calibration, as the earlier construction does:

    ZFC proves: (there is no positive integer zero) iff Con(ZFC).

Neither side of this equivalence is proved here. No new end-to-end proof-
assistant certificate is claimed. The complete original twelve-variable proof
is preserved in `upstream/POSITIVE12_PROOF.md`, and its full old arithmetic DAG
is preserved alongside it, permitting exact before/after comparison.

## Fixed coefficients and variables

The fixed constants are the compact Wang943 tuple used by package 30:

    beta = 2^(5^10)-1, K0 = K, MC = MC, MF = MF_source.

The last constant is the **shifted** high mask. `COEFFICIENT_BINDING.json`
specifies the compressed byte payloads, decompressed SHA-256 checksums, aliases,
base, and immutable source recipes. The four constants are chosen as a whole;
none is an additional unknown. The local payloads are the same bytes as those
used for the signed-sixteen specialization in the parent package.

The twelve supplied variables, all strictly positive integers, are

    J,F,alpha,z,h,i,T,s,w,eta,zeta,t.

Every other symbol below is a polynomial abbreviation, not a quantified
variable. Define the common interface

    q = beta*J+1, Cw = q-F-alpha, X = wq, Y = sq^3, E = XY,
    k = eta+zeta, c = kY+eta, a = E+Y, H = 4a+3,
    Delta = a^2+H = (a+2)^2-1,
    ell = EkY, A = 1+ell(ell+k), G = 1+Delta*c^2, b0 = X+ac,
    R = ((q-1)(q-F)+alpha)(q^2-1)+(MC+q*MF)J,
    Nk = k-hE-R,
    Nt = (K0+w)Cw+(q-F)-z(q-1).

Next put

    I = ic^2, D = 1+Delta*I^2, Q = Delta*(D-1) = (Delta*I)^2,
    d = Q-1, v = cT, b = c+RD,
    Paux = QDv^2, Uaux = Qb^2, e = Paux+Uaux-1,
    Baux = 2Qvb,
    M = k(I^2+T^2), L = HM+1, W = b0+Ht.

The words `Paux` and `Uaux` distinguish these auxiliary expressions from the
final polynomial; the emitted optimized circuit does not evaluate them
separately because it only needs their products with H squared.

## Definition by a conjugate product

For formal square roots u^2=G, tau^2=A and f^2=D, define

    N = product over all eight choices u=±sqrt(G), tau=±sqrt(A), f=±sqrt(D)
          of [d(W-Lu-HM*tau)^2-H^2*e+H^2*Baux*f].

The product is invariant under each independent sign reversal and is an
integer polynomial in the twelve supplied variables. The root notation is
only a convenient definition; it adds no quantified variables or algebraic
number computation to the delivered equation.

The product equation and system are

    P12 = Nk*Nt*(1+N)-1 = 0;
    Nk=1, Nt=1, N=0.

## A complete scalar evaluator

All displayed operations below are ordinary integer additions, subtractions,
and multiplications. Powers with exponent two are single multiplication gates.
Shared expressions are reused.

    H2 = H^2,
    HQ = H2*Q,
    HP = HQ*(D*v^2),
    HU = HQ*b^2,
    n = (HM)^2*A,
    dn = d*n,
    He = HP+HU-H2,
    j = 4*HP*HU,
    W2 = W^2,
    L2G = L^2*G,
    Trace = 2*d*(W2+L2G),
    Kroot = d*(W2-L2G),
    Knorm = Kroot^2,
    AA = 2*(dn+He),
    constant = (dn-He)^2-j,
    at = Trace-AA,
    bt = constant-Knorm,
    coef = 16*dn*j,
    vr = at*(at*Trace+2*bt)-coef,
    ur = bt^2-at^2*Knorm,
    N = ur*(ur+Trace*vr)+Knorm*vr^2.

The emitted JSON provides an ordered binary-gate expansion of these expressions,
including the common interface. A source row has the form
`[new_register, operation, first_operand, second_operand]`. Integer operands
are literal constants; string operands are input ports or preceding registers.
The system specifies comparisons, and the product specifies one output to be
equated to zero. `build_and_verify.py` checks that every gate and input is live.

## Why this is the conjugate product

For a temporary indeterminate x, let

    C(x)=d(x^2+M^2*A)-e,
    F(x)=(C(x)^2+D*Baux^2-4*d^2*x^2*M^2*A)^2
          -4*C(x)^2*D*Baux^2,
    F_H(z)=H^8*F(z/H).

Expanding the four factors for tau and f shows that

    N = F_H(W-L*sqrt(G))*F_H(W+L*sqrt(G)).

The elementary identity

    (C^2+j-K)^2-4*j*C^2 = (C^2-K-j)^2-4*K*j

then gives

    F_H(z) = [(d*z^2)^2-AA*(d*z^2)+constant]^2-coef*(d*z^2).

Indeed H^2*e=He and H^4*D*Baux^2=j, by their displayed definitions. The
identity holds over the polynomial ring, so it introduces no division or
nonvanishing assumptions.

Set x_±=d(W±L*sqrt(G))^2. Their sum and product are Trace and Knorm. Modulo
the monic relation x^2-Trace*x+Knorm=0, the expression
x^2-AA*x+constant is at*x+bt. Squaring and subtracting coef*x leaves
ur+vr*x. Its product at the two roots is

    (ur+vr*x_+)(ur+vr*x_-)
      = ur^2+Trace*ur*vr+Knorm*vr^2
      = ur*(ur+Trace*vr)+Knorm*vr^2.

This proves the scalar evaluator as an exact polynomial identity, even when
quadratic roots coincide, a radicand is zero or square, or integer parameters
are signed. The semantic consistency equivalence is applied only to the stated
positive domain.

## The three saved operations

The source's 111-operation equation already implements the trace/remainder
identity above. Three elementary factorizations remove one multiplication each.
They do not merely preserve the zero set: they preserve the polynomial.

1. **Share H^2 Q.** The earlier evaluator separately computes
   Paux=Q(Dv^2), Uaux=Qb^2, HP=H^2 Paux, HU=H^2 Uaux. Given Dv^2 and b^2,
   this is four multiplications. The new evaluator computes HQ=H^2Q,
   HP=HQ(Dv^2), HU=HQb^2 in three. Paux and Uaux have no other consumers.
2. **Square after multiplying.** Earlier Knorm=d^2(W2-L2G)^2 uses four
   operations: subtract, two squares, multiply. Now
   Knorm=[d(W2-L2G)]^2 uses three: subtract, multiply, square. No other
   consumer needs d^2.
3. **Horner evaluation of the final quadratic.** Earlier
   N=ur^2+Trace*ur*vr+Knorm*vr^2 takes seven binary operations.
   N=ur(ur+Trace*vr)+Knorm*vr^2 takes six.

All multiplications by fixed numerals, including 2,4,16, are charged. System
comparisons and reuse are free, exactly as in the source metric. The counts are

| Presentation | Unknowns | Equations | Exact/max degree | Multiplications | Add/subtract | Total |
|---|---:|---:|---:|---:|---:|---:|
| Unshifted system | 12 positive | 3 | 1072 | 63 | 41 | 104 |
| Product equation | 12 positive | 1 | 1081 | 65 | 43 | 108 |
| Shifted system | 12 positive | 3 | 1072 | 63 | 40 | 103 |

The unshifted product count is the system count plus four operations:
Nk*Nt, N+1, their product, and subtracting 1.

## Logical equivalence and the inherited proof boundary

Because the product polynomial is unchanged, the complete mathematical proof
in `upstream/POSITIVE12_PROOF.md` applies word for word. Its main steps are
recorded here to make the imported obligations explicit.

First N is a square modulo 4: writing Trace=2x0 gives
Knorm=x0^2-4d^2W^2L^2G, and therefore
N ≡ (ur+x0*vr)^2 modulo 4. At P12=0, all three factors are integer units;
1+N cannot be -1, so N=0 and Nk=Nt=epsilon with epsilon=±1. The system has
epsilon=1 immediately. The inherited transport/mask theorem gives

    Cw≥0, q≥16, X≥q, Y≥q^3, 3q<R<q^4-2,
    k=R+epsilon+hE>E, kY<c<2kY.

These are properties of the selected **whole compiler tuple**, not consequences
of arbitrary four coefficient substitutions.

The weight M=k(I^2+T^2) gives the uniform estimate

    2(v*sqrt(D)+b)
      < min(M*sqrt(A), M*(sqrt(G)-sqrt(A))).

Every complex root x of F satisfies |x|<M*sqrt(G). If N=0 and G were not a
square, quadratic conjugation would provide two F-roots separated by
2L*sqrt(G)/H>2M*sqrt(G), contradicting this bound. Hence the recovered main
root is an integer. Positivity of W and the same bound force its positive
sign. The rational inner root yields rational roots of the integer radicands
D and A, hence integer roots. The auxiliary equation has the form

    S^2 V^2-(S^2-1)y^2=1,  S=Delta*I≥2, V integer, y rational.

The inherited rational Pell saturation lemma makes y an integer. Consequently
the main congruence modulo H recovers an integer gamma; the main root bound
makes gamma positive. The signed-quotient compiler interface then reconstructs
the canonical positive witness, forces epsilon=+1, and extracts a blank K215
halting run. The K215 refutation calibration identifies that with a finite ZFC
refutation. Conversely a canonical compiler witness gives

    t=gamma+M*bmain+M*tau+y>0,

which makes a conjugate factor vanish and gives Nk=Nt=1. Thus the source
polynomial, and identically the new polynomial, has a positive zero exactly
when a finite ZFC refutation exists. Negating gives the consistency equivalence.

The full inequalities, integrality argument, signed-quotient handling and
source dependencies are provided in the preserved source proof. They have not
been replaced by numerical testing. The present change adds no new compiler
hypothesis and no coefficient rebinding.

## The 103-operation shifted system

Use z for the old z coordinate minus one. The equality Nt=1 becomes

    (K0+w)Cw = F+z(q-1).

Indeed substituting z_old=z+1 into Nt-1 gives exactly the difference of these
two sides. They can be compared directly. Evaluating the old Nt requires two
additions/subtractions after its products are known, while the new comparison
requires only the addition F+z(q-1). The other two equations are unchanged.

A positive shifted solution gives an unshifted one by z_old=z+1. Conversely,
a positive unshifted solution reconstructs the authentic compiler, where
Cw>0 and wq=2^R with R>3q. For q≥16 these imply w>q>F. Thus

    (K0+w)Cw-F = (z_old-1)(q-1)>0,

so z_old≥2 and z=z_old-1 remains strictly positive. The shift therefore
preserves existence in the required domain. This completeness argument uses
the compiler only after reconstruction and does not assume its stronger
bounds prematurely. This standard coordinate shift is also proved in wave-4
package 26, `proofs/RATIO12_PROOF.md`, Section 8.

## Exact degrees

Polynomial identity preserves the earlier exact degree. For an explicit
certificate, the base degrees with coefficients fixed are

    deg(c)=5, deg(H)=6, deg(Delta)=12, deg(I)=11,
    deg(D)=34, deg(Q)=deg(d)=46, deg(A)=deg(G)=22,
    deg(b)=38, deg(M)=23, deg(L)=29, deg(W)=11.

It follows that deg(He)=134, deg(dn)=126, deg(Trace)=126,
deg(Knorm)=252, deg(at)=134, deg(bt)=268, deg(vr)=402, and deg(ur)=536.
The highest term of ur is He_top^4; the other two summands in the original
quadratic expression for N have degrees at most 1064 and 1056. Hence
N_top=He_top^8 is nonzero and deg(N)=1072. Nk and Nt have nonzero leading
forms of degrees 7 and 2, so deg(P12)=1081. This holds for every valid
positive beta, not merely for sampled numerical values. The transport shift
does not change the leading residual degrees.

## Reproduction and verification limits

Run `python3 build_and_verify.py` from any current working directory. The
standard-library-only script rebuilds all three DAGs next to itself, checks
source hashes and all four actual coefficient payloads, and verifies the live
operation counts. For each of two primes it tests 60 signed assignments with
random coefficient ports and 60 with the actual coefficient residues. Each is
checked against both the pinned old polynomial and an independently coded
8-dimensional conjugate product. The transport-coordinate identity is checked
as well. No imported source program is executed.

`VERIFICATION.json` records the checks. The universal arithmetic identities
are proved above; finite checks detect transcription errors. Neither these
checks nor the coefficient hashes prove the unbounded compiler theorem or
consistency. The exact new artifact is the bound arithmetic DAG, with its
fixed coefficient recipe and mathematical proof.
