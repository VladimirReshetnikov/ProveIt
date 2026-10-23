# A 60-operation quadratic system and a 125-operation quartic

## Result

Relative to package 30-quartic31 at ProveIt commit
`8c6eec9d19ef80538c8e61ff6e0180040583446a`, the following construction retains
31 strictly positive variables and 22 quadratic equations, and reduces the
equality-comparison circuit from 65 to 60 binary operations. The sum of the
22 squared residuals is a quartic evaluated in 125 operations, instead of
130. Every binary addition, subtraction, and multiplication is charged,
including multiplication by a fixed numeral. Comparisons and reuse of an
already computed register have the same zero cost as in the source.

The improvement is five additions/subtractions, with the same 33
multiplications for the system and 55 multiplications for the quartic. It
does not improve the 59-operation frontier for higher-degree systems, the
67-operation frontier for arbitrary-degree single equations, or the number
of variables. It improves the explicit arithmetic size at the currently
available 31-positive-variable quartic point.

## Exact equations

The positive variables remain

    J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma,
    N,E,P,c,a,X,D,C2,L,F2,V,g,I,Baux,Delta.

Use the complete new 121 by 8801 four-port compiler tuple beta,K0,MC,MF.
`INSTANCE.json` binds these names to beta,K,MC,MF_source respectively in
`../coefficients/payloads`. The complete adapter theorem is
`../coefficients/COEFFICIENT_PROOF.md`; MF_source is already shifted by B-1.
The algebraic identities below hold with all four ports symbolic. Historical
coefficient metadata inside the byte-preserved upstream files remains source
evidence and does not override the active instance.
The coordinate z here is shifted: z_old=z+1. Define the abbreviations

    q=beta J+1, k=eta+zeta, H=4a+3, C=q-F-alpha,
    U=L+1, Y=a-E, Q=c-eta, T=P-k, R=jc-V.

Here R is quadratic, and it only occurs additively in the equations below.
None of these expressions is an additional unknown. The equations are

    U=q^2,
    N=qU,
    X=wq,
    Y=sN,
    E=XY,
    Q=kY,
    T=EQ,
    tau^2=PT+1,
    D=X+ac+gamma H,
    Delta=a^2+H,
    C2=c^2,
    D^2=Delta C2+1,
    k=R+1+hE,
    R=(q-F)(N-q)-CL+(MC+q MF)J,
    (K0+w)C=F+z beta J,
    F2=f^2,
    V=of-c,
    g=y^2-V^2,
    I=i C2,
    Baux=I^2,
    Baux=Delta(F2-1),
    y^2-Baux g=1.

Let r_1,...,r_22 be the left sides minus the right sides. The ordinary
polynomial Q60=sum(r_i^2) has a zero over positive integers exactly when
the displayed system does. All the residuals have degree exactly two.
The coefficient of tau^4 in Q60 is 1, since tau occurs in no other residual;
thus the degree is exactly four on every admissible fixed coefficient slice.

## Zero-set equivalence

Ignoring the transport shift for a moment, the first four changes merely
reorient existing equations so that intermediate expressions are reused.
They are literal polynomial identities, valid for all integer assignments:

1. L=q^2-1 is rewritten L+1=q^2, and its L+1 is reused in N=q(L+1).
2. a=E+sN is rewritten a-E=sN; the same a-E already occurs in E=X(a-E).
3. c=k(a-E)+eta is rewritten c-eta=k(a-E); the same c-eta occurs in the
   defining equation for P.
4. P=E(c-eta)+k is rewritten P-k=E(c-eta); the same P-k occurs in the
   first Pell norm tau^2=P(P-k)+1.

The source transport equation is

    (K0+w)C+(q-F)-z_old(q-1)=1.

Since q-1=beta J, substituting z_old=z+1 gives exactly

    (K0+w)C=F+z beta J.

A new positive solution therefore gives a positive old solution simply by
increasing z by one. Conversely, the inherited Pell/compiler argument for
the source system proves C>0, F<q, X=wq=2^R, and R>3q on every source zero.
In particular w>q>F. The source transport equation then gives

    (z_old-1)(q-1)=(K0+w)C-F>0.

Hence z_old>=2 and z=z_old-1 is strictly positive. This gives a bijection of
positive zero sets. The positivity step uses the already established Pell
consequences; it is not inferred from a polynomial identity alone.

Composing this bijection with the complete new coefficient adapter, the source
compiler and calibrated K215
theorems gives the ordinary mathematical assertion formalizable in ZFC:

    ZFC proves [Q60 has no positive integer zero] iff Con(ZFC).

This is not a consistency proof and is not a new end-to-end Lean/Rocq
formalization.

## Reproducible audit

Run `python3 build_quartic60.py`. Only the Python standard library is needed.
The script reads the literal `upstream/quartic31.json`; it does not execute
upstream code. It checks exact sparse-polynomial equality between every new
residual and its source residual after z_old=z+1, treating all four compiler
ports as independent symbols. All 22 residuals agree exactly, without even
needing a sign reversal. It expands Q60 to 299 symbolic terms, checks all
degrees and the tau^4 coefficient, audits every gate/input for liveness,
and regenerates the complete circuit and sparse-polynomial JSON files.

The expanded 299-term count treats compiler-port exponents as symbolic
coordinates; accidental coefficient coincidences on a particular numerical
slice can reduce that count. The quartic degree certificate is uniform.
Finite algebra checks do not verify the underlying compiler or consistency
statement. They verify exactly the local identities and advertised metrics.

## Source files

- `upstream/quartic31.json`: literal package-30 parent polynomial data.
- `upstream/quartic31_system.json`: literal 65-operation comparison circuit.
- `upstream/quartic31_circuit.json`: literal 130-operation SOS circuit.
- `upstream/30-quartic31/arithmetic/QUARTIC31_PROOF.md`: the parent proof.
- `upstream/27-wave4/operations/upstream/RETAINED59_PROOF.md`: source
  justification for the positive transport-coordinate shift.

The refactor is an identity with all four coefficient ports symbolic. Its active
fixed specialization changes all four ports together using the complete new
adapter. The source files listed in `SOURCE_PINS.json` have been checked against
their Git blob identifiers and restored to exact source bytes; their working
download copies had one added terminal newline, which has been removed.

