# Current thirteen-variable graph: exact metric proof

The object measured is the 88-row `polynomial.json`, with positive integer
unknowns J,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma in that order. Its four integer
leaves are beta,K0,MC,MF. The graph is copied gate for gate from the literal
Lean evaluator `NativeAdaptiveGraph.core`; no substitution is applied to
an unknown. The fourth port is already shifted. This document separates
the exact finite metric proof from the accepted external zero-set theorem.

## Paid schedule and polynomial binding

Each row performs one binary operation on integer leaves, unknowns or earlier
rows. There are48 multiplications,23 additions and17 subtractions, totaling88.
The terminal node is P13. Reverse traversal from it reaches every producer,
all13 unknowns and all four coefficient leaves. Named cuts do not introduce
operations, divisions, exponentiation gates or additional unknowns.

The restricted source parser reads all17 Lean aliases,88 paid rows and26
record fields, and the actual `.out` value projection. It compares the whole
ordered graph, not only residual formulas. The accepted `value_map` and
`eval_polynomial` theorems identify this evaluator with its integer polynomial.
The new JSON updates coefficient metadata only. The historical metadata's
degree assertion is not used by the degree algorithm.

## Degree computation and its cancellations

Work in the polynomial ring over integers on the13 unknowns and four formal
ports. Grade unknowns by1 and ports by0. A sparse monomial stores all17
exponents, so the formal coefficient polynomials are retained exactly.
For a sum of different degrees the larger leader survives; equal-degree
leaders add with the correct sign. Products multiply their complete leaders
in an integral domain. A zero leading difference requires a separate exact
polynomial calculation. The auditor finds exactly three such differences.

For A0 the actual graph gives

    Z=M*ell+h,
    h=M*(k+r)+Y*qm-Bt*W*q3,
    A0=Z^2-M^2*(1+ell*(ell+k)).

Expansion and cancellation give the full identity

    A0=2*M*ell*h+h^2-M^2*ell*k-M^2.

Here M*ell has degree8 and h degree7. This removes the degree16 part and
produces degree15. Both the literal residual and the rewritten expression
are independently expanded and compared as complete sparse polynomials.

For A1 set v=U*X+H*shift. The literal cuts give Delta=a^2+H and
Dstar=U*a*c+v. Therefore

    A1=Dstar^2-U^2*(1+Delta*c^2)
      =2*U*a*c*v+v^2-U^2*H*c^2-U^2.

U*a*c has degree7 and v degree6. The canceled degree14 leaves degree13.
Again the finite comparison is a complete polynomial identity.

The third cancellation is graph gate g81. Because the literal y=V+u,

    g81=y^2-V^2=2*V*u+u^2.

V has degree6, hence this gate has degree7, despite nominal degree12.
The computation uses the full identity, not a three-layer truncation which
would miss its surviving term. No other gate loses its computed top part.

Put

    q0=beta*J, k0=eta+zeta,
    R0=q0^3*(q0-F),
    Bt0=(K0*q0+X)*(q0-F-alpha)-q0*F.

The independently specified complete terminal factor leaders are

    L0=-2*q0^8*k0^2*X*Y^2*Bt0,
    L1=8*q0^2*k0*X^2*Y^4*(q0^2*Y*gamma+R0),
    La=2*X^2*Y^2*f^4*u*R0,
    Ls=i^2*k0^4*Y^4.

Their degrees are15,13,13,10. They are compared against the actual gate
leaders of F0=1+A0, F1=1+A1, Fa and Fs. The output
Fs*(Fa*(F0*F1))-1 has the complete leader L0*L1*La*Ls of degree51.
The certificate stores its full coefficient list, not only selected terms.

Consider the unknown monomial

    J^15 F eta^7 X^6 Y^13 f^4 i^2 u gamma alpha.

The gamma factor forces the q0^2*Y*gamma summand in L1. The additional X
and alpha force the -alpha*X summand in Bt0. The F factor then forces -F
in R0. The chosen eta term in k0^7 has coefficient1. Combining the scalar
factors gives exactly -32*beta^15, with no dependence on K0,MC,MF. The
auditor also extracts this coefficient from the complete output leader.
Since the actual beta=2^94517-1 is strictly positive, this coefficient is
nonzero. Thus the specialized polynomial has exact degree51.

Every gate's specialized degree is checked too. Substitute the four whole
current integers into its complete formal leader modulo a stated prime.
After collecting equal unknown monomials, the certificate supplies a nonzero
coefficient and the complete reduced leader. Such a residue is a rigorous
integer nonzero certificate. Combined with the formal upper bound, it proves
the exact specialized degree. No random evaluation is used for degree.

## Exact current table and coefficient tuple

The full715-digit numeral is parsed from DecimalMachine215. All430 actions
are recomputed using its signed target subtraction, modulus216, mixed-radix
prefix and flag decoder. They are compared entry by entry with the kernel-
checked action cache. The raw target -1 at input125 remains halt215.

Both target sets are derived from these actions. The rail formula counts
targets strictly below q, including the empty q=0 interval, and agrees at
all432 cached values. The actual table constructors are checked against
their frozen source shapes. They produce all942 distinct indexed tiles,
with true west/east bounds256 and north/south bounds512. No color orientation
is inferred from a descriptive slot name.

The selector weight of a tile is

    1+2^10*(1+west+2^8*north+2^17*east+2^25*south).

Start remains physical0. The other941 distinct weights are sorted in
descending order and all941 printed floor ranks are independently computed.
Every physical index/weight pair is compared with the full accepted Lean
PhysicalData list. Initializer abstract928 is physical504. The34 control
entries have true west/north/east/south positions978/960/969/942 and powers
10/18/27/35. Every coefficient is doubled. The complete3297-entry array,
including every zero, is compared with the frozen2011 array.

Writing rho=2^47 and G(n)=sum_{j<n}rho^j, the reconstructed integers are

    beta=rho^2011-1,
    K=rho^18+rho^1004+rho^2020
        +sum_e c[e]*rho^(1005-e),
    MC=beta-G(951)-rho^960*G(26)-rho^1004,
    MF=beta+8*G(917)-4+(2^45-4)*rho^1005
        +rho^960*G(9)+rho^987*G(8)+rho^1004.

The source-owner shapes bind all exponents, control directions, scaling,
support endpoints and the fourth-port shift. Every nonzero reflected index
is at most1005. Mask reconstruction also uses the explicit2011 radix digits
and978 support positions; both routes agree. Whole integer records and every
decompressed byte agree with the current certificate and accepted page.
The minimal unsigned sizes are11815,11868,11815,11815 bytes:47313 total.
The source high mask is shifted by beta exactly once.

## Dependence, controls and logical scope

For each of the13 unknowns the auditor supplies two positive integer input
tuples differing only in that unknown, with different exact output residues
at the actual whole fixed ports. Equality of integer polynomials would imply
equality of every residue, so this proves genuine dependence. Four analogous
port perturbations prove formal coefficient dependence. These witnesses
do not test or prove the positive-zero characterization.

Negative controls alter actual gate operators/operands, alias indices, record
fields and the output projection, as well as graph count/degree/domain data,
dead gates and rational leaves. Other controls alter the actual mask and
kernel source shapes, nonzero and zero coefficient entries, full port bytes
and the fourth-port shift. All must be rejected using explicit guards that
remain active under Python optimization.

The separate accepted NativeAdaptiveCurrent2011 theorems establish positive
zero existence iff not DiophantineConsistency.ConZFC, and no positive zero
iff that exact consistency predicate, for this same current tuple. The
generic interface retains all port/mask hypotheses; the current specialization
discharges them. This packet links to those source pins and accepted evidence;
it does not recompile Lean or claim a kernel totalDegree theorem.

The historical13/88/51 form used a larger tuple. This is its exact current
47313-byte specialization with the already accepted external Lean endpoint,
not a new global dimension/operation/degree record or an internal HA/PA/ZFC
derivation. Lower-operation and lower-variable tradeoffs remain separate.
