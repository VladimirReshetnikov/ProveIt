# A one-addition first-norm recoding loses the upper ratio bound

Replacing one positive ratio slack by a positive first-Pell-index gap
gives a literal **87=47M+40A** polynomial source. The saving is unsound:
the new source accepts **every positive ordinary input**, for every fixed
tuple of compiled constants. It therefore cannot retain the universal
compiler's representation of a set having a rejected input.

The [coupled88 source](complete75_coupled_index_linear88.md) maps into
the proposed source, but the inverse does not preserve positivity.
Sections 2–3 give a kernel counterfamily, and Section 4 proves failure of
the intended coordinate bijection even at unchanged accepted inputs.
Those facts alone would not prove a false input projection. Section 5
supplies the stronger result: an explicit outer congruence construction
extends to a full new 87 zero at **any** positive input, with all 19
supplied coordinates strictly positive.

This rejects the specified one-addition rewrite, not other 87-operation
constructions. The established complete
bounds remain 75 for a comparison system and 88 for a single polynomial.
The [source](complete75_first_norm_ratio_obstruction.py) and
[receipt](complete75_first_norm_ratio_obstruction.json) audit the actual
edited DAG and the component counterexamples below.

## 1. The exact source saving

Write the existing computed quantities as

    X=wq³, Y=sq³, E=XY, V=XY², P=2V+1,
    g=tau_gap, k=eta+zeta, c=kY+eta.

The current first factor is

    N0=g²+E(kY)(2g−k).                               (1)

It reconstructs the original positive Pell root as `tau=Vk+g`.
Replace the supplied positive coordinate zeta by a supplied positive
coordinate t, named `first_index_gap` in the checker, and use

    k=2g+t, c=kY+eta,
    N0=g²−E(kY)t.                                   (2)

The same node `twice_tau_gap=g+g` now feeds k directly. Delete the
subtraction `first_signed_gap=2g−k`, change k's second argument from
eta/zeta to `twice_tau_gap`/t, and change the final norm addition to a
subtraction. All other gates and all seven other unit factors are
retained. The exact certificate graph has 86 operations and one
comparison to 1; subtracting 1 gives the 87-operation polynomial.
There are still 19 supplied positive witnesses. Neither the ordinary
input nor a fixed compiler numeral is removed or made free.

For arbitrary integer assignments, the new polynomial is identically
the old polynomial after the substitution

    zeta_old=2g+t−eta.                               (3)

This identity does not imply positive-domain equivalence. In the old
domain, eta,zeta>0 impose

    kY<c<k(Y+1).                                    (4)

The new domain imposes only the first inequality. The new t instead
records a genuine first-Pell quantity: if N0=1 and

    tau=chi_P(n), k=2psi_P(n),

then the recurrence `chi_P(n)=P psi_P(n)−psi_P(n−1)` gives

    g=psi_P(n)−psi_P(n−1),
    t=k−2g=2psi_P(n−1).                             (5)

Every established complete88 zero has n=(R+1)/2≥2, so both coordinates
in (5) are strictly positive. Thus the forward map is valid. It does
not replace the missing upper inequality in (4).

## 2. Counterexamples within the kernel's external scale bounds

For every integer ell≥4, choose

    q=2^ell, R=3q+3, X=2^R, Y=q³,
    a=Y(X+1), A=a+2, Delta=A²−1, E=XY, H=4a+3,
    P=2XY²+1, n=(R+1)/2.

These satisfy exactly the external conditions used by the
[half-binomial42 theorem](pell_kernel_half_binomial42.md):

    q≥16, 3q+1≤R<q⁴, q³ divides X and Y.

Also R≡3 mod4 and popcount(R)=4. The latter is strictly smaller than
the old necessary threshold `3ell+2`.

Set

    c=psi_A(R), d=chi_A(R), k=2psi_P(n), tau=chi_P(n),
    g=psi_P(n)−psi_P(n−1), t=2psi_P(n−1),
    eta=c−kY,
    h=(k−R−1)/E, gamma=(d−X−ac)/H.                  (6)

Every coordinate in (6) is a strictly positive integer, but
`eta>k`, so the inverse zeta in (3) is negative. Here is a direct proof
of the crucial inequality, independent of the old ratio theorem.
The elementary Pell bounds give

    psi_A(R)>(2A−1)^(R−1),
    psi_P(n)≤(2P)^(n−1).

Since R−1=2(n−1) and `(2A−1)²>2PX`,

    c/k > X^(n−1)/2 > Y+1.                         (7)

The last inequality uses X=2^R>2(q³+1) and n≥2. Both this inequality
and `(2A−1)²>2PX` hold already from the displayed parameter choices;
no mask, population or floor identity is assumed.

The remaining positivity and divisibility are elementary. Since
P≡1 modE, the psi recurrence gives psi_P(n)≡n modE, so h is integral;
strict Pell growth makes it positive. The sequence

    E_A(j)=chi_A(j)−a psi_A(j)

has initial values1,2 and satisfies `E_A(j)≡2^j modH`. Thus gamma is
integral because X=2^R. Also `d−ac=2c−psi_A(R−1)>c>X`, so gamma>0.
Equation (5) gives g,t>0. Both Pell norms, the first-index equation,
the main exponent equation and the lower ratio equation now hold.

## 3. The full strong auxiliary equations still hold

The example retains the strong auxiliary norm and both congruences.
For the fresh A,c,R in (6), put

    m=2cR, f=chi_A(m), v=psi_A(m),
    i=Delta*v/c², T=i*c²=Delta*v,
    y=psi_T(R), U=chi_T(R)/T,
    j=(U+R)/c, o=(U+c)/f.                           (8)

These are precisely the canonical minus-sign auxiliaries, but their
integrality can also be checked directly. Expanding
`(chi_A(R)+c sqrt(Delta))^(2c)` shows that c² divides v: its first
odd coefficient contains `2c*c`, and every later odd term contains
at least c³. Hence i is a positive integer, and the Pell norm gives

    T²=Delta(f²−1).                                (9)

For R=2h0+1, write the integer polynomial
`chi_T(R)/T=Q_h0(T²)`. The standard recurrence identities are

    Q_h0(0)=(-1)^h0 R,
    Q_h0(1−A²)=(-1)^h0 psi_A(R).

They are proved in the retained
[half-parameter proof](../../1980/HALF_PARAMETER_PELL_92_PROOF.md).
Here h0 is odd. Since T is divisible by c² and
`T²≡−Delta=1−A² modf`, these identities give

    U≡−R modc, U≡−c modf.

Thus j and o in (8) are positive integers. Indeed T≥Delta*c²>A,
and Pell growth gives U>c>R. The remaining auxiliary equations are

    T²(U²−y²)=1−y²,
    U=jc−R=of−c.                                   (10)

They follow from the Pell norm and the definitions. No auxiliary norm
or sign constraint was weakened. Every modified kernel equality holds,
including the computed root definitions, while (7) violates the missing
upper ratio and popcount(R)=4 violates the former projection theorem.

The theorem-domain examples use parametrically defined auxiliary
towers. The checker does not pretend to materialize those towers.
It separately materializes a complete small modified-kernel example at
q=1,R=3, which is outside the external q≥16 domain:

    X=8, Y=1, a=9, c=483, k=68, tau=577,
    g=33, t=2, eta=415, zeta_old=−347, h=8, gamma=24.

All of (8)–(10) are evaluated exactly for that prototype. The general
proof, rather than this small example, supplies the valid-domain family.

## 4. Extra full-source zeros at unchanged accepted inputs

There is also a full-source failure of the intended coordinate
bijection. Begin with any positive zero of complete88 at its fixed
compiled constants and ordinary input x. Retain its q,R,X, all outer
coding coordinates and input index `u=2*cell_bits*x+b`. The established
theorem gives

    X=2^R, W=2^u, R≡3 mod4, q≥16,
    3q+1≤R<q⁴, u odd, 3≤u<2q<R.

Replace Y by q³, hence set s=1, and rebuild (6)–(8) at this retained R.
The proof above still applies: it used R≥3q+1 and R≡3 mod4, not the
special formula R=3q+3, except for the separate population example.
In particular eta>k and all new main/auxiliary coordinates are positive.

Rebuild the input at the same u with

    kappa=psi_A(u), mu=chi_A(u),
    delta=(kappa−u)/Delta,
    rho=(mu−a*kappa−2^u)/H, sigma=gamma−rho.          (11)

Odd u gives `psi_A(u)≡u modDelta`; strict Pell growth makes delta
positive. For the other two witnesses, put `G_j=E_A(j)−2^j`.
The recurrence gives

    G_0=G_1=0,
    G_(j+2)=2A*G_(j+1)−G_j+H*2^j.

It proves by induction that every G_j is divisible by H and
`G_(j+1)>G_j≥0` for j≥1. Thus rho=G_u/H and
`sigma=(G_R−G_u)/H` are strictly positive integers. The input norm,
its root definition, and `rho+sigma=gamma` follow exactly. Also
`psi_A(u)<psi_A(R)=c`, restoring the input-index gap.

All outer arithmetic is unchanged: it uses the retained q,R,X and
coding values, and none of its packing, mask or transport definitions
uses Y. In the full factor source, the two main norms, input norm,
auxiliary norm, strong norm, index unit, transport unit and coupled
linear unit therefore all equal1. This is a full positive zero of the
87-operation source at the same input. Its uniquely prescribed inverse
(3) has zeta<0, so it is outside the image of the old positive domain.

This establishes a strict enlargement of the witness relation whenever
the original compiled language has a member. This argument alone would
not establish an enlargement of the set of accepted inputs. The next
section provides the additional outer construction needed for that
stronger conclusion, including languages with no accepted inputs.

## 5. The complete modified polynomial accepts every positive input

Fix any constant tuple from the established compiler, including

    B=2^d, d≥4, 0<MC,MF<B−1, K0=DC+B*DR>0,

and its positive odd input offset b. All its other mask hypotheses and
fixed program constants remain unchanged. The construction below needs
only the displayed size hypotheses; it does not replace the actual
compiled constants by convenient toy numerals.

Fix any ordinary input x>0, and put

    u=2d*x+b, W=2^u.

Write d=d0*2^v with d0 odd. Choose an integer k0 sufficiently large, and
define

    ell=d*2^k0, M2=2^(v+k0), q=2^ell,
    J=(q−1)/(B−1).

The quotient J is integral since ell is a positive multiple of d. Require
M2≥4, ell>4d0, and ell≥v+k0; these hold for all sufficiently large k0.
In particular q≡0 modM2 and `ell=d0*M2`.

Choose the unique integer e in `[0,4d0)` satisfying

    e≡(q²+W)(q²−1)+(MC+q*(MF+B−1))*J  modulo d0,
    e≡3 modulo4.                                   (12)

The Chinese remainder theorem applies because d0 is odd. Next choose
the unique residue of C modulo ell satisfying

    C≡0 modulo d0,
    C≡e+W−MC*J modulo M2,                           (13)

and select its representative in the interval `W<C≤W+ell`. Set

    Z=C−W,
    F=(K0+2^e)*C,
    alpha=q−C−Z−F−2d*x.                            (14)

Then Z,F,C are positive integers. The bound e<4d0 is independent of
k0. Since C≤W+ell and Z≤ell, for a fixed constant K1 depending only on
K0,d0 one has

    C+Z+F+2d*x ≤ (K1+1)(W+ell)+ell+2d*x.

Thus q=2^ell exceeds this expression for every sufficiently large k0.
Choose such a k0, so alpha>0. No uniform size bound on the existential
witnesses is required.

Now use exactly the source's packed index

    R=(q²−Z−qF)(q²−1)+(MC+q*(MF+B−1))*J.            (15)

Modulo d0, the definitions give C≡F≡0 and Z≡−W, so (12) yields
`R≡e modd0`. Modulo M2, q≡0 gives

    R≡Z+MC*J≡C−W+MC*J≡e.

Together these prove

    R≡e modulo ell, R≡3 modulo4.                  (16)

The positivity in (14) also gives F+Z<q. Therefore, with
`G=q²−Z−qF`,

    2q−1≤G≤q²−q−1,
    0<(MC+q*(MF+B−1))*J<(q−1)(1+2q).

Consequently

    (2q−1)(q²−1)<R<q⁴−q³,
    3q+1<R<q⁴, R>u, R>3ell, R>e.                 (17)

Here q>W=2^u>u and q>ell, so the latter comparisons follow from the
first one. Define the positive integer X=2^R. Equation (16) implies

    X≡2^e modulo q−1.

Hence the exact positive transport coordinate

    zplus=1+C*(X−2^e)/(q−1)>1                     (18)

is integral. Substituting F from (14) gives precisely the source unit

    (K0+X)C+(q−F)−zplus*(q−1)=1.                  (19)

Equations (14) also give both computed definitions
`C=q−F−Z−alpha−2d*x` and `W=C−Z=2^u`. The repunit relation, packed
index, input width and transport are therefore all satisfied with the
original fixed constants and the unchanged ordinary input.

Finally set Y=q³, s=1 and `w=2^(R−3ell)>0`. Rebuild (6)–(8) and (11)
using this R. All their hypotheses follow from (17), R≡3 mod4, and
the odd index u<R. They supply every remaining positive coordinate,
including g,t,eta,h,f,i,j,o,y,delta,rho,sigma. In the actual edited
source the factors then have values

    N0=N1=N2=N3=N4=Nk=Nt=Lnew=1.

For the last factor, `k−hE=R+1` and `V=jc−R` give
`Lnew=V−jc+k−hE=1`. Thus the product minus1 is zero. This proves
the exact input projection

    { x>0 : the proposed87 polynomial has positive witnesses }
      = {1,2,3,...},                               (20)

for every fixed compiled constant tuple. In particular, compiling an
empty set or any other set with a rejected input yields false positives
for those inputs. The full witness tuple is specified by integer
formulas; its Pell towers need not be numerically expanded for the
existence proof.

## 6. Executable evidence and the next constraint

Run `complete75_first_norm_ratio_obstruction.py` with the repository's
SymPy-enabled Python; `--write-receipt` regenerates the stored receipt.
It checks 512 full-DAG coordinate identities, 416 positive first-norm
recodings, five main counterexamples within the q/R theorem domain,
60 exact positive input reconstructions, and every retained equation of
the materialized small strong-kernel tuple. It also builds 168 positive
outer tuples at d=4,...,24 and x=1,...,8, varying the admissible masks
and positive compiler numerals. Each is compared against the actual
edited source's repunit, packing and computed C,W registers; the
transport congruence is verified with exact modular exponentiation.
The general auxiliary extension and all-input theorem are proved above,
not inferred from these finite tests. Full compiler-sized Pell towers
are explicitly not materialized by the checker.

The saving is real at the arithmetic-graph level, but it erases the input
predicate. A successor using this coordinate must encode the upper ratio
again or add a different condition that excludes the constructed
all-input zeros. The positivity of the first-Pell gap cannot perform
that work.

The root's independent proof/source review and a separate independent
proof/source/default review both pass without findings. The root checked
both CRT reductions, the positive representative interval, the strict
packed-index bounds, the transport offset, the complete positive Pell
extension, and the literal source substitution. The separate review's
additional checks cover 168 compatible-mask CRT outer fixtures, 198 odd-quotient
recurrence identities, 30 fresh main Pell families and 240 positive input
reconstructions. These supplement the all-input proof and do not replace
its parametric construction of the full witness tuple.

A further independent native-controller review also passed the full strengthened
proof, source and default receipt check, including the outer CRT and positive
auxiliary restoration.
