# A 59-operation system in 16 positive unknowns

Pinned source: ProveIt `f0ae4e0991ca44a7bb4e5671d42e33d775e48035`.

This construction combines package 09's retained auxiliary coordinates
(`low_degree/retained16_system60.json`) with package 12's positive
transport-coordinate shift (`proofs/ORDINARY_BLANK_PROOF.md`, Section 7).
It improves the smallest stated arithmetic-system count from 60 to 59,
at the cost of using 16 unknowns instead of package 12's 15. It does not
improve the 67-operation frontier for a single equation.

All unknowns below range over strictly positive integers:

    J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma.

Use one entire admissible Start-only compiler tuple
`beta=B-1,K0,MC,MF`, with MF the shifted source mask. Package 11's T4
tuple can be used with its proved interface. No individual port may be
spliced from another tuple.

Define the following polynomial abbreviations, not additional unknowns:

    q=beta J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H, D=X+ac+gamma H,
    G=(q-1)(q-F)+alpha,
    R=G(q^2-1)+(MC+q MF)J,
    L=E kY, V=of-c, U=jc-R,
    I=ic^2, A0=Delta(f^2-1).

The seven equations are

    tau^2-L(L+k)=1,
    D^2-Delta c^2=1,
    A0(V^2-y^2)+y^2=1,
    k-hE-R=1,
    (K0+w)C=F+z(q-1),
    I^2=A0,
    U=V.

## Equivalence and the shift

The old retained-coordinate system has exactly the same equations except
its transport equation is

    (K0+w)C+(q-F)-z_old(q-1)=1.

The identity q-F-1=(q-1)-F shows that this old equation, after the
substitution z_old=z+1, is exactly the displayed new equation. Thus every
positive new solution gives a positive old solution. The old compiler
soundness theorem applies without alteration.

Conversely every positive old solution has C>0, q>1 and X=wq=2^R by the
inherited Pell/compiler argument. Its earlier outer bounds give R>3q;
in particular w>q>F. Therefore (K0+w)C-F>0. The old transport equation
rewrites as

    (K0+w)C-F=(z_old-1)(q-1),

so z_old>=2. Hence z=z_old-1 is strictly positive and gives a new
solution. The coordinate substitutions are inverse on positive zero
sets. This also proves existence equivalence, which is all that is
required for the consistency statement.

The old retained-coordinate system restores the same Pell auxiliary
conditions as the 15-coordinate quotient-eliminated system, as proved
in package 09's low-degree argument. Composing this result with the
fixed K215/compiler equivalence yields the ordinary mathematical theorem

    ZFC proves: no positive solution of this system iff Con(ZFC).

This is a formalizability statement based on the inherited compiler and
Pell proofs, not a newly checked Lean/Rocq theorem or a claim that the
finite algebra audit proves the complete semantic bridge.

## Exact counts

The original source uses 60 binary arithmetic gates. Its three transport
output gates are

    trans_part=innerC+(q-F),
    zrep=z_old(q-1),
    Nt=trans_part-zrep,

and it compares Nt with 1. The new source retains zrep, deletes
trans_part, replaces Nt by transport_rhs=F+zrep, and compares innerC
with transport_rhs. Consequently it uses 59 gates: 33 multiplications
and 26 additions/subtractions. Every operation and every input is live.
Comparisons are uncharged, following the repository's explicit convention.

The seven exact residual degrees are

    22,18,24,7,2,22,6.

The largest is 24, so the sum of their seven squares has exact degree
48 and 79 operations. That single equation is a supplementary tradeoff;
the new frontier result is the 59-operation system.

`build_retained59.py` performs an exact sparse-polynomial degree audit,
gate and input liveness checks, and 200 signed integer/rational checks
of the transport identity. It writes the complete circuit JSON and a
verification receipt. The copied base circuit and sparse polynomial
utility originate in package 09; their authorship and the repository's
license should be retained in the enclosing delivery.
