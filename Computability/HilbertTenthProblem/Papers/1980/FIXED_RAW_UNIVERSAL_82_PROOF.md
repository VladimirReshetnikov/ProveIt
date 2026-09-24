# An 82-operation fixed-index universal certificate

For every recursively enumerable set S of positive integers, one can
effectively fix positive compiler numerals such that the system below
has positive integer witnesses exactly for raw inputs x in S. Its
complete straight-line certificate has **82 operations: 44 multiplications
and 38 additions/subtractions**, with **33 positive existential witnesses
and 21 equations**. Numerals and comparisons are free, but every
multiplication by a numeral is counted.

The improvement over84 changes the tableau geometry. Adjacent vertical
computation strips may have different time origins, giving cyclic
neighbor offsets1,h. The input endpoint is then at position x+2, so
its power has the fixed base B. Converting that position to a binary
exponent costs one multiplication; reusing the retained base-two Pell
congruence saves three operations. The net saving is two additions.

The [source and checker](../verification/explore_fixed_raw_universal_82.py)
and [receipt](../verification/explore_fixed_raw_universal_82.json) list
all82 instructions and all21 source residuals. The theorem is proved
mathematically and checked symbolically and on finite examples. It is
not a Lean formalization, and full astronomical Pell tuples are not
numerically materialized.

## 1. Fixed computational relation and its compiler

Use the [helical unary tableau theorem](EXPLORATION_HELICAL_UNARY_TABLEAU.md)
for a fixed semidecision machine for S. It has a fixed alphabet, four
initialization phases, exact deterministic updates, no head escape,
and a halted head on the last row. Horizontal row-boundary bits
propagate inside a vertical strip only. Every vertical boundary cell
has one constant symbol. This allows neighboring strips to be shifted
in time without introducing any invalid seam.

The normalized input has t+1 ones, where t=x+2; its head starts at
the right end and has a fixed first transition. The3-by-3 block lift
therefore has two fixed symbols: Start at the initial head and End at
the first unary cell. The helical theorem proves the exact equivalence
between halting and a cyclic word with offsets0,-1,-h, a unique Start
at0, and End at t<N. Completeness can choose a single rectangle with
both symbols unique. Soundness applies at arbitrary cyclic periods.

Use the native two-marker compiler from
[the84 proof](FIXED_RAW_UNIVERSAL_84_PROOF.md), unchanged. Enumerate End
as state0 and Start as state1. If the alphabet has k states and the
homogeneous clause mask has population m>=k, use m+2 Boolean positions
per cell, k genuine and the remaining positions ignored dummies.
With the fixed clause coefficients c_si and mask mu, choose

    R>=max((m+2)sum c_si,mu)+2, a power of two,
    B=R^(k+m+1)=2^d, CS=R,
    Ds=sum_(i<k)c_si*R^(k-1-i), s=C,R,Y,
    MC=B-1-sum_(j=2)^(m+1)R^j, MF=mu*R^(k-1).

The native cell is `sum_j z_j R^j`. End has code1; Start has code CS.
The low mask permits only positions2,...,m+1. The local field mask
tests homogeneous at-most-one, equal-occupancy, and forbidden-triple
clauses. The coefficient-mass argument gives field and cell values
at most B-2, with no inner or outer carry. The two mask populations
sum to d; MC is odd and MF is even.

All these numerals, including the bit width d, depend only on the
fixed machine and its finite relation. None depends on x, the time
or space of its run, or any existential witness.

## 2. All coordinates and equations

For raw x>0 supply33 strictly positive existential coordinates:

    q,P,C,v,J,align,F,alpha,z,Z,
    a,c,dmain,f,h0,i,j,k0,o,r,s,w,tau,eta,zeta,gamma,yaux,
    W,kappa,muP,delta,phiP,rho.

The source names `Jrep,zquot,d,h,k,ga,y_aux,mu,phi` respectively denote
`J,z,dmain,h0,k0,gamma,yaux,muP,phiP`. The fixed cell bit width d is
named `cell_bits` in the source and is distinct from dmain.

Use the counted expressions

    t=x+2, u=d*t, Lambda=q^2, D0=q^3,
    Scode=Z+qF, Mcode=(MC+q*MF)J,
    X=wD0, Yp=sD0, Delta=a^2+4a+3,
    A0=a+2, Uaux=j*c-(2r+1).

A0 is mathematical shorthand; no separate register for it is needed.
The seven outer equations are

    (B-1)J=q-1,                      P*v=q,
    (B-1)align=P-1,                  C+alpha+u=q,
    (DC+B*DR+DY*P)C=F+z*(q-1),
    r=(Lambda-Scode)*(Lambda-1)+Mcode,
    C=CS+Z+W.                                           (1)

The ten retained kernel equations are

    X*Yp^2*(X*Yp^2+1)*k0^2=tau*(tau+1),
    c=Yp*k0+eta,                     k0=eta+zeta,
    k0=r+1+h0*X*Yp,
    a=Yp*(X+1),
    dmain=X+a*c+gamma*(4a+3),
    dmain^2=Delta*c^2+1,
    (i*c^2)^2=Delta*(f^2-1),
    Delta*(f^2-1)*(Uaux^2-yaux^2)=1-yaux^2,
    Uaux=o*f-c.                                         (2)

The four input exponent equations are

    kappa=u+delta*(a+1),             c=kappa+phiP,
    muP^2=1+Delta*kappa^2,
    muP=W+a*kappa+rho*(4a+3).                           (3)

No additional inequality, power relation, digit test, marker predicate,
or period equation is imposed on the supplied coordinates. All such
facts are consequences of these21 equations and positivity.

## 3. Soundness in dependency order

The geometry, marker decomposition, and strengthened bound first give

    q>=P>=B>=16, 0<Z<C<q, 0<W<C<q, 0<u<q.

The fixed mask ranges and repunit equality give `0<Mcode<q^2-1`.
Positivity of r then gives `Z+qF<=q^2`. Since Z>0, F<q; combining
Z<q and F<q makes the packed field strictly below q^2. Thus
`q^2<=r<q^4`, exactly the preliminary bounds of the retained kernel.

The kernel proof applies at D0=q^3 before any square or power
interpretation is assumed. It recovers

    X=2^(2r+1), c=psi_A0(2r+1), a>X,
    q^3 divides binom(2r,r),
    q=B^N, P=B^h, 1<=h<=N.

The last two power forms follow from q^3|X, P|q, and the two repunit
congruences. No local-state interpretation has been used.

Apply the [fixed-base exponent proof](EXPLORATION_FIXED_BASE_EXPONENT_BRIDGE.md)
to (3). The norm and gap give `kappa=psi_A0(v0)` with
`0<v0<2r+1`. The first congruence gives `v0=u mod(a+1)`; both are
strictly below a+1, so v0=u. Then

    muP-a*kappa = 2^u mod(4a+3).

Both W and 2^u lie strictly between0 and4a+3, since

    2^u<2^q<2^r<X<a<4a+3, W<q.

Hence `W=2^u=B^(x+2)=B^t` exactly, and W<q gives t<N.

The inverse-packing identity and central-binomial divisibility now
give the two exact masks

    Z AND (MC*J)=0, F AND (MF*J)=0.

Every Z cell has its End and Start positions absent. CS inserts the
Start bit at cell0; W=B^t inserts the End bit at cell t. The cells
are distinct, so C=CS+Z+W is a pair of disjoint bit insertions. It
types all C cells without assuming genuine occupancy yet.

Let Rword and Yword be the cyclic shifts with digits C_(i-1) and
C_(i-h). Their exact integer formulas are

    Rword=B*C-kR*(q-1), Yword=P*C-kY*(q-1).

The actual field `Factual=DC*C+DR*Rword+DY*Yword` lies strictly
between0 and q-1. The upper bound is the compiler bound; positivity
uses DC*C>0 before occupancy recovery. Equation(1) makes F congruent
to Factual modulo q-1, and 0<F<q makes them equal.

The field mask enforces at-most-one occupancy and its propagation
under shift1. The inserted Start bit makes every occupancy1. Thus
all cells are genuine states, the fixed ternary relation holds, and
Start and End occur exactly once at0 and t respectively. Dummy bits
at either marked cell are harmless.

The helical unary theorem now reconstructs one genuine halting
computation on exactly x=t-2. Its unique Start prevents the selected
End from belonging to another strip's computation. This proves
soundness for every positive solution, without assuming N is a
multiple of h or that h is the physical width of the recovered strip.

## 4. Positive completeness

If x belongs to S, the normalized machine halts on t+1 ones with
t=x+2. Choose a sufficiently wide strip of physical width h and a
sufficiently long padded time period Htime. The helical theorem gives
N=h*Htime, one Start at0 and one End at t<N, with the required local
offsets1,h. Assign the genuine native cell codes with dummy0 and set

    q=B^N, P=B^h, W=B^t, Z=C-CS-W,
    J=(q-1)/(B-1), v=q/P, align=(P-1)/(B-1).

Since t>=3 and N>t, there are ordinary nonzero cells after removing
the two marker bits, so Z>0. Its mask vanishes and Z is even.
The actual field is positive and satisfies its mask. Every genuine
cell is at least1, so C>=J. The wrap quotients therefore satisfy

    kR>=1, kY>=floor(P/(B-1))=align>=1.

Taking `z=DR*kR+DY*kY` gives a positive transport witness. Native
cells are at most B-2, hence q-C>=J+1. Also

    J>=B^(N-1)>=B^t=2^u>u.

Thus `alpha=q-C-u>0`. All seven outer equations hold after computing
the actual packed r. The vanishing masks give population3dN and
central-binomial divisibility. This r is odd because Z and qF are
even while MC and J are odd; its strict bounds are unchanged.

The full fresh positive kernel construction retained from84 applies
at this actual r,D0, supplying all seventeen kernel coordinates in(2).
It is a new witness at the new index, not a numerical reuse of an
earlier packed witness. Finally set

    kappa=psi_A0(u), muP=chi_A0(u),
    delta=(kappa-u)/(a+1), phiP=c-kappa,
    rho=(muP-a*kappa-W)/(4a+3).

The fixed-base bridge proves integrality and strict positivity of all
five coordinates, including x=1. Consequently every one of the33
existential coordinates is positive and all21 equations hold.

## 5. Exact ledger and verification

| Part | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|
| Geometry, transport, masks, bound register and markers |12|12|24|
| Retained positive Pell kernel |25|18|43|
| Fixed-base raw-input bridge, including d(x+2) and stronger bound |7|8|15|
| **Complete source** |**44**|**38**|**82**|

The transport's fixed numeral is DC+B*DR. The input bridge reuses
both a and4a+3, already computed by the main kernel. Multiplication
by the fixed cell bit width d is included. There is no input-dependent
constant or omitted semantic test in the ledger.

The checker expands all source residuals, including the retained
acyclic correction by a preceding norm residual. It verifies that
all supplied fixed aliases depend only on compiler numerals. Component
receipts cover the native compiler, exact helical seam and input
semantics, base-two Pell identities, positive common outer/adapter
examples, and aliases that would occur if the raw-input bound were
deleted. The numerical bridge examples use moderate independent Pell
parameters; the full packed-kernel converse is proved mathematically.
No global optimality or numeral-size bound is claimed.
