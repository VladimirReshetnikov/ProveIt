# An 88-operation fixed-index universal certificate on positive raw inputs

For every recursively enumerable set S of positive integers, one can
effectively choose **fixed positive numerals**, independent of input x,
such that the system below has strictly positive integer witnesses
exactly when x is in S. Its complete straight-line certificate uses
**88 operations: 47 multiplications and 41 additions/subtractions**,
with **36 positive existential unknowns and 23 equations**. Fixed
numerals and equality comparisons are free. Multiplication by a fixed
numeral is counted.

This is a complete fixed-index raw-input result. The fixed numerals
depend effectively on an index for S, but remain the same as x varies.
It improves the preceding complete89 bound by one operation. The
construction uses a fixed unary-input marked tableau, a three-cell
overlap relation, and the retained positive Pell kernel. It does not
compile the varying input into its numerals.

The [executable source](../verification/explore_fixed_raw_universal_88.py)
and [receipt](../verification/explore_fixed_raw_universal_88.json) give
every primitive instruction, all source residuals, and their exact
equivalence. The theorem is a mathematical proof with symbolic and
bounded computational checks, not a Lean formalization.

## 1. Fixed compiler numerals

Normalize a semidecision machine for S as in
[the fixed unary tableau theorem](EXPLORATION_FIXED_UNARY_TABLEAU.md).
Its initial tape has t+1 consecutive ones ending under the head at
coordinate0, where t=x+2. The first transition writes an origin flag
and moves left. The machine never visits coordinates above0 and halts
exactly for x in S. Its fixed initial-row phase graph describes
`L^a I^t Q R^b`. This uses no input-specific phase or local rule.

Lift the radius-one relation to its finite alphabet of allowed3-by-3
windows. The exact overlap rule is a ternary relation on center, right,
and next. Its fixed Start symbol S3 is the initial-head window, and its
fixed End symbol E3 is the leftmost-input window. Put S3 at alphabet
index0 and E3 at its highest index k-1, with k>=2. Enumerating all
allowed windows and overlap triples is a finite effective computation
depending only on the fixed machine.

Use the [unique-start homogeneous compiler](EXPLORATION_UNIQUE_START_CYCLIC_67.md)
on this finite relation. It produces fixed positive numerals

    B=R^(k+m), DC, DR, DY, MC, MF,
    CE=2R^(k-1), E=DR+B*DY, Bm1=B-1.

Here R and B are powers of two, B>=16; CE divides B; the low mask
forbids Start's bit and allows m other Boolean positions; the field
mask tests the finite relation. Its two mask populations sum to the
bit width of B. All off-diagonal products are bounded by the fixed
coefficient-mass estimate, so there is no carry ambiguity. Ignored
dummy bits above all genuine state positions make the populations
balance even after excluding Start from the low field.

Only these fixed numerals enter the arithmetic schedule. Their size
is unrestricted under the agreed measure. They do not depend on x,
the computation length, the chosen torus dimensions, or any witness.

## 2. All coordinates and all equations

Supply raw input x>0 and the following36 strictly positive unknowns:

    q,P,C,v,J,align,F,alpha,z,T,
    a,c,d,f,h0,i,j,k0,o,r,s,w,tau,eta,zeta,gamma,yaux,
    W,kappa,mu,delta,phi,rho,L,beta,Tend.

The source uses `Jrep,zquot,Tmarker,h,k,Lend,betaend,y_aux,ga` for
`J,z,T,h0,k0,L,beta,yaux,gamma`, respectively. The k in the fixed
alphabet description is unrelated to the positive kernel coordinate k0.
Define the following expressions by the counted schedule, not by new
supplied coordinates:

    t=x+2, Z=B*T, Lambda=q^2, D0=q^3,
    Scode=Z+q*F, Mcode=(MC+q*MF)*J,
    X=w*D0, Yp=s*D0, Delta=a^2+4a+3,
    A0=a+2, u=j*c-(2r+1).

The seven outer equations are

    (B-1)J=q-1,                       P*v=q,
    (B-1)align=P-1,                   C+alpha+t=q,
    (DC+E*P)C=F+z*(q-1),
    r=(Lambda-Scode)*(Lambda-1)+Mcode,
    C=2+B*T.                                             (1)

The ten retained positive Pell equations are

    X*Yp^2*(X*Yp^2+1)*k0^2=tau*(tau+1),
    c=Yp*k0+eta,                      k0=eta+zeta,
    k0=r+1+h0*X*Yp,
    a=Yp*(X+1),
    d=X+a*c+gamma*(4a+3),
    d^2=Delta*c^2+1,
    (i*c^2)^2=Delta*(f^2-1),
    Delta*(f^2-1)*(u^2-yaux^2)=1-yaux^2,
    u=o*f-c.                                             (2)

The four new exponent equations are

    kappa=t+delta*(a+1),              c=kappa+phi,
    mu^2=1+Delta*kappa^2,
    mu=W+kappa*(A0-P)+rho*(Delta-(A0-P)^2).               (3)

The two endpoint equations are

    C=L+CE*W*Tend,                    L+beta=W.           (4)

There are no additional power, inequality, digit, period, uniqueness,
or halting conditions imposed on the witness. The proof derives them
from these23 equations and positivity alone.

## 3. Soundness in dependency order

First (1) gives `0<Z=C-2<C<q` and `0<t<q`. Before interpreting any
power, (4) gives `0<L<W<C<q`, since CE>=2 and Tend>0. Thus the strict
bound needed by the exponent decoder is already established without
assuming its conclusion.

Apply the complete unique-start67 soundness proof with the stronger
bound C+alpha+t=q. It needs only C<q, which is retained. The positive
packed index first bounds both fields and gives `q^2<=r<q^4`. The
unchanged43-operation kernel proves

    q=B^N, P=B^h, N>=2, 1<=h<=N,
    J0=2r+1, X=2^J0,
    a=Yp*(X+1), c=psi_(a+2)(J0).                         (5)

Mask decoding types Z and F. Since Z=B*T has zero unit digit, C=Z+2
has unit cell exactly Start2 with no dummy bits, and every other
cell forbids the Start bit. The actual local field is positive even
before occupancy recovery, because DC*C>0. Its bound below q-1 and
the transport congruence recover F exactly. Occupancy propagates along
the consecutive strides h,h+1 from the unit Start; every cell is
genuine one-hot, the fixed relation holds everywhere, and Start occurs
at no other cyclic index.

Next the [17-operation exponent argument](EXPLORATION_RAW_INPUT_EXPONENT_BRIDGE.md)
applies to (3). Its norm equation writes kappa=psi_(a+2)(u0). The
positive gap c=kappa+phi forces `0<u0<J0`; the first congruence gives
`u0=t mod(a+1)`. Since both indices are strictly below a+1, u0=t.
Put `H=Delta-(A0-P)^2`. The final congruence then gives
`W=P^t mod H`, while the retained kernel supplies

    P^t<q^q<=2^(q^2)<=2^r<X<A0<H.

Since `0<W<q<H`, this is the exact equality

    W=P^(x+2)=B^(h*t)<q, hence h*t<N.                    (6)

Finally (4) gives `floor(C/W)=CE*Tend`. All higher base-B digits and
all dummy contributions are divisible by CE. A genuine one-hot cell
is divisible by CE exactly when its genuine state is the highest
one, E3. Thus digit ht of C is E3. Its remainder is L, with 0<L<W.

We now have exactly the cyclic hypothesis of the fixed unary tableau
theorem: a unique Start at0, End at ht, ht<N, and the fixed ternary
rule on offsets0,-h,-h-1. The unique start prevents this endpoint from
belonging to another rectangle: reaching another rectangle's input
end would cross its own initial head, which has the same fixed Start
window. The reconstructed computation therefore begins with exactly
t I cells and its Q head, represents raw input x=t-2, and halts.
Consequently x belongs to S. Soundness never assumes N=h(h+1).

## 4. Strictly positive completeness

Suppose x is in S. The fixed machine halts on unary length x+3.
The tableau theorem supplies independently large dimensions h+1,h,
with one Start and End at index ht in the cyclic presentation of
length N=h(h+1), where t=x+2 and ht<N. Encode this word by genuine
one-hot cells with all dummy bits zero; take q=B^N, P=B^h, W=P^t.

The unique-start67 converse supplies all its positive coordinates at
the **actual new packed index** using low field Z=C-2, including the
full fresh positive fixed-minus Pell witnesses in (2). In particular
the index is odd; no witness from the previous packing is reused by
numerical identification. Its positive transport quotient follows
from every cell being at least2.

Change only the old bound slack to `alpha=q-C-t`. This remains
positive: with `J=(q-1)/(B-1)`, typed even cells satisfy

    C<=(B-2)J, q-C>=J+1,
    N-1>=ht>=t, J>=B^(N-1)>=B^t>t.

The exponent lemma constructs the five positive witnesses in (3):

    kappa=psi_A0(t), mu=chi_A0(t),
    delta=(kappa-t)/(a+1), phi=c-kappa,
    rho=(mu-(A0-P)*kappa-W)/(Delta-(A0-P)^2).

All quotients are integral by the proved congruences. The inequalities
t>=3, t<q<J0, and the kernel's size bounds make delta,phi,rho strictly
positive, including the smallest input x=1.

End occupies digit ht. Set `L=C mod W`, `beta=W-L`, and
`Tend=floor(C/W)/CE`. The unit cell2 and ht>=1 make L and beta
positive; the genuine nonzero End makes Tend positive. These solve
(4). All36 existential coordinates are therefore positive, and all23
equations hold for every halting input. The fixed numerals were chosen
before x and are unchanged by these witness choices.

## 5. Exact complete straight-line size

| Part | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|
| Unique-start cyclic source, including full Pell kernel |38|29|67|
| Raw exponent, including x+2 and strengthened bound |7|10|17|
| Endpoint and its remainder bound |2|2|4|
| **Complete system** |**47**|**41**|**88**|

The exponent instructions reuse `P-1` and the discriminant register;
`A0-P=(a+1)-(P-1)` avoids separately constructing A0. Start uniqueness
reuses the existing marker product Z=B*T and changes a fixed mask.
Neither saving deletes an equation or treats a variable expression
as a free numeral. The endpoint factor CE*W is explicitly counted.

The source mechanically expands each primitive register and compares
all23 residuals with (1)--(4). As in the retained kernel, one auxiliary
residual differs by an explicit multiple of an earlier norm residual;
the dependency is acyclic and preserves simultaneous zero sets.
All36 supplied existential names are distinct, and raw x is separate.

## 6. Evidence and limitations

Author and independent complete scoped proof/source reviews pass.
Fresh author and independent default runs exactly match the saved receipt.

The standalone component checks cover the full source, finite scalar
and cyclic mask cases, marker uniqueness, endpoint divisibility with
dummy bits, exponent congruences and strictly positive witnesses, and
fixed unary tableaux with varying inputs. The integrated checker also
constructs exact outer, endpoint and bounded Pell-adapter witnesses
on common q,P,C,W values, and rejects a different raw exponent at the
same endpoint. These adapter examples use moderate independent Pell
parameters; they do not materialize the enormous full packed-kernel
tuple. The general positive kernel converse is the retained proof.

No bound on compiler-numeral size, no improvement to the separately
Lean-formalized certificate, and no global optimality of88 is claimed.
The earlier direct q^2-scale deletion from89 remains unsound; the
present88 is a different construction with its full q^3 kernel scale.
