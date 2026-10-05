# Three nonnegative selected forms per signed relator slot

For the new uniform recipe assume r>=1. Each generic relator slot can
use three selected input words in place of the four selected coordinates
H4,H5,H6,H7. The two inverse slots
share two newly computed input forms, and each also selects the positive
subset mass S4=H4+H5+H6+H7. Thus one relator pair uses six selected
words instead of eight. A stronger weighted global bound and an explicit
simultaneous no-carry induction justify the changed interface.

This is a positive projection theorem for a specified finite relation,
with local arithmetic accounted below. It is not a whole emitted source,
same-supplied-tuple substitution, numerical universal gate bound or
unconditional linearity rule for AND. Root requested the formed-input
continuation and independently identified the weighted-bound margins.

## 1. A common integral pair of signed input forms

For fixed P=[p,q;s,t] in SL2(Z), retain the representation S(P) of the
frozen relator-plane note and its decoder

    C=[1,0,0,-1;1,1,0,-2;2,0,1,-4].                       (1)

The right vector w0=(2q,p-t,-2s)^T satisfies S(P)w0=w0 and
S(P^-1)w0=w0. Direct multiplication gives the same pt-qs=1 cancellations
as the previously proved left-normal identity. If P is noncentral,
normalize w0 to a primitive integer vector w.

Apply the elementary integer-plane construction of the frozen
`positive7_relator_plane_action_pascal.md` to rows orthogonal to w.
Explicitly, after a fixed coordinate permutation make w1 nonzero,
let g=gcd(w1,w2)>0 and choose a*w1+b*w2=g. The two row vectors

    u=(w2/g,-w1/g,0), v=(-w3*a,-w3*b,g)                   (2)

form an integer basis of the lattice of rows orthogonal to w. For a
row(x,y,z) in that lattice, the integer coefficients are b*x-a*y and
z/g, the latter integral because gcd(g,w3)=1. Undo the fixed coordinate
permutation in u,v. Therefore there are fixed integral3-by-2 matrices
E_+,E_- such that

    S(P)-I3=E_+ [u;v],
    S(P^-1)-I3=E_- [u;v].                                 (3)

For P=I2 or -I2, use u=(1,0,0), v=(0,1,0) and E_+=E_-=0.
This gives one uniform interface without any zero-normal division.

Put ell_1=u C and ell_2=v C, four-entry integer rows. On the four
history words define L_j=ell_j H_(4,5,6,7). The same two signed forms
work for the positive and inverse slots. All divisions, Bezout choices
and matrix coefficients in(2)--(3) are fixed integer preparation; none
is a runtime operation or an added existential relation.

For each relator and j=1,2, choose

    lambda_j=1+max(0,-min_i ell_(j,i)),
    a_(j,i)=ell_(j,i)+lambda_j.

Every a_(j,i) is a positive integer. Define the computed words

    S4=H4+H5+H6+H7,
    A_j=sum_i a_(j,i) H_i = L_j+lambda_j*S4.                (4)

The A_j are formed once per relator and shared by its two sign slots.
Let M>=1 be the maximum of all a_(j,i), taking M=1 if there are no
relators. On every positive supplied history assignment,

    0<S4<=S=sum_(i=1..7) H_i,
    0<A_j<=M*S4<=M*S.                                    (5)

These are inequalities of whole integers before binary typing, not
assumptions about the digits of H_i.

## 2. The changed finite relation and pretyping order

Use the same fixed strictly positive weighted7 alphabet, common column
sum Cmass and ordinary input z(x). Let m=8+2r and choose a fixed power
of two

    K>max(Cmass,m,3M+1).                                  (6)

The input loader, positive history words, shared endpoint convention,
selector hats, positive height slack and the complete prescribed native
AND component remain as before. Let D=S0+height_slack, B=K D,
J=sum_sigma(Shat_sigma-1), P=(B-1)J+1 and mu=(D-1)J.

When r=0 there are no relator selections to replace: retain the preceding
source, with no new S4 producer or claim of its liveness. All new recipe
and local producer counts in this note refer to r>=1.

The eight paired letters keep their52 selected raw-coordinate fields.
For each relator sign sigma, supply exactly three positive output hats,
whose nonnegative unhats are Z_sigma,0,Z_sigma,1,Z_sigma,2. Their
selection lanes are

    (S4,(B-1)S_sigma,Z_sigma,0),
    (A1,(B-1)S_sigma,Z_sigma,1),
    (A2,(B-1)S_sigma,Z_sigma,2).                           (7)

All other selector, paired-selection, aggregate-range and D-power lanes
are unchanged. Let Ztot be the sum of these retained raw selected outputs.
The number of selected fields is N=52+6r, and the number of native lanes
is ell=m+N+2=62+8r. Replace the old global comparison by

    M*S+Ztot+g=P,                                         (8)

where g is one positive supplied slack, as before. In positive hats its
equivalent offset is N, not the old selected-field count.

Every raw unhat is nonnegative. Since S>=7 and M>=1, equation(8) forces
P>1, J>=1, B<=P, S<P, Ztot<P and M*S<P. By(5), every formed input
in(7) lies below P; so do all original H_i. As in the frozen geometry,
D,J,S_sigma,mu and (B-1)S_sigma lie below P. Every selected output is
below P by(8). All lane inputs and outputs are nonnegative before the
native equations, and the computed packs are nonnegative on every
positive supplied assignment, even away from(8).

Pack the ell lanes at radix P and bind the same complete prescribed
AND component at scale P^ell. Its theorem first gives dyadic P, the
last lane gives dyadic D, and(6) makes B dyadic. The repunit identity
then gives P=B^n, J=sum_(j=0)^(n-1) B^j with n>=1. The selector checksum
is carry-free because m<B, so exactly one letter is selected at each
cell. The retained selection lanes prove selection of the canonical
base-B digits of H_i,S4,A1,A2. They do not yet identify digits of a
formed input with a linear expression in the separate history digits.

## 3. Reconstructing the relator action, with every subtraction paid

For a relator sign sigma compute

    T_sigma,1=Z_sigma,1-lambda_1*Z_sigma,0,
    T_sigma,2=Z_sigma,2-lambda_2*Z_sigma,0.                  (9)

Append E_sigma*(T_sigma,1,T_sigma,2)^T to the existing three original
relator increment accumulators. The paired-letter block is unchanged.
Apply the same common-baseline positive7 postprocessor, or its fused
recurrence version. Keep all seven comparisons

    B V_i=H_i+P F_i-z_i(x),                               (10)

and the same endpoint equality, possibly implemented by F7=F1.
All expressions here are linear in H and in the raw selected words,
with fixed integer coefficients. Their computed intermediates may be
signed without changing any supplied positive domain or native input.

At a cell where the canonical formed digits agree with(4), equation(9)
recovers selection of L1,L2. Equations(3) then give the exact original
relator difference (S(P^sign)-I) C H_(4,5,6,7) at that cell. The next
section proves the needed agreement without assuming it in advance.

## 4. Simultaneous recovery of states and formed-input digits

At a full positive zero, write every H_i in its canonical n-digit
base-B expansion. Also write the formed inputs S4,A_j canonically;
Section2 proved that all these whole words lie in[0,P). The selected
outputs have the corresponding canonically extracted digits. The
computed V_i can therefore be expanded as a formal linear combination
of these digit streams. Its coefficients need not be canonical digits
away from the recovered prefix; equation(10) remains an exact integer
equality of the resulting polynomials in B.

At cell0, reduction of(10) modulo B fixes each H_i(0)=z_i(x), since
both values lie in[0,B) and S0<D<B. Their aggregate mass is below D.
There are no lower digits to carry. Thus S4(0) is its actual subset
mass, and A_j(0) is its actual coefficient-weighted mass, at most
M*S0<MD<B. Neither formed input carries out of this cell. The selected
digits in(7) consequently satisfy the genuine linear-form interpretation
here. Equation(9) and the unchanged paired action make V(0) the actual
positive next state. Its total mass is Cmass*S0<Cmass*D<B.

Inductively suppose state cells below j and formed-input digits there
have been recovered, all their state masses are below D, and no lower
carry occurs in S, S4 or A_j. Subtracting the known lower coefficients
from(10) and reducing the next coefficient modulo B recovers H_i(j)
as the actual next state from cell j-1: every actual coordinate is
nonnegative and its total is below Cmass*D<B. The aggregate word S
has no incoming carry, since every earlier recovered mass was below D.
Its digit at cell j is the actual mass just recovered, already below B.
The aggregate native lane

    S AND ((D-1)J)=S

therefore forces that mass below D. Equations(4)--(6), with zero lower
formed carries, now show that S4(j) and every A_j(j) equal their true
linear expressions and are below MD<B. This recovers the formed digits
and their absence of carry at the same cell. Selection and(9) then give
the actual next positive-matrix action coefficient.

This proves the induction through the last pre-state. The top coefficient
of(10) forces F to be the genuine terminal state, which is positive.
Its mass need not have been given a range premise. The retained endpoint
equality thus accepts exactly the intended nonempty word for the ordinary
input x. No form-digit correctness was used before recovering its state
cell, and no a priori duration-dependent height bound was assumed.

**Remark 1 (retained obstruction to a naive linearity shortcut).**
At B=8 take four positive raw history values(5,1,1,1), whose subset
sum S4 is8. Selecting the lowest cell gives S4 AND7=0, while separately
selecting and adding the four values gives8. Thus selection does not
commute with addition when a formed input carries. This is a local
counterexample to an unconditional input-form argument, not a claimed
zero of the full native/history system. The induction above is the
required missing hypothesis; the new proof does not assume AND linearity.

## 5. Positive completion and the weighted global slack

Conversely, follow any accepted nonempty word in the fixed positive7
alphabet. Choose a dyadic D greater than every actual state mass,
including the endpoint, and put B=KD, P=B^n and J to the repunit.
Pack the actual pre-states and selectors. Equations(5)--(6) make every
formed cell nonnegative and below B, so the computed S4,A_j words have
exactly the intended digit streams without carries. Supply the three
selected form hats in(7); absent selections still have hat1.

At a paired-letter cell the retained selected total is at most the
state mass. At a relator cell it is S4+A1+A2, at most(2M+1) times
that mass. Hence, as whole integers,

    Ztot<=(2M+1)S, S<=(D-1)J.

The required slack is positive:

    g=P-M*S-Ztot
      >=P-(3M+1)S
      >=[(K-3M-1)D+3M]J+1>0.                             (11)

All native lane bounds and identities hold at these computed ports;
the prescribed native converse supplies its fresh positive auxiliaries.
The exact recurrences telescope and the endpoint is the intended one.
Thus the finite relation has the same ordinary-input projection as the
original universal alphabet. The changed fields, K, global slack and
native lane count do not give a same-tuple identity with the old source.
The fixed exponent ell still depends only on the compiler alphabet;
the unbounded duration n is recovered from the repunit.

## 6. Local paid ledger and unchanged unpaid boundaries

One shared producer S4 requires three additions if it is not already a
paid intermediate of the sum S. The author identified the following
explicit shared producer, which root is adopting in the proposed source:

    h45=H4+H5; h67=H6+H7; S4=h45+h67;
    h12=H1+H2; h123=h12+H3; S=h123+S4.

These six additions compute both S4 and S, exactly the old cost of
summing seven history words. Every register is used when r>=1. This
is a paid local reassociation with no extra three-addition producer;
it is not an assertion that an earlier source already had these nodes.
For each relator, the two four-term positive forms A1,A2 cost8M+6A.
They are shared between its two inverse slots. Equation(9) costs2M+2A
per slot. Appending its3-by-2 action uses6M+6A per slot: two coefficient
products and two successive accumulator additions in each row. Thus:

| Per relator pair | M | A |
| --- | ---: | ---: |
| Two formed input producers | 8 | 6 |
| Uncentering for both signs | 4 | 4 |
| Both signed actions, including six accumulator updates per sign | 12 | 12 |
| Total | 24 | 22 |

The phrasing "updates per sign" refers to six binary additions into
three accumulators, not six additional coordinates. Zero or unit fixed
coefficients may still be retained in this uniform literal upper schedule.
The new weighted global comparison requires one M*S multiplication;
its following two additions are the same count as before. In addition
to these costs, every retained output hat must be un-hatted and summed,
and all three native packs must use the new ell=62+8r. The power P^ell
must be charged at that exponent; no difference of binary-chain costs
is presumed free or monotone.

Removing two selected fields per relator removes two unhat operations,
two terms from the selected-output total, and two native lanes, but those
local differences alone are not a complete compiler ledger. A future
source must compose the new producers, selection geometry, global guard,
old paired action, native header, recurrence arithmetic and finalizer.
No complete operation bound, degree or new numerical universal bound is
claimed in this note. The supplied raw selected-field count is52+6r;
with the existing shared-terminal convention the positive witness count
is96+8r. The input forms and M*S are computed, not supplied witnesses.

## 7. A precise obstruction to only two homogeneous positive forms

For a noncentral P in SL2(Z), S(P)-I has rank2. If q is nonzero,
the minor on rows1,2 and columns2,3 is2q^2; if s is nonzero, the
minor on rows2,3 and columns1,2 is2s^2. When q=s=0, determinant1
over integers forces P=I or -I, excluded here. The right invariant
gives rank at most2. Since C has a unimodular first3-by-3 submatrix,
W=(S(P)-I)C also has rank2. Moreover

    W*(1,1,2,1)^T=0.                                     (12)

Suppose the exact map W on four independent history inputs had a fixed
linear reconstruction from only two homogeneous linear forms, each
nonnegative on every
strictly positive integer history assignment. Such a form must have
nonnegative coefficients: a negative coefficient is exposed by letting
that one coordinate grow with the others fixed at1. Since rank W=2,
the two form rows must span the rowspace of W. By(12), each would
annihilate the strictly positive vector(1,1,2,1). A nonnegative row
can do that only when it is zero, contradicting rank2.

This rules out a two-form homogeneous factorization with unconditional
nonnegative inputs at the same cut. It is not a lower bound on arbitrary
guarded, affine, nonlinear or state-restricted selection interfaces.
The three forms(4) evade exactly this obstruction by retaining the
selected positive mass needed to subtract their offsets.

**Open question 1 (separate guarded affine route).** The author considered
centering a signed form by a fixed multiple of D*J, whose selected
constant-cell offset could be computed from the selector word rather
than selected again. Such a route needs its own paid pretyping bound,
positive completion margin and formed-input carry proof; it is not
certified here. The homogeneous obstruction does not refute it.

**Open question 2 (root's emitted source task).** Emit and independently
audit the three-form relation with the full native component and all
conversions charged. The inherited fixed universal presentation remains
unmaterialized numerically. No existing frozen source is altered or
assigned this projected saving before that separate task is complete.

## 8. Evidence boundary

All new arguments and local schedules are handwritten. The frozen
relator-plane, paid sparse-action and one-AND geometry notes are read
inertly; their exact byte/read bindings are recorded separately when
the packet is frozen. No supplied, archived, committed, predecessor or
frozen helper is executed or imported; no saved scientific source or
coefficient array is evaluated or degree-propagated. No scientific
sampling, local emitter or build is used. Aristotle independently read
the full draft and checked the integral input factorization, simultaneous
state/form induction, weighted completion, local counts, shared sum and
qualified two-form obstruction, without a mathematical correction.
Root also read the full draft and the shared-sum addition, independently
handchecked the proof, and requested no further correction. These local
reviews do not certify a complete emitted source. New files remain in/tmp;
repository files, Git and all earlier frozen artifacts are unchanged.
