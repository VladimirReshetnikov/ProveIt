# Guarded affine centering uses two selected forms per relator sign

For r>=1, the three-form interface can be replaced by two selected forms
per signed relator slot. A common computed center lambda*D*J is removed
after selection by a paid product with the existing selector. The new
global guard proves positivity of the formed inputs before the native
theorem is invoked, and a simultaneous state/form induction proves that
their canonical digits have the intended affine meaning.

The per-relator producer, uncentering and appended-action schedule is
22M+24A. Four shared multiplications and two additions produce the center
and global guard, replacing the former weighted guard's1M+2A. The changed
relation has52+4r selected fields and62+6r native lanes. These are local
and interface ledgers, not a complete emitted source or numerical
universal operation bound. Root requested this continuation of the
credited affine question in the frozen three-form note. The author
identified the guard and the common-center sharing used below.

## 1. Retained fixed integer factorization and a common center

Retain the fixed positive7 alphabet, its ordinary input z(x), and the
same r presentation relators. For each fixed P in SL2(Z), the three-form
note supplies two integer four-entry rows ell_1,ell_2 and two fixed
integer3-by-2 matrices E_+,E_- satisfying

    (S(P^sign)-I3)C=E_sign [ell_1;ell_2],
    C=[1,0,0,-1;1,1,0,-2;2,0,1,-4].                       (1)

All coordinates on the right are in the original decoder/output order.
The integer basis, fixed permutations and central P=+/-I2 convention
are exactly those already proved there. Their fixed preparation has
no new runtime division, witness or arithmetic charge. For this note,
the right side of(1) is the sole matrix interface needed.

Take maxima over all relators and both form rows. Define fixed integers

    nminus=max(0,all -ell_(j,i)),
    pplus=max(0,all ell_(j,i)),
    lambda=nminus+1, Cg=2lambda+1.                        (2)

Thus lambda>=1 and Cg>=3. The SAME lambda is used in every form, not an
independent shift for each row. Choose one fixed power of two

    K>max(Cmass,m,Cg,lambda+pplus), m=8+2r,                (3)

where Cmass is the common positive7 column sum. This is fixed compiler
preparation independent of the ordinary input and history length.

Keep D=S0+height_slack, B=KD, selector unhats S_sigma, their checksum J,
Pscale=(B-1)J+1, S=sum_(i=1..7)H_i and mu=(D-1)J. To avoid confusion,
Pscale is the packed-history scale, whereas P in(1) is a fixed2-by-2
relator matrix. Compute the shared center registers

    hcenter=lambda*D, Wcenter=hcenter*J,
    A_j=ell_j H_(4,5,6,7)+Wcenter.                        (4)

The two A_j for one relator are shared between its two sign slots.
They are computed integer polynomials, not extra positive witnesses.
They are not claimed nonnegative away from the guard below.

## 2. A guard that proves the native input domain

Leave the eight paired letters'52 raw selected fields unchanged. Each
signed relator has only two positive output hats, with raw nonnegative
unhats Z_sigma,1 and Z_sigma,2, in the lane order(A1,A2). The two lanes
are

    (A_j,(B-1)S_sigma,Z_sigma,j), j=1,2.                   (5)

There is no selected subset-mass field. Let Ztot sum every retained raw
selected output, paired and relator. Keep one positive global slack g,
but replace the old global comparison by

    Cg*(D*J-S)=Ztot+g.                                    (6)

Every raw unhat is nonnegative on every positive supplied assignment.
At a full zero, the separately retained comparison(6) therefore gives

    DJ>S>=7, J>=1, Ztot<Cg*DJ.                            (7)

This inference uses no native typing or history recurrence. For each
form, with L_j=ell_j H_(4,5,6,7), positivity of the histories gives

    -nminus*S<=L_j<=pplus*S.

Consequently(2),(4),(7) imply

    A_j>=lambda*DJ-nminus*S>0,
    A_j<=(lambda+pplus)*DJ<Pscale.                       (8)

The final strict inequality follows directly from(3): for any integer
T<K and J>=1,

    Pscale-T*DJ=[(K-T)D-1]J+1>0.                         (9)

In particular S<DJ<Pscale and Ztot<Cg*DJ<Pscale. Thus all original
histories and all selected outputs lie below Pscale. As in the frozen
geometry, D,J,S_sigma,mu and(B-1)S_sigma are also nonnegative and below
Pscale; moreover Pscale>=B>1. These facts now precede the native theorem.

Pack the lanes at radix Pscale. Retain selector lanes, paired-selection
lanes, the aggregate range lane(S,mu,S), and the power lane(D,D-1,0).
The total number of selected fields and native lanes is

    N=52+4r, ell=m+N+2=62+6r.                             (10)

If(6) is written using hats, its exact equivalent is

    Cg*(DJ-S)+N=sum_all_selected_hats+g.                  (11)

The new offset N cannot be replaced by the old count.

At a full zero, the bounds just proved make every lane nonnegative and
less than Pscale. Hence its three packs are nonnegative, their padded
native parameters are positive, and the scale Pscale^ell is positive.
Only NOW invoke the unchanged complete prescribed-AND theorem with its
fresh positive auxiliaries. It gives dyadic Pscale and exact AND on the
packs. Lane separation gives all individual AND identities; the last
lane makes D dyadic. Fixed dyadic K makes B dyadic, and the repunit
identity gives

    Pscale=B^n, J=1+B+...+B^(n-1), n>=1.                  (12)

The selector checksum is carry-free since m<B, so it selects exactly
one letter at each cell. The lanes extract the canonical base-B digits
of their input words. They do not yet identify a digit of A_j with the
affine expression in(4).

The domain argument here is a guarded application of the native
projection theorem. An emitted ordinary integer sum of squares forces
every residual, including(6), to vanish; (7)--(9) then prove its computed
native input parameters belong to the theorem's positive domain. It is
unnecessary that the native polynomial have no extraneous signed-input
zeros outside that domain, since those tuples fail the outer guard.
No helper rewrite or unspecified domain inference is being used.

**Remark 1 (retained loss of off-guard positivity).** The stronger old
invariant that all computed form words are positive on every positive
supplied assignment does NOT transfer. For the valid noncentral matrix
P=[1,1;0,1], take the primitive right invariant(1,0,0), so the stated
basis recipe allows u=(0,-1,0), v=(0,0,1). Then ell_1=(-1,-1,0,2).
Set all selector hats to1, giving J=0, and set(H4,H5,H6,H7)=(3,1,1,1).
Every supplied history and selector hat is positive, but A1=-2,
independently of positive D and lambda. This is an off-guard domain
counterexample, not a full positive zero. Equation(6) excludes it because
its left side is negative and its right side positive. The proof invokes
native semantics only after this guard, rather than importing the old
unconditional pack-positivity statement.

## 3. Selected-center recovery and simultaneous carry proof

For each relator sign compute one shared offset and two differences:

    Q_sigma=hcenter*S_sigma,
    T_sigma,1=Z_sigma,1-Q_sigma,
    T_sigma,2=Z_sigma,2-Q_sigma.                          (13)

The same paid offset is used twice. No extra native selection lane or
new supplied witness is needed. After(12), the selector digits are0/1,
and hcenter=lambda*D<B by(3). Thus Q_sigma is exactly the word having
center digit lambda*D in each selected cell and0 elsewhere, without
carries. The already paid mask obeys the useful exact identity

    K*Q_sigma=lambda*((B-1)S_sigma+S_sigma).               (14)

Equation(14) is NOT a free division rule: schedule(13) actually pays the
one product hcenter*S_sigma. No runtime division by K is introduced.

Append E_sigma*(T_sigma,1,T_sigma,2)^T to the existing d/e/f increments.
Keep the paired action, common baseline and positive7 postprocessor,
including its optional fused recurrence form. Retain all seven equations

    B V_i=H_i+Pscale F_i-z_i(x),                          (15)

and the original endpoint equality, or the alias F7=F1. The computed V_i
is a linear combination of the history, selected and offset words. Its
formal base-B coefficients may be signed away from the recovered prefix;
no canonical expansion of V_i is assumed.

At cell0, reduction of(15) modulo B recovers each H_i(0)=z_i(x), because
both sides' entries are in[0,B) and S0<D. There are no lower carries.
For this state, and later for any recovered state of mass a<D, the
coefficient of A_j is

    a_j=ell_j h_(4,5,6,7)+lambda*D,
    0<lambda*D-nminus*a<=a_j
       <=lambda*D+pplus*a<=(lambda+pplus)D<B.             (16)

Thus each formed coefficient lies strictly between0 and B. The first formed cell
has neither borrow nor carry. Selection and(13) recover exactly L1,L2
in the selected relator slot, and(1) makes V(0) the actual positive next
state. Its mass is Cmass*S0<Cmass*D<B.

Inductively suppose all earlier states and formed digits have been
recovered, their state masses are below D, and no carries or borrows
occur in the lower coefficients of S or A_j. Subtract the known lower
coefficients in(15) and reduce modulo B. The next actual state has total
mass below Cmass*D<B, so this determines each canonical H_i digit as
that actual state coordinate. The aggregate word S has no lower carry;
its current digit is the actual mass, already below B. The retained AND
identity S AND((D-1)J)=S therefore improves this mass bound to<D.
Formula(16) now recovers the formed coefficients, with no incoming or
outgoing carry or borrow, and selection plus(13) gives the correct next
matrix action. This closes the simultaneous induction.

The top coefficient of(15) gives the genuine positive terminal state.
No prior range bound on its coordinates is used. The endpoint condition
therefore accepts exactly the intended nonempty word for ordinary x.
The inherited initial coordinates1 and7 are3 and1, so the empty word
never accepts and this nonempty restriction loses no ordinary input.
The fixed lane exponent ell is independent of the unbounded recovered
duration n. No assumption of unconditional AND linearity occurs.

## 4. Positive completion under one enlarged height choice

Conversely, follow any accepted nonempty word of the fixed positive7
alphabet. Let a_max be the largest mass of any state in this finite
trajectory, including the endpoint. For a given relator, let p_j be
max(0,all coefficients of its row ell_j), and fix

    G=max(1,all p_1+p_2), Tguard=Cg+G.                    (17)

Choose a power-of-two D>Tguard*a_max. This determines a positive height
slack D-S0. Define B,Pscale,J, histories and selectors by the genuine
trajectory and(12). At every cell the forms(4) have the coefficients
in(16), so no carries or borrows occur. Supply the two selected form
hats per relator sign, and the retained paired fields. Absent selections
still have positive hats1. All local AND identities and lane bounds hold.

At a paired-letter cell the selected total zsel is at most its state
mass a. At a relator cell,

    zsel=L1+L2+2lambda*D<=G*a+2lambda*D.

Thus, in either case, the coefficient needed for the global slack obeys

    Cg*(D-a)-zsel
       >=(Cg-2lambda)D-(Cg+G)a
       =D-Tguard*a>0.                                   (18)

For a paired cell this is a weaker valid bound using G>=1. Packing these
positive coefficients gives exactly the positive integer

    g=Cg*(DJ-S)-Ztot.                                    (19)

Their coefficients are also below Cg*D<B, although only positivity of
g is required. The arbitrary finite duration introduces no new fixed
constant: Tguard and K were chosen solely from the fixed alphabet.

Every native parameter is positive, every lane is correct at these
ports, and the complete prescribed-AND converse supplies its positive
auxiliaries. Equations(15) telescope to the genuine positive endpoint.
This proves the converse without deleting any native equation or
requiring a new height-certificate component. The changed fields, guard
and radix choice preserve the ordinary-input projection, not identical
values of all formerly supplied witnesses.

## 5. Paid local schedule and incremental interface ledger

Use the original six-addition sum S; a separate S4 consumer is no longer
needed. Shared work, outside the per-relator ledger, is

    hcenter=lambda*D; Wcenter=hcenter*J; DJ=D*J;
    gap=DJ-S; bound=Cg*gap; rhs=Ztot+g.                    (20)

This is4M+2A, including every multiplication by a fixed numeral. The
old three-form weighted guard cost1M+2A. The difference is3M. No
coefficient preparation or copy is charged as runtime arithmetic.

For each relator, compute its two four-term signed dot products L1,L2
with all eight coefficient products retained, then add Wcenter to each.
This costs8M+8A. For each of its two sign slots, compute(13) in1M+2A.
Append the3-by-2 action directly into the d/e/f accumulators using six
coefficient products and six additions. The latter count includes every
accumulator update, not merely three separate outputs. Therefore:

| Per relator pair | M | A |
| --- | ---: | ---: |
| Two centered form producers | 8 | 8 |
| Shared selected offset and two subtractions, both signs | 2 | 4 |
| Both signed actions, fully appended | 12 | 12 |
| Total | 22 | 24 |

The fixed per-relator roles are eight signed form coefficients and twelve
signed action coefficients. The common positive lambda and Cg are global
roles. Together with the inherited alpha,gamma,K,kappa_minus_one, this
is6+20r fixed roles. The recipe, including(1), ties them to the actual
fixed matrices;
these identities are not asserted for independently arbitrary numeral
assignments. Central relators may retain zero coefficient products in
this uniform upper schedule. No generic minimality is claimed.

Relative to the frozen three-form cut24M+22A per pair, this is-2M+2A
per pair, besides the shared+3M. The selected count decreases by2r:
unhatting every retained selected field and summing their raw total each
remove2r additions, so this prefix saves4r A. Three Horner
packs with the same initialization each lose2r lane appends, saving
6r M+6r A in total. At precisely these unchanged-consumer cuts the
combined non-power difference is

    (3-8r)M-8r A.                                        (21)

The fixed power must now be emitted at ell=62+6r. If the chosen source
uses the binary chain length powcost(t)=floor(log2 t)+popcount(t)-1,
its multiplication difference is

    powcost(62+6r)-powcost(62+8r).                         (22)

It is not silently dropped or assumed negative. A different actual
power schedule must be accounted on its own terms.

With the inherited terminal alias F7=F1 the finite relation has96+6r
positive witnesses: seven histories, six terminal coordinates, m
selector hats, N selected hats, two outer slacks and21 native auxiliaries.
Ordinary x is separate. The same15 native comparisons, one global
comparison and seven recurrences remain. Fixed arity and an unbounded
recovered nonempty duration are unchanged. For r=0 retain the preceding
source; this note does not introduce unused centers for that case.

**Remark 2 (retained provisional independent-shift schedule).** The first
guard sketch allowed separate lambda_j. Its direct schedule28M+24A per
pair with shared guard increment1M is valid, but less efficient. It pays
each lambda_j*DJ separately and each lambda_j*(D*S_sigma) separately.
Choosing one common lambda in(2) permits both products to be shared as
in(4),(13). The earlier schedule was not a counterexample or a lower
bound; it is retained to distinguish it from the final ledger(21).

**Open question 1 (separate complete-source task, credited to root).**
Emit the entire changed finite relation and authenticate every source
row, consumer, lane, fixed role and final sum-of-squares cost. Formula(21)
is only an incremental ledger at specified cuts, not such an emitted
source audit or an assigned numerical universal operation bound. The
fixed universal presentation remains numerically unmaterialized.

## 6. Provenance and execution boundary

The frozen three-form note left affine D*J centering as a credited open
question. The present guard and shared-center proof resolve that
question only for the exact finite relation above. Its homogeneous
two-form obstruction is unchanged: these affine forms depend on D,J,
and their positivity requires a separately retained guard.

All new algebra, proof and ledgers are handwritten. Dependencies are
read inertly. No supplied, archived, committed, predecessor or frozen
helper is run or imported; no saved scientific source or coefficient
array is evaluated or degree-propagated. No scientific sampling, local
emitter or build is used. New files remain in/tmp; repository files,
Git and earlier frozen artifacts are unchanged. Exact dependency bytes
and read spans are bound in the companion metadata.

Root and Riemann each read the full draft and independently checked the
guard, native-domain invocation, common offset, simultaneous induction,
positive completion, local ledger and incremental power boundary, with
no mathematical correction requested. Each also reread the complete
native positive-scale proof inertly. Their local proof challenges do not
certify a newly emitted whole source. Aristotle earlier corroborated
the guarded positivity/completion argument and identified the need to
state the lost off-guard invariant explicitly, as retained in Remark1.
