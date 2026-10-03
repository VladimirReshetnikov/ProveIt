# Signed bound units give a767-operation complete U15,2 compiler

The [complete771 compiler](gpcp_checksum_global_units771.md) admits a further
four-operation reduction to **767=352M+415A**, with125 positive witnesses,
18 comparisons, three fixed positive program parameters and ordinary positive
input. Its exact degree is228339. Supplying the initial history value gives
770=353M+417A,126 witnesses,19 comparisons and exact degree9484.
The [source](gpcp_positive_bound_units767.py) and
[receipt](gpcp_positive_bound_units767.json) include both initial interfaces and
independent switches for the pair of AND bounds and pair of geometry bounds.

Each converted bound becomes an integer unit whose sign may remain negative.
The new full positive zero set maps **surjectively** onto771, with an explicit
positive section. The projection retains every coordinate except enabled bound
slacks and the global history slack. It is not asserted to be a bijection, and
the complete polynomials are not identical off zero. All fixed U15,2 transitions,
tiles, program numerals, input recoding, allowed padding and positive domains are
retained. Thus the same actual ordinary-input universal slices are represented.
The separate75-certificate/87-polynomial bounds are unchanged.

## 1. Literal bound factors and operation counts

The source retains the771 global unit

    G=P_history−Sigma−beta_global.

It optionally converts both AND X-bound comparisons into

    H_r=X_r−r_r−beta_r,
    H_h=X_h−r_h−beta_h,                                (1)

where r_r and r_h are the recoder and history packed indices. It independently
optionally converts both geometry bounds into

    H_X=X_geo−J−beta_X,
    H_I=J−B_geo−beta_I.                                (2)

The actual geometry is

    q=x+input_slack>=2, Q=q^64, B_geo=2^63*Q.           (3)

This is the width64 recoder geometry of the current compiled source, not the
smaller radix of an older illustrative recoder.

Every bound lhs is already emitted as its base plus a supplied positive slack.
Append one subtraction, rhs minus that lhs, and one multiplication into the
existing product; remove the original comparison. This adds two certificate gates
and removes three finalizer gates, saving exactly one addition per bound. Neither
multiplication nor a fixed coefficient is free. The paired switches add zero,
four or eight certificate gates and remove zero,two or four comparisons.

|Enabled pairs|Computed-initial operations|Comparisons|Exact degree|Supplied-initial operations|Comparisons|Exact degree|
|---|---:|---:|---:|---:|---:|---:|
|none, retained771|771|22|209782|774|23|8672|
|geometry only|769|20|209848|772|21|8738|
|AND only|769|20|228273|772|21|9418|
|both, default|767|18|228339|770|19|9484|

Computed-initial schedules use352M; supplied-initial schedules use353M. The
remaining operations are additions/subtractions. Their witness counts remain
125 and126 respectively. The default certificate costs714=334M+380A; each
single-pair certificate costs710=332M+378A.

At a zero of the anchored finalizer, its complete product is1 and every remaining
ordinary residual vanishes. Each factor is therefore an integer unit. All12
native norms are+1 by the same independent modulo4 exclusions as771. Initially,
G, the two checksums and each enabled H may have either sign. No subsequent
argument assumes their total subproduct is positive before proving its inputs.

## 2. Recover the AND bounds before checksum typing

The actual supplied F0,F1,F2 and computed F3>=8 remain positive before any native
or history interpretation, exactly as proved in771. Its unconditional positive
program frame, decoded selectors and selected words are unchanged. The native
scales in both AND cores are positive multiples of16. The retained padded-input
comparisons give F1=4,F2=2,F3=8 modulo16.

Write C=q_native−sum F_i for either checksum. Because C=±1,

    F0=2−C modulo16,
    r=F0+q_native*F1+q_native²*F2+q_native³*F3
      =1 or3 modulo16.                               (4)

Also X=w*q_native=0 modulo16. If its bound is converted, H=±1 and positive beta
imply X−r=beta+H>=0. Equality is impossible by(4); more precisely

    X−r>=15 when C=+1, and X−r>=13 when C=−1.          (5)

If the pair is disabled, the original strict bound remains. Thus both AND cores
have the strict X>r required by771's local rank and raw population proof before
either checksum sign is known. The ratio slacks, exact first-index and auxiliary
linear comparisons, and full normalized strong factors are untouched.

The complete local proof in771 now applies: its exact indices are n=r+1 and
p=2r+1, its root and ratio give q_native=2^popcount(r), and a negative checksum
would have field residues3,4,2,8 with total field population at least
log2(q_native)+1. Both checksums are therefore+1 independently of G and the
new bound signs. Every ordinary native bound can be restored positively by

    beta_parent=beta_new+H=X−r>0.                      (6)

The full native AND relations follow after this restoration. It is unnecessary
to force H positive, and(5) gives its strict projection margin directly.

## 3. The geometry permits a weak X bound during bootstrap

When the geometry pair is enabled, its units give X_geo>=J and J>=B_geo.
When disabled, the original comparisons give the stronger strict inequalities.
In either case(3) gives

    X>=J>=B_geo>=2^127, J>q.                           (7)

Here X denotes the geometry X only. Set Y=q(2*odd_half+1)>=3q>=6,
E=XY, a=Y(X+1), A=a+2 and Delta=A²−1. Then E>2J+1, a>2J+1 and
P0=2XY²+1>A. Its retained first-index comparison gives k=psi_P0(n),
n=J+1 modulo E and n>=J+1. The main norm and positive ratio give
c=psi_A(p), p>n and

    c>(2A−1)^(p−1)>A^(J+1)>A*Delta²,
    c>2p, c>Yk>2(2J+1).                               (8)

The normalized strong equation gives pc dividing its index, or can be positively
restored to the full ordinary strong equation by i_old=Delta*i. Thus strict rank
supplies f>2c before the auxiliary value of−c is declared positive. The retained
minus congruences and their strict windows force p=2J+1 and n=J+1 exactly.
The fixed-minus parity theorem forces J odd. These are the same rank and parity
steps as the [shared geometry proof](group_linked_binary_geometry47.md), with
its actual bounds checked in(7)–(8). Neither new unit sign, either checksum sign,
or a history interpretation enters this argument.

The raw ratio and exponent part of
[the population proof](native_binary_input_dilation129.md#2-the-raw-geometry-theorem-at-j9-and-jq)
continues to hold with X>=J here. In detail, its lower ratio first gives

    Y>=X^J, a>X^(J+1).

The exponent comparison is recovered from the main-root congruence modulo4a+3.
The representative estimate needs no strict X>J: since J>=8,

    X^(J+1)>=J^(J+1)>=8^(J+1)>2^(2J+1).

Thus both X and2^(2J+1) lie in(0,a), and congruence implies
X=2^(2J+1)>J. The subsequent ratio error, fractional tail and valuation proof
is unchanged, yielding q=2^popcount(J), since J>q. Both original geometry gaps
are now strictly positive:

    X−J>0, J−B_geo>0.                                 (9)

The second follows from J odd, B_geo even and J>=B_geo. Consequently the positive
projection for enabled geometry bounds is

    beta_X,parent=beta_X,new+H_X=X−J,
    beta_I,parent=beta_I,new+H_I=J−B_geo.               (10)

The strict original gaps were conclusions, not hypotheses used in proving them.
The boundary J−B_geo=1 is possible: q=4, B_geo=2^191, J=B_geo+1 gives odd J with
popcount(J)=2. This is why the completeness section below deliberately uses
paired negative signs instead of requiring a positive geometry index unit.

## 4. Restore the global bound after typing the actual history

After the previous sections, all norms and both checksums are+1. The remaining
unit equation is only

    G*product_(enabled H) H=1.                         (11)

It need not force G or any H positive. We therefore recover the global slack
by a separate scalar and typed-history argument.

Write D for the history height, B_h=131072D and
P_h=(B_h−1)J_h+1. Positivity gives J_h>=0. From G=±1 and beta_global>=1,
Sigma<=P_h. Sigma contains ten strictly positive ports, so each is<P_h and
P_h>=10. Hence J_h>=1 and B_h<=P_h.

These are precisely all uses of the old global equality before binary typing
in [the slope-class history proof, Section3](pcp_affine_slope_class_history.md#3-soundness-without-an-unpaid-group-predicate).
Every class selector is a sum over a subset of nonnegative tile selectors,
so its full-cell mask is at most(B_h−1)J_h=P_h−1. Physical lanes fit below their
powers of P_h, controller and range regions fit in their assigned lanes, and
the two top lanes allow B_h=P_h. The native AND recovered in Section2 makes
P_h dyadic, then the top region makes B_h dyadic. The exact repunit gives a
canonical positive duration; controller lanes give one selected tile per row;
range and physical lanes recover bounded histories and the eight selected words.
The retained transports then recover their chronological affine updates.

Thus the four nonbaseline classes on each side are disjoint per row. As in771,

    Sigma<=2(H_U+H_V)+8<=4(D−1)J_h+8,
    P_h−Sigma >=(131068D+3)J_h−7>1.                   (12)

No sign of G was assumed in obtaining this typed bound. The restored slack of
the original ordinary-global774 source would be beta_new+G=P_h−Sigma. The
projection in this packet instead targets the fixed771 parent, whose global
unit must be+1. Its restored coordinate is therefore

    beta_global,771=beta_global,new+G−1=P_h−Sigma−1>0. (13)

The subtraction of1 in(13) is essential to identify the correct parent.

## 5. Full positive surjection and a positive section

Given any new positive zero, apply(6),(10) to enabled native bounds and(13)
to the global slack. All other coordinates, including the three program
parameters and ordinary x, are retained. Each changed slack has exactly its
bound lhs as sole source consumer. The restored771 tuple therefore has all
original strict bound comparisons, G_parent=1, every original norm/checksum
factor+1 and every other comparison unchanged. It is a complete positive
parent zero.

Conversely take any771 positive zero. Add1 to every enabled native bound slack,
and leave the global slack and all other coordinates unchanged. Each enabled
H is then−1. Switches enable pairs, so their product is+1; G stays+1. The native
norms and checksums do not depend on these private slacks, and every remaining
ordinary comparison still holds. This constructs a new positive zero, and
projecting it returns the original parent tuple exactly.

This is an explicit positive section of a full surjection onto the parent's
positive zero set. It does not require an old gap to exceed1 and covers the
geometry boundary noted above. It does not assert injectivity: different sign
choices may have the same parent image. Both switches disabled retain the
literal771 source as the trivial identity case.

No valid-program word property was used locally; the positive frame and complete
affine history suffice for arbitrary positive program parameters. Restricting
afterward to the parent's valid universal program slices preserves its ordinary
input language and padding convention. No native witnesses need to be rebuilt.

## 6. Guards, exact degrees and arbitrary-point identities

The wrapper requires complete equality with the canonical771 parent for the
selected initial interface. It checks each literal bound lhs and comparison,
its slack's unique consumer, absence of other consumers of the bound lhs, and
the actual q^64 geometry power chain and2^63 coefficient. Public Boolean switches
are checked before caching. Every output, degree and ledger API requires equality
with the complete current canonical packet, including its domains and projection
metadata. Active factors and comparisons are updated; old definitions remain
unchanged and every gate must reach the output.

The new AND units have strict highest terms−r_rec and−r_hist, of degrees199 and
18292 in the computed interface, or199 and547 in the supplied interface. The
geometry units have strict highest terms X_geo and−B_geo, of degrees2 and64.
All are nonzero polynomials. The unchanged parent unit has its established
nonzero highest homogeneous form. Even when the history X-bound residual is
removed, the retained first-index residual

    hist__and__R10b−hist__and__R11

has strict highest term−r_hist. Its degree is the original maximal outer degree,
18292 or547. Thus the remaining sum of squares still has a nonzero highest form
of twice that degree. Multiplying by each new factor adds its exact degree,
which proves the table's exact output degrees. The three guarded main-norm
cancellations and every retained propagated degree entry are unchanged.

For arbitrary integers the source exposes formal `project_to_parent` and
`section_from_parent` maps. Their positive zero-set scope is as proved above;
they are not unrestricted positive maps. If F_new is evaluated at a supplied
tuple and F_parent at its formal projection, direct source substitution gives

    F_new+1 = G*product_(enabled H)H * (F_parent+1).    (14)

The formal projection makes the removed parent bound residuals zero and its
G_parent exactly1; all other residuals and native factors retain their values.
The checker verifies(14), every unchanged parent register, and the complete new
manual finalizer. A separate formal-section check evaluates the parent bound
residuals r_i=rhs_i−lhs_i: the new signs are r_i−1, so it verifies the full new
output and the old removed squares without assuming those residuals vanish.

Default execution recomputes the receipt; `--write` regenerates it. All eight
source/count/degree/output-closure ledgers, positive and signed full-output maps,
actual residue-gap branches, weak geometry boundary estimates, paired negative
sections including index gap1, and both global-slack branches are checked.
These are finite algebraic and scalar checks, not materialized complete compiled
Pell zeros. The complete positive proof, rather than those fixtures, establishes
the universal projection.

Author writer39232 and fresh96128 passed on the final frozen source. Root's
full proof/source review and fresh49978 passed; its independent modular
executor checked192 full-source projection/output corrections(96 signed),
32 zero-selector contexts and all eight cost/privacy/interface ledgers.
Native's independent full proof/source/dependency review and fresh35815
passed with no findings. Its separate audit checked192 manual projection
maps and192 manual section maps(96 signed each),192 formal section
right-inverse components on the bound/G=1 locus,32 zero-selector cases,
16 exact-degree certificates modulo two primes, eight cost/closure/domain
contexts,160 malformed callers and1122 pretyping residue cones. Both reviews
confirmed the weak-global chronology, positive section at geometry index
gap1, and the surjection scope without a bijection claim.
