# REJECTED DRAFT: marker996 color-coordinate error

This draft is not an accepted proof. During its full author/root review,
the coefficient map exposed a decisive semantic error: physical978 is
the low packed West bit, not East bit0. At Start it is253 mod2=1, so
the marker's current odd part is1+1=0, not1. The claimed forced odd
temporal marker and offset18 monotonicity below do not follow. The
finite probe made the same wrong coordinate interpretation; its numerical
controller and raw-byte checks do not repair this proof gap. No main
equation was promoted from this draft. The corrected A997 proposal is
developed separately in `../marker997-independent/PROOF.md`.

The rejected text below is retained as development history. Minor
transcription corrections made during self-review do not validate it.

## Former draft: complete length1997 tuple

This complete ordinary argument retains all942 admissible sorted tiles,
all3297 specified coefficient entries and every transition. It moves the
zero-weight physical marker and bare marker monomial to996, places the
sole doubled clause below it at995, and uses prime cell length1997.
The clause has the Boolean dummy977 as its only extra non-temporal unit.
The complete tuple has978 physical positions and978 native tests.

Preliminary one-hotness still precedes label recovery. Fractional phases
0..6 and11..46 use the low clause directly. Phases7..10 first use the483
padding tests at54..536: a first prefix count4 fails bit3, so at most3 of
the first483 selectors are present and the total count is at most462.
This is enough for the low clause to force at most one selector. The
selector/control-source separation then resets every field through995.

The fractional-phase contradiction uses all nine South-copy tests and
the actual forced-Start clause, without first decoding its labels. The
clause forces a nonzero physical South block in every phase; any positive
fractional phase would force all its bits zero. Full label decoding may
then proceed. The marker's decoded odd part is Start plus East bit0.
Besides the old field offsets19 and20, offset18 needs a new argument:
it gives e_theta=e+delta_Start on a finite cycle, impossible when that
cycle contains Start. Thus the whole field alignment is recovered.

Canonical markers encode the shifted Boolean sum Start+Eastbit0, rather
than the Start indicator alone. All916 padding tests, actual masks,
every simultaneous safe dummy subset, rank and controller are proved
below. Formal degree is controlled by bare996 times physical marker996,
at1992; four zero fields remain at1993..1996. A passing modular controller
does not substitute for these native soundness and completeness arguments.

Completeness uses exactly Pc996 in section11, relative to the retained
ordinary arithmetic, full syntactic-refutation and foundational contracts.
Both complete positive P66 witness maps and the uniform Carrier65
corollary are included. No old packed witness is substituted.

The immediate complete source is `../padding-staircase-independent/PROOF.md`,
SHA256 `69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8`.
The local phase lemma is expanded here, not used as an unproved citation.
The complete finite language remains the radix55 page
`../../candidates/one-page-compact66-radix55/equation.tex`, SHA256
`440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`.
The retained positive P66, signed-source bridge, ordinary arithmetic and
complete syntactic calibration are the full contracts explicitly named
by that source and its predecessors, now used at the new native interface.

## 1. Complete finite language and the explicit floor-rank bijection

Let `old_t_j`, j=0..942, denote every one of the943 indexed old tiles of
the pinned radix55 page, with all430 actions, the whole436-character seed,
62-character alphabet, closed decoder and every indexed tile family
retained. The integer represented by that seed may equivalently be
printed in decimal; this proof changes no decoded action. First define
abstract admissible tiles

    b_0=old_t_0, b_i=old_t_(i+1), 1<=i<=941.

The removed tile is exactly `old_t_1=(5,0,0,0)`, with unscaled selector
coefficient6145. Old selector1 is zero in every pre-deletion cell because
its first-mask bit is set. Hence this deletion preserves and reflects
the whole admissible language, not just a chosen family of computations.
Write `b_i=(w_i,n_i,p_i,s_i)` and define

    u_i=w_i+2^8*n_i+2^17*p_i+2^25*s_i,
    a_i=1+2^10*(1+u_i), M=2^44,
    pi(0)=0,
    pi(i)=1+sum_(j=1)^941 floor((M-1+a_j-a_i)/M), 1<=i<=941.

The complete indexed tile list has942 distinct tuples. The four color
ranges fit the displayed mixed-radix packing, so distinct tuples have
distinct u_i and a_i. Its complete coefficient calibration gives
`0<a_i<M`. Consequently every summand in the rank formula is0 or1,
and it equals1 exactly when a_j>a_i. The941 non-Start weights are
strictly ordered: pi is an exact permutation of1..941, with the larger
weights assigned the smaller positions. Start remains at0 independently
of its weight. These assertions involve all942 coefficients, with no
unspecified tie-breaking or sorting algorithm in the equation recipe.

Define the new physical tile at position pi(i) to be b_i. This is a
complete explicit bijection onto precisely the allowed old selectors.
The original initializer `old_t_929=(3,436,4,4)` is abstract b_928 and
has physical position504 under pi. All indexed families are transported
through this same map; no action, machine state, color or transition is
changed or selected by an unspecified index.

On each cell, and therefore on every finite rectangle or periodic/helical
word, the bijection preserves and reflects the full selector assignment,
every tile color, edge equality, marked Start and signal/computation
condition. Its inverse restores every allowed old selector and inserts
zero at old selector1. Thus the whole retained syntactic-refutation
calibration, including independently cofinal canonical rectangles,
transfers. No previous packed integer is reused: new words are encoded
afresh at the new positions and new B. The permutation preserves the
whole sum and maximum of all selector coefficients.

Write the physical tiles as `t_j=(w'_j,n'_j,p'_j,s'_j)` and put

    tcomp_j=(255-w'_j,511-n'_j,255-p'_j,511-s'_j),
    uold_j=w'_j+2^8*n'_j+2^17*p'_j+2^25*s'_j,
    ucomp_j=2^34-1-uold_j.

Genuine complemented horizontal colors lie in6..255 and vertical colors
in73..511; empty cells have zero colors. This componentwise bijection
preserves and reflects every edge equality and periodic/helical seam,
with the retained state/color calibration and full index map above.

Selector0 remains Start, with complemented tuple `(253,76,252,510)`.
Its south bits1..8 lie at physical943..950 and current-copy tests961..968.
Its complemented East bit0 is zero. The marker at996 receives the bare
Start contribution and the shared18 contribution from physical Eastbit0
at978; its spatial predecessor987 is absent. Consequently its odd
non-temporal part is Start+Eastbit0. For every decoded cell these two
bits cannot both be one: a Start's Eastbit0 is zero. Their sum is Boolean.
After full labels are recovered, forced Start therefore supplies an odd
marker contribution. This fact is not used before the separate
fractional-phase argument and full label recovery.

For reference the exact sorted terminal tiles are

    t_940=(206,10,0,0), t_941=(0,0,0,0).

Both complemented south values are511. The earlier local south-bit0
contradiction at offset20 is therefore unavailable. Section7 instead
proves uniform global exclusions for both19 and20. The proof needs only
that each selected terminal tile has its own fixed south value, which
already follows from count decoding and the complete finite language.

## 2. The whole doubled count lemma with two Boolean summands

Put `rho=2^47`, `M=2^44=rho/8`, `M'=2M=2^45=rho/4`, and
`mu=M'-4=2^45-4`. Let `x_j` be arbitrary Boolean selectors with
`n=sum_j x_j<=942`, and W an arbitrary unsigned34-bit copied-label value.
The reflected part of the clause has

    Q=sum_j(2^34-ucomp_j)*x_j+W,
    Acl=2n+2^11*Q.

The physical flag does not appear in Q. Let the actual incoming carry
satisfy0<=k<=57 and let the temporal summand tau_c and the extra bare
summand b each be Boolean. Suppose the actual digit of
`Acl+k+tau_c+b` avoids mu. The complete low part satisfies

    0<=2n+k+tau_c+b<=2*942+57+1+1=1943<2048.

The nine tests at bits2..10 force this low part to be in0..3, hence
n<=1. If n=1, then `k+tau_c+b<=1`; neither k nor tau_c is assumed
zero at this stage. The34 tests at bits11..44 require
`Q=0 mod2^34`, since the low part creates no carry into bit11.

If n=0, then Q=W<2^34, so W=0 and k+tau_c+b lies in0..3. If n=1,
then `0<Q<2^35`, so Q=2^34 and W=ucomp_j. The clause therefore recovers
the empty state or exactly one genuine tile with all34 labels, whether
or not its temporal source was absent beforehand. The flag remains
arbitrary Boolean. No equality involving the flag is used in this lemma.

Conversely an empty reflected value0 with total small summand in0..3
passes mu and has no outgoing carry. An occupied reflected value is
`M'+2<rho`; with k=tau_c=0 and either b=0 or b=1 its actual digit
`M'+2+b` passes mu and has no outgoing carry. Removing multiples of rho
does not alter any tested bit. The proof below establishes the Boolean
hypothesis on tau_c before applying this lemma in every cell; b is a
physical dummy bit x_977 and is already Boolean independently of decoding.

## 3. Full physical support, coefficients and fixed tuple

Set `L=1997`, `d=47L=93859`, `B=rho^L`, and `beta=B-1`. The full support is

    Es={0..941} union {942..950} union {960..968}
       union {969..976} union {978..985}
       union {977,996}.

There are978 physical positions:976 weighted positions, one zero-coefficient
Boolean dummy at977, and a separate zero-coefficient Boolean marker at996.
There is no high dummy. Position978 is the weighted east-bit0 label.
Define every unscaled coefficient `c_e`, `0<=e<=3296`, by

    c_j=1+2^10*(uold_j+1)=1+2^10*(2^34-ucomp_j), j=0..941;
    c_(978+j)=2^(10+j), c_(969+j)=2^(27+j), j=0..7;
    c_(960+j)=2^(18+j), c_(942+j)=2^(35+j), j=0..8;
    every unlisted c_e=0, including c_977=c_996=0.

The actual reflected weights are `c'_e=2c_e`. Every selector weight is
below M', all doubled weights are even, and the doubled labels sum to
M'-2048. Thus `max c'_e<M'`. The unscaled coefficient sum is6145 below
that of the Boolean-dummy4027 source. With
`G_m(x)=sum_(j=0)^(m-1)x^j`, the complete unscaled polynomial is

    Phi(x)=sum_(i=0)^941 a_i*x^pi(i)
           +2^10*x^969*(x^9+2^17)*G_8(2x)
           +2^18*x^942*(x^18+2^17)*G_9(2x).

The two geometric sums expand to exactly the34 label coefficients above,
with no marker or dummy weight. The selector part is the exact floor-rank permutation
defined in section1; the34 label terms are unchanged. Separately the
physical support is the disjoint union
`[0,950]`, `[960,985]`, `{996}`: the first interval joins all942
selectors to nine south labels, and the second joins the remaining25
labels to dummy977. Physical support is not inferred from nonzero Phi.
These explicit expansions prove both concise recipe identities. Define

    Lambda=rho^995,
    DC=rho^18+rho^996+sum_(e=0)^985 c'_e*rho^(995-e),
    DR=rho^9, K=DC+B*DR,
    MC=beta-sum_(e in Es)rho^e,
    Ccore=rho^960*G_9(rho)+rho^987*G_8(rho)+rho^996,
    Z=8*rho*G_916(rho),
    MF_native=4+(2^45-4)*Lambda+Ccore+Z
             =8*G_917(rho)-4+(2^45-4)*Lambda+Ccore,
    MF_source=MF_native+beta.

The equivalent closed recipes are

    K=rho^18+rho^996+rho^(L+9)+2*Lambda*Phi(1/rho),
    MC=beta-G_951(rho)-rho^960*G_26(rho)-rho^996,
    MF_source=beta+8*G_917(rho)-4+(2^45-4)*Lambda+Ccore.

The first reflected exponent is995-985=10. The sum terminates at985,
the last possible nonzero coefficient, so every written power is
nonnegative; the zero marker coefficient does not create a negative
power. Neither bare term collides with a nonzero reflected coefficient:
the respective indices are995-18=977 and995-996=-1, both zero by the
specified support and zero extension. The identity
`4+8*rho*G_916(rho)=8*G_917(rho)-4` combines only origin and padding.
The source mask is shifted by beta exactly once.

The whole fixed language and coefficient formula give the finite facts

    T459=sum_(e=459)^996 c'_e=137820284543942,
    sum_(e=942)^996 c'_e=M'-2048=35184372086784,
    T459+2^10+60<rho.                                (T)

These concern the entire array, including every sorted selector and
label coefficient. They are independently checked from the complete
indexed tile list. The T459 bound is used only in the early staircase,
through field536; the eventual whole low reset uses preliminary
one-hotness and selector/control-source separation.

## 4. Scalar boxes and the outer recovery

The sole clause tests43 bits. The17 label-copy tests and one combined Start/East marker
test add18. The low block8*G_917(rho)-4 has coefficient4 at origin0
and coefficient8 at each of fields1..916, giving917 bits: one bit2
origin test and916 bit3 padding tests. Therefore

    pc(MF_native)=978, pc(MC)=d-978,
    MC=2 mod4, MF_native=4 mod8.

All tested fields are disjoint. MC clears exactly978 bits, one at every
physical position. New selector1 is allowed and carries the largest
non-Start selector weight in the complete floor-rank ordering.
There is no forbidden new selector and no exceptional +rho restoration.
The zero-weight marker and precisely bit0 of the sole dummy are cleared.
There is no extra dummy-bit clearing; a digit2 or3 at977 meets an MC bit,
whereas digits0 and1 do not. Removing the exceptional field1 term does not
change origin residues, since rho is divisible by8. Padding fields1..916
are disjoint from origin0, the copy fields960..968 and987..994, marker996
and clause995. Every low-block coefficient is4 or8, both below rho. The highest native
mask field is996, below L; no test is placed at the product tail.
Every DC coefficient is below rho, with no nonzero bare/reflected
collision; section5 proves the complete support statement. Hence

    0<MC<beta, 0<MF_native<beta, 0<DC<B,
    beta>=31 odd, K>0, 0<MC<beta<MF_source<2beta.

The retained positive arithmetic and inverse-population argument uses
these scalar boxes, origin residues and complementary populations before
native interpretation. It supplies `q=B^N`, positive C,F, `F+C<q`,
`0<F<q-1`, and for `J=1+B+...+B^(N-1)` the actual masks

    (C-1) AND (MC*J+1)=0,
    F AND (MF_native*J-1)=0.                            (1)

C has Boolean digits on every position in Es, including the sole dummy977.
Absent positions are zero, every new selector is allowed, and Start is
forced at the origin. Marker values and the dummy are arbitrary Boolean at this
stage, independently of selectors. No extra0/2 part is permitted, and no
alignment, occupation or carry-free conclusion has yet been used.

## 5. Complete reflected, copy, marker and clause geometry

All physical positions other than996 are at most985. There is one
reflected band, with first exponent10. The shared bare exponent18
corresponds to c'_977=0, and bare996 lies above the reflected band.
Their coefficients are both1. The spatial residue9 lies below the band.
Every reflected coefficient occurs once and is below M', so every DC
coefficient is below rho without combining any coincident nonzero terms.
Since L=1997>2*996, circular support differences add no case.

Formal product support satisfies

    maxdeg(DC*C_cell)=2*996=1992<L,
    maxdeg(reflected*C_cell)=995+996=1991,
    maxdeg(DR*C_cell)=9+996=1005<L.

The bare-marker product, not clause-plus-marker, controls the first bound.
At output h let the entire reflected contribution be

    E_h=sum_(f in Es) c'_(995+f-h)*x_f,

with every coefficient outside the specified array zero. Every c' is even.
For0<=h<=536, the coefficient index is at least459. Each has at most one
Boolean source, so the complete suffix in(T) gives

    E_h=0 mod2 for every h,
    0<=E_h<=T459 for h<=536.                           (2)

This needs no count, occupation, alignment or label equality. For h<10
there is no reflected contribution; every later contribution is retained.

There is a second, conditional bound for all fields0..995. Every reflected
source is in the same current B-cell. If n<=1, all selector sources
together contribute at most one coefficient below M'. A nonselector
source f>=942 has coefficient index

    995+f-h>=995+942-995=942.                          (2a)

All nonzero coefficients at such indices belong to the fixed label
family. Different sources have distinct coefficient indices, so arbitrary
Boolean control sources contribute at most the whole label sum M'-2048.
No agreement between these bits and any tile has yet been assumed. Thus

    E_h<2M'-2048 for0<=h<=995, conditional on n<=1.    (2b)

In particular this covers the incoming reset for marker996, as well as
every label-copy test. At marker996 itself only evenness is needed for
the early parity statements; its aligned outgoing reset is proved below.

Before temporal addition the complete tested-field identities are

    target960+j: current942+j + E_(960+j), j=0..8;
    target987+j: current969+j + spatial978+j + E_(987+j), j=0..7;
    target995: all current coefficients c'_e + currentdummy977;
    target996: currentselector0 + currentEastbit0 + E_996.

The temporal-copy spatial predecessors951..959 are absent. Spatial-copy
targets987..994 are absent from Es; their two unit sources are exactly
the intended West and East labels. The bare marker lies above all these
tests. At marker996 the shared18 source is978 (Eastbit0) and spatial
predecessor987 is absent. The marker remains a zero-weight physical bit.

At clause995 the bare996 term has no source, bare18 supplies dummy977,
and spatial predecessor986 is absent. Its complete non-temporal value is
Acl+x_977 with a Boolean extra independent of any decoding. Predecessor994
is also the last spatial-copy target: its unit sources are currentWestbit7
at976 and spatialEastbit7 at985. Its reflected contribution is the
adjacency sum treated in section8; its aligned temporal source is absent.

The shared18 term occurs exactly once. Its use by both copy families and
the clause does not duplicate its coefficient. Every low reflected term
is included in E_h; no absence is claimed where the band actually overlaps.

## 6. A full cyclic carry bound before interpretation

In soundness the retained arithmetic recovery gives X=2^R and q=B^N.
Since X=wq and w is positive integral, w=2^(R-dN). Modulo q-1 its action
is a cyclic binary rotation. Completeness uses B^width directly. Thus the
following treatment of arbitrary field offsets and binary phases covers
the actual transport in both directions.

Let Csum_prev be the complete Boolean-dummy coefficient sum before
removing old selector1. The retained whole weighted derivation gives

    Csum_old=(1075/8)*rho-Cold+965470,
    Cold>106rho, Csum_prev=Csum_old-3M<28rho+965470,
    Csum=Csum_prev-6145<28rho+965470.

Cold is fixed by the old threshold
`7904*(Cold+3)+8=118788496120850159560`; the comparison
`7904*(106rho+3)+8=117913245443814349992` proves its lower bound.
The exact6145 deletion follows from old_t_1=(5,0,0,0). This is a bound
on the complete coefficient sum used by the new single band, not an
assertion that old and new kernels coincide.

Here Csum is the unscaled sum. The actual reflected coefficient sum is
`Csum'=2*Csum<56rho+1930940`, with every coefficient doubled once.
The descending rank is a permutation, so this whole sum is unchanged.

Each reflected coefficient has at most one Boolean predecessor at any
output, because it occurs in exactly one band. The two bare terms and
DR contribute at most three Boolean units. There is no extra dummy part
anywhere. Thus, before any count, phase, occupation or label recovery,

    Uraw<=Csum'+3<56rho+1930943.

Both distinct bare terms are counted exactly once. There is no
extra dummy contribution or coincident nonzero DC coefficient.

For every whole-cell offset and fractional binary phase0..46, a temporal
digit is at most `rho/2`. Each original digit is Boolean, so its shifted
value stays below rho even at phase46; there is no spill into another
field. In every phase1..46 every temporal digit is even. Every raw total
therefore satisfies

    0<=a_j<(113/2)*rho+1930943,
    a_j+57<58rho,

since `1931000<rho`. The monotone cyclic map
`k_j -> floor((a_j+k_(j-1))/rho)` preserves the finite box0..57.
Iteration from zero stabilizes, and cyclic telescoping identifies its
digit word with the transport residue. In soundness, strict F from(1)
already identifies that representative and excludes the zero/all-ones
ambiguity; completeness constructs the word first.

The full temporal support is a translate of Es, including the zero-weight
marker and Boolean dummy, with no additional spill position. Write bph
for its fractional binary phase. Two sufficient reset bounds will be
used, in their stated domains:

    bph<=10 and 0<=h<=536:
        E_h+3+2^bph+57 <= T459+2^10+60 < rho;
    n<=1 and 0<=h<=995, in any phase:
        E_h+3+2^bph+57 < 2M'-2048+rho/2+60 < rho.     (2c)

The first uses only the complete coefficient tail(2), not count or label
decoding. It also resets the predecessor53 of the first staircase field54.
The second uses (2a)..(2b) and preliminary one-hotness, not copied-label
equalities. Since2M'=rho/2 and2048>60, it is strict even at phase46.
Section7 proves n<=1 without presupposing this second reset. It then gives
zero incoming carry at every South-copy test, the other copies and
marker996. Fractional phase is excluded using the nine South tests and
the actual Start clause; marker parity is used only after full labels
are recovered. Its separate aligned outgoing reset is proved in section8.

## 7. Early padding staircase, preliminary count and full alignment

At clause995 the temporal summand is2^bph*epsilon with epsilon Boolean,
regardless of the whole-field offset or whether its source is physically
present. Every doubled selector coefficient is2 modulo2048, every doubled
label coefficient is0 modulo2048, and the only extra non-temporal summand
is x_977. Let k denote its actual incoming carry in0..57. No vanishing
of k, low-band reset, label equality or alignment is yet assumed.

For phases0..6, the complete low part obeys

    0<=2n+k+x_977+2^bph*epsilon
      <=2*942+57+1+64=2006<2048.                      (2d)

Reduction by rho preserves its residue modulo2048. The clause mask's
bits2..10 force this low part into0..3, and hence n<=1 in every cell.
For phases11..46, the temporal term is divisible by2048. The low residue
is exactly2n+k+x_977<=1942<2048, and the same tested bits again force
n<=1 in every cell. These are preliminary count conclusions only; they
do not recover labels or use any copy test.

It remains to handle phases7..10. The first bound in(2c) resets every
field0..536 before counting. In particular every padding test at a field

    h=54+r, 0<=r<=482,
    S_r=x_0+x_1+...+x_r,

has zero incoming carry. These are all genuine bit3 tests among1..916;
none is the exceptional origin. In its reflected sum, the coefficient
index corresponding to source f is

    995+f-(54+r)=941+f-r.

It is a selector coefficient exactly for0<=f<=r, since r<=482 and all
these physical source positions are selectors. The other nonzero
coefficients have indices942..985 and are label coefficients, each a
multiple of2048. Thus the entire reflected value is2*S_r modulo16.
The bare marker term has no input because h<=536<996. The shared18
term and spatial9 term contribute at most two Boolean units in total.
The temporal term2^bph*epsilon is divisible by16 in these phases. Hence
the actual padding digit is congruent modulo16 to

    2*S_r+u_h, 0<=u_h<=2.                             (2e)

Both the zero incoming carry and preservation of modulo16 under radix
reduction were established before this test is used. Suppose S_482>=4.
Starting with S_0=x_0<=1, every next prefix count changes by0 or1, so
there is a first r for which S_r=4. Then(2e) is8,9 or10 modulo16,
all with bit3 set, contradicting the actual mask. Therefore S_482<=3.
There are459 remaining selector positions483..941, so n<=3+459=462
in every cell. This conclusion uses neither labels nor occupation.

At the clause in these phases the complete low part now satisfies

    0<=2n+k+x_977+2^bph*epsilon
      <=2*462+57+1+1024=2006<2048.                    (2f)

The same bits2..10 force it into0..3, hence n<=1. The staircase is used
only to avoid a possible low-part wrap; it does not assume the desired
one-hot conclusion. A raw low value2*512+1024=2048 shows why this
intermediate step cannot simply be omitted in phase10.

Now n<=1 in every cell in every fractional phase. Bound(2c) therefore
resets every field0..995, including all incoming South-copy carries,
without assuming full labels. The origin mask forces selector0, hence
the origin's unique selector is Start. Write its still-arbitrary physical
copied-label word as W in[0,2^34), and put

    U=253+2^8*76+2^17*252+2^25*510=17145810173,
    c'_0=2+2^11*(2^34-U)=69752854530.

The actual origin clause avoids mu and has raw value

    c'_0+2^11*W+k+x_977+2^bph*epsilon, 0<=k<=57.

This equation does not assume W=U. For bph<=10 its complete low subtotal
`2+k+x_977+2^bph*epsilon` is at most1084<2048. The low tests force it
into{2,3}, and the high tests then give W=U. For bph>=11 the low subtotal
is2+k+x_977<=60; the same low tests force{2,3}, while the high tests give

    W=U-2^(bph-11)*epsilon modulo2^34.                 (2g)

Taking the actual rho-digit preserves all these tested residues. In(2g)
W is the unique representative in[0,2^34). Its South component
floor(W/2^25) cannot vanish. If epsilon=0 it is510. For11<=bph<=35,
subtracting a power below bit25 can lower510 by at most1. For36<=bph<=44,
the result is510-2^(bph-36), at least254. For bph45 or46 the power
vanishes modulo2^34. The low-phase case already gave South510.

If bph>0, each of the nine current South bits must instead be zero:
its copy has zero incoming carry, even reflected background, no spatial
predecessor, and an even temporal contribution. Its bit0 mask therefore
forces that current bit0. All nine would give South0, contradicting the
actual Start clause. Thus bph=0. Full label decoding was not used to
exclude a fractional phase, and no marker value was assumed.

Every temporal digit is now Boolean, even before its field offset is
known. The complete clause is Acl+x_977+tau_c with incoming carry in0..57,
so section2 recovers zero or one selector and all34 labels in every cell.
An occupied cell gives k+x_977+tau_c<=1. At this stage the marker is still
arbitrary Boolean. Its decoded odd part at the forced Start is1+0=1,
so its test requires an odd temporal digit. This is the first use of
the marked cell's Eastbit0 value in alignment.

Let r be the remaining rho-field offset modulo L, so the temporal
preimage of target e is e-r modulo L. The odd temporal digit at996
comes from a physical position f in Es. Every such f lies in0..996,
so the ordinary representative is

    r=996-f, 0<=r<=996.                              (3)

The current forced Start is now decoded. Its south bits1..8 require
odd temporal digits at targets961..968, with zero incoming carries and
only even reflected backgrounds. If f=996 in(3), r=0. Otherwise f<=985,
so11<=r<=996. If r>961, target961 has wrapped preimage L+961-r,
at least L-35>996, which is absent. Hence r<=961. For11<=r<=17,
the interval[961-r,968-r] contains951, absent from Es. For21<=r<=961,
targets961 and962 have two distinct selector preimages in0..941 in the
same temporal cell, contradicting its one-hotness. Only18,19,20 remain.

At offset18 the marker temporal source is996-18=978, Eastbit0. Let
e_i be the decoded current Eastbit0 and delta_i its Start selector.
The zero incoming carry and even reflected background give

    e_(theta(i))=e_i xor delta_i.

Here theta is a fixed permutation of the finite cells. In every decoded
cell, delta_i and e_i cannot both be1: delta_i=1 selects Start, whose
Eastbit0 is0. Thus e_i+delta_i is itself Boolean and the parity equality
is the ordinary equality

    e_(theta(i))=e_i+delta_i.                          (3c)

Summing around any theta-cycle gives sum(delta_i)=0. The forced Start
belongs to a cycle with delta=1, a contradiction. This needs no unique
Start and no assumption about any non-Start tile's Eastbit0. Offset18
is therefore excluded. Offsets19 and20 are handled globally as follows.

Let S_i be the decoded complemented south color in cell i, with S_i=0
for an empty cell. Let delta_(j,i) indicate selector j in that cell.
Decoded one-hotness gives at most one such indicator. Each physical
terminal selector is a fixed tile and so has a fixed south value; neither
of the following arguments imposes an additional restriction on that value.

At offset19, all nine targets960..968 have preimages941..949 in the
same temporal cell without wrap. The current sources are all nine south
bits. Even reflected backgrounds and zero incoming carries give

    S_i=(2*S_(theta(i)) mod512)+delta_(941,theta(i)),    (3a)

where theta is a fixed permutation of the finite cells. On any one of
its finite cycles, orient the indices so `x_(j+1)=2*x_j+epsilon_j mod512`,
with `epsilon_j=delta_(941,j)`. Write sstar for the fixed complemented
south value of tile941. Then epsilon_j=1 implies x_j=sstar.

Suppose this cycle contains the forced Start and choose x_0=510. The
three-step recurrence modulo8 is

    x_0=4*epsilon_(-3)+2*epsilon_(-2)+epsilon_(-1) mod8.

Since510=6 mod8, both epsilon_(-3) and epsilon_(-2) are1. Thus
x_(-3)=x_(-2)=sstar and `sstar=2*sstar+1 mod512`, forcing sstar=511.
Starting instead from x_0=510, however, the entire ordinary doubling
orbit is

    510 -> 508 -> 504 -> 496 -> 480 -> 448 -> 384
        -> 256 -> 0 -> 0.

It never reaches511, so every epsilon on this forward orbit must be0.
It cannot return to510, contradicting the assumed finite cycle. This
uniform argument holds for every possible fixed terminal south value.
In the actual sorted language sstar=511: the graph really does contain
its self-loop, so it would be false to claim all graph cycles are zero.
The needed conclusion is only that no cycle contains the forced Start510.

At offset20, all nine targets have preimages940..948 in one temporal
cell. The first two are selectors940 and941; the remaining seven are
south bits0..6. The exact relation is

    S_i=(4*S_(theta(i)) mod512)
          +delta_(940,theta(i))+2*delta_(941,theta(i)). (3b)

At most one of the two indicators is1. Consequently every S_i has
residue0,1 or2 modulo4. At Start, S_i=510, so the small summand in(3b)
must be2. It follows that `S_(theta(i))=127 mod128`, and therefore
`S_(theta(i))=3 mod4`, contradicting the universal residue restriction.
No specific terminal tile color or occupation conclusion was used.

Therefore r=0. The dependency order is complete: the three phase ranges
first give preliminary one-hotness, using the early staircase only for
7..10. The conditional selector/control bound then resets the low fields.
The actual Start-clause residue and nine South parities exclude nonzero
fractional phase without full labels. The Boolean-temporal count lemma
then decodes every cell. Start's decoded Eastbit0 and South bits constrain
the whole-field offset, and the three finite-cycle arguments exclude
18,19,20. No marker, occupation or post-alignment equality is used early.

## 8. Every mask and reset, and the changed shifted-marker relation

After alignment each of the17 label-copy tests has its two intended
Boolean summands, even reflected background and zero incoming carry.
Its bit0 mask forces all spatial east/west and temporal south/north
equalities. The marker has current Start delta_i, current Eastbit0 e_i,
temporal marker a and even E_996. Since delta_i+e_i is Boolean, its
parity mask gives the exact relation

    a_(temporal predecessor of i)=delta_i+e_i.          (4)

This marker need not be one in every occupied cell or be the Start
indicator alone. Equation(4) records its full changed interface.

Put `Aadj=sum_(e,e+1 in Es)c'_(e+1)*x_e`. Every x_e, including dummy977,
is Boolean. The complete sole-clause predecessor is

    field994: Aadj+currentWestbit7+spatialEastbit7.

Its aligned temporal source994 is absent. The marker bare term lies
above994, and there is no second reflected band. At most one selected
predecessor meets a selector coefficient, while every label coefficient
occurs at most once, including adjacencies941->942,968->969 and977->978.
The dummy contributes c'_978 at most once. Hence

    Aadj<=2M'-2048,
    Aadj+currentWestbit7+spatialEastbit7+57<rho.

The predecessor resets carry. Clause995 has no aligned temporal source
and its actual value is x_977 in an empty cell or M'+2+x_977 in an
occupied cell. Both Boolean dummy choices pass mu and have no outgoing
carry. Empty cells are allowed at this stage; their dummy need not be0.

At marker996 the reflected nonselector indices are at least941. Their
sum is at most c'_941 plus the whole label sum. Here sorted terminal
t_941=(0,0,0,0) gives c'_941=2050, so this sum is at most M'+2.
The one selector contribution is below M'. Adding the two current units,
one temporal bit and the global57 carry gives less than2M'+62<rho.
Thus the aligned marker also resets outgoing carry. Its incoming carry
was already reset at clause995 before this bound is applied.

At any padding field h in1..916, every reflected source f satisfies

    0<=f<=985-995+h<=906.

These are selector positions in the same current cell, so after decoding
E_h is0 or one doubled coefficient. A doubled selector coefficient is2
modulo2048 and a doubled label coefficient is0 modulo2048. The full
aligned raw value is

    E_h+x_(current,h-18)+x_(spatial predecessor,h-9)
       +x_(temporal predecessor,h).

The bare marker has no input since h<996; absent or negative-index sources
are zero. The three unit terms are Boolean. Therefore its residue modulo
2048 is in0..5 and bit3 is zero. Incoming carry is zero by section6,
including h=1 because field0 resets, and the actual digit is below rho.
This proves all916 tests without asserting that their entire digits
are small: a large multiple of2048 can be present.

Every simultaneous safe dummy subset preserves these bounds. Dummy977
cannot be a reflected padding source0..906. Its shared, marker-bare,
spatial and temporal outputs995,1973,986,977 all lie above916; reflected
dummy outputs start at995+977-985=987, also above padding.

The complete highest products are field1991 with raw c'_0*x_996 and
field1992 with raw x_996 from bare996. The first is below M', and its
incoming carry is at most57, so its outgoing carry is zero. Field1992
therefore has Boolean digit and zero outgoing carry. Fields1993..1996
are raw and actual zero. This four-field top band resets every B-cell
origin and supplies the strict representative bound. No low-padding
field is assumed zero to derive this tail statement.

At aligned origins only the temporal selector contributes, since every
DC/DR exponent is positive. Canonical one-Start words with nonzero stride
have zero at the first origin and0/1 elsewhere, as required by its shifted
bits and later bit2 tests. Safe dummy subsets preserve these resets.

For soundness genuine complemented colors are positive and empty colors
zero. Spatial equality propagates occupation around the one-cell rotation
cycle from forced Start; hence all n_i=1. Equation(4) fixes a consistent
marker pattern from the decoded tile labels. Start's north76 differs
from south510, so temporal stride is nonzero. Inverse complementation
and the exact floor-rank bijection recover the whole old admissible
marked blank computation and its syntactic refutation.

## 9. Fresh canonical words with a shifted marker

A refutation gives, by the retained whole signal/helical theorem, genuine
one-Start admissible rectangles with independently cofinal width and
height. Transfer their selectors through the explicit old-to-physical map of section1,
complement their colors, and encode all labels and selectors afresh on Es.
Set the marker in cell j equal to Start plus Eastbit0 in its temporal
successor, so(4) holds exactly; set the sole dummy initially zero. With
transport B^width this is `a_j=delta_(j+width)+e_(j+width)` modulo N.
That sum is Boolean for every decoded tile, including Start. It is a
fresh pattern, not an all-one or Start-only flag. Every simultaneous
Boolean subset of the safe low-977 bits leaves it and all tile data intact.

Construct the cyclic fixed point before imposing strict F. The words are
decoded by construction, and the same carry bound and aligned resets
apply. In particular every low padding digit has residue in0..5 modulo
2048 for every safe dummy subset, and every occupied sole clause has actual value M'+2 or M'+3,
proving positivity.
The top zero band and highest physical position give, for every subset,

    0<F<q/rho<q/7,
    0<C<q/rho^(L-997),
    2C+F<q*(1/7+2/rho^(L-997))<q/3,
    alpha=q-F-C>0.                                    (5)

These bounds exclude the all-ones representative and imply `0<F<q-1`.
The shifted marker is independent of every safe dummy choice; no preceding
packed word, all-one flag rule, or old tail bound is reused.

## 10. Actual binary rank and ordinary safe increments

Set `t=dN`, `q=2^t`, `Mbig=q^2`, and

    S'=(C-1)+qF,
    Tmask=(MC*J+1)+q*(MF_native*J-1).

Both words lie below Mbig and are disjoint by the actual masks. Their
mask populations are `(d-978)N+1` and `978N+1`, from origin changes
10 to 11 and 100 to 011. In the combined8*G_917-4 block, subtracting1
changes only the very first coefficient4 to3; it does not borrow through
any later field or alter the other916 bit3 tests. Thus `pc(Tmask)=t+2`.
The actual defining rank
with exactly one source-mask shift is

    R=[q(q-F)-C]*(q^2-1)+(MC+q*MF_source)*J
     =(Mbig-S')*(Mbig-1)+Tmask
     =(Mbig-1-S')*Mbig+(S'+Tmask).

Binary disjointness gives `pc(R)=3t+2`. Independently, the origin residues
`C=1 mod4,F=0 mod4,J=1 mod4` give `R=3 mod4`. Neither identity assumes
native global carry-freeness.

For a safe unused low-dummy bit at cell j with `j+1<N` and `j+width<N`,
put

    deltaC=rho^977*B^j,
    deltaRaw=(K+B^width)*deltaC.

Its DC exponents are at most1973: the reflected maximum is1972,
the marker-bare output1973, and the shared18 output995. None of these
odd bare terms collides with a nonzero reflected coefficient, because
the would-be indices are-1 and977. Every local coefficient is therefore
below rho and the local residues are distinct. The spatial exponent is986
and the temporal exponent977. Those two later cells, if equal, have
distinct exponents. There is no further coefficient collision or wrap,

and `0<deltaRaw<q/rho^2<q/7`. At every intermediate subset, (5) implies
`F_old+deltaRaw<2q/7<q-1`. The canonical representative therefore changes
by the exact ordinary equality `F_new-F_old=deltaRaw`. Subtracting the
actual rank formula gives

    deltaR=-Gamma*B^j,
    Gamma=rho^977*(q^2-1)*[1+q*(K+B^width)].             (6)

## 11. All fixed prime factors and the complete controller construction

For this exact L and K, Pc996 consists of precisely these finite requirements:

- 47 and1997 are distinct primes, L=1997 and d=93859=47*1997 is odd
  and squarefree;
- the exact orders of2 modulo47,1997 are23,1996 respectively,
  each coprime to d;
- an odd prime lambda>d has45908 dividing kappa=lambda-1,
  B^2!=1 modulo lambda and v_lambda(B^kappa-1)=1;
- Hs=1+B*K+B^2 is nonzero modulo47,1997 and lambda.

Here1996=4*499 and45908=lcm(23,1996)=23*1996. Exact-order evidence
includes complete powers and proper-order tests for primes23 and2,499.
Every primality and factorization requirement is an elementary finite
statement. The complete new B and K enter Hs; the auxiliary prime and
orders are proof data, not coefficients of the equation.

The finite discharge uses lambda275449=6*45908+1 and the residues

    p          B       K       B^2       Hs
    47         3       31      9         9
    1997       911     1656    1166      51
    275449     189436  35639   226927    6093.

The valuation-one lift is
`B^(lambda-1)=35711411953=1+275449*129648 modulo lambda^2`.
Its quotient129648 is nonzero and below lambda. This fixed data is
checked using all tile and label coefficients and the whole new K.

Since B=2^d and d is coprime to each listed order, B has those same
orders modulo both fixed primes. Both exceed2, so B²-1 is a unit
modulo the whole squarefree d. Every fixed prime factor is included
explicitly in the proof below.

Choose fresh independently large positive r_w,r_h and set

    width=lambda^r_w, height=lambda^r_h,
    N=width*height=lambda^n,
    height>lambda, N>d*lambda^2,
    T_orbit=N/lambda, C0=d*lambda.

Then `T_orbit>C0` and `width<T_orbit`. The whole helical-padding contract
allows these independently cofinal dimensions. Powers of lambda are1
modulo kappa. Both fixed orders divide kappa, and Fermat's
theorem supplies B^kappa=1 modulo lambda. Consequently

    q=B^N=B^width=B mod p, for p=47,1997,lambda.

The non-power-of-two factors of Gamma reduce to B²-1 and Hs at every
one of these primes. Their explicit nonvanishing makes Gamma a unit
modulo the whole dN, including all powers of lambda.

LTE gives exact order T_orbit for `B^kappa` modulo lambda^n. The same
power is1 modulo47 and1997, hence modulo their squarefree product d.
Since lambda>d is prime, CRT applies to d and lambda^n and identifies
the full orbit with

    {1+C0*z:0<=z<T_orbit} modulo dN.

Indeed the orbit has T_orbit elements, all congruent1 modulo d and
modulo lambda, and those two congruences specify exactly T_orbit
residues modulo dN. This verifies the entire composite fixed modulus,
not just any chosen prime divisor.

Every residue modulo dN is a Boolean subset sum of

    {B^(2+kappa*j):0<=j<T_orbit} together with B^3.

Indeed normalize the target by B^-2 and choose epsilon in{0,1} such
that subtracting epsilon*B leaves a nonzero residue modulo lambda. Its
least representative a0 modulo C0 satisfies `1<=a0<C0<T_orbit` and
`gcd(a0,T_orbit)=1`. Write the target as `a0+C0*u` and solve

    a0*z0+a0*(a0-1)/2=u modT_orbit.

The a0 consecutive distinct orbit coordinates sum to the target. Include
B^3 exactly when epsilon=1. All bit indices are distinct and the largest
is `2+kappa*(T_orbit-1)=N-T_orbit-lambda+3`; its one-cell and width
translates are below N. Cell3 is distinct and safe. All bits avoid the
first origin.

Apply the subset to `(R0-d*width)*Gamma^-1 mod dN`. Equation(6) gives
the final actual rank `R=d*width mod dN`, with all native conditions and
slack preserved. Rank growth gives

    R>q(q^2-1)>dN+d*width,
    w=2^(R-dN)>B^width, w=B^width mod(q-1).

Write `(K+B^width)C=F+z0(q-1)`. Positivity and strict F give z0>=0,
so the positive integer

    z=1+z0+[(w-B^width)/(q-1)]C

satisfies `(K+w)C+(q-F)-z*(q-1)=1`.

## 12. The whole positive P66 and both full witness maps

Exactly fifteen independent positive inputs are used:
`J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma`. All other symbols are
polynomial abbreviations with the four new fixed ports:

    q=beta*J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY, k=eta+zeta,
    ell=EkY, c=kY+eta, a=E+Y, H=4a+3, Delta=a^2+H,
    D=X+ac+gamma*H,
    R=[(q-1)(q-F)+alpha]*(q^2-1)+(MC+q*MF_source)*J,
    V=f^2*(cT-R)-c, S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2, Nk=k-hE-R,
    Nt=(K+w)C+(q-F)-z*(q-1), Ns=Delta*f^2-S^2,
    P66=N0*N1*Na*Nk*Nt*Ns-Delta=0.

For soundness `Delta=(a+2)^2-1>0`, and the proof-only normalized Ns is
the integer `f^2-Delta*i^2*c^4`. Cancellation gives six integer units.
The retained negative-Pell and mod-4 arguments force four normalized norm
signs positive. The coupled Nk/Nt signs and weak C>=0 remain until the
full main/strong/signed-auxiliary index recovery excludes the negative
branch using eta,zeta>0. At the required stage, the new scalar boxes
give `q(q^2-1)<R<q^4-2` and `E>=q^4>R+2`.

The exact positive bridge is `T_old=f*T`, since
`c*((f*T)*f-1)-R*f^2=f^2*(cT-R)-c`; the strong multiplier bridge is
`i_ordinary=Delta*i`. Neither divides an arbitrary witness. The retained
ratio/population argument supplies `X=2^R`, q=B^N and masks (1), after
which the new sections 5..8 recover the genuine computation/refutation.
No Pc996 premise enters this direction.

For completeness under Pc996, sections 9..11 supply fresh actual native
data with `t=dN`, `pc(R)=3t+2`, `R=3 mod4`, and retained source bounds
`3q+1<=R<q^4`. The complete half-binomial/ratio converse chooses fresh
positive outer data with `X=2^R`, `Y=sq^3`, `v2(Y)=3t`, and s positive
odd. Odd d,N,R make both `w=2^(R-t)` and proof-only `X/q^3=2^(R-3t)`
positive squares. Both odd t modulo 4 phases remain allowed.

Put `A=a+2`, even, and `c=psi_A(R)`, odd. Choose `m=cR`,
`f=chi_A(m)`, and `i=psi_A(m)/c^2`. The c-th power expansion of the
Pell unit at R gives divisibility by c²: the first odd term contains
c² and later odd terms c³. Its odd numerator makes i positive odd;
`f^2=1+Delta*i^2*c^4`, so actual Ns is Delta.

The entire odd-index recurrence

    Q0(Z)=1, Q1(Z)=4Z-3,
    Q_(j+1)(Z)=(4Z-2)*Q_j(Z)-Q_(j-1)(Z)

gives `chi_t(2j+1)=t*Q_j(t^2)`, `Q_j(0)=(-1)^j*(2j+1)` and
`Q_j(1-A^2)=(-1)^j*psi_A(2j+1)`. Set

    Vstar=chi_S(R)/S, ystar=psi_S(R),
    Tstar=(Vstar+c+R*f^2)/(c*f^2).

R=3 mod4 and `S²=Delta*(f²-1)` give `Vstar=-c modf²` and
`Vstar=-R modc`. Since `gcd(c,f)=1` and `f²=1 modc`, Tstar is positive
integral and `Vstar=f²*(c*Tstar-R)-c`. The norm at S gives Na=1.
The fresh outer witnesses give `N0=N1=Na=Nk=Nt=1`, actual `Ns=Delta`;
their whole product is Delta, so P66 vanishes.

The front remains 66 live integer-leaf binary operations and exact degree
157. Factor degrees are 22,18,62,7,2,46; with `q0=beta*J,k0=eta+zeta`,
the complete leading form is

    -8*q0^91*h*gamma*i^4*k0^13*w^13*s^26*T^2*f^4
       *(w*(q0-F-alpha)-z*q0).

The selected coefficient `8*beta^92` is nonzero. These are retained
uniform symbolic facts at new fixed ports, not equality of specialized
old and new polynomials or a new symbolic calculation.

### The uniform Carrier65 corollary at these exact ports

The complete ordinary uniform carrier theorem is
`../carrier65-independent/PROOF.md`, SHA256
`53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749`.
Its scalar conditions are exactly those proved in section4, and the
canonical P66 signs and R>0 needed by its converse are supplied above.
Therefore the exact new1997 ports also admit fourteen positive inputs

    J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma,

with `tau=E*n+k-R` and equation

    N0*N1*Na*Nt*Ns-Delta=0.

Every new positive zero restores `h=(k-R-1)/E>0` and tau as a positive
parent P66 witness, by that theorem's sign-before-positivity and first
Pell-congruence argument. Every canonical zero just constructed yields
the positive integer `n=(tau-k+R)/E`. All four new fixed ports are
preserved in both maps; no previous packed integer or coefficient tuple
is substituted. The literal uniform front has65 integer-leaf operations
and degree150, with nonzero coefficient `-8*beta^88`. This composition
changes the arithmetic front only. It does not identify the new native
tuple with any earlier specialization, and it leaves both its finite
certificate and the full native proof above necessary.

## 13. Consequence and review boundary

Under Pc996 and the retained explicit ordinary syntactic-refutation and
foundational calibration, ZFC proves that this equation has no positive
integer zero exactly when Con(ZFC), for both the displayed P66 equation
and its explicit Carrier65 corollary. A separately checked finite Pc996
certificate removes that finite premise for the exact fixed tuple.
No consistency decision, actual unsolvability, global minimum or new
end-to-end proof-assistant/internal-ZFC replay is claimed.

The explicit floor-rank map preserves and reflects the whole language.
The preliminary count uses the low clause in phases0..6 and11..46 and
the483-field padding staircase in phases7..10. Its one-hot conclusion
supplies conditional low resets through995. The actual forced-Start
clause then has nonzero South in every fractional phase, while the nine
South copies force zero in every positive phase. Only after excluding
those phases is full count/label decoding used. The marker's decoded
Start+Eastbit0 relation constrains field offsets. Offset18 contradicts
a nondecreasing Boolean value on a finite Start-cycle; the complete
uniform19/20 arguments retain the sorted graph's real511 self-loop.

All916 bit3 tests, the changed canonical Boolean marker, every safe dummy
subset, the bare-marker product at1992, four top zeros, actual mask/rank
identities and all fixed-prime controller units are proved at this tuple.
Both positive P66 maps and the uniform Carrier65 composition are included.
The ordinary argument is not a bounded search for native witnesses.

The rejected nearby C997/A996 placement is not this tuple. There the
actual sorted tile1=(0,433,0,438) receives two extra units, selector1 and
Eastbit1, yielding M'+4 and failing bit2. An initial pre-sorting calibration
mistake was caught by the finite author before a complete proof. Moving
the clause below the marker to995 removes that obstruction; its sole
extra is the freely chosen Boolean dummy. A good modular controller alone
would not have repaired the rejected placement.

This adaptation is authored by `/root/controller_certificate`, using
the padding-staircase and below-marker-clause ideas of
`/root/circuit_reduction`, the independently shared copied-South phase
lemma, and the earlier complete sorted proof of
`/root/complemented47_review`. ROOT coordinates independent finite and
mathematical review. Every accepted predecessor is unchanged.
