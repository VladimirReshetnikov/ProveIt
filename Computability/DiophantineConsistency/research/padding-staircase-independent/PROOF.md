# Padding before decoding: the complete length2011 tuple

This complete ordinary argument retains the explicit descending order of
all941 non-Start selector weights and marker1004, moves the sole doubled
clause to1005, and uses prime length2011. Every admissible tile and
transition remains. The new step uses existing padding tests before label
decoding. Fractional phases0..6 and11..46 directly force at most one
selector from the low clause bits. For phases7..10, padding fields64..546
first force at most three of the first483 selectors: a first prefix count
of four would violate their bit3 test. This bounds the total count by462,
so the low clause bits then force at most one selector in this case too.
This preliminary one-hot fact bounds the low reflected selector part;
every remaining reflected coefficient belongs to the fixed label family.
Their combined bound resets all low carries without any decoded-label
premise. Marker parity then excludes every nonzero fractional phase.
The ordinary whole count and two global Start-cycle arguments subsequently
exclude field misalignment. No early copied-label, occupation or
marker-value premise is used.

After count recovery, each padding reflection has at most one selector
source and residue0 or2 modulo2048. At most three Boolean units give a
residue in0..5, avoiding bit3. The origin still tests bit2, so their
combined native mask is `8*G_917(rho)-4`. There remain978 physical
positions and978 native tests. The longer floor recipe is a possible
printed-size cost; a smaller raw tuple does not imply a smaller page.

Soundness uses the explicit finite language/coefficient facts below,
but no controller premise. Completeness uses exactly Pcst in section11,
relative to the retained ordinary arithmetic, full syntactic-refutation
and foundational contracts. Every scalar, physical support, mask, phase,
reset and canonical-subset interface is proved below, followed by both
full positive P66 witness maps and the uniform Carrier65 corollary. All
packed words are encoded afresh and no previous witness is substituted.

The immediate complete source is `../phase-split-independent/PROOF.md`,
SHA256 `934c7984038b578a68b1396fffdb8db71a9039b01a86455a74c8639264a1b966`.
The complete finite language is the radix55 page
`../../candidates/one-page-compact66-radix55/equation.tex`, SHA256
`440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`.
The retained positive P66, signed-source bridge, ordinary arithmetic and
complete syntactic calibration are the full contracts explicitly named
by that source and its predecessors. They are used at the new interface.

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
Its south bits1..8 are all one at physical943..950 and current-copy
tests961..968. The bare marker monomial copies selector0 to1004. After
Start decoding all nine intended unit contributions are one, without
assuming a marker value, occupation or unique Start. The marker's
unit contribution is already one before decoding because the first mask
forces selector0 directly. Section5 includes every reflected contribution;
its evenness preserves these parities.

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
physical bit x_1 and is already Boolean independently of decoding.

## 3. Full physical support, coefficients and fixed tuple

Set `L=2011`, `d=47L=94517`, `B=rho^L`, and `beta=B-1`. The full support is

    Es={0..941} union {942..950} union {960..968}
       union {969..976} union {978..985}
       union {977,1004}.

There are978 physical positions:976 weighted positions, one zero-coefficient
Boolean dummy at977, and a separate zero-coefficient Boolean marker at1004.
There is no high dummy. Position978 is the weighted east-bit0 label.
Define every unscaled coefficient `c_e`, `0<=e<=1004`, by

    c_j=1+2^10*(uold_j+1)=1+2^10*(2^34-ucomp_j), j=0..941;
    c_(978+j)=2^(10+j), c_(969+j)=2^(27+j), j=0..7;
    c_(960+j)=2^(18+j), c_(942+j)=2^(35+j), j=0..8;
    every unlisted c_e=0, including c_977=c_1004=0.

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
`[0,950]`, `[960,985]`, `{1004}`: the first interval joins all942
selectors to nine south labels, and the second joins the remaining25
labels to dummy977. Physical support is not inferred from nonzero Phi.
These explicit expansions prove both concise recipe identities. Define

    Lambda=rho^1005,
    DC=rho^18+rho^1004
       +sum_(e=0)^1004 c'_e*rho^(1005-e),
    DR=rho^9, K=DC+B*DR,
    MC=beta-sum_(e in Es)rho^e,
    Ccore=rho^960*G_9(rho)+rho^987*G_8(rho)+rho^1004,
    Z=8*rho*G_916(rho),
    MF_native=4+(2^45-4)*Lambda+Ccore+Z
             =8*G_917(rho)-4+(2^45-4)*Lambda+Ccore,
    MF_source=MF_native+beta.

The equivalent closed recipes are

    K=rho^18+rho^1004+rho^(L+9)+2*Lambda*Phi(1/rho),
    MC=beta-G_951(rho)-rho^960*G_26(rho)-rho^1004,
    MF_source=beta+8*G_917(rho)-4+(2^45-4)*Lambda+Ccore.

The first reflected exponent is `1005-985=20`; all reciprocal powers
are integral. The bare term at1004 copies exactly selector0 there,
while its coefficient coincides with one reflected coefficient. Their
combined coefficient `1+c'_1` is explicitly retained, not discarded.
The identity `4+8*rho*G_916(rho)=8*G_917(rho)-4` combines only the
origin and padding tests. The native source mask is shifted by beta
exactly once; its closed recipe uses that beta explicitly.

The whole fixed language and explicit coefficient formula give the finite
integer facts

    T459=sum_(e=459)^1004 c'_e=137820284543942,
    c'_1=30099357829122,
    sum_(e=942)^1004 c'_e=M'-2048=35184372086784,
    T459+2^10+60<rho.                                (T)

These are statements about the entire specified array, including all
reordered selectors and all label coefficients. They are independently
checked from the complete indexed tile list in the finite certificate;
they are not estimates inferred from a partial sample. The proof uses
the displayed T459 bound only in the early padding staircase, through
field546. The eventual whole low reset uses the preliminary-count and
selector/label-source separation proved in sections6..7.

## 4. Scalar boxes and the outer recovery

The sole clause tests43 bits. The17 label-copy tests and one Start-copy
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
are disjoint from origin0, the copy fields960..968 and987..994, marker1004
and clause1005. Every low-block coefficient is4 or8, both below rho. The highest native
mask field is1005, below L; no test is placed at the product tail.
After combining the coincident terms at exponent1004, every DC coefficient
is below rho; section5 proves the complete collision statement. Hence

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

## 5. Every reflected overlap and the complete sole-clause geometry

All support members other than1004 are at most985. There is exactly one
reflected band, whose first exponent is1005-985=20. The shared bare
exponent18 lies below it. The bare marker exponent1004 coincides with
the reflected coefficient `c'_(1005-1004)=c'_1`. Its full coefficient
is `1+c'_1<M'+1<rho`. Every other reflected coefficient occurs once,
is below M', and is distinct from exponent18. The spatial residue9 is
also distinct. After this single explicit combination, every DC digit
is below rho. Since `L=2011>2*1004`,
circular support differences add no case.

Formal product support satisfies

    maxdeg(DC*C_cell)=1005+1004=2009<L,
    maxdeg(DR*C_cell)=9+1004=1013<L.

At any output field h, write the entire reflected contribution as

    E_h=sum_(f in Es) c'_(1005+f-h)*x_f,

where every coefficient outside0..1004 is zero. All c' are even, so
E_h is even at every field, without a decoding premise. For0<=h<=546
its coefficient index is at least459. Each such coefficient has at most
one Boolean source, so the whole high-index sum in(T) bounds it:

    E_h=0 mod2 for every h,
    0<=E_h<=T459, h<=546.                             (2)

No one-hot, occupation, alignment or label equality is used in(2).
For h<=19 the reflected contribution is zero; at later fields it is
explicitly retained. In particular marker1004 has an even reflected
background, which may be large before count recovery.

There is a second, conditional bound for the whole reset band0..1003.
Every reflected source belongs to the same current B-cell. A selector
source f<=941 contributes at most one coefficient below M' if the cell
has n<=1. Every nonselector source f>=942 has coefficient index

    1005+f-h>=1005+942-1003=944.                       (2a)

All nonzero coefficients at such indices belong to the fixed label
family942..985. Different sources have different coefficient indices,
so their entire contribution is at most the whole label sum M'-2048.
This includes arbitrary Boolean physical controls; no equality with a
decoded tile is required. Therefore, conditional only on n<=1,

    E_h<2M'-2048, 0<=h<=1003.                         (2b)

At marker1004, the nonselector coefficient indices are at least943,
so the same coarse bound also applies after one-hot recovery. We use
only its evenness and the preceding reset for fractional-phase parity;
its separate aligned outgoing reset is proved below.

Before temporal addition every complete tested-field identity is

    target960+j: current942+j + E_(960+j), j=0..8;
    target987+j: current969+j + spatial978+j + E_(987+j), j=0..7;
    target1004: currentselector0 + E_1004;
    target1005: all current coefficients c'_e + currentselector1.

At the nine temporal copies, spatial predecessors951..959 are absent;
E_(960+j) need not vanish, but is even. At the eight spatial
copies, tested fields987..994 are
absent from Es, and the one bare18 term supplies exactly the intended
west label. The bare1004 term lies above every label-copy target; at its
own test the other bare/spatial predecessors986,995 are absent. Its extra
reflected contribution is E_1004, also even.

At clause1005, the bare marker supplies selector1. The shared-copy
and spatial inputs987 and996 are absent. Its non-temporal raw value
is therefore exactly `Acl+b`, where b=x_1 is Boolean even before
count recovery. The predecessor1004 coincides with the marker test.
Its bare marker input is selector0; shared-copy input986 and spatial
input995 are absent. After alignment its temporal input is the physical
Boolean marker. Its full identity is therefore the reflected adjacency
sum plus x_0 plus that temporal marker. Section8 proves its outgoing
reset explicitly, without assuming that every marker is one.
The bare marker's own marker input contributes only at2008, not at these
tested fields.

The bare18 monomial occurs exactly once in DC and K. Its contribution
to two different families of tested outputs does not double its coefficient.
Every added reflected term in the low tests is included in E_h. The
early staircase uses(2), and the whole conditional reset uses(2b);
no claim of absence is made where a reflected term is actually present.

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

This bound counts the bare marker and its coincident reflected term
separately as summands; combining their DC coefficient neither removes
nor duplicates a contribution.

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

    bph<=10 and 0<=h<=546:
        E_h+3+2^bph+57 <= T459+2^10+60 < rho;
    n<=1 and 0<=h<=1003, in any phase:
        E_h+3+2^bph+57 < 2M'-2048+rho/2+60 < rho.     (2c)

The first uses only the complete coefficient tail(2), not count or label
decoding. It also resets the predecessor63 of the first staircase field64.
The second uses (2a)..(2b) and preliminary one-hotness, not copied-label
equalities. Since2M'=rho/2 and2048>60, its strict inequality holds even
at phase46. Section7 proves n<=1 in every phase without presupposing
the second reset. It then makes all seventeen copy tests and marker1004
receive zero incoming carry. Reduction modulo the even radix preserves
the marker's low bit regardless of outgoing carry. The aligned outgoing
reset at that same field, which is the clause predecessor, is proved
separately in section8.

## 7. Early padding staircase, preliminary count and full alignment

At clause1005 the temporal summand is2^bph*epsilon with epsilon Boolean,
regardless of the whole-field offset or whether its source is physically
present. Every doubled selector coefficient is2 modulo2048, every doubled
label coefficient is0 modulo2048, and the only extra non-temporal summand
is x_1. Let k denote its actual incoming carry in0..57. No vanishing
of k, low-band reset, label equality or alignment is yet assumed.

For phases0..6, the complete low part obeys

    0<=2n+k+x_1+2^bph*epsilon
      <=2*942+57+1+64=2006<2048.                      (2d)

Reduction by rho preserves its residue modulo2048. The clause mask's
bits2..10 force this low part into0..3, and hence n<=1 in every cell.
For phases11..46, the temporal term is divisible by2048. The low residue
is exactly2n+k+x_1<=1942<2048, and the same tested bits again force
n<=1 in every cell. These are preliminary count conclusions only; they
do not recover labels or use any copy test.

It remains to handle phases7..10. The first bound in(2c) resets every
field0..546 before counting. In particular every padding test at a field

    h=64+r, 0<=r<=482,
    S_r=x_0+x_1+...+x_r,

has zero incoming carry. These are all genuine bit3 tests among1..916;
none is the exceptional origin. In its reflected sum, the coefficient
index corresponding to source f is

    1005+f-(64+r)=941+f-r.

It is a selector coefficient exactly for0<=f<=r, since r<=482 and all
these physical source positions are selectors. The other nonzero
coefficients have indices942..985 and are label coefficients, each a
multiple of2048. Thus the entire reflected value is2*S_r modulo16.
The bare marker term has no input because h<=546<1004. The shared18
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

    0<=2n+k+x_1+2^bph*epsilon
      <=2*462+57+1+1024=2006<2048.                    (2f)

The same bits2..10 force it into0..3, hence n<=1. The staircase is used
only to avoid a possible low-part wrap; it does not assume the desired
one-hot conclusion. A raw low value2*512+1024=2048 shows why this
intermediate step cannot simply be omitted in phase10.

Now n<=1 in every cell in every fractional phase. The second reset in
(2c), using the selector/control-source separation(2a), resets all
fields0..1003 without any decoded labels. At the origin the first mask
forces selector0. Its complete non-temporal marker contribution is
1+E_1004, with E_1004 even, and the marker has zero incoming carry.
The marker mask therefore requires an odd temporal digit. Every
bph=1..46 instead makes every temporal digit even, so bph=0. No copied
label, occupation, known marker value or uniqueness of Start was used.

After this phase conclusion, every temporal digit in every cell is
Boolean, since transport now shifts whole rho-fields of the Boolean C
word without spill. In particular the sole clause1005 receives a bit
tau_c in{0,1}, even before its field offset is known. Its full raw
non-temporal value is Acl+x_1 by section5, and its actual incoming
carry lies in0..57. Section2 applies with total small summand
k+tau_c+x_1<=59 and recovers zero or one selector and all34 labels in
**every cell**. An occupied clause gives k+tau_c+x_1<=1, which is
sufficient for this decoding; no separate vanishing of k or tau_c is
used before alignment. The marker is still arbitrary Boolean.
There is no assumption that the clause was temporally clean.

Let r be the remaining rho-field offset modulo L, so the temporal
preimage of target e is e-r modulo L. The odd temporal digit at1004
comes from a physical position f in Es. Every such f lies in0..1004,
so the ordinary representative is

    r=1004-f, 0<=r<=1004.                              (3)

The current forced Start cell is now decoded. Its calibrated south
bits1..8 contribute one to targets961..968. These targets have zero
incoming carry, their extra reflected terms are even, and no other
non-temporal summand is present. Each low-bit mask therefore requires
an odd temporal digit. If f=1004 in(3), then r=0. Otherwise f<=985 and
19<=r<=1004. If r>961, target961 has preimage `L+961-r`, at least L-43
and hence greater than1004. That wrapped residue is absent from Es,
so r<=961. For21<=r<=961, targets961 and962 have distinct selector preimages
`961-r` and `962-r` in0..941. Neither wraps, so they belong to the same
temporal B-cell. Both must be one, contradicting its decoded n<=1.
Offsets19 and20 are excluded globally as follows.

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

Therefore r=0. The dependency order is complete: phases0..6 and11..46
give preliminary count directly, while phases7..10 first use the early
padding staircase and then preliminary count. The selector/control-source
bound supplies all low resets; marker parity forces fractional phase zero
despite its even reflected background. This makes the clause's temporal
summand Boolean, and the whole count lemma decodes every cell;
the forced Start's labels and the two finite-cycle arguments exclude
every nonzero field offset. No second clause, known marker value or
post-alignment equality is used at an earlier stage.

## 8. Every mask and reset, and the shifted Start-marker relation

After alignment each of the17 label-copy tests has its two intended
Boolean summands, an even reflected background as specified in section5,
and zero incoming carry. The actual digit has that same parity, forcing
all spatial east/west and temporal south/north label equalities. The
marker test at1004 has current Start selector x_0, temporal marker a,
and even E_1004. Its parity mask therefore gives

    a_(temporal predecessor of i)=x_(0,i).              (4)

This marker tracks the shifted Start indicator. It is not asserted to be
one in every occupied cell.

Put `Aadj=sum_(e,e+1 in Es)c'_(e+1)*x_e`. Every x_e, including x_977,
is Boolean. The complete sole-clause predecessor is

    field1004: Aadj+x_0+a_temporal.

The first extra unit is the bare1004 term applied to selector0. The
second is the aligned temporal Boolean marker. Every other bare/spatial
source is absent, and there is no foreign reflected band. The temporal
marker is retained even though its coefficient in Phi is zero.
At most one selected predecessor meets a selector coefficient, and every
label coefficient occurs at most once. The doubled label sum is M'-2048, including
adjacencies941 to942,968 to969 and977 to978. The Boolean dummy contributes
c'_978 at most once and creates no additional term. Consequently

    Aadj<=2M'-2048,
    Aadj+x_0+a_temporal+57<=2M'-2048+59<rho.

The predecessor resets carry. With alignment established, clause1005
has no temporal source because1005 is absent from Es. An empty decoded
cell has x_1=0, so its actual clause value is0. An occupied cell has
actual value `M'+2+x_1`, either M'+2 or M'+3. All these values avoid
mu and have zero outgoing carry, independently of marker values.

For a padding field h in1..916 the full reflected contribution E_h may
be nonzero. Any contributing source f satisfies

    0<=f<=985-1005+h<=896.

Thus every reflected source is a selector position in the same current
cell. After count decoding there is at most one such source, so E_h is
either0 or one c'_e. A doubled selector coefficient is2 modulo2048,
and a doubled label coefficient is0 modulo2048. Hence E_h is0 or2
modulo2048, including the empty case. The complete aligned raw value is

    E_h+x_(current,h-18)+x_(spatial predecessor,h-9)
       +x_(temporal predecessor,h).

The bare marker has no input since h<1004. Any absent or negative-index
source is zero. The last three terms are Boolean, so the full raw residue
modulo2048 is in0..5. Adding these units creates no carry into bit11, and bit3 is
zero. The incoming carry is zero by section6, including h=1 because
field0 resets; the actual digit is below rho by that same reset bound.
Since2048 and rho are multiples of16, reduction by either preserves
bit3. This proves all916 padding tests without asserting their actual
digits are at most5: a large multiple of2048 may be present.

Every simultaneous safe Boolean dummy subset retains the decoded
selectors and this bound. More specifically, dummy977 cannot be one of
the reflected padding sources0..896, and its bare/spatial/temporal
outputs995,1981,986,977 all lie above916.

Field2009 is the complete last product field, with raw value
`c'_0*x_1004`. Since c'_0<M' and incoming is at most57, its digit is at
most M'+57 and its outgoing carry zero. The remaining field2010 is raw
zero and therefore actual zero. This one untested top field resets every
B-cell origin and gives the strict representative bound.
The new padding argument does not assume that the low fields themselves
are zero or uniformly small; their residue constraint is the needed fact.

At aligned origins only the temporal Start selector contributes, because
all DC/DR exponents are positive. Canonical one-Start words with nonzero
stride have zero at the first origin and0/1 elsewhere, as required by
the shifted first-origin bits and later bit-2 tests. Safe low-dummy
subsets preserve this and all resets.

For soundness, genuine complemented colors are positive and empty colors
are zero. Spatial equality propagates occupation through the one-cell
rotation cycle from the forced Start; all n_i=1. Equation(4) consistently
fixes the marker pattern according to Start selectors, without requiring
that pattern to be constant. Start's north76 differs from south510,
so the temporal stride is nonzero. Inverse complementation and the exact
floor-rank bijection from section1 recover the complete old admissible marked blank
computation and its syntactic refutation.

## 9. Fresh canonical words with a shifted marker

A refutation gives, by the retained whole signal/helical theorem, genuine
one-Start admissible rectangles with independently cofinal width and
height. Transfer their selectors through the explicit old-to-physical map of section1,
complement their colors, and encode all labels and selectors afresh on Es.
Set the marker in cell j equal to the Start selector in its temporal
successor, so (4) holds exactly; set the sole dummy initially zero. With
transport B^width, this means `a_j=x_(0,j+width)` modulo N. This is a
freshly encoded marker pattern, not an all-one flag. Every simultaneous
Boolean subset of the safe low-977 bits leaves it and all tile data intact.

Construct the cyclic fixed point before imposing strict F. The words are
decoded by construction, and the same carry bound and aligned resets
apply. In particular every low padding digit has residue in0..5 modulo
2048 for every safe dummy subset, and every occupied sole clause has actual value M'+2 or M'+3,
proving positivity.
The top zero band and highest physical position give, for every subset,

    0<F<q/rho<q/7,
    0<C<q/rho^(L-1005),
    2C+F<q*(1/7+2/rho^(L-1005))<q/3,
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

Its DC exponents are at most1982, its spatial exponent is986, and
its temporal exponent is977. The coincident local terms at exponent1981
combine to coefficient `1+c'_1<rho`; every other local coefficient
is a single doubled coefficient below rho or the bare unit at995.
Thus the complete ordinary local sum has distinct residues after this
explicit combination, with every coefficient below rho. The two later
cells, if equal, have distinct exponents986 and977. There is no further
coefficient collision or physical wrap,
and `0<deltaRaw<q/rho^2<q/7`. At every intermediate subset, (5) implies
`F_old+deltaRaw<2q/7<q-1`. The canonical representative therefore changes
by the exact ordinary equality `F_new-F_old=deltaRaw`. Subtracting the
actual rank formula gives

    deltaR=-Gamma*B^j,
    Gamma=rho^977*(q^2-1)*[1+q*(K+B^width)].             (6)

## 11. All fixed prime factors and the complete controller construction

For this exact L and K, Pcst consists of precisely the finite requirements:

- 47 and2011 are distinct primes, with L=2011 and
  `d=94517=47*2011` odd and squarefree;
- the exact orders of2 modulo47,2011 are23,402 respectively,
  and each order is coprime to d;
- an odd prime `lambda>d` has `9246 | kappa=lambda-1`,
  `B^2!=1 modlambda`, and `v_lambda(B^kappa-1)=1`;
- `Hs=1+B*K+B^2` is nonzero modulo47,2011 and lambda.

Here `402=2*3*67` and `9246=lcm(23,402)=23*402`.
Exact-order evidence includes the complete powers and proper-order tests
for primes23 and2,3,67 respectively. Every primality and factorization
requirement is an elementary finite statement. The complete new K and
B are required in Hs; auxiliary orders and lambda are proof data, not
coefficients of the equation.

The intended finite discharge uses lambda120199=13*9246+1 and the
following complete residues:

    p          B       K       B^2       Hs
    47         37      26      6         29
    2011       1283    1995    1091      674
    120199     37435   114787  99283     36379.

The valuation-one lift is
`B^(lambda-1)=7300767062=1+120199*60739 modlambda^2`, with its
nonzero quotient60739 strictly below lambda. This exact fixed data is
checked from all tile and label coefficients and the whole K.

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

    q=B^N=B^width=B mod p, for p=47,2011,lambda.

The non-power-of-two factors of Gamma reduce to B²-1 and Hs at every
one of these primes. Their explicit nonvanishing makes Gamma a unit
modulo the whole dN, including all powers of lambda.

LTE gives exact order T_orbit for `B^kappa` modulo lambda^n. The same
power is1 modulo47 and2011, hence modulo their squarefree product d.
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
No Pcst premise enters this direction.

For completeness under Pcst, sections 9..11 supply fresh actual native
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
Therefore the exact new2011 ports also admit fourteen positive inputs

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

Under Pcst and the retained explicit ordinary syntactic-refutation and
foundational calibration, ZFC proves that this equation has no positive
integer zero exactly when Con(ZFC), for both the displayed P66 equation
and its explicit Carrier65 corollary. A separately checked finite Pcst
certificate removes that finite premise for the exact fixed tuple.
No consistency decision, actual unsolvability, global minimum or new
end-to-end proof-assistant/internal-ZFC replay is claimed.

The explicit floor-rank permutation preserves and reflects the whole language.
The three phase ranges use preliminary count before label recovery.
Phases7..10 first use every bit3 padding test in the483-field staircase
to bound the first483 selectors by3, then the low clause bits force
one-hotness. The other phases yield that preliminary count directly.
Selector/control-source separation then supplies the whole low reset;
marker parity excludes every nonzero phase, and the whole count lemma
recovers labels. The uniform global arguments exclude both offsets19
and20 without terminal
color restrictions, including the sorted graph's real511 self-loop. All916
bit3 padding tests follow from the complete selector-only reflected
sources and their residues modulo2048. The prime length2011 retains
one untested top zero field, strict representatives and every safe-subset
bound. The actual masks, origin shift, DC collision, rank and controller
are proved for this tuple, with both positive P66 maps included. All
fixed finite facts in(T) and the new controller are independently checked
by the complete certificate; the ordinary argument is not a bounded
search for native witnesses.
This adaptation is authored by `/root/controller_certificate`, using
the padding-staircase idea of `/root/circuit_reduction`, the complete
phase-split proof and the earlier sorted proof of
`/root/complemented47_review`. ROOT coordinates independent finite and
mathematical review. Every accepted predecessor is unchanged.
