# Uniform low-field padding: the complete length2963 tuple

This complete ordinary argument puts all916 padding tests at binary bit2
of fields1..916. After field alignment each such field has at most three
Boolean unit contributions and zero incoming carry, so bit2 is zero.
Together with the existing origin test, these917 bits have the concise
single-block mask `4*G_917(rho)`. No padding at the product tail is needed,
and the whole cell length decreases to2963.

The single clause1956 and low parity geometry are restated in full.
The forced Start's marker first recovers fractional binary phase zero
without tile or label decoding. Reflected label terms at the relevant
low tests are even and bounded. The clause's temporal bit is absorbed
into the count lemma's bounded small summand, and decoded Start labels
recover the remaining field alignment before padding is interpreted.

Soundness uses no new controller premise. Completeness uses exactly Pclp
in section11, relative to the retained ordinary arithmetic, complete
syntactic-refutation and foundational contracts. Every scalar, physical
support, mask, phase, reset and canonical-subset interface is proved
below, followed by both full positive P66 witness maps. All packed words
are encoded afresh with the new B and no old witness is substituted.

The immediate complete source is `../composite-length-independent/PROOF.md`,
SHA256 `08572f95382f4c5c1867d10f5fbf9c27859e1b3b58fc34663f63497d25a5f98a`.
The complete finite language is the radix55 page
`../../candidates/one-page-compact66-radix55/equation.tex`, SHA256
`440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`.
The retained positive P66, signed-source bridge, ordinary arithmetic and
complete syntactic calibration are the full contracts explicitly named
by that source and its predecessors. They are used at the new interface.

## 1. The complete admissible finite language and exact index bijection

Let `old_t_j`, j=0..942, denote every one of the943 indexed old tiles of
the pinned radix55 page, with all430 actions, the whole436-character seed,
62-character alphabet, closed arithmetic decoder and every indexed tile
family retained. Define the new942 tiles by the explicit map

    g(0)=0, g(j)=j+1 for1<=j<=941,
    t_j=old_t_(g(j)), j=0..941.

The removed tile is exactly `old_t_1=(5,0,0,0)`, whose selector coefficient
is6145. The correctly renamed initializer is now
`t_928=old_t_929=(3,436,4,4)`. All remaining indexed families and table
entries are transported through g; no action, seed symbol, machine state,
color or transition is changed or selected by an unspecified index.

In the pre-deletion native interpretation, old selector1 is zero in every
cell because the corresponding first-mask bit is set. The map g is an
exact bijection from the new selectors to precisely those old selectors
that are allowed. On every cell, and hence on any finite rectangle or
periodic/helical word, it preserves and reflects the whole admissible
selector assignment, every tile color, every edge equality, the marked
Start, and every signal/computation condition. The reverse map simply
deletes the identically zero old selector1. Therefore the complete retained
syntactic-refutation calibration, including its independently cofinal
canonical rectangles, transfers along this bijection. It is the same
admissible language, not an unproved restriction to a convenient subfamily.
No old packed integer word is reused: all new words are encoded afresh.

Writing `t_j=(w_j,n_j,p_j,s_j)`, define

    t'_j=(255-w_j,511-n_j,255-p_j,511-s_j),
    uold_j=w_j+2^8*n_j+2^17*p_j+2^25*s_j,
    ucomp_j=2^34-1-uold_j.

Genuine horizontal colors lie in6..255 and vertical colors in73..511;
empty cells have zero colors. This componentwise bijection preserves and
reflects every edge equality and periodic/helical seam, with the full
retained state/color calibration and the explicit index map above.

Selector0 remains the forced Start, with complemented tuple
`(253,76,252,510)`. Its south bits1..8 are all one, at physical positions
943..950 and current-copy tests961..968. The bare marker monomial copies
selector0 to1005. Once that forced Start's labels are decoded, all nine
intended unit contributions are one without assuming a marker value,
occupation or unique Start. The marker unit contribution alone is already
one before label decoding, because the first mask forces selector0
directly. Section5 proves that every additional reflected contribution
at these fields is even and does not alter their parity.
The other exact calibration is

    t_941=old_t_942=(4,437,2,437), t'_941=(251,74,253,74).

Its complemented south bit0 is zero. The whole pinned language and the
explicit g determine this tuple, not an independently chosen tile table.

## 2. The whole count lemma with a Boolean temporal summand

Put `rho=2^47`, `M=2^44=rho/8`, and `mu=2^44-2=M-2`. Let `x_j` be
arbitrary Boolean selectors with `n=sum_j x_j<=942`, and W an arbitrary
unsigned34-bit copied-label value. The non-temporal clause has

    Q=sum_j(2^34-ucomp_j)*x_j+W,
    Acl=n+2^10*Q.

The physical flag does not appear in Q. Let the actual incoming carry
satisfy0<=k<=29 and let the temporal summand be a Boolean bit tau_c.
Suppose the actual digit of `Acl+k+tau_c` avoids mu. Define the effective
small summand `k'=k+tau_c`, so0<=k'<=30. The nine tests at bits1..9
force n+k' to be0 or1 because `n+k'<=972<1024`. Thus n<=1, and the
occupied case n=1 has k'=0, hence separately k=0 and tau_c=0. The34 tests
at bits10..43 require `Q=0 mod2^34`; no carry from n+k' enters bit10.

If n=0, then Q=W<2^34, so W=0 and k+tau_c is0 or1. If n=1, then
`0<Q<2^35`, so Q=2^34 and W=ucomp_j. The clause therefore recovers
the empty state or exactly one genuine tile with all34 labels, whether
or not its temporal source was absent beforehand. The flag remains
arbitrary Boolean. No equality involving the flag is used in this lemma.

Conversely an empty raw value0 with k+tau_c equal0/1 has digit0/1 and
no outgoing carry. An occupied raw value is `M+1<rho`, passes mu when
k=tau_c=0, and has no outgoing carry. Removing multiples of rho does
not alter any tested bit. The proof below establishes the Boolean
hypothesis on tau_c before applying this lemma in every cell.

## 3. Full physical support, coefficients and fixed tuple

Set `L=2963`, `d=47L=139261`, `B=rho^L`, and `beta=B-1`. The full support is

    Es={0..941} union {942..950} union {960..968}
       union {969..976} union {978..985}
       union {977,1005}.

There are978 physical positions:976 weighted positions, one zero-coefficient
Boolean dummy at977, and a separate zero-coefficient Boolean marker at1005.
There is no high dummy. Position978 is the weighted east-bit0 label.
Define every coefficient `c_e`, `0<=e<=1005`, by

    c_j=1+2^10*(uold_j+1)=1+2^10*(2^34-ucomp_j), j=0..941;
    c_(978+j)=2^(10+j), c_(969+j)=2^(27+j), j=0..7;
    c_(960+j)=2^(18+j), c_(942+j)=2^(35+j), j=0..8;
    every unlisted c_e=0, including c_977=c_1005=0.

Each selector coefficient is below M; the labels sum to M-1024 and
`max c_e<M`. The coefficient sum is6145 below that of the Boolean-dummy4027
source. With `G_m(x)=sum_(j=0)^(m-1)x^j`, the complete polynomials are

    Psi(x,t)=x^969*(x^9+t^17)*G_8(tx)
             +t^8*x^942*(x^18+t^17)*G_9(tx)
             +(2-t)*x^1005,
    Phi(x)=sum_(j=0)^941 [1+2^10*(1+w_j+2^8*n_j+2^17*p_j+2^25*s_j)]*x^j
           +2^10*Psi(x,2).

Only the specializations Psi(x,1) and Psi(x,2) enter the construction.
The new marker term (2-t)*x^1005 has exactly the same values at both
specializations as t^34*(2-t)*x^1005. Thus deleting t^34 changes none of
the four fixed integers. Psi at one has35 coefficients equal to one and
includes the physical marker; Psi at two omits its weight. Physical support
must therefore never be inferred solely from nonzero Phi coefficients. Define

    Lambda=rho^1956,
    DC=rho^18+rho^1005
       +sum_(e=0)^1005 c_e*rho^(1956-e),
    DR=rho^9, K=DC+B*DR,
    MC=beta-sum_(e in Es)rho^e,
    Ccore=rho^960*G_9(rho)+rho^987*G_8(rho)+rho^1005,
    Z=4*rho*G_916(rho),
    MF_native=4+(2^44-2)*Lambda+Ccore+Z
             =4*G_917(rho)+(2^44-2)*Lambda+Ccore,
    MF_source=MF_native+beta.

The equivalent closed recipes are

    K=rho^18+rho^1005+rho^(L+9)+Lambda*Phi(1/rho),
    MC=beta-rho^977-G_942(rho)-Psi(rho,1),
    MF_source=beta+4*G_917(rho)+(2^44-2)*Lambda+Ccore.

The first reflected exponent is `1956-985=971`; all reciprocal powers
are integral. The bare term at 1005 copies exactly selector 0 there.
The identity `4+4*rho*G_916(rho)=4*G_917(rho)` combines only the
origin and padding tests. The native source mask is shifted by beta
exactly once; its closed recipe uses that beta explicitly.

## 4. Scalar boxes and the outer recovery

The sole clause tests43 bits. The17 label-copy tests and one Start-copy
test add18. The low block4*G_917(rho) tests bit2 once in each of fields
0..916, giving917 bits: one origin test and916 padding tests. Therefore

    pc(MF_native)=978, pc(MC)=d-978,
    MC=2 mod4, MF_native=4 mod8.

All tested fields are disjoint. MC clears exactly978 bits, one at every
physical position. New selector1 is allowed: it denotes old selector2.
There is no forbidden new selector and no exceptional +rho restoration.
The zero-weight marker and precisely bit0 of the sole dummy are cleared.
There is no extra dummy-bit clearing; a digit2 or3 at977 meets an MC bit,
whereas digits0 and1 do not. Removing the exceptional field1 term does not
change origin residues, since rho is divisible by8. Padding fields1..916
are disjoint from origin0, the copy fields960..968 and987..994, marker1005
and clause1956. Every low-block coefficient is4<rho. The highest native
mask field is1956, below L; no test is placed at the product tail.
Distinct kernel residues and coefficients below rho give

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

All support members other than1005 are at most985. There is exactly one
reflected band, whose first exponent is1956-985=971. The shared bare
exponent18 lies below it; the bare marker exponent1005 is distinct from
all its nonzero coefficients because `c_(1956-1005)=c_951=0`. The spatial
residue9 is also distinct. All DC coefficients are therefore below rho,
and each reflected coefficient occurs once. Since `L=2963>2*1005`,
circular support differences add no case.

Formal product support satisfies

    maxdeg(DC*C_cell)=1956+1005=2961<L,
    maxdeg(DR*C_cell)=9+1005=1014<L.

At any output field h, write the entire reflected contribution as

    E_h=sum_(f in Es) c_(1956+f-h)*x_f,

where every coefficient outside0..1005 is zero. For every0<=h<=1005,
its coefficient index is at least951, beyond every selector0..941.
Thus E_h consists only of distinct label coefficients, all even, and
unconditionally satisfies

    E_h=0 mod2, 0<=E_h<=M-1024.                        (2)

No one-hot, occupation, alignment or label-equality premise is used in(2).
For h<=970 the reflected contribution is zero; at higher low fields it
may be nonzero and is explicitly retained.

Before temporal addition every complete tested-field identity is

    target960+j: current942+j + E_(960+j), j=0..8;
    target987+j: current969+j + spatial978+j + E_(987+j), j=0..7;
    target1005: currentselector0 + E_1005;
    target1956: all current coefficients c_e.

At the nine temporal copies, spatial predecessors951..959 are absent
and E_(960+j)=0. At the eight spatial copies, tested fields987..994 are
absent from Es, and the one bare18 term supplies exactly the intended
west label. The bare1005 term lies above every label-copy target; at its
own test the other bare/spatial predecessors987,996 are absent. Its extra
reflected contribution is E_1005, even by(2).

At the clause1956, the bare marker's potential input951 is absent, as
are the shared-copy and spatial inputs1938 and1947. Its non-temporal raw
value is therefore exactly Acl. The predecessor1955 receives the bare
marker's input950, a Boolean south-bit8 label. The shared bare18 term
ends at1023, and the spatial9 term at1014. Its full identity is therefore
the reflected adjacency sum plus x_950; the reset is proved in section8.
The bare marker's own marker input contributes only at2010, not at these
tested fields.

The bare18 monomial occurs exactly once in DC and K. Its contribution
to two different families of tested outputs does not double its coefficient.
Every added reflected term in the low tests is included in(2); no claim
of its absence is made where it is actually present.

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

Each reflected coefficient has at most one Boolean predecessor at any
output, because it occurs in exactly one band. The two bare terms and
DR contribute at most three Boolean units. There is no extra dummy part
anywhere. Thus, before any count, phase, occupation or label recovery,

    Uraw<=Csum+3<28rho+965473.

For every whole-cell offset and fractional binary phase0..46, a temporal
digit is at most `rho/2`. Each original digit is Boolean, so its shifted
value stays below rho even at phase46; there is no spill into another
field. In every phase1..46 every temporal digit is even. Every raw total
therefore satisfies

    0<=a_j<(57/2)*rho+965473,
    a_j+29<30rho,

since `965502<rho`. The monotone cyclic map
`k_j -> floor((a_j+k_(j-1))/rho)` preserves the finite box0..29.
Iteration from zero stabilizes, and cyclic telescoping identifies its
digit word with the transport residue. In soundness, strict F from(1)
already identifies that representative and excludes the zero/all-ones
ambiguity; completeness constructs the word first.

Throughout fields0..1005 the reflected contribution obeys(2), while
the two bare terms and DR contribute at most3. Therefore

    (M-1024)+3+rho/2+29<rho

forces every outgoing carry there to zero in every fractional phase.
In particular the marker1005 and all seventeen label-copy tests receive
zero incoming carry before any tile-count or alignment conclusion.
The full temporal support is a translate of Es, including the zero-weight
marker and Boolean dummy, with no additional spill position.

## 7. Marker parity first, Boolean count second, Start alignment third

The actual first mask forces selector0 at the origin. Section5 identifies
the complete non-temporal contribution at marker1005 as this selector
plus E_1005, hence exactly `1+E_1005` in that cell. The latter summand
is even. Its incoming carry is zero by section6, and the entire raw
value stays below rho by the same low-field bound. Thus its actual low
bit is the low bit of one plus the temporal digit. The marker mask
requires that bit to be zero, so the temporal digit is odd. Every
fractional phase1..46 makes all temporal digits even. Consequently the
fractional binary phase is zero. This argument has used no count clause,
copied label, occupation, known marker value or uniqueness of Start.

After this phase conclusion, every temporal digit in every cell is
Boolean, since transport now shifts whole rho-fields of the Boolean C
word without spill. In particular the sole clause1956 receives a bit
tau_c in{0,1}, even before its field offset is known. Its full raw
non-temporal value is Acl by section5, and its actual incoming carry lies
in0..29. Section2 applies with effective summand k+tau_c<=30 and recovers
zero or one selector and all34 labels in **every cell**. An occupied
clause forces both incoming carry and temporal bit to zero; an empty
clause may have actual digit1. The marker is still arbitrary Boolean.
There is no assumption that the clause was temporally clean.

Let r be the remaining rho-field offset modulo L, so the temporal
preimage of target e is e-r modulo L. The odd temporal digit at1005
comes from a physical position f in Es. Every such f lies in0..1005,
so the ordinary representative is

    r=1005-f, 0<=r<=1005.                              (3)

The current forced Start cell is now decoded. Its calibrated south
bits1..8 contribute one to targets961..968. These targets have zero
incoming carry, their extra reflected terms vanish, and no other
non-temporal summand is present. Each low-bit mask therefore requires
an odd temporal digit. If f=1005 in(3), then r=0. Otherwise f<=985 and
20<=r<=1005. If r>961, target961 has preimage `L+961-r`, at least L-44
and hence greater than1005. That wrapped residue is absent from Es,
so r<=961. The remaining cases are:

- At r=20, target961 forces selector941 to be one. The already proved
  clause lemma fixes that source cell to tile941 with all complemented
  labels. Target962 also requires preimage942, the south-bit0 position,
  to be one. Tile941 has complemented south74 with bit0 zero, a contradiction.
- For21<=r<=961, targets961 and962 have distinct selector preimages
  `961-r` and `962-r` in0..941. Neither wraps, so they belong to the same
  temporal B-cell. Both must be one, contradicting its decoded n<=1.

Therefore r=0. The dependency order is complete: the even reflected
background preserves marker parity, which forces fractional phase zero;
that makes the clause's temporal summand Boolean; the stronger count
lemma decodes every cell including Start; its labels exclude every
nonzero field offset. No second clause, known marker value or
post-alignment equality is used at any earlier stage.

## 8. Every mask and reset, and the shifted Start-marker relation

After alignment each of the17 label-copy tests has its two intended
Boolean summands, an even reflected background as specified in section5,
and zero incoming carry. The actual digit has that same parity, forcing
all spatial east/west and temporal south/north label equalities. The
marker test at1005 has current Start selector x_0, temporal marker a,
and even E_1005. Its parity mask therefore gives

    a_(temporal predecessor of i)=x_(0,i).              (4)

This marker tracks the shifted Start indicator. It is not asserted to be
one in every occupied cell.

Put `Aadj=sum_(e,e+1 in Es)c_(e+1)*x_e`. Every x_e, including x_977,
is Boolean. The complete sole-clause predecessor is

    field1955: Aadj+x_950.

The extra unit is the bare1005 term applied to the south-bit8 label at950.
There is no foreign reflected band. Every other bare/spatial source and
aligned temporal source is absent, by section5 and max Es=1005.
At most one selected predecessor meets a selector coefficient, and every
label coefficient occurs at most once. The label sum is M-1024, including
adjacencies941 to942,968 to969 and977 to978. The Boolean dummy contributes
c_978 at most once and creates no additional term. Consequently

    Aadj<=2M-1024,
    Aadj+x_950+29<=2M-1024+30<rho.

The predecessor resets carry. With alignment established, the clause1956
has no temporal source because1956 is absent from Es. The sole clause
therefore has exact actual value0 or M+1 and zero outgoing carry,
independently of marker values.

Every padding field h in1..916 lies below the first reflected exponent
971 and the bare marker exponent1005. After alignment its complete raw
value is

    x_(current,h-18)+x_(spatial predecessor,h-9)
       +x_(temporal predecessor,h),

with any absent or negative-index source interpreted as zero. Each term
is Boolean, even before occupation is used. The incoming carry is zero
by section6, including h=1 because field0 resets. Its actual digit is
therefore in0..3 and avoids the bit2 mask4. This proves every one of the
916 low padding tests. Arbitrary simultaneous safe dummy choices retain
the same Boolean domains and bounds; more specifically, dummy977 has
no output in1..916 under any aligned kernel or temporal term.

Field2961 is the complete last product field, with raw value
`c_0*x_1005`. Since c_0<M and incoming is at most29, its digit is at
most M+29 and its outgoing carry zero. The only later field2962=L-1
is raw zero and therefore actual zero. This untested top zero field
resets every B-cell origin and will give the strict representative bound.
The new padding argument does not assume that the low fields themselves
are zero: their allowed values0..3 are essential.

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
map g from section1 recover the complete old admissible marked blank
computation and its syntactic refutation.

## 9. Fresh canonical words with a shifted marker

A refutation gives, by the retained whole signal/helical theorem, genuine
one-Start admissible rectangles with independently cofinal width and
height. Transfer their selectors through the inverse of g from section1,
complement their colors, and encode all labels and selectors afresh on Es.
Set the marker in cell j equal to the Start selector in its temporal
successor, so (4) holds exactly; set the sole dummy initially zero. With
transport B^width, this means `a_j=x_(0,j+width)` modulo N. This is a
freshly encoded marker pattern, not an all-one flag. Every simultaneous
Boolean subset of the safe low-977 bits leaves it and all tile data intact.

Construct the cyclic fixed point before imposing strict F. The words are
decoded by construction, and the same carry bound and aligned resets
apply. In particular every low padding digit lies in0..3 for every safe
dummy subset, and every occupied sole clause has actual value M+1,
proving positivity.
The top zero band and highest physical position give, for every subset,

    0<F<q/rho<q/7,
    0<C<q/rho^(L-1006),
    2C+F<q*(1/7+2/rho^(L-1006))<q/3,
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
10 to 11 and 100 to 011. In the combined4*G_917 block, subtracting1
changes only the very first coefficient4 to3; it does not borrow through
any later field or alter the other916 bit2 tests. Thus `pc(Tmask)=t+2`.
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

Its DC exponents are at most2933, its spatial exponent is986, and
its temporal exponent is 977. Coefficients are below rho and DC residues
are distinct. The two later cells, if equal, have distinct exponents
986 and977. Thus there is no coefficient collision or physical wrap,
and `0<deltaRaw<q/rho^2<q/7`. At every intermediate subset, (5) implies
`F_old+deltaRaw<2q/7<q-1`. The canonical representative therefore changes
by the exact ordinary equality `F_new-F_old=deltaRaw`. Subtracting the
actual rank formula gives

    deltaR=-Gamma*B^j,
    Gamma=rho^977*(q^2-1)*[1+q*(K+B^width)].             (6)

## 11. All fixed prime factors and the complete controller construction

For this exact L and K, Pclp consists of precisely the finite requirements:

- L=2963 is prime and distinct from47, so
  `d=139261=47*2963` is odd and squarefree;
- `ord_47(2)=23`, `ord_2963(2)=2962`, and both orders are coprime to d;
- an odd prime `lambda>d` has `68126 | kappa=lambda-1`,
  `B^2!=1 modlambda`, and `v_lambda(B^kappa-1)=1`;
- `Hs=1+B*K+B^2` is nonzero modulo each of47,2963 and lambda.

Here `2962=2*1481`, with1481 prime, and `68126=lcm(23,2962)`.
Exact-order evidence includes the full powers and all proper-order tests:
prime23 for order23 and primes2,1481 for order2962. Every primality and
factorization requirement is an elementary finite statement. The complete
new K and B are required in Hs; auxiliary orders and lambda are proof
data, not equation coefficients.

Because B=2^d and d is coprime to both orders, B has exact orders23 and
2962 modulo47 and2963 respectively. Both exceed2, so B²-1 is a unit
modulo the whole squarefree d. These explicit finite conditions use the
new tuple, including its shorter cell length.

Choose fresh independently large positive r_w,r_h and set

    width=lambda^r_w, height=lambda^r_h,
    N=width*height=lambda^n,
    height>lambda, N>d*lambda^2,
    T_orbit=N/lambda, C0=d*lambda.

Then `T_orbit>C0` and `width<T_orbit`. The whole helical-padding contract
allows these independently cofinal dimensions. Powers of lambda are1
modulo kappa. Each of the two fixed orders divides kappa, and Fermat's
theorem supplies B^kappa=1 modulo lambda. Consequently

    q=B^N=B^width=B mod p, for p=47,2963,lambda.

The non-power-of-two factors of Gamma reduce to B²-1 and Hs at every
one of these primes. Their explicit nonvanishing makes Gamma a unit
modulo the whole dN, including all powers of lambda.

LTE gives exact order T_orbit for `B^kappa` modulo lambda^n. The same
power is1 modulo47 and2963, hence modulo their squarefree product d.
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
No Pclp premise enters this direction.

For completeness under Pclp, sections 9..11 supply fresh actual native
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

## 13. Consequence and review boundary

Under Pclp and the retained explicit ordinary syntactic-refutation and
foundational calibration, ZFC proves that this equation has no positive
integer zero exactly when Con(ZFC). A separately checked finite Pclp
certificate removes that finite premise for the exact fixed tuple.
No consistency decision, actual unsolvability, global minimum or new
end-to-end proof-assistant/internal-ZFC replay is claimed.

All916 padding tests now use bit2 of fields1..916, whose complete aligned
raw values are0..3 with zero incoming carry. Combining them with the
origin gives the exact closed mask4*G_917(rho). The shorter length2963
retains one untested top zero field, strict representatives and every
safe-subset bound. Every whole integer, native mask, actual rank and
controller is proved for this tuple, with both positive P66 maps included.
The author is `/root/complemented47_review`; ROOT coordinates independent
finite and mathematical review. Every accepted predecessor is unchanged.
