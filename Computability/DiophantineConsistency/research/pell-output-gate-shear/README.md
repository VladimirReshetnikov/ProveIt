# A fixed output-gate shear after the neighbor shears

This is an ordinary, code-free proposal for the complete neighbor-sheared
quartics. It makes one reversible integer coordinate change:

    x_35 = z_35 - 4z_10 - 5z_12 - 2z_25 - z_27,
    x_i = z_i for every i other than35.

The two complete affected residuals simplify by hand. The proof below,
together with the existing complete parent coefficient lists, gives
prospective exact height54709, exact row height128 and exact support5728
plain/5734 weighted. This removes53 expanded monomials in each profile.
It introduces two monomials and increases some retained coefficient
magnitudes; there is no coefficientwise nonincrease assertion.

These are theorem deductions about the specified substituted polynomials,
not generated polynomial data or an accepted finite endpoint. No proposed
equation JSON, expanded-polynomial artifact, coefficient collector, helper,
application, import, AST, search, Lean, TeX or PDF has been run or produced.
The only machine inspections used existing saved parent data as inert JSON:
row occurrences, existing coefficients and existing degree censuses. All
new coefficient arithmetic in the tables is ordinary hand algebra.
Independent ordinary review and a separately reviewed finite implementation
would precede any new endpoint. The maintained compact66 page is unchanged.

## 1. Exact parents, notation and retained scope

The parents are BOTH complete `data/{plain,weighted}` profiles in
`research/neighbor-gate-shear-verification`. Its whole48-payload MANIFEST is

    1f22236100cfc3d60322996f9732afe192ea145e51ca20b8072cf2ca17bd3d68.

ROOT accepted this exact endpoint in b035f6cc10, following the separate
full ordinary evidence PASS. The existing packet retains all nine
observed first/fresh successful processes, independent full code reviews,
whole SOS forward/inverse
identities and the exact inherited source/calibration boundaries. The
proposal author also authored the prior neighbor finite implementation;
the separate ROOT and peer reviews, process observations and endpoint
acceptance supply the independent basis for those parents.

The complete existing parent data have the following measured census:

| Profile | Integer coordinates | Rows | Terms | Degree | Height | Row height |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Plain | 316 | 218 | 5781 | 4 | 93109 | 160 |
| Weighted | 315 | 217 | 5787 | 4 | 93109 | 160 |

All coordinates are live. All indices in this note are zero based. For
each profile write the entire pinned parent as

    Q(x) = sum_j r_j(x)^2.

Bind the following distinct unrestricted integer coordinates in the new
chart, identically in both profiles:

    a=z_10, b=z_11, c=z_12, u=z_21,
    p=z_25, r=z_27, v=z_35, k=z_36.

Their literal names are respectively crt.encoded.a, crt.encoded.b,
crt.encoded.c, mul.40, mul.64, mul.75, mul.137 and add.142.

The lower-case `r` is the coordinate at index27; an indexed `r_j` is an
entire residual row. Set

    L = -2a-4b+2c+2u+2p,
    H = 4a+5c+2p+r,
    W = 8a+6c+2r,
    J = 4H+W = 24a+26c+8p+6r,
    K = k-W-3.

These are linear forms or, for K, an affine form; they are not new
unknowns. In expressions for the old rows, the same symbols denote the
corresponding old coordinates before the substitution. Every occurrence
of H uses only coordinates fixed by the new shear.

SOURCE_PINS binds the whole existing verification packet, the whole
accepted neighbor ordinary proposal and its two complete ordinary review
pairs, both complete finite static review pairs, and the outside neighbor
evidence review and ROOT acceptance. This is source authentication,
not a new transitive native, compiler, calibration or Lean replay.

## 2. Complete occurrence guard and the two complete rows

Reading EVERY literal row of BOTH pinned profiles gives exactly

| Coordinate | ALL rows containing it, plain | ALL rows containing it, weighted |
| --- | --- | --- |
| 35 (the changed coordinate v) | 19,20 | 19,20 |
| 36 (the output coordinate k) | 20,59,90 | 20,59,91 |

The second line is needed for the complete cubic support argument. No
later row contains coordinate35. Thus exactly two rows can change; the
other216 plain/215 weighted rows remain literal, including every guard,
label sum, restoration constraint and private-witness boundary.

The COMPLETE old rows19 and20, including constants and every linear part,
are respectively

    A = v-L^2+8L-12,
    B = k-(8a+10c+4p+2r+2v)^2-24a-26c-8p-6r-4v-3
      = K-4(v+H)^2-4(v+H).

Each old row has22 literal monomials. Expanding the displayed expressions
gives every actual term in the pinned rows, not merely their leading
parts. The coordinate36 consumers outside row20 are, in both profiles,

    row59 = z_14-z_15-2k*z_70+6z_70-z_75,

and the label-sum row90 plain/91 weighted

    -a-b-4u-2z_24-4z_26-2z_29-2z_31-4z_32-2z_34
    -2k-4z_39-2z_40-2z_43-2z_47-4z_68-2z_69+q,

where q=z_105 plain and q=z_106 weighted. Consequently these rows supply
no cubic monomial k times two coordinates from {a,c,p,r,v}; they do
supply the retained additional4ak quadratic contribution used below.

## 3. Whole integer inverse, rows and SOS identity

Let T be the displayed map from z to x. Its inverse is

    z_35 = x_35+4x_10+5x_12+2x_25+x_27,
    z_i = x_i for every i other than35.

Both compositions are the identity on ALL of Z^n, since T fixes the four
coordinates used in H. This elementary shear has determinant1. Define
EVERY new row by r'_j(z)=r_j(Tz) and define the WHOLE polynomial

    R(z) = sum_j r'_j(z)^2 = Q(Tz).

The two complete replacements are

    A' = v-L^2+8L-12-H,
    B' = k-4v^2-4v-8a-6c-2r-3 = K-4v^2-4v.

Indeed, substituting v-H in the whole old square argument changes
8a+10c+4p+2r+2v to2v. Substituting it in the old linear part removes the
p term and gives exactly the displayed a,c,r,v terms. The first row
becomes A-H. Thus, as an identity in the whole integer polynomial ring,

    R = Q-A^2-B^2+(A')^2+(B')^2.

There are23 monomials in A' and7 in B'. This decreases the sum of residual
monomial occurrences by14 while retaining every row. No row equation is
discarded or weakened. T and its inverse give both directions of the
entire integer zero-set correspondence, independent of source witnesses.

## 4. Complete difference by homogeneous degree

Let Delta=R-Q and s=v+H. The elementary identity

    (K-4t^2-4t)^2 = 16t^4+32t^3+(16-8K)t^2-8Kt+K^2

together with (A-H)^2-A^2=-2HA+H^2 gives the following exhaustive
homogeneous decomposition. The subscript is total degree.

    Delta_4 = -16(s^4-v^4),
    Delta_3 = 2HL^2-32(s^3-v^3)+8(k-W)(s^2-v^2),
    Delta_2 = -82Hv-39H^2-8WH-16HL+8kH,
    Delta_1 = 0,
    Delta_0 = 0.

For the last cancellation, the constant-12 in A gives+24H, whereas the
constant-3 in K gives-24H. Keeping these constants is essential. The
difference contains no variables outside {a,b,c,u,p,r,v,k}. Therefore
every monomial outside the displayed degree supports is unchanged, even
if it receives contributions from other literal rows. The following
tables compare FULL parent coefficients, not isolated row contributions.
They are exhaustive within those supports and apply to BOTH profiles
except the explicitly stated weighted ab^2 offset.

## 5. All70 possibly changed quartic coefficients

The alphabet {a,c,p,r,v} has70 monomials of degree4. All70 are present with
positive coefficients in the existing whole polynomial, in both profiles.
Every other quartic coefficient is unchanged. On the35 monomials not
containing v, subtract16H^4. The complete table is:

| Monomial | Old | New |
| --- | ---: | ---: |
| a^4 | 16812 | 12716 |
| a^3c | 57172 | 36692 |
| a^3p | 8208 | 16 |
| a^3r | 15232 | 11136 |
| a^2c^2 | 93109 | 54709 |
| a^2cp | 31104 | 384 |
| a^2cr | 47616 | 32256 |
| a^2p^2 | 6384 | 240 |
| a^2pr | 6336 | 192 |
| a^2r^2 | 7488 | 5952 |
| ac^3 | 71162 | 39162 |
| ac^2p | 39744 | 1344 |
| ac^2r | 52224 | 33024 |
| acp^2 | 15552 | 192 |
| acpr | 15360 | 0 |
| acr^2 | 16128 | 12288 |
| ap^3 | 2112 | 64 |
| ap^2r | 3264 | 192 |
| apr^2 | 1728 | 192 |
| ar^3 | 2560 | 2304 |
| c^4 | 26365 | 16365 |
| c^3p | 22416 | 6416 |
| c^3r | 22480 | 14480 |
| c^2p^2 | 12576 | 2976 |
| c^2pr | 10368 | 768 |
| c^2r^2 | 12192 | 9792 |
| cp^3 | 3456 | 896 |
| cp^2r | 4224 | 384 |
| cpr^2 | 2304 | 384 |
| cr^3 | 4480 | 4160 |
| p^4 | 896 | 640 |
| p^3r | 640 | 128 |
| p^2r^2 | 576 | 192 |
| pr^3 | 256 | 128 |
| r^4 | 864 | 848 |

On the35 monomials containing v, the complete table is below. Since v
occurs only linearly in A, all its quartic terms come from the quadratic
part of B. That row's entire old quartic part is16(v+H)^4 and its new
quartic part is16v^4. This proves
all the zeros simultaneously and rules out hidden row contributions.

| Monomial | Old | New |
| --- | ---: | ---: |
| a^3v | 4096 | 0 |
| a^2cv | 15360 | 0 |
| a^2pv | 6144 | 0 |
| a^2rv | 3072 | 0 |
| a^2v^2 | 1536 | 0 |
| ac^2v | 19200 | 0 |
| acpv | 15360 | 0 |
| acrv | 7680 | 0 |
| acv^2 | 3840 | 0 |
| ap^2v | 3072 | 0 |
| aprv | 3072 | 0 |
| apv^2 | 1536 | 0 |
| ar^2v | 768 | 0 |
| arv^2 | 768 | 0 |
| av^3 | 256 | 0 |
| c^3v | 8000 | 0 |
| c^2pv | 9600 | 0 |
| c^2rv | 4800 | 0 |
| c^2v^2 | 2400 | 0 |
| cp^2v | 3840 | 0 |
| cprv | 3840 | 0 |
| cpv^2 | 1920 | 0 |
| cr^2v | 960 | 0 |
| crv^2 | 960 | 0 |
| cv^3 | 320 | 0 |
| p^3v | 512 | 0 |
| p^2rv | 768 | 0 |
| p^2v^2 | 384 | 0 |
| pr^2v | 384 | 0 |
| prv^2 | 384 | 0 |
| pv^3 | 128 | 0 |
| r^3v | 64 | 0 |
| r^2v^2 | 96 | 0 |
| rv^3 | 64 | 0 |
| v^4 | 16 | 16 |

Exactly35 quartic terms disappear:34 containing v and acpr. None is
introduced. The unchanged quartic coefficients whose absolute values
could challenge the new height are covered in section8.

## 6. Complete cubic support check

First restrict to the six-coordinate alphabet {a,b,c,u,p,r}. Its56 cubic
monomials split into20 using only {a,c,p,r},30 changed monomials involving
b or u, and six unchanged monomials. On the first20, the difference is

    2H(-2a+2c+2p)^2 - 8H^2J.

Their entire full-coefficient table is:

| Monomial | Old | New |
| --- | ---: | ---: |
| a^3 | 3044 | 4 |
| a^2c | 16016 | 4984 |
| a^2p | 3120 | -1024 |
| a^2r | 2686 | 390 |
| ac^2 | 23310 | 10142 |
| acp | 11584 | 1808 |
| acr | 8700 | 3180 |
| ap^2 | 1584 | -208 |
| apr | 896 | -1168 |
| ar^2 | 80 | -496 |
| c^3 | 13752 | 8592 |
| c^2p | 8782 | 3118 |
| c^2r | 4558 | 1286 |
| cp^2 | 2352 | 312 |
| cpr | 1664 | -752 |
| cr^2 | 256 | -432 |
| p^3 | -240 | -480 |
| p^2r | -320 | -760 |
| pr^2 | -512 | -768 |
| r^3 | -416 | -464 |

On monomials containing b or u the only difference is2HL^2. Since H has
neither b nor u, the quadratic factor2L^2, in order a,b,c,u,p, has
square coefficients8,32,8,8,8 and cross coefficients

    ab:32, ac:-16, au:-16, ap:-16, bc:-32,
    bu:-32, bp:-32, cu:16, cp:16, up:16.

This gives the following30 entries. The parent weighted ab^2 coefficient
is2522 rather than2520, so its new value is2650 rather than2648; this is
the only profile difference in all changed cubic entries.

| Monomial | Old plain | New plain |
| --- | ---: | ---: |
| a^2b | 1764 | 1892 |
| ab^2 | 2520 | 2648 |
| abc | 4772 | 4804 |
| abu | 1916 | 1788 |
| abp | -2176 | -2240 |
| abr | -816 | -784 |
| b^2c | 6830 | 6990 |
| b^2p | -946 | -882 |
| b^2r | -920 | -888 |
| bc^2 | 14088 | 13928 |
| bcu | 1376 | 1216 |
| bcp | 7292 | 7068 |
| bcr | -320 | -352 |
| bup | 1536 | 1472 |
| bur | -384 | -416 |
| bp^2 | 256 | 192 |
| bpr | -1152 | -1184 |
| a^2u | 718 | 654 |
| acu | 1072 | 1056 |
| au^2 | 544 | 576 |
| aup | 768 | 800 |
| aur | -96 | -112 |
| c^2u | -432 | -352 |
| cu^2 | -344 | -304 |
| cup | -768 | -656 |
| cur | -512 | -496 |
| u^2p | -384 | -368 |
| u^2r | -96 | -88 |
| up^2 | -384 | -352 |
| upr | 0 | 16 |

The remaining six of this56-entry alphabet are unchanged, with their
complete old/new values b^3:2156, b^2u:1534, bu^2:896, br^2:-1096,
u^3:576 and ur^2:-304. All55 previously present monomials remain; upr
is the sole new cubic monomial in this alphabet. In particular bpr was
already present, from other rows, and must not be counted as new.

The15 possibly changed cubic monomials containing v but not k and using
only {a,c,p,r,v} have the following complete table:

| Monomial | Old | New |
| --- | ---: | ---: |
| a^2v | 2040 | -8 |
| acv | 4880 | 16 |
| apv | 1808 | 16 |
| arv | 1024 | 0 |
| av^2 | 448 | 64 |
| c^2v | 2872 | -8 |
| cpv | 2096 | -16 |
| crv | 1216 | 0 |
| cv^2 | 528 | 48 |
| p^2v | 376 | -8 |
| prv | 448 | 0 |
| pv^2 | 192 | 0 |
| r^2v | 128 | 0 |
| rv^2 | 112 | 16 |
| v^3 | 32 | 32 |

This removes exactly five terms. The other nine existing cubic monomials
containing v and b or u are unchanged: abv:-32, auv:16, b^2v:-32,
bcv:32, buv:32, bpv:32, cuv:-16, u^2v:-8 and upv:-16. The homogeneous
difference introduces none of the absent b/u-v monomials.

Finally the15 cubic monomials k times a degree2 monomial on
{a,c,p,r,v} have the following complete table:

| Monomial | Old | New |
| --- | ---: | ---: |
| a^2k | -128 | 0 |
| ack | -320 | 0 |
| apk | -128 | 0 |
| ark | -64 | 0 |
| avk | -64 | 0 |
| c^2k | -200 | 0 |
| cpk | -160 | 0 |
| crk | -80 | 0 |
| cvk | -80 | 0 |
| p^2k | -32 | 0 |
| prk | -32 | 0 |
| pvk | -32 | 0 |
| r^2k | -8 | 0 |
| rvk | -16 | 0 |
| v^2k | -8 | -8 |

The complete occurrence guard in section2 shows why these entire old
coefficients are exactly those of-8k(v+H)^2: neither other k consumer
can contribute here. The new part is-8kv^2. Exactly14 terms disappear.
All other cubics, including every k cubic with variables outside this
alphabet, are unchanged by the complete Delta_3 identity. Total cubic
support change is therefore -5-14+1=-18.

## 7. Complete quadratic, linear and constant support check

The support of Delta_2 is contained in the26 entries below. These are
the ten monomials of H^2, eight products of b/u with a/c/p/r, four products
of v with a/c/p/r, and four products of k with a/c/p/r. The entries use
FULL parent coefficients, including the retained extra4ak from the
label-sum row. They agree in both profiles.

| Monomial | Old | New |
| --- | ---: | ---: |
| a^2 | 3445 | 2693 |
| ac | 4364 | 2324 |
| ap | 2216 | 1400 |
| ar | 2708 | 2300 |
| c^2 | 7422 | 6047 |
| cp | 4072 | 2972 |
| cr | 1732 | 1182 |
| p^2 | 2069 | 1849 |
| pr | 2128 | 1908 |
| r^2 | 1145 | 1090 |
| ab | 5342 | 5598 |
| bc | 5078 | 5398 |
| bp | 2592 | 2720 |
| br | 1776 | 1840 |
| au | -480 | -608 |
| cu | 712 | 552 |
| up | 704 | 640 |
| ur | 0 | -32 |
| av | 352 | 24 |
| cv | 480 | 70 |
| pv | 192 | 28 |
| rv | 96 | 14 |
| ak | -44 | -12 |
| ck | -52 | -12 |
| pk | -16 | 0 |
| rk | -12 | -4 |

Exactly pk disappears and exactly ur is introduced. Every other
quadratic coefficient is unchanged; in particular no omitted k or v
quadratic is introduced. The net quadratic support change is zero.

All linear and constant coefficients are exactly unchanged by Delta_1
and Delta_0. The existing full linear height is2116 and the constant is
2674. There is no new linear term in v: the old zero coefficient remains
zero, as the constant/linear cancellation in section4 proves.

## 8. Whole height, degree, liveness and exact census deductions

The existing whole quartic lists have exactly three coefficients with
absolute value greater than54709, identically in both profiles:

    a^3c:57172, a^2c^2:93109, ac^3:71162.

Their new values36692,54709,39162 are in the complete table above. Every
other quartic coefficient outside the70-entry alphabet is unchanged and
has absolute value at most54709. Inside that alphabet all old coefficients
are positive. Every coefficient of(8a+10c+4p+2r+2v)^4 is at most38400.
For completeness the maxima by exponent multiplicity4,3+1,2+2,2+1+1,
1+1+1+1 are10000,32000,38400,38400,15360. Subtracting such a nonnegative
coefficient from an old coefficient in[0,54709] stays in[-38400,54709].
The v^4 correction restores its unchanged value16. Thus all quartic
coefficients have absolute value at most54709, attained at a^2c^2.

The following independent loose bounds cover EVERY lower-degree
coefficient, without assuming that a leading-term improvement controls
the whole polynomial. The old degree3/2 heights are23310/7422. The
coefficient maxima in H, the quadratic part of A, the linear part of A,
the quadratic part of B and the linear part of B are5,16,32,160,26.
For B' the quadratic/linear maxima are4/8. Products of a quadratic and
a linear form have at most three relevant splits per cubic monomial;
products of two linear forms have at most two per quadratic monomial.

* The cubic change from(A-H)^2 is bounded by2*3*5*16=480. The entire old
  and new B-square cubic coefficients are bounded respectively by
  2*3*160*26=24960 and2*3*4*8=192. Hence the whole new cubic height is
  at most23310+480+24960+192=48942, below54709.
* The quadratic change from(A-H)^2 is bounded by
  2*2*5*32+2*5^2=690. Old B-square quadratic coefficients are bounded by
  2*26^2+2*3*160=2312; new ones by2*8^2+2*3*4=152. Hence the whole new
  quadratic height is at most7422+690+2312+152=10576, below54709.
* The entire linear part is unchanged, height2116. The constant remains
  2674. The output k has linear coefficient1 in B and B'; it is included
  in the respective maxima26 and8 and has not been omitted from these
  bounds.

Consequently54709 is the exact height of BOTH specified polynomials.
All residuals remain quadratic. The only parent row coefficient with
magnitude greater than128 is the-160ac in row20. In the new rows A' has
height32 and B' has height8. Every other row is literal; unchanged row12
contains-128ac. Therefore BOTH exact row heights are128.

The exact degree remains4, also witnessed by the coefficient54709. To
prove all coordinates remain live, first use the invertible map: for any
index outside {10,12,25,27}, the partial derivative of R at that index is
the corresponding partial derivative of Q composed with T. It is
nonzero, since Q was live and substitution by T is a ring automorphism.
This includes index35 itself. For the four exceptional source coordinates
a,c,p,r, the complete quartic table supplies respective nonzero pure
fourth coefficients12716,16365,640,848. Hence their derivatives are also
nonzero over Z. All316/315 coordinates remain live.

The tables and the whole difference support prove this exact prospective
census, with no transformed-data generation:

| Degree | Plain old | Plain new | Weighted old | Weighted new |
| --- | ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 1 | 1 |
| 1 | 112 | 112 | 112 | 112 |
| 2 | 809 | 809 | 808 | 808 |
| 3 | 1406 | 1388 | 1408 | 1390 |
| 4 | 3453 | 3418 | 3458 | 3423 |
| ALL | 5781 | 5728 | 5787 | 5734 |

In total55 old monomials disappear and two new ones appear, for a net53
removal. There is no claim that every magnitude decreases: for example
a^2b grows1764 to1892 and abp changes-2176 to-2240. There is no global
GL_n(Z), support, height or row-height optimality assertion.

## 9. Complete witness-map composition and retained calibration

The new T/T-inverse correspondence is universal over the entire integer
coordinate space. It composes with the whole accepted neighbor maps.
Starting with an integer zero of R, apply T to recover a zero of Q, then
in exactly the existing inverse order:

1. Apply the neighbor map N to recover the balanced tuple.
2. Apply the balanced CRT map S to recover the centered tuple.
3. Add all58 fixed centered-chart shifts to recover the raw projected
   tuple.
4. Initialize every one of the83 actual free factored coordinates.
5. Reverse all204 plain/203 weighted monic restoration steps.
6. Perform the mandatory original Horn private-witness overwrites.
7. Apply the whole accepted ordinary source maps and calibration.

For the other direction, construct the complete sealed source witness,
perform the prescribed Horn private overwrite and projection, subtract
the fixed shifts, apply S-inverse, then N-inverse, then T-inverse. Only
the three shear maps and translation are whole-space bijections. The
older private-witness restoration maps are existential and are not
asserted to be identities on arbitrary private tuples.

Thus solvability is preserved with exactly the existing source131,
Round15/C222, ZF-to-ZFC/native, interval and Hstar/H0 boundaries. No new
native or program nonhalting assertion, compiler correctness assertion,
calibrated numeric tuple, fixed-constant recipe, or Lean theorem is
introduced. The older optimized centering exit143 stays unresolved;
the complete historical records and old source remain unchanged. No
old-source MANIFEST is supplied or old outcome relabeled.

The separate main15-positive-variable66-operation degree157 equation
and its complete constants, equation.tex and equation.pdf are unchanged.
This ordinary quartic-coordinate improvement does not claim a shorter
printed specification or a new Lean formalization. It does not combine
the optional older(3,2) CRT shear or perform any parameter search.

## 10. Review and future implementation boundary

This folder contains one ordinary proof and its source pins only. Its
complete new coefficient tables are displayed hand proofs, not a
machine-readable proposed expanded-polynomial artifact. No generated
metrics file or executable source belongs to this proposal. The exact
ROOT acceptance of the pinned neighbor endpoint is committed in
b035f6cc10. This proof and its closure require independent full ordinary
review before acceptance of the proposed mathematical improvement.

A future finite implementation, if separately authorized, would have to
check both whole row lists, the complete occurrence guards, every
forward and inverse coefficient, every table and unchanged coefficient,
the complete support/degree/liveness census, all source maps and the
retained calibration scope. That future work would require separate
full static reviews and an explicit execution release. Nothing in this
ordinary note authorizes such application execution.
