# Two neighboring gate shears after the balanced CRT shear

This is an ordinary, code-free proposal for the two complete accepted
balanced quartics of height98336. It applies the fixed simultaneous map

    x_23 = z_23 - 8z_22,
    x_38 = z_38 - 8z_37,
    x_i = z_i for every other i.

The entire affected part can be checked by hand: each of two disjoint
blocks has31 monomials involving its fixed gate before the substitution
and20 afterwards. No new monomial appears, and every coefficient's
absolute value weakly decreases. Thus22 expanded monomials disappear.
The two coefficients98336 become32. Inspection of the existing whole
parent data, together with the local proof, gives prospective height93109
and row height160. These are theorem deductions about a specified
polynomial, **not generated data, a verified finite endpoint, or a new
printed equation**. No transformed equation or expanded polynomial has
been materialized. Independent ordinary review and a separately reviewed
finite implementation must precede acceptance of an endpoint.

The separate optional observation in section9 concerns the member(3,2)
of the older CRT-gate family. It is not combined with this proposal.

## 1. Exact accepted parents and notation

The parents are the two complete `data/{plain,weighted}` quartics in
`research/balanced-crt-gate-shear-verification`. Their exact whole
48-payload MANIFEST is

    ab5d758f4fea562f883fbed9ba5beaf46d030979350520ce21b6280458e72eed.

ROOT accepted them in09c7afc773 after full source reviews, nine observed
successful first/fresh processes, complete forward/inverse identities,
and ordinary evidence reviews. Their current dimensions and census are:

| Profile | Integer coordinates | Quadratic rows | Expanded terms | Degree | Height | Row height |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Plain balanced parent | 316 | 218 | 5803 | 4 | 98336 | 256 |
| Weighted balanced parent | 315 | 217 | 5809 | 4 | 98336 | 256 |

All coordinates are live. Indices and rows in this note are zero based.
Write the corresponding complete parent as

    Q(x) = sum_j r_j(x)^2.

For either profile put `a=z_10`, `b=z_11`, `c=z_12`, `u=z_21` and

    M = 2a+4b+2u.

These are unrestricted integer coordinates, not constants. The names
at indices10,11,12,21 are `crt.encoded.a`, `crt.encoded.b`,
`crt.encoded.c`, `mul.40`. The two blocks use the following literal
indices and names, identically in both profiles:

| Block | t | v | k | Preceding/output rows | kappa | nu |
| --- | --- | --- | --- | --- | ---: | ---: |
| First | z_22 = add.50 | z_23 = mul.53 | z_24 = add.61 | 6,7,8 | 5 | 5 |
| Second | z_37 = add.145 | z_38 = mul.148 | z_39 = add.156 | 21,22,23 | 3 | 1 |

`t,v,k` are local aliases for the coordinates in one indicated block.
They do not identify the two blocks with one another. The coefficient
tables below apply separately with the corresponding kappa,nu.

SOURCE_PINS binds every file of the complete accepted verification
packet, its outside ROOT acceptance, and the whole earlier ordinary
balanced-shear note. Authentication of these exact parents is not a
fresh execution or a fresh transitive native/calibration replay.

## 2. Complete occurrence guard and complete old residuals

Reading every monomial in every literal parent residual gives precisely
the following occurrence lists, in both profiles:

| Coordinate | ALL row indices in which it occurs |
| --- | --- |
| 22 | 6,7,8 |
| 23 | 7,8 |
| 37 | 21,22,23 |
| 38 | 22,23 |

In particular, neither changed coordinate23/38 occurs in a later
bilinear, label-sum, guard or restoration row. No residual contains both
22 and37, and no residual contains either block's t together with the
other block's changed coordinate. These are whole-list assertions about
the pinned parents; they are necessary for the global conclusions below.
Checking only the four visibly changed rows would not suffice.

For each block the COMPLETE three old rows, including all constants
and linear parts, are

    r0 = t-M^2-kappa*M-nu,
    r1 = v-(a+2t)^2+2a+4t-2,
    r2 = k-(6a+16t+2v)^2+(6a+16t+2v)+1.

Expanding these expressions gives every literal term of rows6/7/8,
or respectively21/22/23; there are no omitted summands. The first row
has11 literal terms, the second7, and the third11. Their factorizations
do not introduce a coordinate or an existential restriction.

## 3. Universal inverse and the entire proposed polynomial

Let N denote the displayed simultaneous map from z to x. Its two
elementary shears commute, since each fixes both other block coordinates.
It has determinant1 and the complete integer inverse

    z_23 = x_23+8x_22,
    z_38 = x_38+8x_37,
    z_i = x_i for every other i.

The two compositions are the identity on all of Z^n. Define EVERY new
row by `r'_j(z)=r_j(Nz)` and define

    R(z) = sum_j r'_j(z)^2 = Q(Nz).

Only rows7,8,22,23 change. In each block their complete replacements are

    r1' = v-(a+2t)^2+2a-4t-2 = r1-8t,
    r2' = k-(6a+2v)^2+(6a+2v)+1.

The preceding r0 and EVERY other original row are retained exactly.
In particular this is a complete specification by pinned residual list,
not a projection that discards any source constraint. Equivalently,

    R = Q-r_7^2-r_8^2-r_22^2-r_23^2
          +(r'_7)^2+(r'_8)^2+(r'_22)^2+(r'_23)^2.

All these identities hold as polynomials over Z. For the second row,
substitution changes its entire square argument
`6a+16t+2(v-8t)` to `6a+2v`; hence it removes t from the WHOLE row,
including its linear argument. This cancellation is not limited to
the leading homogeneous part.

Thus N and its inverse give both directions of the integer zero-set
correspondence. All rows remain at most quadratic, and the exact degree
is4: an invertible linear change cannot annihilate the nonzero quartic
homogeneous component of Q.

## 4. Exhaustive one-block expansion without a coefficient collector

Let `B0=v-a^2+2a-2` and `L=6a+2v`. The two old and new rows admit the
following whole identities:

    r1  = B0-4t(a+t-1),
    r1' = B0-4t(a+t+1),
    r2  = k-(L+16t)^2+(L+16t)+1,
    r2' = k-L^2+L+1.

The t-containing part of r0^2 is

    t^2-2t(M^2+kappa*M+nu).

The t-containing part of r1^2 is

    -8(a-1)*B0*t + (16(a-1)^2-8B0)*t^2
      +32(a-1)*t^3+16t^4;

the part of (r1')^2 is the same expression with every `a-1` replaced
by `a+1`. The t-containing part of r2^2 is precisely

    t*(32k-64Lk+64L^3-96L^2-32L+32)
      +t^2*(1536L^2-1536L-512k-256)
      +t^3*(16384L-8192)+65536t^4.

There is no t-containing part of (r2')^2. These formulas follow by
squaring a quadratic in t and are exhaustive. In particular the whole
new block's t-containing part is the short expression

    16t^4 + (32a+32)t^3
      +(24a^2+16a-8v+33)t^2
      +(8a^3-16a^2-32ab-16au-32b^2-32bu-8u^2
         -8av-8v-4kappa*a-8kappa*b-4kappa*u+16-2nu)*t.

All terms not containing t agree before and after: both r1 and r2
differences are multiples of t, so their squared differences are also
multiples of t. There is no assertion that t-free terms of an
individual row can be ignored; rather their equality is proved.

## 5. Every old and new t-containing coefficient

These tables expand section4, sorted by total degree rather than the
parent JSON ordering. The old column also matches the ENTIRE31-record
subset of each pinned expanded polynomial that contains22 or37,
respectively. The occurrence guard in section2 proves that no other row
can add to any entry. No other t-containing monomial exists.

| Degree4 monomial | Old | New |
| --- | ---: | ---: |
| a^3*t | 13832 | 8 |
| a^2*t^2 | 55320 | 24 |
| a*t^3 | 98336 | 32 |
| t^4 | 65552 | 16 |
| a^2*t*v | 13824 | 0 |
| a*t^2*v | 36864 | 0 |
| a*t*v^2 | 4608 | 0 |
| t^3*v | 32768 | 0 |
| t^2*v^2 | 6144 | 0 |
| t*v^3 | 512 | 0 |

| Degree3 monomial | Old | New |
| --- | ---: | ---: |
| a^2*t | -3488 | -16 |
| a*t^2 | -9264 | 16 |
| t^3 | -8224 | 32 |
| a*t*v | -2312 | -8 |
| t^2*v | -3080 | -8 |
| t*v^2 | -384 | 0 |
| a*k*t | -384 | 0 |
| v*k*t | -128 | 0 |
| k*t^2 | -512 | 0 |
| b^2*t | -32 | -32 |
| u^2*t | -8 | -8 |
| a*b*t | -32 | -32 |
| a*u*t | -16 | -16 |
| b*u*t | -32 | -32 |

| Degree2 monomial | Old | New |
| --- | ---: | ---: |
| a*t | -160-4kappa | -4kappa |
| b*t | -8kappa | -8kappa |
| u*t | -4kappa | -4kappa |
| t*v | -56 | -8 |
| t^2 | -223 | 33 |
| k*t | 32 | 0 |

| Degree1 monomial | Old | New |
| --- | ---: | ---: |
| t | 16-2nu | 16-2nu |

For the first block substitute kappa=5,nu=5; for the second use3,1.
Thus the a*t entries are respectively-180 to-20 and-172 to-12;
the b*t entries are-40 and-24, the u*t entries-20 and-12, and the
linear t entries6 and14. They are all nonzero. This checks that none
of the numerical specializations silently deletes another entry.

There are10+14+6+1=31 old monomials and4+10+5+1=20 new monomials
per block. Exactly six quartic, four cubic and one quadratic monomial
disappear. Every nonzero new coefficient already had a nonzero old
coefficient, and its absolute value is weakly smaller. Every new
t-containing coefficient has magnitude at most40.

## 6. Global support, height, row size and liveness

The following conclusions depend on the COMPLETE occurrence guard,
not merely a calculation within four selected rows.

First, no block contains the other t, so its two t-supported sets are
disjoint. Every coefficient whose monomial contains neither22 nor37
is unchanged, since the entire polynomial difference belongs to the
sum of the two separate t-supported parts in section4. Hence the local
tables prove globally:

* Exactly22 expanded monomials disappear, and no monomial is introduced.
* Every coefficient's absolute value weakly decreases.
* Both former98336 coefficients `[a*z_22^3]Q` and `[a*z_37^3]Q`
  become32; no larger downstream leading coefficient is created.

The accepted complete old polynomials have5803/5809 terms. Therefore
the specified new polynomials mathematically have5781 plain/5787
weighted terms. This is a consequence of the local support theorem
and the OLD full census, not an observed census of a saved new object.

Inspection of every existing parent coefficient with magnitude above
93109 gives ONLY the two records

    [98336,[10,22,22,22]], [98336,[10,37,37,37]].

Both profiles have `[93109,[10,10,12,12]]`. This a^2*c^2 coefficient
contains neither t and is retained. Combining those whole OLD-data
facts with the complete new tables proves that the specified new
polynomial's height is exactly93109, as an ordinary theorem deduction.
No finite implementation, fresh SOS recollection, reverse whole
substitution or canonical new data has yet verified that deduction.

The two r1 rows retain seven terms each; the coefficient of t changes
from4 to-4. Each r2 row loses exactly the four terms

    -192a*t, -256t^2, -64t*v, +16t,

and retains its other seven terms. Thus residual monomial occurrences
drop by eight and no row coefficient's absolute value grows. Existing
row coefficients of absolute value256 occur ONLY in rows8 and23.
Inspection of all other old rows shows absolute values at most160,
with the retained row20 term `-160a*c` witnessing160. The new four
rows have absolute coefficients at most36, so the specified new row
height is160. This too is a deduction from old literal rows and the
four complete replacement formulas, not a new generated measurement.

All coordinates remain live. For each index j outside{22,37}, N's
only nonidentity images depend on the fixed coordinates22/37, so

    partial_j R = (partial_j Q) o N

is nonzero by the parent liveness and the polynomial automorphism.
For each exceptional t, the coefficient of t^4 in R is16 by the full
table, and so that coordinate is live as well. In particular no
coordinate has been eliminated. The number of rows remains218/217
and their degree bound remains two.

These prospective deductions jointly improve the balanced parents'
support and height at unchanged dimension and row count. They do not
assert a minimum over any larger family, and they do not make this
quartic a shorter complete printed equation than the maintained
fifteen-positive-variable compact66 page.

## 7. Whole witness-map order and retained consistency contract

Write S for the already accepted balanced CRT shear, whose only
nonidentity coordinate is `y_21=x_21-2x_10-2x_11` when mapping the
balanced chart x back to the centered chart y. The complete new
chart-to-centered map is S after N. These two shears commute, but
the following explicit order fixes all map conventions.

From an existing source witness, carry out its accepted mandatory
Horn/private construction and projection, subtract the58 fixed shifts,
apply S inverse to obtain the current balanced tuple, and finally
apply N inverse to obtain the proposed tuple. Conversely, from any
integer zero of R, first apply N, then S, then add all58 fixed shifts;
initialize all83 actual free factored coordinates; reverse all204
plain/203 weighted monic restorations; carry out the mandatory original
Horn private overwrites; and apply the accepted whole source ordinary
maps and calibration. This is exactly the parent's inverse order with
one new whole-space bijection prefixed.

Only N, S and the translation are claimed to be whole-space integer
bijections. Older private-witness constructions remain existential,
with their original overwrites and restrictions. All sign arguments
are applied to the recovered old tuple. The exact source131/Round15/
C222/ZF-to-ZFC/native ordinary contract, interval-witness freshness,
and Hstar/H0 distinctions are inherited from the accepted parent
endpoint. In particular this ordinary chart change preserves the
parent unsolvability/Con(ZFC) equivalence, without strengthening its
transitive calibration assumptions or rerunning any native/compiler
or Lean verification.

## 8. The earlier height obstruction and the bounded next experiment

The accepted restricted lower bound98336 applies to changes of
coordinate21 alone, `x_21=u-ma-nb`, followed by constant translations.
Both terms a*z_22^3 and a*z_37^3 are invariant in that family. N is
outside that family. It fixes22 and37 themselves while changing their
neighboring output coordinates23 and38, thereby changing the complete
downstream square arguments that caused the large terms. Thus reducing
the98336 barrier does not logically require changing coordinate22 or37;
changing the corresponding neighbor can suffice.

A bounded future implementation would materialize exactly this one N,
in both profiles, preserving every row and the complete maps. It must
independently check every full forward and inverse polynomial identity,
all four changed rows and every unchanged row, the exact occurrence
lists, both full coefficient censuses, degree and liveness, and source
binding. In particular it must verify the old-coefficient inspections
used in section6, not infer a complete artifact from selected tables.
Neither a search over shears nor any new native/calibration computation
is part of the proposal. No application code or execution is supplied.

## 9. Separate optional observation about the member(3,2)

This section does NOT change the fixed N above and does not combine
two experiments. In the original ordinary family S_(m,n), moving from
the balanced(2,2) member to(3,2) substitutes `u -> u-a` in the current
balanced parent. It has the same trivial integer inverse, but retains
the98336 barrier because rows7/8 and22/23 remain fixed.

The eight forms from the whole accepted family proof become

    M = 4b+2u,
    L_12 = 6a+4b+8c+2u+2z_27,
    L_15 = 4b+4c+2u+4z_27+2z_30,
    L_19 = -4a-4b+2c+2u+2z_25,
    L_25 = -4a+4u,
    L_50 = -4a-4b+c+2u,
    L_51 = -4a-4b+2u+2z_66,
    L_52 = -8a-8b+4u+2z_65+2z_67.

For example row5 gains `-a`, row25 becomes

    z_41-16u^2+32a*u-16a^2-14u+12a-4b-6,

and row15 loses all occurrences of a because both its L_15 and M
lose a. Direct counting in the COMPLETE thirteen row formulas of
the accepted ordinary note gives these changes of residual support:

| Affected row or role | Change of number of literal monomials |
| --- | ---: |
| 5 | +1 |
| 6 | -4 |
| 12 | -1 |
| 15 | -7 |
| 21 | -4 |
| 25 | +2 |
| second bilinear row:73 plain/74 weighted | -1 |
| each of the other six affected rows | 0 |
| Total residual monomial occurrences | -14 |

This row sparsity does not prove a decrease of expanded quartic
support. For a concrete obstruction to that inference, the coefficient
of a^2*b*u, zero in the current balanced quartics, becomes-25728.
In the accepted leading-form identity its contributions from
L_12,L_19,L_50,L_51,L_52 are respectively

    3456, -1536, -1536, -1536, -24576,

whose sum is-25728; all other affected fourth powers contribute0.
The old family analysis also shows that no unaffected row contributes
to that coefficient. Thus at least one quartic monomial reappears.
The whole expanded support of(3,2) remains unresolved here. No data,
whole height claim or census for that member is produced, and it is
not the bounded candidate proposed for implementation in section8.
