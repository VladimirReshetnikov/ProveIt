# A second fixed shear: center the pair-sum gate

This code-free ordinary proposal starts with the two complete polynomials
specified by the accepted coord35 theorem in `research/pell-output-gate-shear`.
It makes the further whole-integer coordinate change

    old_coord35_chart_27 = z_27-z_10-z_12,
    old_coord35_chart_i = z_i for every other i.

For BOTH profiles the resulting specified polynomial has coefficient height
between32053 and41466 inclusive, exact residual height96 and exact degree4.
All316 plain/315 weighted coordinates remain live. The row counts stay
218/217, and the total number of residual monomial occurrences falls by9.
The exact expanded support and exact coefficient height are not determined
here. In particular no new5728/5734 successor-support claim is made.

The bounds prove a strict whole-height improvement over the preceding
ordinary54709 theorem. These are hand deductions about completely specified
polynomials, not generated artifacts or a new accepted endpoint. The actual
finite neighbor artifacts still have height93109. Coord35 has an accepted
ordinary theorem at commit a3dc95494b; its finite implementation and this
further proposal are separate workflows. No application, helper, import,
AST, substitution, coefficient collector, search, Lean, TeX or PDF ran in
this research. Only existing immutable JSON/text/hash/Git data were read.

## 1. Exact parents and coordinate names

Let Q be either whole accepted neighbor polynomial under manifest

    1f22236100cfc3d60322996f9732afe192ea145e51ca20b8072cf2ca17bd3d68.

It is the literal sum of every saved residual square. Its finite acceptance
is b035f6cc10. Let T be the accepted ordinary coord35 map

    x_35=w_35-4w_10-5w_12-2w_25-w_27,
    x_i=w_i for i!=35,

and write P(w)=Q(Tw). The entire proof defining P, its tables and maps is
the closed code-free parent at manifest

    916d271f8e0433ba02753ce8082aa8f606d1d24509a226bdd9b9a478d905cbab.

Both complete ordinary reviews and joint ordinary acceptance are retained.
Their exact conclusion is height54709, row height128, supports5728/5734;
generated transformed artifacts and a finite endpoint are not thereby
accepted. This proposal does not modify either parent or its evidence.

Use the following distinct unrestricted integer coordinates:

    a=z10, b=z11, c=z12, u=z21, p=z25, r=z27,
    v=z35, k=z36, t=z30, s=z42, l=z44, m=z45, n=z46.

The names of indices10,11,12 are crt.encoded.a/b/c. The remaining literal
names are mul.40, mul.64, mul.75, mul.137, add.142, mul.96, add.177,
mul.184, mul.188 and mul.194, in the same order. All indices are zero based.
Named output symbols below mean the coordinate at their numerical subscript,
not an additional unknown. Set

    D=a+c,
    L=-2a-4b+2c+2u+2p.

Every new constant and coordinate map is printed here. There is no hidden
parameter search, program index, coefficient table or consistency oracle.

## 2. Whole inverse, complete occurrences and composed map

Define U by w27=z27-a-c and all other wi=zi. Its inverse is
z27=w27+w10+w12, with every other coordinate fixed. Both compositions are
the identity on the whole integer space, and det(U)=1. Define EVERY row
of the new polynomial by composition with U, and put

    F(z)=P(Uz)=Q(TUz).

Thus its integer zero set corresponds in both directions to the entire
parent zero set. No source-witness hypothesis is used for these maps.

Reading every saved neighbor row gives all occurrences of coordinate27:

    11,12,14,15,17,20,27,30,31,32

in BOTH profiles. The coord35 theorem adds coordinate27 linearly to row19
and leaves it in row20. Therefore the complete changed-row set for U in
the P chart is exactly

    11,12,14,15,17,19,20,27,30,31,32.

All other207 plain/206 weighted rows remain whole literal rows. In
particular no late guard, label sum, private-witness condition or source
boundary changes. The target coordinate is mul.75 in both profiles.

The composition relative to the actual neighbor chart is particularly short:

    x27=z27-a-c,
    x35=z35-3a-4c-2p-r,
    xi=zi otherwise.

Its inverse is z27=x27+x10+x12 and
z35=x35+4x10+5x12+2x25+x27, all other coordinates fixed. The two
successive shears need not commute; these formulas fix their actual order.

## 3. Every complete affected row

The following table gives the ENTIRE rows before and after U, including
output, constant and all linear parts. Write y_j=z_j solely to shorten
output labels. The old column uses w variables with the same short names;
the new column uses z variables.

| Row | Complete old row in P | Complete new row in F |
| --- | --- | --- |
| 11 | r-D²+2D-1 | r-D²+D-1 |
| 12 | y28-(8a+4b+8c+2u+2r)²-2a-4b-2u | y28-(6a+4b+6c+2u+2r)²-2a-4b-2u |
| 14 | t-(4c+2p+2r)²+16c+8p+8r-6 | t-(-2a+2c+2p+2r)²-8a+8c+8p+8r-6 |
| 15 | y31-(2a+4b+4c+2u+4r+2t)²+2a+4b+8c+2u+8r+4t+1 | y31-(-2a+4b+2u+4r+2t)²-6a+4b+2u+8r+4t+1 |
| 17 | y33-(6a+b+8c+2r)²-24a-3b-32c-8r-2 | y33-(4a+b+6c+2r)²-16a-3b-24c-8r-2 |
| 19 | v-L²+8L-12-4a-5c-2p-r | v-L²+8L-12-3a-4c-2p-r |
| 20 | k-4v²-4v-8a-6c-2r-3 | k-4v²-4v-6a-4c-2r-3 |
| 27 | y43-(8a+6c+2r+2s)²+8a+6c+2r+4s | y43-(6a+4c+2r+2s)²+6a+4c+2r+4s |
| 30 | n-(2a+2b+2p+2r)²+24a+24b+24p+24r-35 | n-(2b-2c+2p+2r)²+24b-24c+24p+24r-35 |
| 31 | y47-(4a+4c+4r+4l+2m+2n)²-4c-4l-2m | y47-(4r+4l+2m+2n)²-4c-4l-2m |
| 32 | y48-(5c+4r+2t)²+c | y48-(-4a+c+4r+2t)²+c |

Each equality follows by substituting r-a-c in the complete old row. The
old rows other than19/20 are the existing saved neighbor rows themselves;
the two exceptions are the full accepted coord35 replacements. In
particular row30's output n is z46, distinct from its square argument.

Let E_j be the old row and E'_j its replacement. In the complete integer
polynomial ring,

    F=P+sum_(j in changed rows)((E'_j)²-E_j²).

No row is discarded. A finite sum over this explicitly printed fixed
eleven-element set is just ordinary polynomial notation.

The exact residual monomial-occurrence comparison is

| Row | Old monomials | New monomials |
| --- | ---: | ---: |
| 11 | 7 | 7 |
| 12 | 19 | 19 |
| 14 | 11 | 16 |
| 15 | 29 | 22 |
| 17 | 16 | 16 |
| 19 | 23 | 23 |
| 20 | 7 | 7 |
| 27 | 15 | 15 |
| 30 | 16 | 16 |
| 31 | 25 | 14 |
| 32 | 8 | 12 |

The total falls by9. All these counts include outputs, constants and
remaining linear terms; row31 still has a linear c term after its square
loses both a and c. This is not an expanded-quartic support count.

## 4. Exact residual height96 and degree/liveness witnesses

The saved neighbor rows have only three coefficients above magnitude96:
row12's -128ac, and row20's -160ac and -100c². The coord35 change already
removes the latter two. After U, the complete new row12 has maximum
magnitude72. The other ten new rows have maxima at most72: their square
arguments, outputs, constants and linear parts are all included in the
table above. Every unchanged row has height at most96. Unchanged rows16
and26 contain -96bc. Hence the exact whole residual height is96.

For transparent exact quartic witnesses, the next table gives the old/new
contributions from EVERY row whose quadratic part changes. Other affected
rows11,19,20 have unchanged quadratic parts. A pair x/y means old/new.

| Row | a⁴ | c⁴ | a²c² | b²c² | a³c | ac³ |
| --- | --- | --- | --- | --- | --- | --- |
| 12 | 4096/1296 | 4096/1296 | 24576/7776 | 6144/3456 | 16384/5184 | 16384/5184 |
| 14 | 0/16 | 256/16 | 0/96 | 0/0 | 0/-64 | 0/-64 |
| 15 | 16/16 | 256/0 | 384/0 | 1536/0 | 128/0 | 512/0 |
| 17 | 1296/256 | 4096/1296 | 13824/3456 | 384/216 | 6912/1536 | 12288/3456 |
| 27 | 4096/1296 | 1296/256 | 13824/3456 | 0/0 | 12288/3456 | 6912/1536 |
| 30 | 16/0 | 0/16 | 0/0 | 0/96 | 0/0 | 0/0 |
| 31 | 256/0 | 256/0 | 1536/0 | 0/0 | 1024/0 | 1024/0 |
| 32 | 0/256 | 625/1 | 0/96 | 0/0 | 0/-256 | 0/-16 |
| Whole old P | 12716 | 16365 | 54709 | 36349 | 36692 | 39162 |
| Whole new F | 6076 | 8365 | 15445 | 32053 | 9812 | 12138 |

Every entry is the appropriate ordinary multinomial coefficient in the
fourth power of its printed square argument. Whole old values are supplied
by the accepted coord35 tables or the unchanged saved neighbor coefficient.
Adding all eight contribution differences proves the six whole new values;
unaffected-row contributions are retained, not assumed zero. The values
are the same in both profiles.

All rows remain quadratic, and the coefficient32053 proves exact degree4.
For every variable except a,c, differentiating P composed with U gives
the corresponding nonzero parent derivative composed with U, since these
columns of U are identity. This includes r itself. U is a ring
automorphism, so those derivatives stay nonzero. The two exceptional
variables have pure fourth coefficients6076 and8365. All316/315
coordinates therefore remain live.

## 5. Whole quartic upper bound41466

The following elementary coefficient comparisons apply to ENTIRE quartic
parts of residual squares. If a row's quadratic part is -A² for a linear
form A, its quartic part is A⁴. Every old changed quadratic row has a
nonnegative square argument before U.

For rows12,17,27,31 the new square argument is obtained by reducing or
deleting nonnegative coefficients. Their fourth powers therefore decrease
coefficientwise. For row15, the a coefficient changes2 to-2 and the c
coefficient4 disappears; all other absolute coefficients stay fixed.
Every new coefficient of its fourth power has absolute value at most
its nonnegative old coefficient, so its signed value also cannot increase.
The other changed rows11,19,20 have the same quadratic parts as before.

Only rows14,30,32 can increase a quartic coefficient. The maximum absolute
coefficient of their NEW fourth powers is respectively384,384,1536.
For rows14/30 all four absolute coefficients are2, giving maximum
24*2⁴=384. For row32 the absolute coefficients are4,1,4,2; maximizing
the five exponent-multiplicity types gives at most256,1024,1536,1536,768,
hence1536. Since their OLD fourth-power coefficients are nonnegative,
the increase of any entire quartic coefficient is at most

    384+384+1536=2304.

The whole parent P has every quartic coefficient at most39162 except
a²c²=54709. To bind this assertion to the actual saved data: the neighbor
quartics have exactly six coefficients above39162 in absolute value:

    a³c57172, a²c²93109, a²cr47616,
    ac³71162, ac²p39744, ac²r52224.

The complete accepted coord35 table changes those to respectively
36692,54709,32256,39162,1344,33024. All other quartic coefficients are
unchanged or are among its fully checked70-entry table, whose remaining
new values are at most39162. Thus every nonexceptional new F quartic
coefficient is at most39162+2304=41466. The exceptional a²c² has the
new value15445 proved in section4, also below41466.

This is a one-sided coefficient bound. Negative coefficients are bounded
separately next, rather than silently assumed absent.

## 6. Whole quartic lower bound-35040

For a quadratic polynomial whose coefficients have absolute value at most C,
each coefficient of its square has absolute value at most6C². A degree-four
monomial has at most three unordered degree-two/degree-two partitions;
each off-diagonal product contributes at most2C². Repeated exponents only
reduce this bound. This is coefficient arithmetic, not a bound on values.

Rows54 onward remain unchanged by both relevant coordinate changes to
their quadratic parts. There are164 such rows plain and163 weighted.
Every quadratic coefficient has magnitude at most4 except three rows
with bound8: indices176,188,192 plain and177,189,193 weighted. These
are complete saved-row observations, not a selected sample. Therefore
all their total quartic coefficients are bounded below by

    -(161*6*4²+3*6*8²)=-16608

in both profiles; the weighted count is smaller, so this common bound
still holds. No tail quadratic coefficient, sign or row is omitted.

Among rows0 through53, rows0--4 have monomial quadratic parts and hence
nonnegative quartic coefficients. Every other row's quadratic part is
the negative square of an explicit linear form. All have same-sign
linear-form coefficients except exactly the following eight rows in F.
The table gives the complete mixed-sign form and a bound on every
negative coefficient magnitude of its fourth power.

| Row | Mixed-sign linear form | Bound |
| --- | --- | ---: |
| 14 | -2a+2c+2p+2r | 384 |
| 15 | -2a+4b+2u+4r+2t | 1536 |
| 19 | -2a-4b+2c+2u+2p | 768 |
| 30 | 2b-2c+2p+2r | 384 |
| 32 | -4a+c+4r+2t | 1536 |
| 50 | 2a+4b-c-2u | 768 |
| 51 | 2a+4b-2u-2y66 | 768 |
| 52 | 4a+8b-4u-2y65-2y67 | 12288 |

Each bound follows by the five fourth-power multiplicity types; it also
bounds every positive coefficient if needed. The sum is18432. Thus the
whole F quartic part has every coefficient at least

    -18432-16608=-35040.

Together with section5, every quartic coefficient has absolute value
at most41466. No claim that all new quartic coefficients are positive
or that every magnitude decreases is made.

## 7. Every cubic coefficient: a separate whole bound40094

The complete coord35 tables imply a global cubic bound23310 for P:
every changed new cubic magnitude in those tables is below23310, and
the unchanged saved neighbor cubic height is23310. Its looser printed
48942 bound need not be used here.

Write each row as a homogeneous quadratic part plus a linear part plus
its constant. Cubics arise only from twice quadratic times linear.
Output coordinates must be kept in those linear parts. The following
classification supplies a bound on EVERY change, without constructing
the new cubic expansion.

For rows12,17,31, separate their positive old cubic contribution from
the negative output-coordinate contribution. The positive parts are
respectively 2A²(2a+4b+2u), 2B²(4B-b), and 2C²(4c+4l+2m), with their
old nonnegative square arguments A,B,C from section3. Each positive
part decreases coefficientwise. Their old coefficient maxima are
bounded by3072,9216,768. The middle bound follows from
2B²(4B-b)<=8B³ coefficientwise and the maximum coefficient1152 of
(6a+b+8c+2r)³. Their total possible decrease is13056.

The corresponding negative output parts are -2y28 A², -2y33 B² and
-2y47 C². These become less negative coefficientwise, contributing
only a nonnegative increase, at most256+192+64=512. They have not
been omitted on the grounds that the output is a linear coordinate.

For row11, the cubic change is2D³, with coefficients at most12 (a
deliberately loose bound). For row27, both the square argument and
its positive linear part decrease coefficientwise, so the entire
negative cubic part becomes less negative; its old magnitude is at
most4608. These contributions only increase coefficients, by at most
4620 together.

Rows14,15,30,32 have nonpositive old cubic coefficients. Their old
coefficient magnitudes are at most768,1536,1152,80, summing3536.
Their NEW cubic magnitudes are at most384,1536,1152,64, summing3136:

* Row14 is -8A³-2tA², with A=-2a+2c+2p+2r. The output t is distinct
  from every variable of A, and384 bounds both disjoint supports.
* Row15 uses the complete linear part, including y31; its quadratic
  coefficient bound32 and linear coefficient bound8 give
  2*3*32*8=1536.
* Row30 is -24A³-2nA², with A=2b-2c+2p+2r. Distinct output n and
  the cubic multinomial bound give1152.
* Row32 is -2(c+y48)A², A=-4a+c+4r+2t. The output y48 is absent
  from A. Each support has magnitude at most2*32=64. The analogous
  old bound is2*40=80.

Thus these four rows decrease a coefficient by at most3136, or increase
it by at most3536+3136=6672. Finally, row19's cubic change is
-2L²(a+c), bounded by64, and row20's is -16v²(a+c), bounded by16.
Their combined absolute change is at most80.

Combining all signs gives an absolute bound no larger than

    23310+max(13056+3136+80+512, 4620+6672+80+512)
    =40094.

Charging the nonnegative output increase512 also on the negative side
is harmless slack. This proof includes all eleven affected rows and
every output-coordinate cubic. All other cubic contributions remain
literal. The bound is below41466.

## 8. Every quadratic, linear and constant coefficient

For a row q+l+d with quadratic coefficient bound C, linear coefficient
bound M and constant d, every quadratic coefficient of its square is
at most2M²+2|d|C in magnitude. This includes every output coefficient
in M. For each complete affected row, the old/new bounds are

| Row | Old square quadratic bound | New square quadratic bound |
| --- | ---: | ---: |
| 11 | 12 | 6 |
| 12 | 32 | 32 |
| 14 | 704 | 224 |
| 15 | 192 | 192 |
| 17 | 2432 | 1344 |
| 19 | 2432 | 2432 |
| 20 | 152 | 96 |
| 27 | 128 | 72 |
| 30 | 1712 | 1712 |
| 31 | 32 | 32 |
| 32 | 2 | 2 |

The sum of both columns is13974. The accepted coord35 tables imply
the whole old P quadratic bound7422, since all changed new quadratic
magnitudes there are below the unchanged saved bound7422. Therefore
every new F quadratic coefficient has magnitude at most

    7422+13974=21396.

For linear terms, composition by the homogeneous linear U can change
only the coefficients of a and c. Saved whole neighbor linear values,
which the coord35 theorem leaves unchanged, are a:-1232, c:576,
r:-1694. They become a:462, c:2270, r:-1694. Every other linear
coefficient is unchanged and has magnitude at most2116. Thus the
exact new whole linear height is2270. The constant is unchanged2674.

All degrees have now been bounded independently: quartic41466,
cubic40094, quadratic21396, linear2270, constant2674. Consequently

    32053 <= height(F) <= 41466 < 54709,

where the lower witness is the exact b²c² coefficient from section4.
This is a rigorous whole bound, not an asserted exact new height.

## 9. Full source-map composition and scope

For an integer zero of F, apply U to get a zero of P, then the accepted
coord35 T to get a zero of the actual neighbor Q. Continue in the exact
accepted inverse order: neighbor N, balanced S, all58 translations,
all83 free-coordinate initializations, all204 plain/203 weighted reverse
monic restorations, mandatory original Horn private-witness overwrites,
and the whole accepted ordinary source maps/calibration. The forward
existence map constructs the sealed source witness, performs its prescribed
private overwrite/projection, subtracts shifts, then applies S inverse,
N inverse, T inverse and U inverse. Only the shears and translation are
whole-space bijections; the older private restorations remain existential.

The exact source131/Round15/C222/ZF-to-ZFC/native, fresh-interval and
Hstar/H0 boundaries are unchanged. No new calibrated tuple, raw private
tuple identity, old324 polynomial/old327 body identity, native execution
or compiler correctness result is claimed. The preserved optimized
centering exit143 remains unresolved with unknown cause.

Composing the whole zero-set equivalences and negating gives the same
ordinary ZFC-provable equivalence between no integer solution of F and
syntactic Con(ZFC). The new argument is a finite integer polynomial
identity with an explicit inverse; it assumes no consistency or semantic
soundness of ZFC. The inherited calibration remains its stated dependency.

This note is a new ordinary proof requiring two full independent reviews.
Its author independently reviewed the preceding coord35 ordinary note;
that does not supply independent approval of this new note. No finite
implementation, output artifact, coefficient collector or execution is
authorized by it. A later implementation would need its own two complete
static approvals and separate ROOT release before its first import/run.
The exact expanded support, exact height and every future generated file
would then require whole forward/inverse/SOS/census/map verification.

The main one-page15-positive66-operation degree157 equation, all constants,
equation.tex/equation.pdf and paused Lean work are unchanged. This quartic
height improvement does not itself shorten their printed specification.
The old accepted alternatives are retained and no global optimum is asserted.
