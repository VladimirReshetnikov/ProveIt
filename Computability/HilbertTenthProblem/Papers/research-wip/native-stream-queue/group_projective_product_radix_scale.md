# A product native scale removes one group-compiler multiplication

The [literal source](group_projective_product_radix_scale.py) saves one
multiplication from the [label-aligned group compiler](group_projective_label_aligned_lanes.md).
For the usual illustrative ten-letter table it gives **227 certificate /
244=103M+141A polynomial operations**, six comparisons,36 positive witnesses
and degree **at most3396**. The corresponding parent has245 operations and
exact degree3504. The [receipt](group_projective_product_radix_scale.json)
stores the complete emitted default source and bounded exact checks.

The change uses the prescribed native AND scale to recover the history radix
as a power of two. Its top-block test can then use the constant2. All physical
macros, state flow, histories, ordinary input, fixed program numerals and outer
comparisons are retained. This is a complete fixed-table accepted-input
representation, with fresh positive native witnesses in the converse.
The numerical universal subgroup alphabet is **not instantiated**:244 is an
illustrative compiler ledger, not a new numerical universal bound. The
established75/87 frontier is unchanged.

Only the canonical nonempty `joint` unit-product family is supported. Both
supplied/computed P and both inherited range-mask recipes remain available.
No positive-tuple bijection with the parent's native coordinates is asserted,
and the full polynomials need not agree away from zero.

## 1. Literal scalar interface and the paid saving

Retain the parent's notation. There are n non-idle edges stored injectively
in m lanes. J is their selector sum. The eight physical packed words are
H_b,M_b,Z_b, and the controller words are H_c,M_c. Set

    T=P^(m+8),
    T2=P^a,   a=2m+8 for reused controller range masks,
                    or a=m+16 for the separate eight-lane range mask.

These powers are already emitted by the parent; no new exponentiation
primitive is introduced. Write R_M for the retained history range mask and

    H0=H_b+P^8 H_c+T H_b,
    M0=M_b+P^8 M_c+T R_M,
    Z =Z_b+P^8 H_c+T H_b.

The old complete scalar AND interface is

    H=H0+B*T2,        M_old=M0+(B−1)*T2,
    Q_old=T2*P^2,     q_old=16Q_old,
    B=16D,           D=u+height_slack,
    u=alpha*x+beta+1.                               (1)

The new interface keeps H,Z and every lower block, and uses

    M=M0+2*T2,        Q=2B*T2,       q=16Q=32B*T2.   (2)

In the literal source, retain the multiplication `range_Bshift=B*T2`.
Replace the other top multiplication `(B−1)*T2` by `2*T2`, replace the native
scale row by `q=32*range_Bshift`, and delete the private `T2*P^2` row. Thus
precisely one multiplication disappears. Multiplication by32, by2 and all
other fixed coefficients remains charged. In particular Q is a mathematical
name for q/16, not an uncharged additional source expression.

The guard reconstructs the complete canonical label-aligned joint parent
and checks the actual rows and private consumer of the deleted scale. The
retained B*T2 now has both its old H consumer and the new q consumer. The
source is topologically reordered, active scale metadata records its B
factor and exponent a, and every emitted gate must reach the complete
output. Historical parent records retain their original meanings.

## 2. Positive computed native fields before any radix typing

The joint scalar factor remains

    L=G−P,   G=sum_(i=0)^3 H_i+sum_(j=0)^7 Zhat_j+beta_global,

and the full finalizer is U*L times one plus the sum of the unchanged outer
residual squares, minus1. At a positive zero, L=epsilon in{−1,+1}; each other
individual factor is also a unit. Independently of either sign, positivity
gives P>=12, H_i<P and0<=Zhat_j−1<P. The retained repunit relation, supplied
or computed, is exactly

    P=(B−1)J+1.

It forces J>=1 and B<=P. The fixed-numeral margin, input and height definitions
are unchanged, so B>m and B=16D>=16. No endpoint or Boolean interpretation is
used at this stage.

The parent's scalar block bounds therefore still apply:

    H_b,M_b,Z_b<P^8,       0<=H_c<=M_c<P^m.

The range coefficients satisfy(2D−1)J<P. Thus R_M<P^m for the reused mask,
or R_M<P^8 otherwise. The reused case requires m>=8, exactly as in the
parent. Splitting the lower, controller and range regions gives

    0<=H0,M0,Z<T2.                                    (3)

These are inequalities in ordinary integer base P; P is not yet assumed
dyadic. In particular no AND or one-hot conclusion is used to prove them.

Equations(2)–(3) imply

    H−Z >= (B−1)T2+1 >0,
    M−Z >= T2+1 >0,
    Q−H−M+Z >= (B−4)T2+2 >0.                         (4)

They also imply0<=H,M,Z<Q. Reconstruct the same four native truth fields
mathematically from the factored index:

    F0=16(Q−H−M+Z)−15,
    F1=16(H−Z)+4,       F2=16(M−Z)+2,
    F3=16Z+8.                                        (5)

All are strictly positive before typing; their sum is q−1 and each is below q.
Their residues modulo16 remain1,4,2,8. The factored index is still exactly
r=F0+qF1+q^2F2+q^3F3. The source's folded A+1 port is merely the existing
polynomial factoring of this same identity.

## 3. Native signs, product-scale typing and separated lanes

Apply the local argument in
[the joint-bound unit proof, Sections3–4](group_projective_joint_bound_unit.md).
Its hypotheses before the complete AND theorem are precisely the positive
fields and checksum in(5), q>=16, the unchanged positive native coordinates,
X=q(w+S)>r with r=(q−1)S, the odd quotient Y/q and both paid ratio slacks.
None requires q to be a pure power of P. The individual norms and strong
condition restore first, followed by the rank and linear-sign argument.
The negative native index sign would give exact binary population at r−2;
the checksum and r congruent to1 modulo16 contradict that branch. The
native product is therefore+1, and its product with L forces L=+1.

The same raw-kernel exponent and valuation proof recovers q as a power of two;
the complete native theorem then gives H AND M=Z. Equivalently one may invoke
the complete theorem after the signs are restored, since its component contract
accepts any prescribed positive scale. From the new paid identity

    q=32B*P^a,       B,P positive integers,       a>0,

unique prime factorization now forces **both B and P to be powers of two**.
Since B=16D, D is dyadic too. This conclusion is obtained without first using
the top AND block. The repunit relation then gives P=B^t and J=1+B+...+B^(t−1)
for some positive integer t, by the usual Mersenne divisibility argument.

T2=P^a is consequently a power of two. Using(3), ordinary binary block
separation gives the exact identity

    (H0+B*T2) AND (M0+2*T2)
       = (H0 AND M0) + T2*(B AND2)
       = H0 AND M0,                                 (6)

because dyadic B>=16 has B AND2=0. This identity does not require B<P; it also
holds at B=P. There is no carry from either lower block into T2.

The lower controller, physical-selection and history-range blocks are
literally unchanged. Their separated AND relations therefore recover the
same Boolean edge fields, one-hot checksum, ordered macro path, selected
source coordinates and range digits. The original initial height bound and
all four signed transports are retained. The full parent's carry-free history
argument proves exactly the same paired-action predicate

    (1,u,1,u) -> (0,1,0,1)

for the fixed macro table and ordinary x>0. This proves direct soundness
without importing parent native coordinates at the new scale.

## 4. Positive converse and the universality boundary

Take any genuine accepted macro word for the fixed table. The parent's
construction chooses a sufficiently large dyadic D, supplies the same
positive histories, output hats, edge hats and joint slack, and sets
B=16D and P=B^t. Keep all of those outer coordinates. They satisfy every
unchanged outer comparison and every unchanged lower AND lane.

Use the new M and q from(2). The new Q=2B*T2 is dyadic and all words fit below
Q by(3)–(4). Equation(6) proves the complete new scalar AND. The prescribed-
scale native converse and the retained computed-field/unit coordinate maps
supply fresh strictly positive native auxiliaries for this actual new q and
index r. The joint scalar factor is already+1. Hence the emitted complete
polynomial has a positive zero. Conversely Section3 reconstructs a genuine
accepted word from any new positive zero, to which the original compiler's
completeness theorem applies.

Thus the existential ordinary-input projections coincide for every fixed
nonempty table accepted by the canonical parent and every permitted fixed
alpha,beta. Physical macros and program constants are never changed to
obtain the saving. The abstract
[universal subgroup construction](group_commutator_universal_substrate.md)
can still supply a compatible fixed alphabet, but this packet does not
instantiate its numerical generators. The sample ten-letter table is not
asserted universal, and244 is not compared as a universal bound against254
or the independent75/87 results.

## 5. Arbitrary-point comparison and literal degree bounds

Let W_old and W_new be the old and new native/joint unit products evaluated
on the same supplied integer coordinates, and let S be the sum of squares of
the other outer residuals. Those outer residuals are unchanged exactly.
Consequently the two complete outputs obey the all-integer identity

    F_new−F_old=(W_new−W_old)*(1+S).                  (7)

The checker also replays the entire old source after substituting exactly
`range_Bminus_shift=2*T2` and `selection__q=32B*T2`, recomputing every downstream
register. That changed-interface replay agrees with every retained new
register, every residual and the new output. Neither check asserts equality
of the original full polynomials, or a bijection between their positive
native tuples.

|Illustrative physical macros|Parent/new polynomial|New certificate|New M+A|Comparisons/witnesses|New degree bound|
|---|---:|---:|---:|---:|---:|
|`(1,2,3,4,5,6,7,8,1,2)`|245/244|227|103M+141A|6/36|3396|
|`(8,6,4,2,7,5,3,1)`|227/226|209|97M+129A|6/34|2132|

These rows use the joint family, reused controller mask and computed P.
The same one-multiplication saving applies to every supported recipe; the
number of comparisons, witnesses and finalizer gates does not change.

Degree bounds are propagated through the actual emitted DAG. At the guarded
main-norm subgraph the exact polynomial identity is

    (X+ac+gamma)^2−(a^2+4a+3)c^2
      =X^2+2Xac+2Xgamma+2acgamma+gamma^2−(4a+3)c^2.

The source checks every defining row before cancelling the a^2c^2 term for
this bound. No zero equation is used to lower degrees. All other rows use
the ordinary maximum/sum rules. For the default the individual factor bounds
are472,860,500,389,389,778,2, totaling3390; the largest outer residual degree
is3. Thus the complete bound is3396. The analogous supplied-P default has
247 operations,37 witnesses and degree at most1738. These are conservative
upper bounds; the inherited exact-degree routine is not reused at the changed
scale.

## 6. Reproduction and evidence

Run `python3 group_projective_product_radix_scale.py`; `--write` regenerates
the receipt. It covers five nonempty tables, both mask choices when permitted,
and supplied/computed P, checks complete literal ledgers and source closure,
and compares signed as well as positive arbitrary-point values using(7) and
the complete changed-interface replay. The caller guard deliberately rejects
empty tables instead of extending their special source and degree conventions.

The author writer and fresh replay passed16 literal ledgers and384 complete
changed-interface/register/residual/output identities,192 signed. Scalar checks
include1024 pretyping block contexts,1022 with a nondyadic B or P, and624 dyadic
block identities covering B=P. Twelve genuine signed-shear outer histories
with1752 chronological rows verify every outer comparison and the joined AND
at the new scale. Five malformed or unsupported callers are rejected.
These fixtures do not materialize full native Pell witnesses; their existence
is the complete positive-converse argument in Section4.


Two independent full proof/source/dependency reviews and separate fresh replays
pass with no findings. The first checked the pretyping lower-block margins,
local native sign proof at the product scale, subsequent dyadic B/P recovery,
fresh native extensions, literal one-multiplication saving and guarded degree
bound. The second used an independent executor to check448 complete
register/residual/factor/finalizer corrections(224 signed) across14 additional
table/mask/length contexts,14 degree/domain/opcode/liveness ledgers and288
pretyping corner boxes, including nondyadic fields and B=P. It independently
constructed12 reflected-shear outer paths with1464 rows and permuted physical
tables. All five local links resolve. These are finite algebra and outer-path
checks, not materialized complete Pell witnesses. Source and receipt are frozen
unchanged after review.
