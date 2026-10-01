# Selected products for slope classes, with one baseline omitted

This packet reduces the complete [affine-pair history](pcp_uniform_affine_pair_history.md)
by supplying selected-history products only for exceptional **slope
classes**. It preserves the original fixed tile table, its tile IDs, and
the chronological word. Every selection, range, radix, duration,
transport, and positive-domain condition remains paid.

Let a nonempty table of `s` tiles act by

    (U,V) -> (a_i U+c_i, b_i V+d_i),

where `a_i,b_i>=1` and `c_i,d_i>=0` are fixed integers. Choose one upper
slope `a0` and one lower slope `b0` appearing in the table. If there are
`du` distinct upper slopes and `dv` distinct lower slopes, put

    u=du-1, v=dv-1, g=u+v, N=s+g+4.                    (1)

The raw source has **19 comparisons** and **s+g+26 positive witnesses**.
Its optional [native-unit rewrite](pcp_uniform_affine_pair_units.md)
has **10 comparisons** and **s+g+20 witnesses**. Writing `C=M+A` for the
raw certificate, the raw SOS costs `C+56`, and the unit polynomial costs
**C+32=(M+13)M+(A+19)A**. Their exact degrees are respectively
**24N+16** and **58N+28**.

For the already instantiated 34-tile odd-integer example, `du=3,dv=4`
so only **five** products replace the former 68. The selected baselines
are `a0=b0=4096`. The raw certificate costs 415; the unit version costs
**418=181M+237A**, or **447=191M+256A** as one polynomial, with **59
witnesses** and degree **2522**. Its previous uniform-history unit
component cost 728, had 122 witnesses, and had degree 8148. This is a
concrete improvement for that example table, not a numerical universal
alphabet or a change to the separate 75/88 bounds.

## 1. Class products and exact transports

Keep one supplied positive `Shat_i` for every original tile, with proof
notation `S_i=Shat_i-1`. For every upper slope `a!=a0`, let

    I_a={i:a_i=a},       G_a=sum_{i in I_a} S_i.

Supply one positive `ZUhat_a`, representing `ZU_a=ZUhat_a-1`. It will
be the selection of the upper history by `G_a`. Do the analogous
construction for each lower slope `b!=b0`, using `J_b` as a class set,
`G'_b` as its selector, and `ZVhat_b`. Only these `g` product hats are
supplied. In particular there are none when both coordinates have a
single common slope.

Under one-hot tile selection the exact next-history expressions are

    NU=a0*H_U+sum_{a!=a0}(a-a0)*ZU_a+sum_i c_i*S_i;
    NV=b0*H_V+sum_{b!=b0}(b-b0)*ZV_b+sum_i d_i*S_i.     (2)

The baseline class uses `H_U-sum ZU_a` or `H_V-sum ZV_b` implicitly;
it needs no selected-product coordinate or packed lane. The source
evaluates (2) directly on the hats. For example its first linear form is

    a0*H_U + sum(a-a0)*ZUhat_a + sum c_i*Shat_i
       - sum(a-a0) - sum c_i.                          (3)

All coefficients, including negative slope differences, are fixed paid
numerals. Negative differences are allowed; the next-state expression
is not asserted nonnegative before typing. The carry argument below
first identifies it with the actual selected positive affine map.

`linear_forms` metadata gives both exact coefficient maps, constants,
and output registers for a later separately audited linear-form pass.
The default emitter here charges each nontrivial multiplication and
sum, sharing only identical literal instructions. The optional emitter
hook has the contract of computing exactly these two forms with its
emitted paid gates; the theorem does not authorize an arbitrary
replacement expression.

## 2. Positive wrapper and one joined AND

Use the same fixed numeral as the raw parent:

    K=least power of two >=max(8,s+4,1+max_i(a_i+c_i,b_i+d_i)).

Supply positive `height_slack=rho`, `H_U,H_V`, `global_bound=beta`, all
`s` selector hats, all `g` product hats, and 22 independent prescribed
AND64 auxiliaries. The three positive parameters remain
`Vinitial,Ufinal,Vfinal`. Compute

    D=Vinitial+Ufinal+Vfinal+rho;
    B=K*D;
    J=sum_i Shat_i-s;
    P=(B-1)*J+1.                                       (4)

The three outer comparisons are

    H_U+H_V+sum ZUhat_a+sum ZVhat_b+beta=P;
    B*NU+1=H_U+P*Ufinal;
    B*NV+Vinitial=H_V+P*Vfinal.                         (5)

To compute each class selector, its positive hat is the paid expression

    Ghat_a=sum_{i in I_a} Shat_i-(|I_a|-1),             (6)

and likewise below. This value is unconditionally at least one. It is
not an existential coordinate. Original tile selectors are used for
the controller and offsets; changing the class order does not change
tile order or the meaning of a selector.

Order upper classes by their first original tile index and put them
before the similarly ordered lower classes. Let `Gpack` be their
decoded base-`P` pack, and let `Zb` be the same pack of selected
products. With `R_l(P)=sum_{j<l} P^j`, compute

    S=sum_i S_i*P^i;          Mc=J*R_s(P);
    Hb=H_U*R_u(P)+P^u*H_V*R_v(P);
    Mb=(B-1)*Gpack;
    T=H_U+P*H_V;             RM=(D-1)*J*(1+P).         (7)

The zero-length repunit is zero. Thus `Hb=Mb=Zb=0` when `g=0`.
If `u=v>0`, the source factors `Hb=(H_U+P^u H_V)R_u(P)`. If the two
retained partitions coincide as ordered sets of original tile IDs,
their group-hat expressions and the decoded selector pack are shared:
`Gpack=(1+P^u)*Ghalf`. This is an exact polynomial identity on every
integer assignment. Different slope values attached to the same
partition do not prevent this sharing.

The joined words are

    C=P^g*S+P^(g+s)*T;
    H=Hb+C+P^(g+s+2)*B;
    M=Mb+P^g*Mc+P^(g+s)*RM+P^(g+s+2)*(B-1);
    Z=Zb+C;
    Scale=P^N.                                        (8)

Powers, repunits, and the shared `C` are actual source gates. Apply
the complete prescribed AND64 to `(Scale,H+1,M+1,Z+1)`, inlining the
three wrappers exactly as in the parent by using padded words
`16H+12,16M+10,16Z+8`. The 64 native gates and all their positive
auxiliaries and 16 comparisons are retained in the raw source.

## 3. Soundness without an unpaid group predicate

Before any equation, positivity gives `D>=4`, `B>=32`, decoded
selectors and products nonnegative, `J>=0`, and `P>=1`. The class
definitions give `0<=G_a,G'_b<=J` because they are sums over subsets
of the original nonnegative selectors. All words in (7)--(8) are
nonnegative, including the hatted packs minus their repunits.
Consequently the conceptual AND arguments and computed `F3=16Z+8`
are positive before any native theorem is used.

The global comparison in (5) implies `P>=g+3>1`; hence `J>0` and
`B<=P`. Each history and each decoded product is less than `P`.
Also each original and each class selector is at most `J`, so its
full-cell mask is at most `(B-1)J=P-1`. Thus the physical regions
`Hb,Mb,Zb` fit in exactly `g` lanes, including the empty region if
`g=0`. The controller regions fit in `s` lanes; `T,RM<P^2`; and
`B,B-1<P^2`. These are algebraic bounds before Boolean typing.
In particular the two top lanes allow `B=P` at duration one.

The native AND theorem yields `P^N` dyadic, hence `P` dyadic, and
splits across the disjoint regions. Its top region says
`B AND (B-1)=0`, making `B` dyadic; then `D=B/K` is dyadic. Together
with (4), this gives

    P=B^t, J=1+B+...+B^(t-1), t>=1.                    (9)

The controller region says `S_i AND J=S_i` for each original tile.
Its checksum `sum S_i=J` and `s<B` force exactly one selected tile
at every time. Therefore every derived class selector has Boolean
digits: its digit is one exactly when that selected tile is in the
class. No extra group-typing equation is needed.

The range region makes all history digits lie in `[0,D-1]`. The
physical AND regions then give precisely the selected histories for
the retained slope classes, since `(B-1)G_a` consists of full selected
cells. The strict scalar bounds on every decoded product prevent
output carries between these physical lanes.

At time `j`, let `i` be the selected original tile. Formula (2) now
has digit exactly `a_i U(j)+c_i` and `b_i V(j)+d_i`, respectively:
the exceptional term is present if and only if its slope differs
from the chosen baseline. These digits are nonnegative and less than
`B`, because for `0<=x<D`,

    a_i*x+c_i <= a_i*(D-1)+c_i < (a_i+c_i)D < KD=B.    (10)

This proves the carry bound even for a baseline with negative
exception coefficients. All four boundary digits are less than `D`.
Both transport equalities are therefore equalities of canonical
base-`B` expansions, recovering every initial, interior, and terminal
digit. Positive slopes and nonnegative offsets preserve positivity
of the true states. A nonempty common tile word is recovered.

## 4. Positive completeness and the unit option

Given any accepted nonempty tile word, choose dyadic
`D>Vinitial+Ufinal+Vfinal`. The state sequences are nondecreasing,
so all states are less than `D`. Set `rho` to the positive difference
and use (9). Supply the original Boolean tile selectors and only the
selected products for exceptional classes. Unused classes have hat
one. All original histories are positive and (2) is the true update.

For each coordinate the retained classes are disjoint, so

    sum ZU_a<=H_U,  sum ZV_b<=H_V.

Writing `Hsum=H_U+H_V`, the global slack is

    beta=P-Hsum-sum ZU_a-sum ZV_b-g
        >= ((K-4)D+3)J+1-g >0.                        (11)

Here `g<=2s-2`, `K>=s+4`, `D>=4`, and `J>=1` make the displayed
bound strictly positive, including `t=1` and `g=0`. All joined AND
regions are valid. The complete prescribed-scale theorem supplies
fresh positive native witnesses at the new scale `16P^N`.
Reusing old witnesses at the previous scale is not asserted.

The optional unit rewrite applies without modification: it combines
the first, main, auxiliary norm, and checksum units and projects six
unconditionally positive computed fields. The history proof above
already establishes `P>=1,Z>=0` on every positive supplied tuple,
so its pretyping positivity argument remains valid. It changes no
outer field or comparison, costs three additional multiplications,
removes nine comparisons and six supplied fields, and preserves the
exact positive word relation by its explicit root-gap bijection.

This proves the same relation as the former full selected-product
history, not an identity of their differently parameterized output
polynomials. The fixed-table scope still excludes the empty word;
the ordinary-input GPCP boundary already has this exclusion.

## 5. Paid baseline choice, exact degree, and evidence

`build_raw` compiles every allowed pair of baseline slopes when the
corresponding argument is `auto`, compares actual emitted operation
counts, and breaks ties by multiplications and then the numeric baseline
pair. The table determines this finite compiler search; it adds no
runtime choice witness. This claims the best of the emitted baseline
circuits, not a globally optimal arithmetic circuit. `build` defaults
to the unit option, and `unit_product=False` returns the raw source.
`build_from_tiles` retains the parent's nonempty fixed-word validation.

The exact degree argument survives the smaller packing. With each
supplied variable of degree one, `deg P=2` and `deg q_native=2N`.
The top radix region uniquely gives `deg H=deg M=2N-3`, while the
range region gives `deg Z=2N-5`, also when there is no physical region.
The linear transports still have degree at most three. The raw first
Pell residual uniquely has degree `12N+8`, yielding SOS degree `24N+16`.

For the unit source put `d0=2N`. The four factors have degrees
`5d0+7,12d0-4,3d0+5,d0`, with the same main-norm cancellation and
nonzero highest forms proved in the unit parent. The retained strong
residual uniquely has outer degree `4d0+10`. The inequalities used
there remain strict for `N>=5`, the present minimum. Thus the default
product has exact degree `58N+28`; its same-cost SOS alternative has
degree `84N+16`. These statements use literal polynomial degrees,
not substitutions valid only at zeros.

The [source](pcp_affine_slope_class_history.py) and
[receipt](pcp_affine_slope_class_history.json) retain every fixed-numeral
operation. The initial replay checked 504 complete arbitrary raw
residual/SOS identities, 504 full unit-restoration identities, and
504 genuine positive outer paths across all baseline choices on five
tables. Cases include zero exceptional products, singleton and
nondyadic tables, negative coefficient differences, shared upper/lower
partitions, unused classes, and duration one. Six exact weighted
factor-degree checks cover both source families. Outer fixtures are
expressly not numerical instantiations of the large native Pell tuple;
its positive extension is supplied by the proof.

Independent final proof/source/fresh-default reviews by root and
`reduce_complete75` passed without findings. Both checked the pretyping
class bounds, zero-product case, negative baseline coefficients,
positive slack, fresh native witnesses, and exact degree formulas at
the new minimum `N=5`. The latter additionally checked 256 signed full
residual/SOS identities on 16 separate random tables using minimum and
maximum baselines, and 128 genuine outer paths through duration seven.
No finite fixture is claimed to materialize full native Pell zeros.
