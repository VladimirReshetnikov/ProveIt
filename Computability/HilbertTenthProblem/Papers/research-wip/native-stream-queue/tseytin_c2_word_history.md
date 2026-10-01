# A complete paid history for the literal Tseytin C2 semigroup

The [source](tseytin_c2_word_history.py) and
[receipt](tseytin_c2_word_history.json) give a fixed polynomial with **374
operations, 161M+213A, 52 positive existential witnesses and degree at
most 5814**. Its sole positive parameter is `word`. Precisely,

    ∃ positive witnesses: F(word,witnesses)=0
      iff word=enc8(u) for a word u over {a,b,c,d,e}, and u=C2 aaa.

Here `enc8(u)=8^|u|+raw8(u)`, with letters `a,b,c,d,e` assigned digits
`1,2,3,4,5`. Invalid positive integer encodings are rejected by the
same polynomial; alphabet validation is proved below. The duration of
the rewrite history is unbounded, while the witness list is fixed.

This instantiates the actual semigroup table and preserves its
noninvertibility. It supplies the complete encoded-word predicate,
including arbitrary-position rewrites and chronology. It does **not**
include a paid map from an ordinary program/input pair to the Tseytin
query word. In particular, 374 is not a new ordinary-input universal
operation bound and does not change the established 75/87 result.
The [group-completion obstruction](tseytin_group_completion_obstruction.md)
remains applicable: sending C2 directly into a group destroys this
predicate, whereas the present word history does not.

## 1. Actual presentation and actual fixed tile table

The nine symmetric defining relations are

    ac=ca, ad=da, bc=cb, bd=db,
    eca=ce, edb=de, cdca=cdcae,
    caaa=aaa, daaa=aaa.

These are exactly Tseytin's C2, not C1 with its different seventh
relation. The primary source is the translated original paper in the
[appendix to the 2024 edition](https://arxiv.org/pdf/2401.11757):
§1(2), printed page 23, gives this table; §7, Lemma 9 and Theorem 2,
followed by Corollary 1 on printed page 37, give the fixed-target
undecidability result for `aaa`. The local primary PDF text was checked
against both locations. The source imports and literally checks the
same table against the earlier obstruction packet.

Introduce a fresh symbol `#`, assigned digit 6. The fixed tile table has
**24 tiles**: the six copies `(c,c)` for `c` in `abcde#`, followed by both
orientations of each of the nine displayed relations. No tile except
the delimiter copy contains `#`. For a tile `(l,r)`, the numerical
append map is

    (U,V) -> (8^|l| U+raw8(l), 8^|r| V+raw8(r)).       (1)

The receipt stores all 24 word pairs and all 24 four-integer maps.
Their upper and lower slope sets are both
`{8,64,512,4096,32768}`. The paid history planner chooses baseline 64
for both coordinates, leaving four upper and four lower selected
slope-class products. It emits and prices each candidate; the choice
does not create an existential selector for the compiler itself.

One application at an arbitrary position is already represented
literally. For `u=p l s` and a defining orientation `l -> r`, select the
copy tiles for `p`, the single tile `(l,r)`, and the copies for `s`.
The selected images are exactly `(p l s,p r s)`, so both contexts are
preserved. Numerically,

    enc8(p l s) = 8^(|l|+|s|) enc8(p)
                  + 8^|s| raw8(l) + raw8(s).           (2)

Equation (2) explains the ports; it is not passed off as a constant-cost
standalone predicate with unpaid powers or digit alignment. The
complete selected append history below pays these obligations for an
unbounded succession of applications using a fixed number of
coordinates.

## 2. Delimiters recover the complete semigroup relation

Write `σ(w),τ(w)` for the top and bottom concatenations of a nonempty
tile word. The exact word equation is

    σ(w) # aaa = u # τ(w).                            (3)

This is the already proved delimiter construction in
[the fixed-input bridge, §4](gpcp_fixed_program_input_bridge.md#4-fixed-tiles-and-a-single-varying-boundary),
here specialized to all nine actual C2 relations in both directions.
For completeness, each step `u_j -> u_(j+1)` uses the context-copy
selection just described. Separate successive selections by the
delimiter copy. Then (3) telescopes as a literal word equality. A
reflexive derivation of `aaa` uses its three letter-copy tiles.

Conversely split a selected tile word at its delimiter copies. Let
`(X_j,Y_j)` be the two images of chunk `j`. Splitting (3) at the
literal delimiters gives

    X_0=u, X_(j+1)=Y_j, Y_last=aaa.                   (4)

In a chunk, each tile is either a letter copy or one oriented
relation. Replace those disjoint factors from left to right, moving
the cursor by the **new** factor length after each replacement. This
gives an actual C2 derivation `X_j ->* Y_j`, including length-changing
relations. Equations (4) concatenate these derivations. No cancellation
law in the semigroup, invertible image, bounded imbalance, or endpoint
flow surrogate is used.

Empty chunks are harmless. All defining sides are nonempty, so the
empty word cannot derive `aaa`. In particular the numerical input
`word=1` is rejected. The isolated word `b` is also rejected, even
though it and `aaa` have the same image in the trivial group completion.

## 3. Four paid boundary gates, with alphabet validity included

The history starts at `Uinitial=1`, with computed lower initial and
terminal endpoints

    Vinitial = 8*word+6,
    Vfinal   = 4096*Ufinal+3145.                      (5)

There is one supplied positive endpoint witness `Ufinal`. Both
expressions in (5) are strictly positive on every positive assignment,
and both use exactly one multiplication and one addition.
`3145=raw8('#aaa')`, while `4096=8^4`. Substitute these two graph
definitions into every use of the original history parameters,
including its height. This is an exact positive graph substitution,
not a new unsupplied endpoint condition. It removes `Vfinal` as a
witness and removes its otherwise necessary endpoint comparison.

The resulting transport equations imply

    enc8(σ(w)#aaa) = 8^|τ(w)|*(8*word+6)+raw8(τ(w)). (6)

For a valid `word=enc8(u)`, this is exactly (3). Conversely start with
**any** positive integer `word`. Appending base-eight digits preserves
its leading digit. The left side of (6) has leading digit 1, so the
canonical base-eight expansion of `word` also begins with 1. Call its
remaining digit string `u`. The left side contains neither digit 0 nor
digit 7, so neither does `u`. Every tile contributes equally many
delimiter digits to its top and bottom; all non-copy tiles contribute
zero. Counting delimiter digits in (6) therefore gives

    count_#(σ(w))+1 = count_#(u)+1+count_#(τ(w)),

and forces `count_#(u)=0`. Thus all remaining digits of `u` lie in
`1..5`, and it is genuinely a C2 word. This proves alphabet and
sentinel validity without a separate digit predicate or an assumed
valid-input slice. The count argument is a proof about already
recovered literal words, not an uncharged runtime arithmetic gate.

For a later paid loader, the source API is `build(form='coupled')`;
`parameters=['word']`; native register prefix `and__`; and public
registers `c2_initial,c2_terminal`. A composed loader may make `word`
an existential coordinate and constrain its value with its own fully
paid equations. The loader is absent from the present count.

## 4. All chronological and positive-domain obligations remain paid

The implementation uses the existing complete
[slope-class affine history](pcp_affine_slope_class_history.md), with
the guarded [factored linear emitter](pcp_affine_factored_transports.md).
For this table, `s=24`, `g=8`, and the physical scale exponent is
`N=s+g+4=36`. The fixed numeral is `K=65536`, determined by the actual
tile slopes and offsets. Fixed-numeral multiplications are charged.

Writing `rho,beta` for positive height and global slacks, the inherited
wrapper computes

    D=Vinitial+Ufinal+Vfinal+rho, B=K D,
    J=sum_i(Shat_i-1), P=(B-1)J+1.                  (7)

It retains all three outer comparisons: the global bound and both
chronological transports. It retains the 24 positive selector hats,
the eight positive selected-product hats, and both positive history
words. The selected affine updates include the full paid coefficient
forms and all offsets in (1).

Before any native conclusion, endpoint positivity gives `D>=4`,
`B>=32`, `J>=0`, `P>=1`; the global comparison forces `P>1`. Class
selectors are sums over subsets of original nonnegative selectors,
so they are at most `J` before bit typing. The global bound places
histories and selected products below `P`. The joined words therefore
fit their complete allocated lanes, including two top lanes when
duration is one. They are nonnegative before the native theorem.

The complete prescribed AND first types `P`, and the top lane
`B AND (B-1)=0` then types `B`, hence `D`. The exact relation (7)
gives `P=B^t` and `J=1+B+...+B^(t-1)` with `t>=1`. The 24 selector
lanes and their checksum force exactly one tile at each time; `24<B`
excludes carries in the checksum. The range and selected-product
lanes recover the actual current histories and selected slope
classes. Every selected update satisfies

    0 <= a_i z+c_i < (a_i+c_i)D < K D=B

for `0<=z<D`, and likewise on the lower side. The endpoints are below
`D` by construction of the height. Both transports can consequently
be compared as canonical base-`B` expansions: they recover all
intermediate states in their actual chronological order.

For every finite selection satisfying (3), choose a sufficiently
large dyadic `D` above the endpoint sum. Positive affine maps here
are monotone, so all intermediate values are below it. Supply the
canonical packed histories and Boolean selectors. The class products
on each side are disjoint, and the parent's explicit bound

    beta >= ((K-4)D+3)J+1-g > 0

applies with `g=8`. This constructs every positive outer coordinate;
the complete AND theorem then supplies fresh native witnesses. There
is no fixed duration cap and no materialization of enormous Pell
witnesses in the finite checker.

The smaller native forms are the guarded positive-scale projection,
six positive graph definitions, normalized norm units, and finally
[the native index/coupled-linear units](native_binary_index_coupled_units.md).
Their hypotheses hold here: before equations `q=16P^36>=16`, folded
ports are `16H+12,16M+10,16Z+8`, computed `F3>0`, and supplied truth
fields remain positive. Positive scaling gives `X=q(r+beta_native)>r`.
The cited native proof restores signed checksum/index factors in its
established order before invoking full AND semantics. Its conditional
normalization changes only private native coordinates. Accordingly all
five forms represent exactly the same `word` predicate and preserve
outer histories, but no bijection between every normalized/coupled
native tuple or arbitrary-point polynomial equality is claimed.

## 5. Literal costs, degree bounds, and evidence

The chosen raw history costs `345=146M+199A`; (5) adds `2M+2A`.
Every gate has a path to the displayed final output. The native
transformations and finalizers are emitted literally.

| Form | Certificate | Comparisons | Positive witnesses | Final polynomial | Degree bound |
|---|---:|---:|---:|---:|---:|
|Raw prescribed AND|349|19|59|405 = 167M+238A|880|
|Positive scale|349|18|58|402 = 166M+236A|880|
|Six computed fields|349|12|52|384 = 160M+224A|2008|
|Normalized norm units|354|8|52|377 = 161M+216A|6094|
|Index and coupled units|357|6|52|**374 = 161M+213A**|**5814**|

The last two rows use the integer-product finalizer. Their same-cost
SOS alternatives have degree bounds 10472 and 11352 respectively.
These are source-propagated upper bounds, not asserted exact degrees.
The default has factor bounds
`931,2158,503,72,1154,429,429`, totaling 5676, and maximum retained
residual bound 69, giving `5676+2*69=5814`.

The receipt stores the complete default polynomial source, domains,
comparisons and source digest, all five cost ledgers, both available
finalizers, actual table maps and priced history candidates. Author
checks include unrestricted endpoint graph identities, independent
raw residual evaluation, and the inherited transformation-specific
whole-output corrections on positive and signed assignments. The
norm/coupled audits use their actual correction formulas, not a false
claim that all five output polynomials agree away from their zeros.

The word tests cover all 18 oriented relations at all 961 choices of
prefix/suffix of length at most two: **17,298 arbitrary-position
cases**. They enumerate **14,424 selected tile words** through length
three and solve each exact numerical endpoint equation before testing
the input alphabet; all five positive solutions are valid and recover
actual derivations. Complete actual outer paths also cover every one
of the 18 orientations, including expansions and contractions. The
fixtures check all three transport/global equations and the literal
joined AND. They are finite algebra and history checks, not complete
native Pell zeros and not a replacement for the unbounded proof.

Author verification: the final writer and fresh default replay passed, including
all five literal forms and both unit finalizers. The 38 genuine outer
histories contain 531 chronological rows and cover all 18 oriented rules.
Seven local link destinations resolve. Independent full proof/source review
and a further fresh default replay pass without findings. A separate
executor checks64 complete raw endpoint/residual/SOS identities, half
signed, and all five literal ledgers and supplied domains. It independently
enumerates all331776 selected words of exactly four tiles, solves the
integer endpoint equation before assuming input validity, and reconstructs
actual C2 derivations for all four positive solutions. No invalid code is
accepted. These additional finite checks retain the unbounded proof and
the distinction between outer histories and full native Pell witnesses.
