# Reusing paid selector sums gives the sparse compiler505 operations

The [literal source](residue_affine_sparse_control_codes.py) replaces the
control-state encoding in the [537-operation compiler](residue_affine_sparse_terminal537.md).
Its default complete polynomial costs **505=177M+328A**, with **67 positive
witnesses**, **seven comparisons**, one fixed program parameter E=3^e,
ordinary positive input x, and degree **at most5091**. The certificate
costs485=170M+315A. The [receipt](residue_affine_sparse_control_codes.json)
contains the emitted complete schedule and exact validation records.

The fixed U21 table, its branches and prime payload operations are unchanged.
Only the numerical codes in the control transport are replaced. The new
codes are injective and fit the existing radix. Their sums reuse selector
expressions already paid for by the prime and action lanes. No new lane,
witness, radix multiplier or input encoding is introduced.

The new and parent polynomials have **identical positive zero sets on their
supplied coordinates**, including arbitrary positive program/input parameters.
They need not agree away from zero: Section4 gives the exact complete-output
correction. The same valid U21 recipes therefore retain the full universal
ordinary-input representation. This is an independent substrate bound above
the separate established75/87 frontier.

## 1. Literal state codes and the current-control expression

There are36 edges, indexed0 through35 in the inherited literal order.
Edges0,1 are the two loader edges. Body states are1 through21, the loader
state is0 and the halt state is22. Write E_i for the nonnegative decoded
edge selector word, J=sum_i E_i, and

    L=E_0+E_1,
    I=sum_(increment edges i) E_i,
    G_p=sum_(edges i using prime p) E_i.

The complete parent already pays J,L,I and every G_p with p>2. All these
are exact linear forms on arbitrary integer assignments to the selector
hats; this fact does not require Boolean typing.

Assign the following fixed prime weights:

|p|2|3|5|7|11|13|17|19|
|---|---:|---:|---:|---:|---:|---:|---:|---:|
|w_p|0|1|2|3|8|9|17|10|

For body state q, let p(q) be its instruction's prime and define

    c(q)=w_(p(q))+4*[instruction q is increment]+d_q,

where the only nonzero corrections are

    d_9=1, d_11=16, d_12=32, d_13=32, d_14=48, d_18=16.

Set c(0)=0 and c(22)=63. In increasing state order0,...,22 the codes are

    0,1,14,21,9,17,13,10,5,18,8,25,41,32,57,3,12,4,24,2,6,7,63.   (1)

They are pairwise distinct. Every code lies in[0,63]. The unchanged radix
is B=64h with h=E+x+eta>=3, so each code is strictly below B before any
native or repunit equation is used.

Let A_q=sum_(edges with source q) E_i. The current-control word is the
exact identity

    C_c=sum_(p>2) w_p G_p +4(I−L)+sum_q d_q A_q.       (2)

The I−L subtraction removes the increment contribution at the loader;
its prime2 contribution is already zero. Each body state's edge is thereby
assigned exactly its code(1), including both branches of a test/decrement.
The six exceptional A_q are computed from their actual edge lists, and
equal correction coefficients are grouped. Formula(2) uses30 new gates
when added to the already needed non-control source. The old numeric
current-control expression used48.

The API also supports guarded alternative plans. They specify integer
prime weights, an increment coefficient alpha, per-state corrections and
a halt code, while retaining loader code0. If w_2 is nonzero, the exact
first part of(2) is replaced by

    w_2(J−L)+sum_(p>2)(w_p−w_2)G_p+alpha(I−L).

Every derived body/halt code must be positive, all codes must be distinct,
and their maximum must be less than3*C_B with the unchanged C_B=64.
Signed fixed coefficients are allowed in these arithmetic expressions;
positivity of a control digit is proved from its selected state and valid
code, not from the signs of intermediate additions. The default cost is
not claimed for all alternative plans.

## 2. The target-control expression uses two paid prefixes

Besides the complete groups above, two useful intermediate sums are
already paid in the parent:

    A_4=E_2+E_6+E_8+E_11,
    A_3=E_5+E_8+E_9.

The first is a prefix of the decrement-action selector sum; the second
is a prefix of the prime17 selector sum. The implementation discovers
these exact selector vectors from the retained literal rows. It does not
assume that a source register with a suggestive name has the right value.

For target state t_i of edge i define

    r_i=c(t_i)−1−4*[i in{2,6,8,11}]−[i in{5,8,9}].

Then the target-control word has the polynomial identity

    N_c=J+4A_4+A_3+sum_i r_i E_i.                     (3)

For the exact table and codes(1), the residual coefficients r_0,...,r_35 are

    -1,0,9,20,0,7,16,16,7,7,9,0,17,16,7,0,0,24,
    40,31,56,2,23,1,11,3,23,5,24,6,0,62,0,23,0,23.    (4)

Equal nonzero coefficients share their selector sum. Positive terms are
summed and the negative terms subtracted. Exact two-input operation caching
also reuses any identical already paid gate. This literal schedule costs
41 new gates, compared with55 for the parent's target-control expression.
It does not use a zero equation, a Boolean condition or an uncharged sum.

A configurable plan may instead supply a finite list of coefficient/edge-set
basis terms for(3). Each edge set must be nonempty, contain distinct valid
indices, and be the exact vector of an already paid retained selector sum.
The compiler derives every residual coefficient from the requested codes
and those vectors. This is a checked scheduling interface, not a claim of
optimality over code choices or arithmetic circuits.

## 3. Identical positive zeros after typed chronology

The old control comparison is

    B*N_id=C_id+22P,

where the digits are the original state numbers. Replace it by

    B*N_c=C_c+63P.                                    (5)

Both initial codes are zero, so no initial constant is omitted. The final
multiplication uses the actual halt code63. Every other comparison and
native factor is retained exactly.

At a zero of either supported finalizer, all ordinary residuals vanish
and the individual native/repunit factors are units. The full pretyping,
local native rank and exponent recovery, repunit-sign and AND arguments
of [the computed-scale proof](residue_affine_sparse_scale538.md), as adapted
to h>=3 in [the537 terminal-bound proof, Section2](residue_affine_sparse_terminal537.md),
use the positive computed scale, remainder comparison and native equations. None
uses the control comparison. Thus they apply unchanged to the new source.
They recover

    B dyadic, P=B^T, J=1+B+...+B^(T−1), T>=1,

and exactly one selected edge per time row, with the same selected prime,
action and range digits as before. All native ports and source rows in
these arguments are unchanged.

Consequently C_c and N_c have canonical T-digit base-B expansions whose
digits are respectively c(source) and c(target) of the selected edge.
The code bound proved before typing is enough for every digit. Comparison
of the T+1 digits in(5) gives

    c(source_0)=0,
    c(target_j)=c(source_(j+1)) for0<=j<T−1,
    c(target_(T−1))=63.

By injectivity these are exactly initial loader state0, every correct
control adjacency, and final halt state22. Conversely, any edge word with
those state equalities satisfies(5). The old state labels0,...,22 also
fit below B, so on the typed domain the old and new control comparisons
are equivalent.

The payload, paid prefix count and input proofs in the537 parent therefore
remain valid. More strongly, at a new positive zero the reconstructed
edge chronology makes the old control residual zero on the **same supplied
coordinates**. Every other residual and the native unit product already
coincide. Recomputing the removed old control gates thus gives an old zero
without changing any witness. The reverse implication follows by the same
typed edge word at an old zero. This proves identical positive zero sets,
not merely equality of existential input projections.

In particular the nontrivial native sign arguments are not assumed from
the desired chronology, and control codes are never used as prime-payload
values. No change to the actual U21 transition table or numerical input
recipe is involved.

## 4. Exact source preservation, finalizers and degrees

Let r_old and r_new denote the old and new control residuals, U the
unchanged native/repunit product, and S the sum of squares of every other
ordinary residual. The product finalizers satisfy, on all integer tuples,

    P_old=U*(1+S+r_old^2)−1,
    P_new=U*(1+S+r_new^2)−1,
    P_new−P_old=U*(r_new^2−r_old^2).                   (6)

For the same-cost SOS finalizer, the correction is simply
r_new^2−r_old^2. These identities include signed assignments and do not
require any factor to be nonzero. They are not asserted polynomial equality.

The source guard reconstructs the complete canonical537 caller in the
selected native form and packing recipe and requires exact equality. The
caller must have the literal U21 and inherited prime list. It then verifies
the actual old control rows and removes only their ancestry absent from
all other comparisons. Existing prime/action/remainder gates shared by
other constraints remain. It verifies that no removed private register
is exported by another active interface. The two control ports are
recursively remapped to their new outputs, and every final emitted gate
must reach the complete polynomial output. New gate names cannot collide
with any old register or input. Historical parent dictionaries remain
provenance; no old rewrite is reapplied to the altered source.

The full old control ancestry had106 gates:48 current,55 target and3
transport gates. The new ancestry has74:30 current,41 target and3
transport. The saving is32 gates, comprising16 multiplications and16
additions/subtractions. No supplied coordinate or comparison disappears.

|Native form, shared packing|Certificate|Comparisons|Witnesses|Polynomial|Degree bound|
|---|---:|---:|---:|---:|---:|
|Normalized norm units|482=168M+314A|9|67|508=177M+331A|5345|
|Coupled index units|485=170M+315A|7|67|505=177M+328A|5091|

The unshared packing schedules are also emitted and audited: their
polynomial costs are647=247M+400A and644=247M+397A respectively, with
the same corresponding degree bounds and witness counts. They are useful
comparison schedules, not improved bounds.

Both control words remain degree-one forms in the selectors, and their
transport residual has degree at most2. The radix, scale, every native
factor and every other residual are unchanged. The complete degree
dictionary in either form/finalizer is therefore the parent's dictionary.
The default factor bounds remain816,1900,442,65,1018,375,375,2, summing4993;
the maximum other residual bound is49. The product bound is5091 and the
same-cost SOS bound9986. These are propagated upper bounds, not claims
of exact total degree or a circuit lower bound.

## 5. Validation and scope

Run `python3 residue_affine_sparse_control_codes.py`; `--write` regenerates
the receipt. The checker covers both native forms, shared/unshared packing,
both finalizers and four valid plans: the default, doubled codes, no target
basis, and body/halt codes shifted upward by one while loader0 is retained.
The last plan explicitly exercises nonzero w_2 in Section1.

Sixteen source/degree ledgers give1536 complete retained-register,
interface, factor and finalizer correction identities on768 assignments,
including384 signed assignments. Separate sharing checks give384 complete
outputs on192 assignments, including96 signed. Exact selector-vector
propagation verifies both new control sums before numerical evaluation.
Every emitted gate is an ancestor of the complete output.

There are436 typed control-word fixtures, including36 accepted words that
cover every literal edge. They compare chronological validity with both
old and new numeric equations. Three actual halted U21 outer histories
with175 rows pass the unchanged payload, remainder and prefix constraints
and the new control comparison. Eleven malformed caller/plan cases are
rejected. These are algebraic, control and outer-history fixtures; no full
native Pell witness is materialized by these finite checks.

The fixed U21/primes are deliberately guarded rather than silently claiming
support for arbitrary tables. All code constants and scalar products are
included in the literal source count. The positive-zero theorem is general
for plans accepted by the stated guards; the505 cost belongs to the displayed
default.

The author writer and separate fresh replay pass. Root independently
reviewed the complete proof/source/dependencies and passed the final
four-plan replay. His separate API audit checks768 complete finalizer
and degree cases on384 assignments, including192 signed, across twelve
contexts with nonzero w_2, negative coefficients and a maximum code191.
Additional checks cover11472 typed-control equivalences and28 actual
halted U21 outer histories with7315 rows.

Gibbs independently reviewed the full proof/source/dependencies and passed
a fresh replay, with no findings. His separate executor checks384 complete
register, factor, residual and finalizer corrections, including192 signed,
across24 contexts/six plans;48 coefficient vectors and48 literal
degree/opcode/closure checks also pass. A separate control oracle covers
all46656 three-edge U21 words. His own counter interpreter supplies36
halted histories with6174 rows and216 old/new transport identities.
All local links resolve. These independent finite checks retain the
algebraic and outer-history scope above; they do not materialize full
native Pell witnesses.
