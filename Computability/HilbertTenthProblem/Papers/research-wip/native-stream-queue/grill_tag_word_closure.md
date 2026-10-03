# Grill word closure removes all intermediate width coordinates

This finite-horizon certificate uses **t+1 positive witnesses**, **t+2 residuals** and exact degree **2t+2**. Its literal complete schedule costs

    10t+7−z(t) = (4t+3−z(t)) multiplications + (6t+4) additions/subtractions,

where z(t) is the number of zero program exponents among the first t phases. The horizon t>=1 and finite natural program are external. Every gate and the complete finalizer are paid. This is not a fixed-arity universal equation or an improvement to the separate87-operation universal bound.

The construction certifies a completed word equation. A positive zero implies that the actual queue halts **at or before t**. An actual halt **exactly at t** supplies a positive zero. At a fixed t these statements do not assert equivalence with all runs halting by t, equality to the earlier first-halt witness relation, or a bijection with the affine history coordinates. Taking the union over all external horizons gives precisely the same padded-input halting predicate.

The stop-at-first-short-queue proof pattern is already used in [binary_tag_four_tile_history.md, Section2](binary_tag_four_tile_history.md). The new mechanism here is the special Grill appendant identity, its telescoping content equation and deletion of all intermediate widths. The fixed Grill macro semantics and positive input cone are those of [grill_tag_affine_scout.md](grill_tag_affine_scout.md); this note does not resolve that scout's separate universal-input decoder and primary compiler questions.

## 1. Two rows and the exact content identity

Fix a nonempty program `(n_0,...,n_{K−1})` of natural integers. At step i use n_(i mod K). A nonempty queue removes its first bit d and, if d=1, appends

    g_i = 0(10)^(n_i).

A zero head appends the empty word. Empty queue halts. The front of every word is its least significant bit. For a word v, write `val(v)=Σ_j v_j 2^j` and `scale(v)=2^length(v)`.

Supply positive ordinary input x, positive Z0, and positive head hats D_i. Define

    d_i=D_i−1,                 H_i=4^(n_i),
    R_i=1+(2H_i−1)d_i,         S_0=1,
    S_(i+1)=S_i R_i,           C=Σ_(i<t) d_i S_i,
    B=Σ_(i<t) 2^i d_i,         P0=3x+Z0.

The complete polynomial is

    F = (P0*S_t−2^t)^2
        + (Z0+P0*C+3B−2^t)^2
        + Σ_(i<t) d_i(d_i−1).                         (1)

For every integer d, `d(d−1)>=0`, with equality precisely at0 and1. Thus an integer zero of F forces both displayed rows and every Boolean head. This is an unsquared nonnegative Boolean penalty, not an unsquared arbitrary residual. All positive zeros have D_i in{1,2}.

For Boolean d_i, R_i is precisely the scale of the selected appendant:1 for empty, or2H_i for g_i. The content of the nonempty appendant is

    val(g_i)=2(H_i−1)/3,
    3*val(selected g_i)=R_i−1−d_i.

Let G be the concatenation of all selected appendants, in step order. Then

    scale(G)=S_t,
    3*val(G)=Σ_i S_i(R_i−1−d_i)=S_t−1−C.             (2)

The last equality telescopes `S_i(R_i−1)=S_(i+1)−S_i`. Its algebra is exact; only the word interpretation requires Boolean heads.

At a positive zero, `P0*S_t=2^t` and Boolean heads imply that S_t is a power of2. Therefore P0 is also a power of2, say `P0=2^ell`. Since `P0=3x+Z0>3x`, the ell-bit, high-zero-padded binary word w with content x exists and lies in the positive code cone. In particular ell>=2. The first row says

    ell+length(G)=t.

Substituting `Z0=P0−3x` into the second row and using(2) gives

    B=x+P0*val(G).                                    (3)

Both sides are values of words of length t: the left is the t-bit head word `h=d_0...d_(t−1)`, and the right is w followed by G. Fixed-length binary coding is injective, including high zeros. Hence the two rows are exactly the global word closure

    h = w G(h).                                      (4)

Conversely, for a word w of width P0 satisfying the input cone, a Boolean head word of length t satisfying(4) gives both rows and F=0. There is no unpaid power predicate in this externally fixed finite schema: the terminal length equation forces the initial dyadic width.

## 2. Why every closure implies actual halting

A global word equation must not be mistaken for a legal trace through its entire supplied length. The following induction deliberately stops at the first empty queue.

Let `G_<j` be the concatenation of the appendants selected by the first j proposed heads. Initially the actual queue is w. Suppose it has not emptied before step j. After consuming j heads, its current word is the suffix of `w G_<j` obtained by deleting its first j bits. This assertion holds at j=0.

Because `w G_<j` is a prefix of the complete word `w G(h)=h`, if the current suffix is nonempty its first bit must be h_j=d_j. The actual program phase is j mod K, so the actual appendant is exactly the selected j-th appendant. Deleting the head and appending that word proves the induction at j+1. The argument never reads an appendant produced after the queue has already emptied.

If the queue empties at some j<t, it has genuinely halted. Otherwise the induction continues through all t steps. The final queue is obtained by removing t bits from the length-t word `w G(h)`, and is empty. Thus every positive zero gives an actual halt at a time tau<=t.

Conversely, consider a genuine run from a padded binary x in the stated cone that first empties after exactly t steps. Record its actual heads. Every bit in the initial word or appended during the run has then been consumed exactly once, in FIFO order, so those t heads form precisely `w G(h)`. Equations(2)–(4) give a positive zero by setting `D_i=d_i+1` and `Z0=P0−3x`.

Therefore, for each fixed program,

    some positive zero at some external t
      iff some high-zero-padded binary x, with P0>3x, halts.

The program and cyclic phase start are fixed throughout. No padding-insensitivity or universal ordinary-input decoder is inferred. Every positive closure has t>=3: w has length at least2 and contains a1, whose selected appendant has length at least1. Horizons1 and2 consequently have no positive zero for any program.

## 3. Genuine post-halt witnesses

For program `(0,1,1)`, take x=1,Z0=1, hence P0=4 and initial queue `10`. Its actual run has heads `100` and halts after3 macros. Nevertheless the six-bit word

    h=100010

satisfies closure. The selected appendants concatenate to `G=0010`, so `wG=100010`. The exact scalar values are

    t=6, S_t=16, C=3, B=17,
    4*16=64,
    1+4*3+3*17=64.

The positive head hats are `(2,1,1,1,2,1)`. This is a positive integer zero of(1). It is not a first-halt-at6 history. The formal restoration of an intermediate affine width would give

    P_4=P0*S_4/2^4=1/2,

so no positive-integer affine lift exists. The old local history cannot fire from its empty endpoint.

More generally, every suffix `(010)^m` appended to `100` gives a closure at `t=3+3m`: phase repetition makes G(010)=010, while the actual initial queue still halts at3. This illustrates why the relation to causal histories is existential halting equivalence across horizons, not a full positive-zero bijection. At a fixed t, a head word uniquely determines P0, then Z0 and x if the two rows are satisfiable; distinct closure words can nevertheless provide different witnesses.

## 4. Share the scaled prefix products

A direct evaluator of(1) computes S_i,C and multiplies P0 into S_t and C at the end. Its literal schedule costs

    11t+7−z(t) = (5t+3−z(t))M + (6t+4)A.

A better complete evaluator carries the already scaled values:

    A_0=P0,
    T_i=d_i A_i,
    A_(i+1)=A_i+(2H_i−1)T_i,
    E=Σ_i T_i.

Induction over the polynomial ring gives, on **all supplied tuples**,

    A_i=P0*S_i,             T_i=P0*d_i*S_i,
    E=P0*C.                                           (5)

Thus the two residuals become

    A_t−2^t,
    Z0+E+3B−2^t,

with exactly the same polynomial F, including every off-zero value. No Boolean identity is used in(5). This eliminates t multiplications from the displayed direct schedule, not merely t comparisons or uncharged source expressions.

The complete scaled ledger is as follows. All2^i,2^t,4^(n_i) are program/horizon constants in this fixed schema; their runtime multiplication by a variable is charged unless the coefficient is0 or1.

| Work | Multiplications | Add/subtract |
|---|---:|---:|
| P0=3x+Z0 |1|1|
| t shifted heads and Boolean factors |t|2t|
| T_i and scaled width recurrence |2t−z(t)|t|
| Sum E and weighted binary B |t−1|2t−2|
| Two residuals, including3B |1|4|
| Two squares and summation with t Boolean penalties |2|t+1|
| **Complete total** | **4t+3−z(t)** | **6t+4** |

The [emitter](grill_tag_word_closure.py) folds constant-only arithmetic and neutral0/1 operations, reuses identical commutative subexpressions and verifies that every emitted gate reaches the output. It does not claim arbitrary algebraic-circuit optimality. The [receipt](grill_tag_word_closure.json) contains complete direct/scaled sources in both Boolean finalizer modes for the representative horizons1,3,6, plus deterministic regeneration of the wider tests.

Against the earlier aggregate affine certificate's literal `15t+2−z(t)` schedule, the scaled closure saves5(t−1) operations and t−1 positive witnesses. This is a comparison of two different finite-horizon witness relations: the old one specifies first halt at t and restores every positive intermediate width, while the new one may include post-halt closures. Their unions over horizons define the same padded-input halting predicate. For the genuine `(0,1,1),x=1,Z0=1,t=3` example, the old aggregate uses46 operations and6 positive witnesses; the new one uses36 operations and4, with degree8 instead of4.

## 5. Degree and the integer-domain boundary

Each R_i is affine in its distinct head hat, with nonzero coefficient `2H_i−1`. Hence S_t has degree t and P0*S_t has degree t+1. The first residual square has degree2t+2. The second residual has degree at most t+1. Its leading square cannot cancel the first square over the reals; the Boolean penalties have degree2. Consequently F has exact degree2t+2 for every fixed program and t>=1. This is a formal polynomial degree, not only a syntactic upper bound.

The reference mode squares the Boolean residuals too. On integer assignments it has exactly the same zeros, and the entire off-zero correction is

    F_all_squared−F = Σ_i [b_i^2−b_i],
    b_i=d_i(d_i−1).

The reference costs t extra multiplications and has the same exact degree2t+2. It is not used in the main ledger.

The unsquared Boolean factors are nonnegative on integers, not on arbitrary real inputs. The distinction is substantive even with x and Z0 positive integers. For program `(0,1,1)`, t=3 and x=Z0=1, set `d=(1,delta,0)`. Direct substitution gives

    F=delta*(3333delta−1).

Thus `delta=1/3333`, equivalently positive real `D_1=3334/3333`, gives a non-Boolean zero. The public evaluator rejects this fractional assignment. No positive-real zero theorem is asserted.

## 6. Interfaces and evidence

`build(program,horizon,mode='scaled',square_boolean=False)` requires an exact nonempty tuple of natural program exponents and an exact positive integer horizon. `mode='direct'` emits the identical direct polynomial; `square_boolean=True` emits the all-squared reference. The returned packet lists every input, positive witness, residual, intermediate register and source row. `checked` validates the entire packet against a fresh canonical emission; no public mutable cache exists. `evaluate` requires exact positive integer assignments, or explicit `signed=True` for integer algebra checks. `decode_zero` requires a positive zero and returns the exact global words and actual first halting time. It never asserts that a post-halt witness lifts to a causal affine history.

The author checker passed96 live complete-DAG ledgers,64 exact expanded whole-polynomial identities and288 exact residual identities,768 complete signed evaluations,48 full Boolean-finalizer corrections,4,320 arbitrary positive candidate tuples and53 malformed-input rejections. Its complete small head-word census considered4,088 words across four programs and horizons1–9, finding101 positive closures; all decoded to actual halts, six before the supplied horizon. A separate converse check lifted102 actual padded-input halting runs. Exact sparse polynomial expansion attained the degree formula on the declared finite cases; the general degree proof is Section5.

The emitted-source tests do not prove universality, quantify the external horizon or bound witness bit lengths. A uniform fixed-arity version would still have to pay for phase-controlled products and content accumulation, enforce the global word semantics, and handle the ordinary input decoder. The constants2^i and2^t are free only because i and t belong to this external finite schema.

Run the standalone standard-library checker:

    python grill_tag_word_closure.py \
      --output /path/to/fresh-receipt.json \
      --expect grill_tag_word_closure.json

The source imports neither the affine scout nor downloaded creator code. It rejects optimized execution, checks receipts with exact types, and writes only an explicitly requested output. Original reports and the frozen affine scout remain unchanged.

An independent full source/proof review passed without findings. Its checker proved144 complete emitted polynomial/count/degree/liveness identities and792 residual identities across six programs and horizons1–6, including72 direct/scaled identities;432 signed evaluations passed. Its complete12,276-head-word census found247 positive closures, including20 post-halt examples, all of which halted by the supplied horizon;494 source/decoder checks,81 malformed-input rejections and two copy-isolation checks passed. Its fresh replay passed. Root separately read the source and reproduced the frozen author receipt. These finite results supplement the general arguments above.
