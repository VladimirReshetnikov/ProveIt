# Weak-cone native Grill closure: 208 complete operations

The complete native Grill compiler for fixed program `(0,1,1)` now costs **208=93M+115A**, with31 positive witnesses,11 comparisons and formal degree at most1187. Its sum-of-squares alternative costs **232=99M+133A**, with37 witnesses,20 comparisons and degree at most484. The change replaces `P0=3x+Z0` by `P0=x+Z0`, removing exactly one multiplication from each complete schedule.

Unlike the preceding [phase-sharing rewrite](grill_tag_native_phase_sharing.md), this changes the polynomial and the supplied positive zero set. It preserves the existential language of positive ordinary inputs `x` by the [whole-period padding theorem](grill_tag_padding_period.md). The old and new polynomials are identical only after an explicit signed slack substitution. No universal Grill program or ordinary-input universality decoder is established, and the separate87-operation universal bound is unchanged.

The [source](grill_tag_native_weak_cone.py) pins the209 parent SHA256 `760ce9a0ea6e6020ecb52737ccc5c4197f7b84a212c73dc351b9ae3e6ef60069`. Its [receipt](grill_tag_native_weak_cone.json) contains all eight full schedules, exact algebraic checks and carefully scoped semantic fixtures. The padding reference is frozen at source SHA256 `299acc95d66b60fb7fe2b3e3a85ffd3ec7c77f8c53ce2f11d1b59d9f7d59ba48`, proof SHA256 `9dde1ba4982fbc2c84c406e46859c125a3c9a93fccb176a159c23ef6399b6d11`; it is a theorem dependency, not a runtime arithmetic oracle.

## 1. Literal source change and exact algebra

The actual parent has the two paid rows

    three_x__0 = 3*x
    input_width__1 = Z0+three_x__0.

The tripled-input register has exactly one complete-source consumer, the width definition. The slack coordinate also has exactly that one consumer. The child deletes the first row and emits

    input_width__1 = Z0+x.

Every subsequent source row, comparison list, native factor and finalizer row remains literal. The same positive named coordinates are supplied, but their interpretation changes at the initial width.

Write `F_s` for the strong parent's polynomial and `F_w` for the weak child's polynomial, in either finalizer mode. The complete all-value relation is

\[
 F_w(x,Z,\mathbf y)=F_s(x,Z-2x,\mathbf y),
\]

because `3x+(Z−2x)=x+Z`. The source proves this affine identity first, then compares all complete comparison operands, named semantic interfaces, native factors and the final output using an exact expression DAG. This is a polynomial identity over the integers, rationals and reals after the stated substitution; no zero or sign assumption is used. It is not a same-coordinate polynomial identity, and no additive correction is silently discarded.

A positive strong tuple maps to a positive weak tuple by `Z_w=Z_s+2x`, with every other coordinate unchanged. The outputs and residuals agree under this map. Conversely, the formal pullback `Z_s=Z_w−2x` may be zero or negative; it is an integer algebra map and cannot justify applying the strong parent's positive-zero theorem to an arbitrary weak tuple. The weak semantic proof below is therefore supplied independently of that pullback.

There is a useful exact separation on identical supplied tuples. Let `kappa` be the fixed compiler multiplier and `J` the unchanged selector sum. The two heights and global powers satisfy

\[
 D_s-D_w=2xV_{\rm final},\qquad
 P_s-P_w=2\kappa xV_{\rm final}J.
\]

The global-bound left side is unchanged. With residual orientation `left−P`,

\[
 R_{{\rm global},s}-R_{{\rm global},w}
 =-2\kappa xV_{\rm final}J.
\]

At a positive zero, the retained global comparison forces `P>1`, hence `J>0`. The displayed difference is then strictly negative. Since a complete positive zero in either finalizer mode forces that global comparison to vanish, **no identical positive tuple is a zero of both sources**. This makes the distinction between equality of existential input languages and equality of supplied positive fibers explicit.

## 2. Native weak-cone soundness, before using padding

The new positive coordinates give

\[
 P_0=x+Z_0\ge2,\qquad 0<x<P_0,
\]

and the unchanged computed endpoint and height are

\[
 U_f=P_0V_f+x,\qquad D=U_f+\text{phase_initial}+\rho.
\]

On every supplied positive tuple, before any AND or history interpretation,

\[
 U_f>P_0,\quad U_f>V_f,\quad U_f>1,\quad
 D>U_f,\quad D>\text{phase_initial},\quad D\ge5.
\]

Indeed `U_f>=3`, and both other height addends are positive. These are the individual bounds used by the [native parent's geometry proof](grill_tag_native_word_closure.md); its required lower bound `D>=4` still holds. The inequality `P0>3x` was not required for any of them.

The remaining pretyping argument is unchanged. Hats decode to natural selectors and selected products, so `J>=0` and `P=(B−1)J+1>=1`, where `B=kappa D`. The first global comparison at a zero gives `P>1`, `J>0`, `B<=P`, and all prescribed history/selection bounds. Thus

\[
 P_0<D<B\le P.
\]

The paid input-width lane at the top of the joined AND therefore still contains `P0` and `P0−1` strictly inside its base-`P` region. Every other region and its preceding no-carry bound remains unchanged. All joined conceptual native inputs are positive before classification; the same complete native theorem makes the scale and `P` dyadic, separates the regions, and recovers

\[
 P_0\mathbin{\mathrm{AND}}(P_0-1)=0.
\]

Since `P0>=2`, this forces `P0=2^ell` with `ell>=1`. The old radix, range, selector and repunit arguments still recover a genuine common affine history with nonempty duration. The same paid phase equation, including the shared projections, enforces the reverse chronological phase path ending at original phase zero. No native equation, positive slack, phase restriction or range check was removed.

For the word boundary, the recovered sentinel endpoints have the old meanings

\[
 U_f=\operatorname{code}(\operatorname{reverse}(h)),\qquad
 V_f=\operatorname{code}(\operatorname{reverse}(G(h))).
\]

The equality `U_f=P0 V_f+x` needs only the now-proved dyadic width and `0<x<P0`. Multiplication by `P0=2^ell` leaves precisely `ell` low binary positions, and `x` fits in them. Uniqueness of sentinel coding gives `h=w_ell(x)G(h)`. The actual queue follows this word until its first empty state, so it halts at or before the proposed closure length. A post-halt suffix remains a word-closure witness, not a claim that transitions fire from the empty queue.

The integer-product finalizer uses the same native factors and restoration rules. Its pretyping premises remain valid: the native scale is positive, `q_native>=16` and the prescribed `F3>=8`. Consequently the retained norm-sign and positive-restoration theorem still forces the same outer and native constraints at positive zeros. The strong-to-weak algebra map alone is not being used to establish this direction.

## 3. Complete weak-cone converse and equal input languages

Suppose a padded input word with dyadic `P0>x` actually halts. Set `Z0=P0−x>0`, use its actual finite head word, reverse its tile order and build the two positive sentinel histories exactly as in the parent converse. The word equation supplies `U_f=P0 V_f+x`.

Choose a dyadic `D>U_f+phase_initial` and a positive height slack. Because `U_f>P0,V_f,1`, this still bounds every endpoint. Pack the pre-update histories and one-hot selectors at `B=kappa D`, let `P=B^t` and use the corresponding repunit. The global slack remains positive by the parent's unchanged estimate

\[
 \beta\ge((\kappa-4)D+3)J+1-g>0,
\]

where `g` is the number of lower-slope classes. All transport and phase rows telescope. The extra width lane holds because the chosen `P0` is dyadic and below `P`. The full positive converse of the retained native AND supplies the remaining Pell witnesses at that exact scale; the unit mode then uses its retained positive restoration/projection theorem. This proves a complete weak-cone representation, without materializing the enormous Pell witnesses in the finite checker.

Now compare accepted ordinary inputs, existentially quantifying **all** witness coordinates. Every strong zero maps positively to a weak zero by `Z_w=Z_s+2x`.

For the reverse implication, a weak zero first gives an actual halting padded word `w` by Section2. If the program has period `m`, append exactly `2m` zeros. The [padding theorem](grill_tag_padding_period.md) proves that this preserves halting and increases the actual first-halting time by `2m`, because the inserted zero block advances the phase by whole periods without emitting symbols. Its new width is

\[
 P'_0=2^{2m}P_0=4^mP_0>3x.
\]

The extended word lies in the strong cone. Apply the strong parent's full positive completeness theorem to rebuild its histories, slacks and native extension. If the weak witness had a post-halt suffix, this construction uses the recovered **actual first halt**, not that suffix as a causal history. It does not retain a particular packed witness tuple or its proposed duration.

Thus for every fixed finite Grill program and every positive `x`,

\[
 \exists\mathbf z>0:\ F_w(x,\mathbf z)=0
 \quad\Longleftrightarrow\quad
 \exists\mathbf z>0:\ F_s(x,\mathbf z)=0.
\]

Only this existential input-language equality is claimed across the full positive domains.

A small concrete boundary case is program `(0,)`, `x=1`, weak width2 and slack1. The input word `1` halts with heads `10` at time2. Its signed strong pullback slack is `−1`. A true outer packed fixture has

    Vfinal=2, phase_initial=1, height_slack=2,
    H_U=129, H_V=65, Shat0=2, Shat1=65,
    ZVhat0=65, global_bound=3837,
    D=8, B=64, P=4096.

Both full source modes satisfy all four outer comparisons and the joined semantic AND at these outer values. The checker leaves native Pell coordinates as placeholders and explicitly checks that these placeholders are **not** a complete polynomial zero. Appending two zeros gives strong-cone word `100`, width8, strong slack5 and actual first halt4; existence of its full native witnesses follows from completeness, not from the placeholder tuple.

## 4. Complete costs and metadata

Every program/finalizer pair loses exactly one paid multiplication, with no change to the witness or comparison count. The entire retained finalizer is included.

| Fixed program | Finalizer | Parent operations | New M | New A | New operations | Witnesses | Comparisons | Degree upper bound |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| `(0,)` | Sum of squares |192|83|108|191|32|20|304|
| `(0,)` | Native unit product |168|77|90|167|26|11|737|
| `(1,)` | Sum of squares |195|85|109|194|32|20|304|
| `(1,)` | Native unit product |171|79|91|170|26|11|737|
| `(0,1,1)` | Sum of squares |233|99|133|232|37|20|484|
| `(0,1,1)` | Native unit product |209|93|115|208|31|11|1187|
| `(2,0,1)` | Sum of squares |241|105|135|240|38|20|520|
| `(2,0,1)` | Native unit product |217|99|117|216|32|11|1277|

The degree entries are propagated full-source upper bounds. The source retains `exact_degree=None`; no new exact-degree assertion is inferred from the old bound. The invertible linear substitution relates actual degrees, but neither parent's actual degree is established by this packet.

Top-level `full_polynomial_identity` is now false, and the parent phase-sharing proof/adapter metadata is explicitly archived under `strong_parent_metadata`. Current source counts, wrapper counts, scope and input-cone metadata describe the weak source. The parent phase affine identities remain mathematically true, but their historical assertion of a same-coordinate whole-polynomial identity is not presented as the current relation.

The small programs in the table are not claimed universal. No ordinary-input decoder or fixed universal Grill recognizer has been supplied. Whole-period padding also does not make arbitrary single-zero padding harmless; the cited theorem gives explicit counterexamples. This packet leaves those universality obligations open.

## 5. Interfaces and verification

`build(program=(0,1,1),*,unit_product=True,root=None)` emits the complete weak source. `checked`, `canonical_parent`, `rewrite` and `polynomial_source` validate or return full canonical packets and defensive copies. `rewrite` accepts only the pinned complete strong parent. `evaluate` requires every named coordinate to be an exact positive integer, or unrestricted exact integers with explicit `signed=True`. `identity` evaluates the full shifted strong tuple and weak tuple and returns their common output and residuals.

`integer_pullback` returns `Z_s=Z_w−2x` and explicitly permits its output slack to be nonpositive; it is not a positive witness restoration. `strong_to_weak_assignment` accepts a positive strong tuple and returns a positive weak tuple with `Z_w=Z_s+2x`. Both return fresh assignment dictionaries. No executable arbitrary weak-to-positive-strong witness reconstruction is claimed.

The direct parent and its complete inherited source chain are reauthenticated on public calls, including warm cached calls. First construction uses authenticated source bytes and the parent's isolated dependency loader. The source rejects optimized execution and exact-type substitutions. The padding proof pin is recorded as mathematical provenance; no caller-supplied padding fact or runtime oracle is used by the circuit.

The author checks cover eight complete symbolic substituted-polynomial identities and124 formal residual identities;96 complete integer evaluations, including48 signed cases and1,488 residual evaluations;16 rational substitutions;96 exact same-coordinate global-row corrections;48 positive strong-to-weak maps and48 weak-cone pretyping checks. Eight explicit same-coordinate evaluations have different full outputs. The receipt also records263 malformed-call rejections,24 defensive-copy checks, two warm source-pin rejections and the two honest weak outer-AND fixtures above. General language equality is proved by the native arguments and padding theorem, not by these finite evaluations.

Portable replay with the pinned parents available:

    /path/to/research-venv/bin/python grill_tag_native_weak_cone.py \
      --root /path/to/native-stream-queue \
      --expect grill_tag_native_weak_cone.json \
      --output /path/to/fresh-receipt.json

The root argument may be omitted when running beside the inherited WIP sources. The interpreter must satisfy those historical dependencies. The receipt contains no absolute worktree paths or timing fields. Only an explicitly requested output and private temporary guard copies are written.
