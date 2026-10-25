# Independent mathematical review: primitive odd-sum root mergers

## Verdict

**Approved as ordinary integer zero-existence reductions to the explicitly
pinned fifteen-variable free-scale parent.** The two new endpoints are:

| Integer variables | Exact degree | Live binary operations |
|---:|---:|---:|
| 14 | 86 | 112 |
| 14 | 94 | 110 |

The 86/112 endpoint improves the supplied 14/88/119 endpoint in both degree
and evaluator length. The 94/110 endpoint is a different tradeoff. The
13/156/125 and 14/88/115 companions are pointwise-identical recompilations
of existing polynomials, saving redundant subtraction/addition pairs; the
latter is dominated by 14/86/112. No global optimum claim follows.

I read the complete latest `roots/deliverable/PROOF.md`, the actual builders
and DAGs, the immediate `FREE_SCALE15_PROOF.md`, and the incoming 14- and
13-variable root proofs. I independently verified all formulas and live
gates for the two new DAGs, their degrees and two nonzero coefficients each,
the complete fixed coefficient payloads, and the universal merger and lift
identities. The exact finite checker and receipts are
`review/roots_independent_audit.py` and `roots_independent_audit.json`.
Normal and optimized runs agree.

The inherited signed-Pell/native/source34/compiler/refutation theorem is an
ordinary mathematical dependency. This review does not newly prove that
entire historical theorem, build its full proof-assistant closure, or infer
consistency from tests. The new reductions first construct literal parent
zeros and do not invent a new native or canonical-witness premise.

## 1. The odd-sum lemma really excludes all cancellation branches

For integers `b,d,e,s`, `d!=0`, put

    G=4b+1, x=2s+1,
    K=d(s(s+1)-b)-e, N=K²-Gde.

The exact identity is

    16N=[d(x²+G)-4e]²-4d²x²G.

Because `x` is odd it is never zero. At `N=0`, the rational number

    g=[d(x²+G)-4e]/(2dx)

therefore exists and has square `G`. A rational number whose square is an
integer is an integer; `G=1 mod4` then makes `g` odd. Hence
`u=(x-g)/2` is an integer. Substitution gives `du²=e`. Conversely, if
`g²=G`, `du²=e`, and `x=g+2u`, direct substitution makes `K=dgu`, hence
`N=0`.

This is stronger than an informal signed-radical argument: it uses no
independence of square classes, no positivity of `d` or `e`, and no choice
of complex square-root branch. In particular it handles `e=0`, negative
`d`, and negative `e`. A negative `G` cannot occur at a zero because the
identity makes it the square of a rational number. The sole possible
rational-extraction denominator failures are `d=0` or `x=0`; the latter
is excluded syntactically and the former is proved absent at the precise
stage where the lemma is applied.

## 2. Degree-86 equation: unit products before division

The common source front has authentic odd `beta>1`, so
`q=beta(6j+1)+1` is even and nonzero. Also `|12w+4|>=4`, whence
`|X|>=8`; `a=(X+1)Y` is zero or has absolute value at least seven.
Thus `Delta=(a+2)²-1>=3` on every integer assignment. No source zero,
Pell classification, positivity guard, or CRT conclusion is used here.

Write `Acar` for the retained first carrier and
`Sunit=f²-Delta I²`. The carrier is a square modulo four, so
`Acar+1!=-1`. Since `Delta` is zero or three modulo four,
`Sunit` is never three modulo four and cannot be `-1`. Consequently

    (Acar+1) Sunit (N+1)=1

forces the first two factors to be `+1`, and then the last to be `+1`.
This is ordinary integer unit factorization, not an unsupported positivity
claim about `N`.

The recovered strong equation gives `Q=Delta²I²`, so `Q` is zero or at
least nine; `delta=Q-1` is nonzero. Apply the lemma with

    B=budget-p1²-p2², b=B-1, d=delta, e=Cy=QV²-1.

It supplies odd integral `g` and integral `u`. Restore

    p3=(g-1)/2, y=u-V.

Then `p3(p3+1)=B-1`, and the old auxiliary residual is exactly
`Cy-delta(V+y)²=0`. The carrier and strong residual were already zero.
Every new zero therefore yields a literal zero of the old four-residual
SOS polynomial, with all retained inputs and all six coefficient integers
unchanged.

The branch `I=0` is not lost: it gives `Q=0`, `delta=-1`, `Cy=-1`, and
is covered by the signed lemma. If further old source reasoning excludes
it, that happens only after the old zero has been restored. No such
exclusion is silently imported into the new root extraction.

Conversely, from any old zero let `u=V+y`, `g=2p3+1`, and set
`s=p3+u`. The old guard gives `g²=G`, the old auxiliary row gives
`delta u²=Cy`, and `2s+1=g+2u`. Therefore `N=0` and the new product is
one. This polynomial lift works on every old zero, not just canonical
ones, and needs no new rank or interpolation freedom.

## 3. Degree-94 equation: strong-root and triangular recovery

Here `Ds=Delta I²`, `Fs=1+Ds`, and `Q=Delta Ds` are literal
abbreviations. `Fs` is positive and zero or one modulo four. Since
`G=1 mod4`, `N=K²-G Fs` is zero, one or three modulo four, never `-2`.
The carrier exclusion and the unit product therefore give
`Acar=N=0` and auxiliary unit `1`. No unproved sign of the auxiliary
residual is needed. Independently, `Q=Delta²I²` is already a square,
which gives an alternative exclusion of auxiliary unit `-1`.

Apply the same lemma with `b=B-1`, `d=1`, `e=Fs`. Its `K` equals the
literal `s(s+1)-B-Ds`. It yields odd integral `g` and integral `f` with
`f²=Fs`; restoring `p3=(g-1)/2` gives all four parent residuals zero.
The old `Q,V` agree literally because the restored `f²` is the new
`Fs`. Conversely set `s=p3+f` at any old zero; the universal lift gives
the new norm zero. There is no extra existence assumption.

## 4. Exact artifacts and attained degree

The independent audit imports no builder or optimizer. It checks all
named cuts against separately stated arithmetic formulas, covers every
live operation, checks topology and the unrestricted-integer domain,
and verifies every declared variable and coefficient port is live.
It checks operation counts 64/22/26=112 for degree86 and
63/23/24=110 for degree94 (multiplication/addition/subtraction).

The six decompressed numerical payloads match their SHA-256 bindings and
sizes; the actual beta is checked to equal `2^1064921-1`. A recursive
comparison to the supplied lowdegree packet found 57 byte-identical files,
no changed inherited files, and only the separately disclosed leading-form
erratum note added. See `roots_baseline_comparison.json`.

The syntactic degree bounds are attained by independently propagated exact
homogeneous components. In addition to the author's n-dependent witnesses,
I checked the following different coefficients:

    [j^54 w^8 v^8 z^6 r² c^4 f^4] P86
        = -2^78 3^62 beta^54 !=0,

    [j^58 w^8 v^8 z^7 r^4 c^8 y] P94
        = 2^85 3^66 beta^58 !=0.

Their exponents sum to 86 and 94. The actual fixed beta is nonzero, so
these are not merely generic-coefficient degree estimates. The independent
checker also verifies the author's degree witnesses with one factor of n.

The two complete new DAG byte hashes reviewed are:

* 86/112: `e7f9e16bccb246359f38733c92e0e24c825a86917a0e46e36bae13e0e1bf18b5`.
* 94/110: `fd6fde764ce4e6fc45a95b4128b423b95ffa6082ffa16ffd726e5404e98b03a2`.

I also inspected the delivered independent `check.py`: its four-DAG checks
use separate algebraic cuts, complete leading propagation, exact old/new
unit-offset identities, and per-live-gate mutations. Its normal and optimized
receipts report all 453 arithmetic-gate corruptions rejected. Those controls
are transcription evidence, not proofs of the universal arithmetic theorem.

## 5. Previously disclosed leading-form erratum

The inherited `FREE_SCALE15_PROOF.md` omits `U0²R0²` when describing the
*complete* leading carrier form. Directly, `(Z+Uk)²` contributes that term;
the correct degree22 form is

    Acar22=U0²R0²+4U0L0Z0.

I independently noticed this while deriving a different coefficient and
reported it immediately. The author identified it as the already disclosed
upstream erratum and retained that attribution. The latest new proof prints
the corrected complete form and a dedicated erratum note. The old selected
n² coefficient and the author's new n-dependent witnesses remain correct,
since the omitted term is n-free. The new independent audit also explicitly
checks n-free witnesses, so it does not merely avoid the omitted summand.
This prose correction changes neither a polynomial nor a zero-set argument.

## Final boundary

The new universal root-merger and unit-product steps are fully justified,
including negative and zero auxiliary values and all potential `-1` factors.
The maps restore and lift actual parent zeros. Thus the inherited parent's
ordinary refutation-equivalence theorem transfers without strengthening its
assumptions. The supplied fixed DAGs, their arithmetic metrics, and their
new identities are independently checked. No full historical kernel closure,
consistency result, or global minimality conclusion is claimed.
