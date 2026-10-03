# Sparse content row for finite Grill word closure

This is a source-pinned alternative to the scaled [Grill word-closure compiler](grill_tag_word_closure.py). It keeps precisely the same positive coordinates and the same zeros on **every supplied integer tuple**, while replacing the full polynomial by a different polynomial with an exact correction. The complete schedule costs

\[
  11t+5-3z(t)=(5t+2-2z(t))M+(6t+3-z(t))A,
\]

where `z(t)` counts the phases with program exponent zero before the external horizon `t`. The parent costs `10t+7−z(t)`. Consequently this alternative saves `2+2z(t)−t` total operations; it is useful on sufficiently sparse phases and is not a uniform improvement. Both have `t+1` positive witnesses, `t+2` residuals and exact degree `2t+2`.

The [source](grill_tag_sparse_content.py) authenticates parent SHA256 `144129bb04e271588ed1c95d9c91f5682d30c6b5a540154c6c0b9b0c40331d96` before executing the bytes. The [receipt](grill_tag_sparse_content.json) contains complete representative sources, the cost comparisons, counterexamples and finite verification evidence. The original parent source is unchanged.

## 1. The exact row transformation

Fix a nonempty natural program tuple, extend it periodically, and fix `t>=1`. These are external schema parameters. The ordinary input `x`, initial slack `Z0` and shifted heads `D_i` are strictly positive integer coordinates. Put

\[
\begin{aligned}
 d_i&=D_i-1, & H_i&=4^{n_i}, & a_i&=2H_i-1,\\
 c_i&=\frac{2(H_i-1)}3, & P_0&=3x+Z_0,\\
 A_0&=P_0, & T_i&=d_iA_i, & A_{i+1}&=A_i+a_iT_i,\\
 B&=\sum_{i<t}2^id_i, & b_i&=d_i(d_i-1).
\end{aligned}
\]

The constants `c_i` are integers because `4^n≡1 mod 3`. They are zero exactly at exponent zero and are at least two otherwise. The original scaled source has width and content residuals

\[
 r=A_t-2^t,\qquad s=Z_0+\sum_{i<t}T_i+3B-2^t.
\]

Replace only the content residual by

\[
 W=\sum_{i<t}c_iT_i,\qquad e=B-x-W.
\]

Every statement in the following calculation is a polynomial identity, without Boolean, sign or zero assumptions. The recurrence telescopes to `A_t=P0+Σa_iT_i`, and `a_i−1=3c_i`, so

\[
\begin{aligned}
 s-r
 &=Z_0+\sum_iT_i+3B-A_t\\
 &=-3x+3B-\sum_i(a_i-1)T_i\\
 &=3e.
\end{aligned}
\]

Thus the old row is exactly `s=r+3e`. The two pairs of rows vanish simultaneously in both directions over the integers, indeed over any field of characteristic zero.

For Boolean heads, `c_i` is also the little-endian binary value of the appendant `0(10)^{n_i}`. The prefix scale `A_i` places that appendant after the initial word and preceding appendants. Thus `W=P0·val(G)` and `e=0` directly states `B=x+P0·val(G)`. This interpretation is explanatory; the all-value algebra above is sufficient for the transformation.

## 2. Complete finalizers, zero sets and correction

The main old and new polynomials are

\[
 F_{\rm old}=r^2+s^2+\sum_i b_i,\qquad
 F_{\rm new}=r^2+e^2+\sum_i b_i.
\]

For every integer `d`, the product `d(d−1)` is nonnegative, and its zeros are exactly `0,1`. Therefore either complete polynomial vanishes on an integer tuple if and only if its two squared rows vanish and all heads are Boolean. Substituting `s=r+3e` gives both implications

\[
 F_{\rm old}=0\quad\Longleftrightarrow\quad F_{\rm new}=0
\]

on **all integer assignments to the identical named coordinates**, with no positivity premise on those assignments. In particular, their positive zeros and all positive fibers over fixed `x` are identical; no coordinates are eliminated or reconstructed.

Their values away from zeros differ. The full correction is

\[
 F_{\rm old}-F_{\rm new}
 =(r+3e)^2-e^2
 =r^2+6re+8e^2.
\]

This identity holds on every assignment over the rationals or reals too. The optional `square_boolean=True` reference replaces each `b_i` by `b_i²` in both parents. The same correction remains exact, the integer zero relation is unchanged, and the reference additionally has the same old/new zero set over all real tuples. It costs `t` extra multiplications and has the same degree.

The unsquared zero-set theorem must retain its integer domain. For program `(0,)`, `t=1`, the positive rational tuple `x=1/2,Z0=1/6,D0=3/2` gives `F_new=0` and `F_old=1/4`. Conversely `x=1/3,Z0=1/3,D0=3/2` gives `F_old=0` and `F_new=−2/9`. The public evaluator rejects these fractional values. The previous positive-real false zero at program `(0,1,1)`, `t=3`, `x=Z0=1`, `d=(1,1/3333,0)` is also still a zero of the new polynomial; it is not a Boolean history.

## 3. Halting scope and degree remain unchanged

The exact positive-zero equality imports precisely the parent's word-closure semantics, including its limitations. At a positive zero, `P0` is a power of two and determines the padded little-endian input word `w`. The head word `h` equals `wG(h)`. The actual phase-controlled queue agrees with this word until it first empties, hence halts at some time at most `t`. Conversely an actual halt exactly at `t` gives a zero. At a fixed `t`, this is not an assertion that every earlier halt extends to a zero; only the union over external horizons gives the exact padded-input halting predicate.

Post-halt extensions remain. The unchanged positive witness

    program=(0,1,1), t=6, x=1, Z0=1,
    head word='100010', D=(2,1,1,1,2,1)

has `P0=4`, `A_t=64`, `B=17`, `W=16`, hence `r=e=0`. Its actual first halt is at time three. The formal causal width after step four is `1/2`, so this witness still does not lift to a positive-integer first-halt affine history. No initial padding or decoder condition has been relaxed.

For exact degree, write `A_t=P0∏_{i<t}(1+a_id_i)`. Each `a_i` is nonzero, so the width residual has exact degree `t+1`. The new content residual has degree at most `t+1`. The highest homogeneous part of `r²+e²` cannot vanish: it is a sum of real polynomial squares and the leading part of `r` is nonzero. Unsquared Boolean penalties have degree two, below `2t+2`; squared ones have degree four, which can only add further squares when `t=1`. Both finalizers therefore have exact formal degree `2t+2`.

This is still a finite external-horizon schema with `t+1` witnesses. Uniformly encoding phase products, the ordinary input decoder and the unbounded horizon remains unpaid. There is no new fixed-arity universal equation, no change to the global 87-operation bound and no bit-complexity claim. The underlying stop-at-first-empty argument is the parent's existing one, itself analogous to [binary-tag word closure](binary_tag_four_tile_history.md); the present change is the sparse algebraic content row.

## 4. Complete paid schedule

Let `N=t−z(t)` and `h=1` if `N>0`, otherwise `h=0`. Every emitted binary addition, subtraction and multiplication is charged, including runtime multiplications by fixed coefficients.

| Complete component | Multiplications | Additions/subtractions |
|---|---:|---:|
| Initial `P0=3x+Z0` | 1 | 1 |
| Shifted heads and Boolean factors | t | 2t |
| `T_i` and scaled-width recurrences | 2t−z | t |
| Weighted head word `B` | t−1 | t−1 |
| Nonzero content terms and their sum `W` | N | N−h |
| Width and new content residuals | 0 | 2+h |
| Two squares and summation with t Boolean penalties | 2 | t+1 |
| **Complete total** | **5t+2−2z** | **6t+3−z** |

The emitter removes the old unweighted accumulation and old content evaluation only after tracing the complete output's actual dependencies. When `N=0`, it emits `e=B−x` and no fictitious subtraction of zero. The reference squared-Boolean mode adds exactly `t` multiplications. The exact cost gain `2+2z−t` is positive iff `2z>t−2`.

| Program | Horizon | Parent M+A | Sparse M+A | Operations saved |
|---|---:|---:|---:|---:|
| `(0,)` | 1 | 6+10=16 | 5+8=13 | 3 |
| `(1,)` | 1 | 7+10=17 | 7+9=16 | 1 |
| `(0,1,1)` | 3 | 14+22=36 | 15+20=35 | 1 |
| `(0,1,1)` | 6 | 25+40=65 | 28+37=65 | 0 |
| `(0,)` | 6 | 21+40=61 | 20+33=53 | 8 |
| `(1,)` | 6 | 27+40=67 | 32+39=71 | −4 |

This is a literal emitted schedule, not a lower bound or an unrestricted circuit search.

## 5. Guarded interfaces and evidence

`build(program,horizon,*,square_boolean=False,root=None)` emits the sparse packet. `canonical_parent` emits the pinned scaled parent; `rewrite(parent_packet,*,root=None)` accepts only its exact complete canonical packet, rejecting direct-mode packets. `checked` validates every scalar type, source row, register, ledger and metadata field against a fresh canonical emission. All public builders return fresh structures; there is no shared mutable cache. `root` selects the parent directory, defaulting to the module's own directory. The parent file is reauthenticated on every relevant public call and executed directly from those bytes, without cached-bytecode loading.

`evaluate` accepts the complete named positive-integer assignment; explicit `signed=True` enables exact integer algebra checks. `correction` returns both outputs, the three residuals and their complete difference. `decode_zero` first validates a positive sparse zero, then delegates decoding of that same tuple to the pinned parent. It reports the actual first halt and any post-halt extension. The identity map on coordinates is the entire correspondence; there is no additional private lifting API.

The author checker passed 96 complete live-DAG ledgers and canonical parent rewrites across four programs, horizons 1–12 and both finalizers. It expanded 32 complete polynomials independently from closed products, proving 144 residual identities, all full corrections and exact degrees. It checked 384 signed complete corrections and 11,625 unfiltered signed integer tuples, including 12 zeros. A complete 4,088-head-word census recovered the same 101 positive zeros as the parent, including six post-halt examples, and decoded every one. It also checked two positive-real zero-set separations, 57 malformed-input rejections, four copy-isolation cases, a changed-parent-source rejection and both public correction cases. These finite checks support the general proofs above; they do not quantify all programs or horizons by enumeration.

Portable replay, with the pinned parent beside this source:

    python grill_tag_sparse_content.py \
      --expect grill_tag_sparse_content.json \
      --output /path/to/fresh-receipt.json

Alternatively supply `--root /path/to/parent-directory`. The receipt contains no absolute source paths or timing fields. The checker rejects optimized `python -O` execution. It modifies only an explicitly requested output and temporary private source copies used by its guard test.
