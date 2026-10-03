# A paid endpoint projection for four unbounded three-mass histories

The [complete source](three_mass_unbounded_endpoint_projection.py) removes the positive output alias from the four maintained mass-clock polynomials in [the first-coefficient transfer](native_pell_factored_first_coefficient.md). It saves **one multiplication and two additions**, removes one positive witness and one comparison, and preserves the represented natural input/output/clock relation of each fixed program. Computation time remains existential and unbounded.

This changes the height parameterization. The exact witness map is a bijection onto a specified slice of parent zeros, not all parent zeros. The arbitrary-height completeness theorem supplies the reverse existence statement for every represented triple. This packet does not supply a universal program, a new ordinary-input decoder, or an operation bound for arbitrary recursively enumerable sets.

## 1. Literal source and domains

Fix one of the four authenticated finite residue tables. Its state modulus is `K=5`, initial state code is `q_i=1`, and halt code is `q_h=3` for inc/dec or `q_h=2` for the other three. The proof below also applies to the parent construction with fixed `1<=q_i,q_h<=K` and `q_i!=q_h`; only the four listed numerical sources are emitted here.

The free parameters `x,y,T` remain natural integers, including zero. Every auxiliary remains strictly positive. The parent uses the positive auxiliary `F=final_positive`, with

\[
 n_0=Kx+q_i,\qquad n_f=K(F-1)+q_h,\qquad
 h_{old}=n_0+n_f+T+\eta_{old},\qquad F=y.
\]

The child removes `F` and its comparison. With positive `eta=height_slack` it computes

\[
 n_f=Ky+(q_h-K),\qquad
 h=n_0+n_f+T+\eta+K=n_0+Ky+q_h+T+\eta.                 \tag{1}
\]

Thus `y=0` is still a valid parameter assignment to the polynomial. It will be rejected by the remaining equations, not by the evaluator's domain checks. Formula (1) gives `h>=3`, `0<n_0<h` and `0<=T<h` before using any equation, even when `n_f<=0`.

The old endpoint cone uses `F-1`, multiplication by `K`, and addition of `q_h`. The new cone uses multiplication by `K` and addition of the fixed constant `q_h-K`. The saved addition pays the new height addition of `K`, so the certificate count is unchanged. Removing the final equality then removes its subtraction, square and final summation addition. Every remaining comparison and the complete native source are retained. Private-consumer checks prohibit the removed endpoint cone or height-slack input from having an unaccounted use.

| Fixed program | Parent full operations | Child M + A | Child full operations | Positive witnesses | Comparisons | Degree upper bound |
|---|---:|---:|---:|---:|---:|---:|
| inc2; dec2 | 597 | 235 + 359 | **594** | 58 | 19 | 2344 |
| zero3 | 472 | 180 + 289 | **469** | 56 | 19 | 1192 |
| nop | 470 | 178 + 289 | **467** | 56 | 19 | 1192 |
| positive3 | 473 | 185 + 285 | **470** | 56 | 19 | 1192 |

The child certificates still cost 538,413,411,414 operations respectively. All 19 squared residuals and their 18 final additions are paid. All emitted gates and supplied coordinates are live. The displayed degree bounds are propagated through the complete emitted source; they are not exact-degree claims.

## 2. Exact polynomial identity and the slice map

For every supplied integer tuple, including signed ones, define

\[
 F=y,\qquad \eta_{old}=\eta+K,                         \tag{2}
\]

leaving every other coordinate unchanged. The child target and height then equal the parent target and height identically. Every downstream register and all 19 retained comparison operands consequently agree. The twentieth parent residual is `F-y=0`. For the complete SOS outputs,

\[
 P_{child}(x,y,T,\eta,\mathbf w)
 =P_{parent}(x,y,T,F=y,\eta_{old}=\eta+K,\mathbf w).    \tag{3}
\]

This is an all-value polynomial identity, also valid over any commutative ring. It is not equality of two polynomials in unchanged supplied coordinates. The checker proves the two affine cuts by exact coefficients, then compares the full downstream DAG and SOS with a shared exact intern table; it does not infer identity from random tests or hashes.

Once Section 3 proves `y>=1` at every natural/positive child zero, (2) maps it to a valid parent zero. Conversely, a valid parent zero with `eta_old>K` has `F=y>=1`, and the inverse `eta=eta_old-K` is positive. Thus (2) is a bijection exactly between child zeros and the parent zero slice `eta_old>K`. No inverse is asserted on parent zeros with smaller height slack. The public `integer_pullback` reports (2) on signed tuples; it deliberately does not claim an unconditional map into positive parent coordinates.

## 3. Positivity bootstrap and the zero-output boundary

Use the actual outer equations and lane construction from [the unbounded interface](three_mass_unbounded_interface.md) and [the packed-history proof](residue_affine_packed_history.md). Unhatting the positive coordinates gives nonnegative residue-selector words `E_s`, quotient word `W`, and selected quotient words `Z_a`. Let

\[
 J=\sum_s E_s,\quad B=C h^2,\quad P=(B-1)J+1.
\]

Here `C` is the inherited fixed dyadic radix multiplier. The retained global-bound equation is

\[
 J+\widehat W+\sum_a\widehat Z_a+\beta=P.
\]

It forces `J>=1`: at `J=0`, `P=1`, while the positive quotient hat and positive global slack already sum to at least 2. Hence `P>=B`. It also bounds `W,Z_a,J<P`, `E_s,G_a<=J`. Since (1) gives positive `h`, all native padded ports, the range mask `(h-1)J`, and the prescribed scale `B P^v` are positive before any use of the native theorem. In particular, the change has not smuggled a negative endpoint into a required positive native port.

Exactly the original pretyping bounds therefore apply. The native theorem forces the joined AND lanes and dyadic `B,P`; because `B=C h^2` with positive integer `h`, `h` is dyadic. Divisibility `B-1 | P-1` then yields

\[
 P=B^t,\qquad J=1+B+\cdots+B^{t-1},\qquad t\ge1.
\]

The source thus **excludes zero-step histories**; there is no separate `t=0` branch. Selector lanes and their sum make exactly one residue active in each position. The range and class lanes supply actual digits `0<=q_i<h` and the correct selected products. Consequently the computed current and next words are

\[
 C_w=\sum_{i<t}c_iB^i,\quad N_w=\sum_{i<t}n_iB^i,
 \qquad 1\le c_i,n_i<B,
\]

with `c_i=mq_i+s_i`, `n_i=a_{s_i}q_i+d_{s_i}` from the fixed total positive map. These bounds use `h` and the inherited radix constant, not prior positivity of `n_f`.

The unchanged transport equation is

\[
 B N_w+n_0=C_w+B^t n_f.                              \tag{4}
\]

To avoid circular endpoint reasoning, treat `n_f` as an arbitrary integer in (4). Reduction modulo `B`, using `0<n_0<B` and `0<c_0<B`, gives `c_0=n_0`. Subtract these equal terms and divide by `B`. Repeating for the next `t-1` positions gives `n_i=c_{i+1}`. The final remaining integer equality is

\[
 n_f=n_{t-1}>0.                                      \tag{5}
\]

No initial range or positivity assumption on `n_f` was used. If `y=0`, (1) instead gives `n_f=q_h-K<=0`, contradicting (5). Thus every child zero has `y>=1`, and only now is the positive parent witness `F=y` restored. The actual source starts outside halt, and totalization sends halt to a rejecting trap, so this accepting trajectory ends at its first halt.

The physical clock is unchanged. Once chronology holds, the first-halt path is deterministic with no repeated numeric state. The inherited bound `n_i<=mh` gives `t<=mh`, individual tick bounds give total time `<B-1`, and (1) gives `T<h<B-1`. The retained clock congruence therefore forces the supplied `T` to equal the exact sum of ticks. All ticks are positive, so there is no accepted `T=0` endpoint shortcut.

## 4. Completeness and the represented relation

Given any accepting first-halt raw trajectory for a fixed listed program, let its natural input be `x`, positive final mass `y`, and exact physical time `T`. Choose a dyadic height strictly larger than

\[
 n_0+n_f+T+K
\]

and every trajectory quotient. Then `eta=h-n_0-n_f-T-K>0`. Pack its genuine residue selectors, quotient digits and selected products in the inherited `B=C h^2`. The original positive global-slack and clock-quotient constructions work unchanged. Their strict inequalities improve as the freely chosen height grows. The actual positive native extension theorem supplies fresh auxiliaries for the new prescribed scale. This proves child completeness; it does not reuse a parent native tuple whose scale was changed.

Together with Section 3, for every `x,y,T in N`, the child has positive auxiliary witnesses if and only if the corresponding fixed program, started at mass `x+1` and its initial control state, first halts with final mass `y` after exactly `T` native ticks. Equivalently, its represented triples equal the parent packet's. The source has no externally fixed runtime or history length.

The raw valuation/cofactor input convention of the parent is unchanged. Other paid exponent/ordinary-input bridges remain separate; none is silently included in the table above. Fixed-horizon selector and endpoint-mask projections are also separate. In particular, applying `s(s-1)` directly to a packed selector word would wrongly require that entire word to be Boolean: its valid values are position masks, not single-step bits. No such substitution is made here.

## 5. Reproduction and the limits of finite checks

The helper authenticates all nine source/proof/receipt predecessors listed in its `PINS` dictionary on every public entry, reads the current complete circuits from the pinned receipt, and executes no historical Python. Public construction accepts only the four declared variants. Packets, caller values and saved receipts use exact recursive type checks; returned metadata and circuits are defensive copies. `evaluate` retains natural free parameters and positive auxiliaries unless explicitly called for signed identity testing.

From any working directory, using the directory containing the pinned predecessors:

```sh
python /tmp/three_mass_unbounded_endpoint_projection.py \
  --root /home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue \
  --output /tmp/three_mass_unbounded_endpoint_projection.json
python /tmp/three_mass_unbounded_endpoint_projection.py \
  --root /home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue \
  --expect /tmp/three_mass_unbounded_endpoint_projection.json
```

Only the Python standard library is required. The receipt records its own checker source SHA256 and contains all four complete emitted circuits, interfaces, 19 comparisons, counted SOS finalizers and propagated upper degrees.

The author checks four formal whole-source pullback identities and 76 retained comparison identities; 128 complete evaluations, including 32 rational substitutions; 2,432 evaluated retained residual identities; 108 actual finite accepting outer histories; and 157,983 independently enumerated integer instances of the digit-cancellation lemma, including negative trial targets. Four zero-output cases explicitly verify positive computed height and nonpositive target without changing the public domain. It also records 121 rejected calls/pin failures, 24 defensive-copy checks and nine changed-file checks after an earlier successful call. The outer fixtures check all three actual outer comparisons and the complete joined AND, but **do not materialize native Pell witnesses**. The unbounded and positive-extension conclusions rest on the proofs above and the pinned predecessor theorems, not this finite census.
