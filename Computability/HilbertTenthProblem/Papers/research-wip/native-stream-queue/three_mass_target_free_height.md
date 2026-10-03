# Target-free height for four unbounded three-mass clocks

The [complete source](three_mass_target_free_height.py) reduces the four [endpoint-projection polynomials](three_mass_unbounded_endpoint_projection.md) by **two additions**, with every comparison, parameter, witness and finalizer term retained. The complete totals become **592/467/465/468**. The helper emits exactly these four fixed-program forms; computation time remains existential and unbounded.

This is an all-value polynomial identity under a **signed slack substitution**, followed by a separate proof that the represented natural raw input/output/clock triples are unchanged. The substitution can make the parent slack negative. There is no asserted unconditional positive witness map or full natural-zero bijection, and no new ordinary universal input loader, numerical universal program or universal operation bound.

## 1. Actual circuits and cost

The free inputs `x,y,T` are natural, including zero. All existential coordinates are strictly positive. For the fixed state modulus `K=5`, initial code `q_i=1`, and halt code `q_h=3` for inc/dec or `q_h=2` otherwise, retain the already-paid endpoint formulas

\[
 n_0=Kx+q_i,\qquad n_f=Ky+(q_h-K).
\]

The endpoint parent computed

\[
 h_E=n_0+n_f+\eta_E+K+T
     =n_0+Ky+q_h+\eta_E+T.
\]

Its actual private height cone uses four additions:

```
h0 = n0 + nf
v = h0 + eta_E
w = v + K
h_E = w + T
```

The child uses the same supplied positive slack coordinate, now interpreted as `eta`, and computes

```
v = n0 + eta
h = v + T
```

Only `h0` and `w` disappear. The helper checks their literal definitions, the other two height definitions, all private consumers and absence of comparison uses. The target itself remains live in the transport equation. No new numeral multiplication, hidden target reconstruction, CSE or finalizer reduction is used.

| Fixed program | Endpoint parent | New M + A | New full total | Positive witnesses | Comparisons | Degree upper bound |
|---|---:|---:|---:|---:|---:|---:|
| inc2; dec2 | 594 | 235 + 357 | **592** | 58 | 19 | 2344 |
| zero3 | 469 | 180 + 287 | **467** | 56 | 19 | 1192 |
| nop | 467 | 178 + 287 | **465** | 56 | 19 | 1192 |
| positive3 | 470 | 185 + 283 | **468** | 56 | 19 | 1192 |

The certificate bodies cost 536/411/409/412. The full finalizer retains 19 comparison subtractions, 19 squares and 18 additions, costing56=19M+37A. All gates and supplied coordinates remain live. Degree is propagated through the actual complete DAG; **only upper bounds** are claimed.

## 2. Exact signed graph identity

For any supplied integer tuple, set

\[
 \eta_E=\eta-Ky-q_h,                                 \tag{1}
\]

and copy every other coordinate. Then the parent height becomes exactly

\[
 h=n_0+T+\eta.                                      \tag{2}
\]

Every retained downstream comparison operand agrees, so the complete outputs satisfy

\[
 F_{new}(x,y,T,\eta,\mathbf w)
 =F_E(x,y,T,\eta-Ky-q_h,\mathbf w).                  \tag{3}
\]

This polynomial identity holds on all values over any commutative ring. It is not a same-coordinate equality. The checker expands both actual height cones in the supplied variables, then uses their proved equality as one shared cut and verifies every retained comparison and the complete literal finalizer. Exact expression interning supplies the proof; numeric evaluations are supplemental.

Composing (1) with the endpoint predecessor's signed pullback gives `F=y` and `eta_coefficient=eta-n_f` in the older coefficient-transfer packet. These formulas are signed only. The current metadata explicitly archives the endpoint packet's old positive-slice statement as historical provenance; that statement does not describe the new packet.

For example, the actual nop trajectory at raw input40 has

```
x=40, y=41, T=7880,
n0=201, nf=202, h=8192, eta=111.
```

All genuine outer hats and slacks constructed at this height are positive; the three actual outer equations and complete joined AND hold. The pullbacks would have `eta_E=-96` and `eta_coefficient=-91`. This prevents treating the signed map as an unconditional positive restoration. The receipt checks these outer interfaces, not a materialized enormous native Pell zero. Positive native extensions exist by the inherited prescribed-AND theorem, as used in completeness below.

## 3. Direct soundness from height two

The new domain gives

\[
 h=n_0+T+\eta\ge2,\qquad 0<n_0<h,\qquad 0\le T<h.
\]

The target can initially be nonpositive, and it need not be below `h`. Neither assumption is needed for the following argument.

Use the unchanged definitions and constraints of the [unbounded clock interface](three_mass_unbounded_interface.md) and [residue-affine history](residue_affine_packed_history.md). Unhat the positive coordinates to obtain nonnegative selector words `E_s`, quotient word `W`, and selected quotient words `Z_a`. Put

\[
 J=\sum_sE_s,\quad B=C h^2,\quad P=(B-1)J+1,
\]

with the unchanged fixed dyadic multiplier

\[
 C\ge\max\{4,m+1,1+\max_s(a_s+d_s),2384m+2\}.
\]

All four emitted tables and their literal radix constants satisfy these inequalities. The retained global-bound equation is

\[
 J+\widehat W+\sum_a\widehat Z_a+\beta=P.
\]

If `J=0`, then `P=1`, whereas the positive quotient hat and global slack already sum to at least2. Hence `J>=1` and `P>=B`. The same equation bounds `W,Z_a,J<P` and `E_s,G_a<=J`. Also `(B-1)G_a<=P-1`, and the range mask `(h-1)J<P` because `B>h`. Thus every packed lane coefficient is nonnegative and below `P`; the joined words and the prescribed scale have their required positive padded interface. This uses only `h>=2`, not target positivity or the older convenient hypothesis `h>=3`.

The retained native equations now imply the joined bitwise AND and dyadic `B,P`. Since `C` is dyadic and `h` a positive integer, `B=C h²` forces `h` dyadic. From `B-1 | P-1` and `P>=B` follows

\[
 P=B^t,\qquad J=1+B+\cdots+B^{t-1},\qquad t\ge1.
\]

There is no zero-step branch. The selector lanes and selector sum force one residue per position. The range lane gives `0<=q_i<h`; the class lanes select exactly the appropriate quotient digits. Write the resulting current and next words as

\[
 C_w=\sum_{i<t}c_iB^i,\quad N_w=\sum_{i<t}n_iB^i,
 \quad c_i=mq_i+s_i,\quad n_i=a_{s_i}q_i+d_{s_i}.
\]

The fixed map has `a_s>=0,d_s>=1`. Therefore `1<=c_i,n_i<B`, using `c_i<=mh` and `n_i<=(a_s+d_s)h<B`. This estimate is valid already at `h=2`.

The unchanged transport equation

\[
 B N_w+n_0=C_w+B^t n_f                              \tag{4}
\]

then proves chronological execution without assuming any bound on `n_f`. Reduction modulo `B` gives `c_0=n_0`. Subtract and divide by `B`; the next `t-1` positions give `n_i=c_{i+1}`. The final integer equality is

\[
 n_f=n_{t-1}>0.                                     \tag{5}
\]

In particular `y=0`, which would give `n_f=q_h-K<=0`, is impossible. This is a consequence of the actual typed accepting chronology, not an extra domain restriction on the free input `y`.

Totalization sends halt and all rejecting cases to a trap, so an accepted trajectory ends at its first halt. Its deterministic current states cannot repeat, and all are at most `mh`; hence `t<=mh`. Each physical tick is at most `2384h`, so total time `L` satisfies

\[
 L\le2384mh^2<B-1,
 \quad B-1-2384mh^2\ge2h^2-1\ge7.                 \tag{6}
\]

The unchanged clock row gives `L congruent T (mod B-1)`. Since `0<=T<h<B-1`, (6) forces `L=T`. All ticks are positive; `T=0` is therefore rejected. This establishes soundness directly, without first mapping the child to a positive parent tuple.

## 4. Fresh-height completeness

Given an actual first-halt trajectory of one fixed listed program, let its raw input, positive final mass and exact physical time be `x,y,T`. Choose a dyadic `h` strictly larger than `n_0+T` and every current-state quotient. Set

\[
 \eta=h-n_0-T>0.
\]

Pack the genuine residue selectors, quotient digits and selected quotient digits with the unchanged radix `B=C h²`. Every current and next value fits a radix digit by the estimates in Section3, even though the target was omitted from the height formula. Chronological transport and every selection/range lane hold.

The exceptional slope classes are disjoint, so `sum Z_a<=W<=(h-1)J`. If there are `g<=m-1` such classes, the positive global slack obeys

\[
 \beta=(B-2)J-W-\sum_aZ_a-g
       \ge(B-2h)J-g
       \ge C h^2-2h-g>0.
\]

For `h>=2` and `C>=m+1`, the last expression is at least `4m-g>0`. The packed clock word minus the ordinary tick sum is a nonnegative multiple of `B-1`, so its quotient hat is positive. The prescribed-AND theorem supplies fresh positive native witnesses at the actual new scale. None of the negative signed slacks in (1) is used in this construction.

Thus for every natural `x,y,T`, positive child witnesses exist exactly when the same fixed source program started at mass `x+1` first halts at mass `y` after exactly `T` native physical ticks. This is the endpoint parent's represented relation. The proof makes an existence statement using freely chosen new heights, not a bijection between their complete positive zero tuples.

Raw input valuation/cofactor limitations remain those of the existing three-mass compiler. The paid exponential-input packets, their fixed constants, and any universal input-language theorem are separate frozen compositions; no automatic count update to them is asserted here.

## 5. Authentication and bounded verification

The source pins twelve predecessor files: the endpoint trio and the coefficient-transfer, unbounded-interface and packed-history trios. Every documented public API reauthenticates all twelve source/receipt/proof bytes. Historical Python is never imported or executed. `canonical_parent`, `build`, `rewrite`, `checked` and `polynomial_source` require exact canonical variant/packet types; `evaluate` and `integer_pullback` require exact integer assignments and exact complete coordinate keys. Default evaluation retains natural free parameters and strictly positive auxiliaries. Signed evaluation and pullback are algebraic interfaces. Returned packets, nested provenance, sources and assignments are defensive copies. There is no public positive restoration routine.

The [receipt](three_mass_target_free_height.json) contains all four full circuits and records its own helper hash. It proves four exact affine-height/full-DAG identities and76 retained comparisons; checks128 complete evaluations, including32 rational identities and2,432 residual comparisons; and validates96 public signed-map/evaluation cases. It constructs114 genuine finite outer histories, including the nop negative-slack example, and four explicit `h=2,y=0` pretyping cases. It checks252 literal constant/range/clock margins,256 malformed-call or pin rejections,40 defensive copies,84 warmed pin failures across all seven canonical entry points, and rejection of optimized Python. No native Pell tuple is materialized.

The separate [mathematical challenge](review_three_mass_target_free_height_math.md) independently checks the earlier frozen probe and general height argument, including its target-sign and small-height boundaries. Its PASS is a math/probe review, not a full review of this maintained successor's APIs. The maintained full-source audit is a separate checkpoint.

Standard-library reproduction from any directory, with the twelve pinned files under ROOT:

```sh
python /path/three_mass_target_free_height.py --root ROOT \
  --output /path/three_mass_target_free_height.json
python /path/three_mass_target_free_height.py --root ROOT \
  --expect /path/three_mass_target_free_height.json
```

With no `--root`, ROOT defaults to the helper's directory. Saved receipts are compared recursively with exact types. Finite checks supplement the general source and semantic proofs; they do not replace the positive native-extension theorem or supply a new universal machine table. All frozen predecessors remain unchanged.
