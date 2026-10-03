# Independent bounded review of one-step height specialization

**PASS, with no requested correction.** This review covers the three complete illustrative circuits in [the one-step packet](three_mass_one_step_height.md). It preserves the author's bounded source/proof scope; it is not an exhaustive maintained-API audit or a new unbounded-computation result. Inc/dec is explicitly excluded.

Author files are pinned at:

| File | SHA256 |
|---|---|
| `three_mass_one_step_height.py` | `a4420e122bf9134362aa08026237c3d411b9c1f72996477e1665fd8c7c983271` |
| `three_mass_one_step_height.json` | `60019db77c7045f4e34dd8bcd335965d943cc4f475e5c0f53b8236771179a258` |
| `three_mass_one_step_height.md` | `13640b9c38960d3c7d74e7d9e5ca916d6965ae792ec7b9dc079a37f0baa480d0` |

The [independent checker](review_three_mass_one_step_height.py) authenticates that trio and all fifteen predecessor files itself. Full pins appear in the [receipt](review_three_mass_one_step_height.json). It does not call the author's verifier, local proof, clock expansion, ledger or outer-fixture routines. It loads only authenticated current source bytes for bounded canonical construction and interface checks. No historical Python, historical suite or native Pell tower is executed. Independent expression, counting, macro and outer-fixture utilities are copied from this reviewer's preceding mass audits; those helpers are not runtime imports or additional dependencies.

## Literal arithmetic and complete count

The independent reconstruction checks the actual private two-addition height cone, deletes its intermediate, and writes `h=n0+eta`. Every comparison and every subsequent subtraction, square and final sum is retained literally. All 1,397 gates across the three complete child polynomials and all supplied coordinates are live.

| Source | Full M | Full A | Full operations | Positive witnesses | Comparisons | Degree upper bound |
|---|---:|---:|---:|---:|---:|---:|
| zero3 | 180 | 286 | 466 | 56 | 19 | 1192 |
| nop | 178 | 286 | 464 | 56 | 19 | 1192 |
| positive3 | 185 | 282 | 467 | 56 | 19 | 1192 |

The certificate bodies cost 410/408/411; each SOS finalizer costs 19M+37A=56. Thus exactly one addition is saved per source. All reported degrees remain **upper bounds**, not exact-degree claims. The clock quotient coordinate and its three private arithmetic gates remain present and paid.

Direct ring-expression normalization proves the complete identities

\[
 F_{child}(x,y,T,\eta,\mathbf w)
 =F_{parent}(x,y,T,\eta-T,\mathbf w).
\]

No author-supplied height cut is assumed: the actual expressions are normalized before the entire downstream polynomial is compared. All 114 retained comparison operands match. For natural inputs and positive parent witnesses, `eta_child=eta_parent+T` is an unconditional positive embedding and preserves the full output. The signed child-to-parent map can leave the positive domain, so no full positive-zero bijection is inferred.

## The actual one-step premise and the clock proof

I independently reconstruct every one of the 90 literal map/clock rows from unchanged-payload macro semantics. Writing `r-1=5b+s-1`, the current control is `s`, the payload is `6q+b+1`, and the map is

\[
 n'=30q+5b+s',\qquad \tau=1152q+192(b+1)+8.
\]

An initial control either halts or traps, according to the nop/zero3/positive3 condition. Every noninitial control traps. The slope 30 is divisible by the control modulus 5, so this conclusion is independent of `q`. Once native typing and transport have recovered a nonempty chronology, ending at halt therefore forces exactly one transition; no longer path can leave the trap and return to halt.

The inherited pretyping argument needs `h>=2` and `n0<h`, but no `T<h` until its final clock step. Both still hold for `h=n0+eta`. The positive global bound excludes `J=0`, the native constraints type the scale and selector/range lanes, and radix cancellation proves the chronological path and a positive target without presupposing either target positivity or a target bound. Consequently `t>=1` and `y>=1` hold before the one-step control argument is applied.

The checker independently expands the **actual paid clock left side** in the quotient and all edge hats. Its coefficients give precisely

\[
 1152W+\sum_r\bigl(200+192\lfloor(r-1)/5\rfloor\bigr)E_r.
\]

The literal right side is also checked, including the exact `B-1` and positive clock-quotient hat. At `t=1`, the left side is a single positive tick `L`, with

\[
 L\le1152(h-1)+1160=1152h+8<131072h^2-1=B-1
 \quad(h\ge2).
\]

Because

\[
 L=(B-1)(\widehat Q-1)+T,
\]

with `Qhat>=1` and natural `T`, the hat must be 1 and `T=L`. This proves exact clock soundness without requiring `T<h`. Positive ticks reject `T=0` at zeros. The unconditional positive parent embedding proves completeness at the same height and native tuple.

The actual nop fixture `x=0,y=1,T=200,h=2,eta=1` has signed parent slack `-199`. All genuine outer hats/slacks, the three outer equations and the joined AND are checked independently. Positive native witnesses exist by the inherited extension theorem; they are not materialized. The fixture correctly illustrates failure of positive restoration, not failure of the represented relation.

These three relations are exactly `y=x+1`, `T=192(x+1)+8`, with respectively a nondivisibility-by-three guard, no guard, or a divisibility-by-three guard on `x+1`. They do not advance an unbounded universal substrate. In contrast, the separately reviewed two-step inc/dec clock permits a false-time shift when time is removed from the height. Nothing in this review generalizes the one-step argument to it.

## Evidence and replay

The receipt records three complete literal reconstructions, three whole graph identities, 114 operand identities, all 1,397 live gates, 90 independently reconstructed residue rows and three full clock-expression expansions. It adds 48 exact whole-polynomial evaluations, including 12 rational cases; 12 positive parent embeddings; 38 genuine outer histories; 96 height-margin checks; and four explicit inc/dec rejections through construction, parent selection, rewriting and packet checking.

These are bounded checks of the frozen probe and its declared source/proof scope. They are not a broad malformed-packet, warm-cache or copy-API audit. The general domain argument and pinned native theorem establish the represented-relation result; finite fixtures alone do not.

Only Python's standard library is required. Initial generation and a fresh exact typed replay from `/` pass:

```sh
python /tmp/review_three_mass_one_step_height.py \
  --root /home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue \
  --artifacts /tmp \
  --expect /tmp/review_three_mass_one_step_height.json
```

The fifteen predecessors belong under `--root`, and the author trio under `--artifacts`; both may be the same installation directory. No repository or frozen predecessor was modified.
