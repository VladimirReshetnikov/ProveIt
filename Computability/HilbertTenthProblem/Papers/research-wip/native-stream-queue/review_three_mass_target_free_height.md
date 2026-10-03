# Independent maintained-source review: target-free mass height

**PASS. No source, proof or API correction is requested.** This review covers all four complete maintained circuits in [the target-free-height packet](three_mass_target_free_height.md), including their full finalizers, precise domains, literal predecessor maps, degree bounds and public authentication. It is independent of the earlier probe-only mathematical review and does not import that probe.

The reviewed author hashes are:

| File | SHA256 |
|---|---|
| `three_mass_target_free_height.py` | `7df5a60888976b55599014406c9b325a86428da6603f527b8a6fb35cff783d49` |
| `three_mass_target_free_height.json` | `a263e7423cdc57b8fceb66ef9021be843c8a9c69a7f897ee4d3e38eac2488830` |
| `three_mass_target_free_height.md` | `61c207bf1d50729667fe2ea9dd94c49f66e2d4a848a0d6d12968e9dfd9f01e7a` |

The [independent checker](review_three_mass_target_free_height.py) pins these three files and all twelve predecessors itself. The manifest is reproduced in its [receipt](review_three_mass_target_free_height.json). It loads authenticated author source bytes solely to test public APIs; it never calls the author's verification, proof, ledger or fixture routines. No historical Python or historical suite runs. Independent ring-expression, ledger, numeric-execution and source-macro helpers are copied from this reviewer's earlier endpoint audit, with the changed height and maps independently reconstructed here. That earlier checker is not a runtime dependency.

## Literal complete sources

The actual endpoint parent has four additions in its private height cone. The child deletes precisely the endpoint sum and the added `K`, then computes `h=n0+eta+T` with two additions. Consumer and comparison scans confirm privacy of the changed intermediate ports. The target still appears in chronological transport; it is neither erased nor supplied for free.

Every one of the 19 comparisons is retained in order. The independent reconstruction emits the full 19 subtractions, 19 squares and 18 final additions literally, checking that they are exactly the parent finalizer. All gates and all supplied coordinates are live.

| Variant | Full M | Full A | Full operations | Positive auxiliaries | Comparisons | Degree upper bound |
|---|---:|---:|---:|---:|---:|---:|
| `clock_incdec` | 235 | 357 | 592 | 58 | 19 | 2344 |
| `clock_zero3` | 180 | 287 | 467 | 56 | 19 | 1192 |
| `clock_nop` | 178 | 287 | 465 | 56 | 19 | 1192 |
| `clock_positive3` | 185 | 283 | 468 | 56 | 19 | 1192 |

The certificate bodies cost 536, 411, 409 and 412. Each full finalizer costs 56 operations, including every fixed-coefficient use elsewhere in the body. The reduction is exactly two additions in each complete source. All four reported degrees are independently propagated **upper bounds**; neither this review nor the author claims they are exact.

## Full signed graph identities and their domain limit

For the actual fixed `K=5` and halt code `qh`, the child-to-endpoint substitution is

\[
 \eta_E=\eta-Ky-q_h.
\]

Independent normalization of the entire expression DAG proves

\[
 F_{new}(x,y,T,\eta,\mathbf w)
 =F_E(x,y,T,\eta-Ky-q_h,\mathbf w)
\]

over integers, rationals and any commutative ring. This direct proof normalizes the actual affine height expressions and all subsequent products and sums; it accepts no author-supplied height cut as a premise. All 152 retained comparison operands and all 76 residuals across the four sources agree.

The checker also proves the four entire composed identities against the earlier coefficient-transfer sources, with `F=y` and `eta_coefficient=eta-nf`. Thus the current signed map and its historical lineage have both been checked against actual complete polynomials.

These identities are not same-coordinate equality or positive restoration of child tuples. On the genuine nop trajectory

\[
 (x,y,T,h,\eta)=(40,41,7880,8192,111),
\]

the endpoint-parent slack is `-96` and the coefficient-parent slack is `-91`. The independent fixture constructs all outer hats and slacks, checks their positivity, all three literal outer equations, and the complete joined AND. It does not materialize the native Pell tower. The prescribed native-extension theorem supplies those witnesses, as in the general completeness proof.

There is a useful one-way distinction: the inverse affine formula `eta=eta_E+Ky+qh` does embed natural/positive endpoint-parent tuples into the child domain, and takes their zeros to child zeros. This corroborates completeness but does not give a positive map from every child zero back to the parent or a zero-tuple bijection. The current metadata correctly marks the child pullback as signed, denies a full natural-zero bijection claim, and archives the former positive-slice map as historical provenance only.

## Direct soundness, including height two

The actual source gives `n0=Kx+qi`, `nf=Ky+qh-K` and

\[
 h=n_0+T+\eta\ge2,\qquad 0<n_0<h,\qquad 0\le T<h.
\]

The proof must not assume `nf>0` or `nf<h`. Neither is needed. Unhatting the strictly positive auxiliaries produces nonnegative selector and quotient words. The retained global equation excludes `J=0`, since `P=1` would contradict the positive quotient hat plus positive global slack. It follows that `J>=1`, `P>=B`, and all native lane coefficients satisfy the original pretyping bounds. The range mask `(h-1)J<P` remains valid at `h=2`. The literal padded native ports are positive before native typing, without using the target sign.

The inherited prescribed-AND theorem then types the scale, selectors, quotient digits and selected products. The actual dyadic constant in `B=C*h^2`, checked in each source, makes both current and next digits lie strictly between zero and `B`, already at height two. The scale equation yields `P=B^t` with `t>=1`, excluding zero-step histories.

In

\[
 B\sum_{i<t}n_iB^i+n_0
 =\sum_{i<t}c_iB^i+B^t n_f,
\]

treat `nf` as an unrestricted integer. Reduction modulo `B` forces `c0=n0`; subtracting and dividing repeatedly forces `n_i=c_{i+1}` and finally `nf=n_{t-1}>0`. Thus `y=0` is rejected by chronology, not by an undocumented input-domain restriction. The checker explicitly evaluates all four `h=2,y=0` boundary tuples through the public natural evaluator.

The actual finite residue/clock tables agree with independently reconstructed source macros, including rejection traps. An accepted trajectory reaches its first halt, and its current numeric states cannot repeat. They are bounded by `mh`, so `t<=mh`; no bound on the terminal state by `h` is needed for this count. Each tick is at most `2384h`. The actual radix satisfies

\[
 B-1-2384mh^2\ge2h^2-1\ge7.
\]

Consequently total time and the supplied `T` both lie in the clock congruence's canonical range, which forces equality. Positive ticks and `t>=1` exclude `T=0` at zeros. This proves soundness directly; applying a positive parent theorem to the signed pullback would have been invalid.

For completeness, the author's fresh-height construction is sound: choose dyadic `h>n0+T` and larger than every actual path quotient, set `eta=h-n0-T`, and repack at the new radix. Next digits fit by the slope bound even without a target contribution to the height. Disjoint slope classes give the positive global-slack estimate `(B-2h)J-g>0`, valid at `h>=2`; the clock quotient hat is positive. The native theorem supplies fresh positive witnesses at this prescribed scale. This proves equality of represented raw triples without asserting equality of their full witness fibers.

The domain remains natural `x,y,T` and strictly positive auxiliaries for four fixed illustrative programs. Runtime is existential and unbounded. Raw input valuation/cofactor qualifications persist. No exponent bridge, ordinary universal input decoder, universal machine table or new universal operation bound is included in these counts.

## Bounded evidence and reproduction

The independent receipt records four complete literal reconstructions, eight entire graph identities against the two predecessor levels, 152 operand identities, 76 residual identities, all 1,992 paid live gates and four upper-degree checks. It also records 80 exact full evaluations, including 16 rational substitutions, and 1,520 evaluated residual identities.

Independent source-macro checks cover 360 literal map/clock evaluations. Fifty-seven genuine outer histories include the negative-slack nop case. Four `h=2` cases and 128 small-height digit/slack/clock margin checks supplement the general proof. These fixtures do not construct huge native witnesses and are not substitutes for the inherited native theorem.

All seven documented public entry points are exercised. Exact packet/types, signed flags, every positive auxiliary's zero boundary, all three natural inputs' negative boundary, source/finalizer corruption, false degree and map metadata, and defensive copies are checked. There are 230 rejected malformed calls, including all 84 combinations of twelve changed predecessor files and seven public entries after warm successful calls; 20 defensive-copy checks; and rejection under optimized Python.

Only the Python standard library is needed. Both initial generation and a fresh exact typed replay from `/` pass:

```sh
python /tmp/review_three_mass_target_free_height.py \
  --root /home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue \
  --artifacts /tmp \
  --expect /tmp/review_three_mass_target_free_height.json
```

`--root` contains the twelve pinned predecessors; `--artifacts` contains the current author trio. They may be the same installation directory. Filesystem paths do not enter the saved receipt. No repository or frozen predecessor was modified.
