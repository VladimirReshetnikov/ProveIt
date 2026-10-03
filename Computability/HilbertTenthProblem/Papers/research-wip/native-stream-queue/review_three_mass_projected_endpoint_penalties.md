# Independent review of safely composed selector and endpoint penalties

PASS, with no requested change, for `three_mass_projected_endpoint_penalties.py` SHA256 `f5fec893112b011564620834e0b76095c1ea53b9545d4fb76ccabb3230bdaaf6` and author receipt `998d4852eeefd18d9c5d3aa8a3b82e6af31d5d6b9cc0f0817a1715cf1c24f768`. I read the entire final source and companion note and independently checked every emitted candidate's complete polynomial, degree, and paid operation count. The natural proof below is general; the executable examples remain bounded.

The two authenticated parent sources are selector projection `8129ec4da0aded05c98993b7575eb3ccfe42ee908c5d15c18a748a8b53d874b8` and standalone endpoint penalties `7010ab32c2ac44a84ea61f4393b826cdc1401c654f20364dbad7f694e3eb605c`. Both ultimately use the reviewed mass emitter `d5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0` and its pinned original producers.

## Proof of the grouped natural zero condition

At a step with omitted branch k, let `S=sum_(j!=k)e_j` and restore `e_k=1-S`. For each selected endpoint constraint, its forbidden-branch penalty after restoration has one of two forms:

- If branch k is allowed, it is a sum of explicit natural selectors, hence nonnegative.
- If branch k is forbidden, it is `1-A`, where A is the sum of explicit selectors whose branches are allowed. Since `0<=A<=S`, it is at least `1-S`.

Let r be the number of attached penalties of the second kind. There are at most two endpoint masks. Use barrier weight w=1 for r=0 or1, and w=2 for r=2. With the weighted guard

`G_w = w S(S-1) + sum_(j!=k)(1-e_j)^2 v_j + S v_k`,

the complete grouped expression at S>=2 is bounded below by

`(S-1)(w S-r)>0`.

This strict inequality excludes invalid implicit selectors without assuming a legal run, a true guard, or any mass/value relation. At S=0 or1, all selectors including the restored one are natural and one-hot. Every attached mask is then a nonnegative forbidden-selection indicator, and every mass term is nonnegative. Thus the grouped expression is zero precisely for the old one-hot/inactive-mass condition and all attached endpoint conditions.

The initial and terminal masks attach to distinct steps when h>=2; only h=1 can give r=2. The emitter identifies r by the actual forbidden-branch mask's coefficient on that step's omitted selector, rather than by assuming anything about numerical state-code order. All other steps keep w=1. Each weighted guard plus its own endpoint masks is nonnegative independently; consequently grouping the full final sum by step is legitimate even though individual substituted endpoint penalties can be negative away from zero.

Every remaining affine square is nonnegative. A new complete natural zero therefore has natural restored selectors, all original internal rows, and both original endpoint predicates. It is exactly a zero of the projected parent in the same supplied coordinates; restoring the omitted selectors gives the unique corresponding mass-parent zero. The existing mass-coordinate theorem then restores natural original offsets `u=v-e`. Conversely every projected-parent natural zero makes the new masks and additional barriers vanish. This establishes equality of complete natural zero sets with the projected parent and a bijection to the mass-parent zero fibers. It does not supply a natural inverse on arbitrary nonzero tuples.

For B=1, S and the guard vanish identically; a forbidden omitted branch gives a constant positive endpoint penalty. For B=0 at positive horizon, the retained one-hot constant-one square prevents acceptance. At h=0, no endpoint is replaced and no selector is projected. These cases are both covered by the source and consistent with the theorem.

## Exact all-value relation and the necessary one-step repair

Let H be the projected parent and rho its omitted-selector restoration. If A is the chosen endpoint subset, the full emitted polynomial is

`H_new = H - sum_(a in A)(C_a o rho)^2 + sum_(a in A)K_a o rho + sum_t(w_t-1)S_t(S_t-1)`.

My checker reconstructs this formal coefficient identity independently from the original certificate rows and actual branch labels, including every retained input/value/control/time/output row. The relation is an equality of polynomials with a displayed correction, not a same-polynomial or unrestricted integer-zero claim. Combined with the previously reviewed selector correction, it gives the full relation back to the mass parent.

The actual false-zero fixture is correct. The source has prime-three zero-test branches `s -> h` and an unreachable `z -> z` no-op. At horizon one omit the no-op selector and supply

`x=2, e_0_0=e_0_1=1, v_0_0=v_0_1=1, v_0_2=0, y=3, T=584`.

Then S=2 and the reconstructed omitted selector is -1. The two projected endpoint masks each equal -1. Every value/time/output square vanishes; the old two endpoint squares contribute five and the original guard contributes two. Hence the unchanged projected parent is seven, naïve endpoint replacement gives zero, and adding the second barrier gives the correct safe value two. I independently evaluated those full coefficient polynomials, not only the local gate. The raw initial value is three, which fails the source's prime-three zero condition, so the unguarded construction would indeed accept an impossible one-step halt.

## Complete source and paid arithmetic

The independent audit covers all 783 candidate forms across 39 actual native/compact-clean certificates and all 261 corresponding baseline forms. For every candidate it expands the complete DAG into sparse integer coefficients, compares the full polynomial correction, checks each retained residual, each entire weighted guard and the full endpoint-mask port, and independently computes degree and operation counts. Exact integer constants, topological closure, fresh registers, live source nodes, the paid `N0=x+1` loader, and unchanged witness-coordinate lists are checked.

For the no-endpoint mode, the full source rows, output and ledger match the actual projected parent literally. The baseline and child compare the same uniform omitted-branch choices and direct/factored/Horner schedules; the child additionally considers initial, terminal, or both endpoint replacements. Reported minima are only over this finite emitted family. No baseline intermediates are supplied for free to the candidate. Nonunit constants, barrier doubling, affine projections, all squares and final additions are counted.

| Actual fixed-horizon source | Projected parent | Safe child | Witnesses |
|---|---:|---:|---:|
| INC2;DEC2, h=2, native y,T |47|17M+29A=46|6|
| INC2;DEC2, h=2, compact-clean T |46|18M+27A=45|6|
| Three INC2, h=3, native y,T |91|26M+60A=86|15|
| Three INC2, h=3, compact-clean T |88|26M+57A=83|15|
| Prime-three zero test, h=1, native y,T |24|9M+15A=24|3|
| Empty already-halted source, h=0, compact-clean T |5|2M+3A=5|0|

For B>=2 and positive h, some `e_j^2 v_j` survives with coefficient one. Every other added or removed term has degree at most two, so the degree remains exactly three. In the other supported endpoint-bearing cases, the unchanged `T^2` term gives degree exactly two. All 783 candidate degrees were explicitly checked by the independent engine.

## Reproducible independent checks and scope

The independent receipt records:

- 783 complete candidate coefficient identities and exact degrees; 4,323 retained residuals; 1,575 weighted step guards; 56,077 live paid candidate gates.
- 261 literal parent-baseline checks with complete polynomial validation.
- 36 further full identities with alternating per-step omitted selectors and scaled native/compact-clean clocks.
- 14,216 local natural cases covering every omitted position and all pairs of forbidden-support masks for B=1,...,3.
- 2,889 complete natural supplied tuples with actual affine endpoints, including six zeros; all lift to natural original offsets and a zero projected parent.
- Six malformed endpoint-option rejections and the exact complete one-step counterexample above.

The general proof does not depend on these finite bounds. I did not rerun original author suites or the author's larger mask census. The helper uses its own already frozen coefficient/fixture utilities from `review_three_mass_selector_projection.py` (SHA256 `c519ac0693e4928b64a1fead9ab30212570d50eb63331cf3706d335f20906321`), without calling either candidate's `expected` or `verify` routines or the author's polynomial evaluator. It authenticates every executable source before compiling its bytes, obtains original producer fixtures through the authenticated parent loader, and compares saved review receipts with exact types. Fresh replay passed.

```sh
python review_three_mass_projected_endpoint_penalties.py \
  --source three_mass_projected_endpoint_penalties.py \
  --receipt three_mass_projected_endpoint_penalties.json \
  --projection-review review_three_mass_selector_projection.py \
  --dependencies /path/to/pinned/helpers \
  --parent-root /path/to/native-stream-queue --repo /path/to/Proofs \
  --output /tmp/projected-endpoint-review.json \
  --expect review_three_mass_projected_endpoint_penalties.json
```

The public scope remains the inherited research-emitter contract for freshly generated authenticated certificates and fixed x/y/T or x/T interfaces, not hostile arbitrary packet validation. This is an external-horizon raw-input certificate reduction. It supplies no unbounded-history packing, ordinary-counter decoder, universal fixed table, fixed-arity universal equation, or improvement to the universal-polynomial operation bound. The companion note separates the degree-two endpoint-only tradeoff and states these limits accurately. No repository or Git mutation occurred during this review.
