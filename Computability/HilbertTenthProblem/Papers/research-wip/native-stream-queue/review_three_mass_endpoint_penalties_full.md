# Full-circuit review of three-mass endpoint penalties

**PASS; no source or mathematical correction requested.** The new complete
quadratic polynomials have exactly the parent's complete natural zero tuples.
The operation counts 56→51 for the two-step example, 107→100 for native
three-increment histories, and 105→98 for compact-clean histories are fully
paid. The horizon remains external and all `2Bh` natural witnesses remain.

This is a second, broader full-circuit audit, separate from
`review_three_mass_endpoint_penalties.md`. It is limited to the frozen endpoint
construction and its committed mass-coordinate parent; the subsequent mass
report publication `ef114b0bb` is not an input or a claim of this review.

Reviewed source SHA256:
`7010ab32c2ac44a84ea61f4393b826cdc1401c654f20364dbad7f694e3eb605c`.
Author receipt SHA256:
`10cbe0a62be35c03da5e9902e88c55b457c28b3c7295026fb6f33472dbdc82c8`.
The entire companion note, including its separate-review provenance addition,
was read at `36ad25a608c6f4e5abf3b800429b6f4c71c4df2ea2ad7b58f61c1685319560d2`.

## Proof and domain

For natural selectors `e_tj` and mass coordinates `v_tj`, every inactive term
`(E_t-e_tj)v_tj` is nonnegative on the entire natural orthant: `E_t-e_tj` is the
sum of the other selectors. This reasoning does not already assume one-hotness.
The new endpoint penalties are also nonnegative sums of selectors. At a new
zero, every remaining square and each such term must vanish; in particular the
retained `(E_t-1)^2` rows force exactly one selector to be one at every step.

On that one-hot tuple, vanishing initial and final forbidden-support sums says
exactly that the selected branches have the requested source and target states.
Distinct numerical state codes make these conditions equivalent to the two old
coded-state equations. Conversely, an old natural zero has those same selected
endpoints, so both new penalties vanish. All other terms and all supplied
coordinates are unchanged. This proves equality of the full natural zero sets
with identity maps, rather than a projection, a witness-count shortcut, or
merely an equality of accepted inputs.

This argument works for nonextremal state codes, multiple branches sharing a
source or target, false guards, and premature halting. It does not require a
control-code sign bound. At `h=0` the actual emitted polynomial is unchanged.
For `B=0,h>0`, the retained one-hot square is the constant one; both systems
have no zero. The compact-clean case retains the old compact zero tuples and
therefore its previously proved lift to full cleaned certificates; no stronger
off-zero lift is asserted.

The exact all-value correction is

`F_new - F_old = K_initial + K_halt - C_initial^2 - C_halt^2`.

It is not an off-zero polynomial equality. The supplied complete signed example
has `F_new=0,F_old=4` with negative selectors and otherwise natural coordinates.
I independently reproduced it from the full coefficients and literal circuits.
The nonnegative rational example is correctly labelled a local endpoint
counterexample, not a complete rational false zero. Natural integrality is
essential to the one-hot argument. The warning about composing an implicit
last-selector projection is necessary: a substituted forbidden-selector
penalty can become negative away from the zero set.

## Independent source and paid-count checks

The helper pins the candidate, its saved receipt, and committed parent
`c5b680b90f74a792c713d5213d97a06c2b582590` with source hash
`d5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0`.
It uses the parent's already reviewed authenticated archive loader/context only
to load the two original producers. Their exact executable hashes are recorded
and checked again before use. No candidate endpoint, sparse-polynomial,
coefficient-expansion, or source-signature helper supplies the independent proof.

I independently rebuild all 40 author certificates and compare the certificate
hashes. Additional bounded fixtures cover every primitive with both prime
counters and both endpoint interfaces under paid clock scaling, plus empty
nonhalted machines at horizons zero and one: **64 actual certificates** in all.
For each, both direct and factored inactive schedules are emitted in baseline
and endpoint modes.

A separate coefficient algebra substitutes `u=v-e` in every literal original
row. It reconstructs both endpoint code forms directly from the actual ordered
state list and branch table, builds the forbidden-state masks, and checks every
one-hot and inactive row. It then expands every emitted gate and proves the
complete correction coefficient by coefficient. The 128 baseline schedules are
also literally identical to the committed parent's source, output and ledger,
so the comparison uses the same constant folding, sharing and gate metric.

All **10,702 paid gates** across these 256 complete old/new circuits are live.
The helper independently recounts every addition, subtraction and multiplication,
checks coordinate and port metadata, every retained affine residual and every
inactive group, and verifies the paid `N0=x+1` loader. The complete polynomial
has degree exactly two: its `T^2` coefficient is one, also at zero horizon.
No nonzero-leading-coefficient conclusion is inferred merely from samples.

The headline ledgers and all saved full sources match. Savings are compared
using the best of the two actually emitted schedules on each side, not a claimed
global arithmetic optimum. A removed square may coincide with another retained
square in the shared circuit, which explains why the zero-test example saves
only one addition. There is no universal savings formula depending solely on
`B,h`.

The independent receipt also records 1,024 complete signed correction evaluations,
184 all-branch one-hot endpoint cases, 136 actual complete natural-zero fixtures,
120 source guard/horizon rejections, 768 complete natural tuples in a two-step
box, the full signed counterexample, the exact local rational boundary, and
11 invalid-mode/unsupported-interface rejections. The author default saved
receipt replay passed separately. These bounded checks supplement the proof
and full symbolic identities; they do not prove universality or replace a
transfinite/unbounded-history representation.

## Reproduce and scope

```sh
python3 review_three_mass_endpoint_penalties_full.py \
  --source /path/to/three_mass_endpoint_penalties.py \
  --receipt /path/to/three_mass_endpoint_penalties.json \
  --repo /path/to/Proofs \
  --expect review_three_mass_endpoint_penalties_full.json
```

The helper uses standard-library Python and read-only Git. It has no fixed
scratch-directory dependency. `--output` writes a new review receipt; `--expect`
compares the saved receipt recursively with exact types. Fresh replay passed.
No repository edits, Git mutations, historical author-suite reruns or source
report revisions were performed.

The emitter is explicitly a research compiler for fresh authenticated producer
certificates with `x,y,T` or `x,T` interfaces. It is not advertised as a hostile
arbitrary-packet validator or a strict natural-number evaluator; the supplied
source and domain restrictions remain part of its theorem contract. The paid
input is the raw value `x+1`. A fixed universal branch table, a complete ordinary
counter encoding and a fixed-arity unbounded-history representation remain
separate obligations. This reduction does not improve the universal 87-operation
bound.
