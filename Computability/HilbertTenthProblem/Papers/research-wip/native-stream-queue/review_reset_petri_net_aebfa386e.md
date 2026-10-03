# Reset Petri net certificates: full mathematical and source review

The valid-natural-domain mathematics and all fourteen author entrypoints pass review. Two malformed-input API defects are reproducible and repaired by the accompanying narrow patch. The literal nets are fixed universal substrates; their explicit Diophantine certificates have externally chosen horizons and growing arity. They do not improve the fixed-arity universal-operation record.

## Scope and provenance

Archive `docs/incoming/Reset_Petri_Net_Certificates.zip`, arrival `ef2fc7990` / intake `aebfa386e`, SHA-256 **`b1efbc90aac106061e93ffc92adda686b8e1b9f57539aae976bf227dffec83e3`**. All 84 member byte hashes are embedded in the portable companion checker. The archive is unchanged. All substantive Python files, the complete 869-line article, both source-macro proofs, README, validation and provenance were read before execution. All author commands ran in a private extraction; every original member remained byte-identical. The PDF build was not repeated because the article source and arithmetic exports, not typography, are the subject of this review.

The source machine is the 29-rule U15,2 table. I retrieved the [Neary–Woods primary PDF](https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf), SHA-256 `6274cb6828579c234bf9f62b8fecc64dea4bb1ae842b4e2e39b9bfc676114c1b`, and visually inspected Table 16 on PDF page 17. With states A–O corresponding to u1–u15 and 0/1 to c/b, its missing entry is J1. Later prose says u10 reading c has no transition, a source inconsistency; the report correctly follows the printed table, whose J0 rule is present. This does not justify changing the halting cell to J0. The source’s finite blank-tail universality is the imported universality premise; the report supplies the literal register simulation and net reduction.

The credit for budget-controlled reset simulation is appropriate: [Blondin et al., Proposition 3.2](https://michaelblondin.com/papers/BFHMO24.pdf) explicitly uses budgets and irreversible loss from dishonest resets. The report's pooled debt invariant is independently checked below. The one-reset-place obstruction relies on an explicit reduction to one inhibitor arc and [Reinhardt, Corollary 3.1](https://users.informatik.uni-halle.de/~ahyjb/repe.pdf), whose decidability statement was checked in the primary text (download SHA-256 `65c86dd71348ca889d7fe88585824023c163ae8c2dfe22098c7f3575ed63150a`). This is a place-count obstruction under the stated semantics, not a ban on using many reset arcs to the same place.

## Proof audit

The ordinary three-register source has 528 instructions: 295 ADD and 233 SUB, giving 761 branches. The affine loader is `(L,R,T,reserve,budget)=(L,R,0,0,L+R)` plus one START token. Its expanded token count is `2(L+R)+1`; bit length and token mass are different resources. The debt

`D = budget − reserve − sum(registers)`

is exactly cumulative reset loss under **consume, then reset, then produce** semantics. Its ordinary arc contribution is zero for every transition; resetting register p adds the nonnegative post-consumption mass at p. Consequently exact DONE, with every other place empty, forces every zero guess to have been honest. Merely reaching or covering the DONE control token does not suffice. Early cleanup/finish remains possible but cannot reach the exact target with leftover mass.

If the deterministic source halts after h instructions with terminal mass H and peak mass M from initial mass B, the accepting words are exactly pump^k, enter, that unique source word, ordered cleanup, drain^(B+k), finish, with `k>=M−B`. Their lengths are `h+H+B+2k+r+2`; the minimum is `h+H+2M−B+r+2`. This proves the parity progression and unique labelled accepting word at each allowed duration, without a bounded search assumption. HALT has no outgoing instruction, so the endpoint is first halt. Nonhalting inputs do not gain false acceptance through reset guesses.

The strengthened gate

`(E−1)^2 + sum_r (E−e_r)(e_r+sum_i x_ri)`

has nonnegative summands throughout the nonnegative orthant and forces exactly one selector to be one, with inactive bases zero. The ADD/positive-SUB/zero-SUB affine parameterizations therefore capture exact instruction semantics and input typing. For natural inputs, the nonnegative-real zero set is already integral. The omitted tested base in a zero SUB is necessary. The generic reset schema handles weighted input and output arcs, including overlap with reset places; enabledness is measured before consumption, while the reset removes the remaining mass before output.

The peak extension uses `previous_peak+u−new_mass−v=0` and `uv=0`, giving the unique nonnegative pair and hence the running maximum. The minimum-duration certificate has `2813h` witnesses, `6h+2` affine squares and `762h` products, degree two. The source-only certificate has `2811h` witnesses, `5h+1` squares and `761h` products. Optional duration padding adds one natural z and `−2z`. It is genuinely natural-only: the valid h=328 witness with N=389 and z=1/2 is a real zero, whereas natural padding preserves the minimum-388 parity condition.

Control projection is valid only with one consumed and produced control token, no control reset, and the stated one-hot endpoint conditions. For the direct three-register net it leaves five data places: `4626N` witnesses, `7N+6` squares and `771N` products. N is an external firing count. The generic unprojected dimensions and the source-instruction h are not interchangeable.

The prime-coded two-counter source maintains `A=C·2^L·3^R·5^T`, `B_counter=0`, with fixed positive cofactor C coprime to 30. It has 8,408 instruction rows and 10,748 branches. Positive raw A is the source contract; A=0 has a separately checked nonhalting two-instruction loop. Each multiply/divide/remainder macro has the claimed exact instruction count and reaches no internal mass above its proved boundary maximum. This is a semantic encoding of the input, not a paid arithmetic implementation of exponentiation or a compact ordinary-loader circuit.

Shared reset arcs use dispatch, shared reset and marker-specific return. The one-control invariant and the per-register marker equation force the matching return; no other marker can lend its continuation. The stuttering decoder is defined at every reachable intermediate phase and preserves resource/debt semantics. The generic trace certificate must retain the 233 or 2,340 marker places as data. The marker-free outcome certificate is instead indexed by decoded source instructions, with a duration correction of two firings per selected zero branch.

| Literal net | Places | Transitions | Ordinary arcs | Reset arcs |
|---|---:|---:|---:|---:|
| Direct three-counter | 539 | 771 | 2,608 | 233 |
| Direct two-counter | 8,417 | 10,756 | 38,336 | 2,340 |
| Shared three-counter | 778 | 1,007 | 3,546 | 3 |
| Shared two-counter | 10,761 | 13,098 | 47,700 | 2 |

The independent checker verifies the debt and one-control coefficient identities on all **25,632** literal transitions. It also checks nine complete actual peak schemas, 625 rational strengthened-gate cases, 75 complete toy source/peak polynomials, and natural/signed boundary cases.

## Author execution evidence and its limits

All fourteen commands in `run-checks.sh` passed. Representative complete outputs include 437 symbolic three-register macro paths covering all 528 rows; 4,698 TM-macro comparisons; 324 weighted generic reset cases; 252 disabled weighted inputs; 1,296 mutated-coordinate/endpoint rejections; 120 random labelled traces; and 293 fractional-selector rejections. The two-counter source audit covers all 8,408 rows, 1,536 finite prime cases, 261 end-to-end cases and 81 raw-input/cofactor cases. The separate shared-prime audit executes 5,472 finite macros, 491,854 source instructions and 513,742 shared-net firings.

The actual `(L,R)=(6,0)` run has h=328, B=6, H=11, M=25 and minimum fuel 19. Its direct 388-step reset trace and shared 446-step trace were fully replayed. The source/peak witness has 922,664 slots with 1,187 nonzero coordinates; all 1,970 affine squares and 249,936 products were checked. The direct projected trace has 1,794,888 slots with 1,782 nonzero coordinates; all 2,722 squares and 299,148 products were checked.

The prime-coded A=64 example is **not** a materialized physical trace. Its 328 virtual macros account exactly for 738,579,314,485,258,247 physical source instructions, with 656 physical zero SUBs. The minimum direct duration is 857,788,604,036,216,584 and shared duration is 857,788,604,036,217,896. The proofs and finite macro audits support this accounting; neither the enormous trace nor its full polynomial was emitted or replayed. The report says so explicitly.

## Reproducible boundary findings and repair

**1. `peak_quadratic.py:7–8,31–36`: non-Boolean flags can corrupt the declared coordinate range.** `compile_peak(table,1,all_durations=0.5)` treats the value as true when creating the padding term but adds `int(0.5)=0` to the count. The emitted packet declares 2,813 variables yet refers to padding index 2,813. This is an actual malformed emitted schema, not merely a cosmetic metadata alias. Require exact bool for both option flags before branching.

**2. `build_net.py:52–59`: `fire` accepts out-of-domain markings and discards unknown places.** With the actual finish transition, `fire(net,{'q:DRAIN':1,'ghost':999},finish)` returns `({'q:DONE':1},0)`, erasing ghost mass. It also accepts `1.0` and `True` as control tokens and preserves negative unconsumed coordinates. These are invalid supplied markings, not legal-run counterexamples to the debt theorem. Require a dictionary of known string place names with exact natural integer values. The patch also turns the default `initial` helper's integer assertions into explicit checks so that this same input contract survives `python -O`.

Patch: `reset_net_exact_domains.patch`, SHA-256 **`bc3d28a42f97b60e5d5e17075d3383c298038bff01e1296a792af2aff3929720`**. Apply from a private extracted package root with `patch -p1 < /path/to/reset_net_exact_domains.patch`. It changes only `peak_quadratic.py` and `build_net.py`; it is not a wholesale generic source-schema hardening patch. The arithmetic formulas and valid fixtures remain unchanged. The independent normal and `-O` tests reject 32 malformed calls and compare nine full valid schemas. Patched source hashes are `9e4fdb70ccf07869be37d9f23c890c03a82abbe4d6a53c970b96b78ffb6d56d3` for peak and `ae434d354659d7fae5f2ce4014fe804b858ee86df4a4e42d10f94a5ae2f38f71` for build_net. All fourteen private patched author commands also passed; their complete replay is recorded in the companion receipt; expected provenance-hash changes are distinguished from arithmetic export changes.

## A fully charged natural-only simplification

In every actual source gate replace `(E−e_r)(e_r+X_r)` by `(E−e_r)X_r`, where X_r is the sum of the branch's retained natural base coordinates. Keep the one-hot square and every other source, endpoint, peak and duration term. Over naturals, the one-hot square already forces exactly one selector to be one. The remaining products force every inactive X_r, and hence every inactive base, to vanish. Thus the **complete natural zero set is unchanged on the same coordinates**, including canonical uniqueness. The old and new polynomials differ away from zeros by the exact identity

`P_old − P_new = sum_steps (E² − sum_r e_r²)`.

This does not preserve the strengthened nonnegative-real theorem: selectors `(1/2,1/2)` and zero bases give local new value 0 versus old value 1/2. The modification is a natural-only option, not a correction to the author's stronger real-domain construction.

For an explicit complete schedule, compute each printed shared linear form once; form every affine square and both factors from those cached forms; charge one multiplication per nonunit coefficient, square and product; accumulate every summand. Unit negative coefficients use subtraction, with a positive starting term. All shared forms used here are live in the complete canonical-peak source. Removing e_r saves exactly one addition in each of 761 branch factors. The checker derives the counts from complete actual h=1,2,3 packets and verifies twelve full signed polynomial identities.

| h | Original M | Original A | New M | New A | Complete saving |
|---:|---:|---:|---:|---:|---:|
| 1 | 2,285 | 10,496 | 2,285 | 9,735 | 761 |
| 2 | 4,564 | 20,987 | 4,564 | 19,465 | 1,522 |
| 3 | 6,843 | 31,478 | 6,843 | 29,195 | 2,283 |

The schedule has `M=2279h+6`, old `A=10491h+5`, new `A=9730h+5`: **12,770h+11 → 12,009h+11** total operations. These are complete paid counts for this specified sparse shared-form schedule, not a claim of globally minimal arithmetic complexity. Witnesses, residual/product counts, degree two and the external-horizon limitation are unchanged. No unbounded fixed-arity folding is supplied.
