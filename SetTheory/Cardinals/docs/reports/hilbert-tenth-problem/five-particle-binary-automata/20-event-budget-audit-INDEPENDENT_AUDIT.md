# Independent audit of the event-budgeted quartic schema

Date: 2026-10-03. Scope: `PROOF.md`, `example_emitter.py`, `scheduler_reference.py`, and `test_schema.py`, against the pinned evaluator SHA-256 `42e8aa65c05fcf373a03a02be51ebb89a4fdcb1f1070ad776ffe1e8e99049c61` and its checked original dependency. This audit did not modify the theorem or production code. Corrections were communicated to the producer, who changed the proof. Audit code and outputs are confined to this directory.

## Verdict, with the three claims separated

1. **General finite theorem/schema:** accepted at the level of an explicit mathematical circuit construction, after the clarifications below. No soundness, completeness, or canonical-witness counterexample was found. It is not an implemented arbitrary-mass coefficient exporter or a machine-checked proof.
2. **Small implemented emitter:** the exact sample ledger was independently recomputed: A=189, I=78, Dv=0, G=78, Q=4; 612 auxiliary natural variables, 616 residuals, 2013 residual monomials, 9955 ordered-square term occurrences, 4573 collected expanded monomials. Residual degree is at most two. Both residual SOS and expanded polynomial evaluate to zero. The changing factors are 0 and 47, followed by a distinct completion round.
3. **Numerical theorem bounds:** the 10000 primitive prefactor and H_* are supportable conservative bounds for a deliberately chosen implementation of the specified macros. They are not counts mechanically obtained from a general exporter. The accounting below explains a construction within these bounds. Equivalent implementations that flatten class addresses, leave invalid parameters unmasked, use non-one-hot lookup accumulators, or add unnecessary large intermediates do not automatically inherit H_*.

The small emitter uses three natural inputs `(h+, h-, gap_minus_one)`, with x0=h+-h- and x1=x0+gap_minus_one+1. This parameterizes every sorted two-particle support but is not the general theorem's literal four-coordinate canonical-pair input interface. Its count should continue to be identified as a specialization.

## Corrections and clarifications identified

- Zero auxiliaries at T=0 is valid when sorted canonical inputs are externally promised. Enforcing arbitrary signed strict order through a polynomial zero set requires the comparison auxiliaries (or a different input parameterization). The producer made this distinction explicit. For example, a polynomial vanishing for every positive integer pair x<y must vanish identically on that quadrant's algebraic closure, so it cannot distinguish x>=y there without witnesses.
- The pinned home-incidence order is moving branches in their filtered source order, followed by direct branches in their filtered source order. It is not the combined original input branch order. The corrected proof now names that order.
- Trace-generation constants include the horizon T; target constants belong in the acceptance/coefficient ledger lambda. The original sentence omitting T was corrected.
- Guard lookup compares the two class coordinates and branch/domain-image identifier fieldwise. A flattened class address c0*(J+2)+c1 can have quadratic-in-J height and is unnecessary; it is explicitly excluded under the current H_*.
- The revised proof also specifies presence-aware descriptor sorting, a constant dummy moving record when p=0, and a noncontextual true dummy guard when b=0. These resolve otherwise underspecified totalization cases.

## Canonical witness and semantic audit

For signed arithmetic assignment, the value equation fixes v+-v-, and v+v-=0 over naturals gives exactly one pair. The comparator has exactly one Boolean b and slack d for any signed difference, including equality and negative inputs. Constant division has a unique signed quotient pair and bounded remainder because r+h=d-1 over naturals, and then h is unique. A Boolean defining gate needs no extra Booleanity equation when its inputs are already uniquely determined Boolean wires.

These are topologically ordered functional gadgets. An induction through *all* gadgets, including the branches hidden by false masks, proves uniqueness of the entire pre-acceptance auxiliary tuple. Final input/target/completion conditions retain that tuple or reject it. Mutations are not the uniqueness proof.

All raw slots are computed from the same pre-factor support. Competitor exclusions range over all raw keys, including keys failing isolation or guard. Distinct valid raw slots cannot represent the same key: each label's first site identifies its unique occupied coordinate, while the two endpoint shapes cannot simultaneously be the exact raw window at one key. Matching old/new shape ranks produces the simultaneous set output because eligible endpoint unions are disjoint. Sorting then removes any dependence on input particle labeling.

The minimum scan is deterministic, uses strict index improvement, and therefore selects the earliest fixed slot among duplicate minimum indices. A missing winner establishes identity of every future candidate, and candidate completeness establishes identity of every omitted factor. Only then is a CA step completed. Every true changing factor consumes one round and every CA step consumes its own completion round; hence exactly k+T nonidle rounds are necessary and sufficient, and R=T+K accepts exactly k<=K. Idle rounds remain uniquely evaluated rather than releasing witnesses.

The residual ledger and monomial bounds check out: assignment row lengths at most (8,1), comparator (2,8), constant division (1,5,3), Boolean row at most 4. Consequently the stated 9/10/9/4 residual-term and 65/68/35/16 ordered-square coefficients follow. Variable and residual counts are exact when A,I,Dv,G,Q count the actually unfolded circuit.

## Conservative primitive accounting supporting 10000

Use the following implementation costs, all in section-2 primitive units: equality <=4 (one +1 assignment, two comparisons, one Boolean difference); an interval membership <=3; interval membership plus running count <=4; abs <=3; ordinary signed compare-exchange <=3; a Boolean fold uses one binary gate per input. A fieldwise table row has three equalities plus two conjunctions, its constant table-bit mask, and an accumulator fold, hence <=16 primitives. Allowing a fourth identification field would still be <=21 and remains inside the final allocation.

For a fixed descriptor and one of its 2n raw slots, the following explicit implementation allowances suffice:

- key formation: 1
- all three required-site presence scans, including live-position masks and conjunctions: 15n+12
- raw-window count and size equality: 4n+7
- isolation count and size equality: 4n+6
- every one of the 2n competing raw slots, with difference, abs, nonzero/upper-bound tests and Boolean folds: 20n
- two full context scans, stable first-hit selection, counts and rejected-class totalization: 22n+19
- all 2bc guard rows, plus noncontextual bypass: 32bc+3
- active/masking logic: 5

The sum is <=65n+53+32bc. For all 2n raw slots it is <=130n^2+106n+64nbc. For each old particle, each raw slot, and each of the three ranks, charge 10 primitives for old-site formation, equality, active/live masks, displacement, masked product and sum. This is <=60n^2. Forming outputs, their fixed sorting network and the coordinatewise changing flag cost <=2n^2+7n. Thus the factor-evaluation part is bounded by

    C * (200n^2 + 120n + 64nbc + 20).

This is safely below 1000(C+1)(n+1)^2 S_tab, since S_tab=m+b+2bc+1 >=2. If a separate branch/domain field is retained instead of the combined guard identifier, replacing 64nbc by 84nbc is also safely within the same bound.

For completeness, source/candidate/descriptor wiring can be budgeted independently rather than hidden in the preceding estimate. Let Pairs=binom(n,2). A deliberately wasteful finite implementation allowance is

    Pairs*(200n + 200b + 100Delta + 1000)
      + C*(2000 + 200S_tab).

The first term covers pair arithmetic, occupied-marker scanning, every one of the 2b incidence records, moving-attribute selection, all Delta home output slots, and the four slots for every third particle. The second covers source-field multiplexers, the ten descriptor families (free, behind, ahead, dispatch, endpoint, commit, direct, phase-free, phase-near, phase-home), their finite partition arithmetic, presence-aware sorting of both three-position shapes, and masked output fields. One can use up to 120 primitives per finite descriptor family, 200 for the two tiny sorting networks, 100 for partitions, 100 for miscellaneous fixed wiring, plus 200S_tab for record selection; this remains inside 2000+200S_tab.

For n>=2, C>=3Pairs and C>=Delta*Pairs. The displayed source/candidate/descriptor allowance is at most

    C*((200/3)n + (800/3)S_tab + 7300/3),

which is <=1000(C+1)(n+1)S_tab for n>=2 and S_tab>=2. Cases n=0,1 have C=0 and need no candidate or descriptor loops.

The stable minimum and state wiring can be kept within C*(n+12)+10n+40 primitives: eligibility, strict improvement, selected index and n selected coordinates, then changing/completion/idle flags and state selection. Even a several-fold increase stays within the separate 1000(C+1)(n+1)S_tab allocation. Initial admissibility wiring is O(n) and the finite final checks are charged in Q; the 10000 whole-circuit bound leaves more than enough room beyond the three 1000 per-round allocations.

These are construction-level upper bounds, not an assertion that current general-purpose code emitted these gates. Their force is existence of this explicit bounded-loop implementation. Any future general exporter should report its actual A,I,Dv,G,Q and test its emitted structure against its normative macros.

## Height and bit-cost audit

Let M0 denote the parenthesized quantity in H_*, so H_*=100(n+1)M0. On an accepting trace, true coordinates are bounded by H0+2KB3 and candidate outputs add at most 2B3. Shape offsets are bounded by B3. Key differences, context bounds, and raw offset computations use only a fixed number of additions/subtractions or multiplication by a sign. Their magnitudes, and the comparator slacks they induce, are bounded by a small fixed multiple of M0.

Source fields and factor indices are selected one-hot and valid indices/travel parameters are masked before dependent scaling. Their partial selected-field sums therefore do not accumulate b copies of a large field. Fieldwise guard selection avoids J^2 address values. The stable first-hit scan stores one valid context offset rather than summing unbounded offsets. Indicator counts are at most 2n; displacement prefixes for an individual old particle have at most one nonzero eligible contribution. Natural quotient/remainder and sign-pair parts introduce no larger-order values. These facts leave ample room within the factor 100(n+1), including canonical comparator slacks and dummy computations.

This supports the stated H_* for a construction respecting those restrictions. It would not justify H_* for an arbitrary extensionally equivalent arithmetic circuit. The proof now also appropriately distinguishes accepting canonical witnesses from arbitrarily oversized malicious submissions. Verification must use the actual submitted bit length or first enforce the declared bound. Source parsing/table preprocessing and expanded coefficient collection remain separate costs, as disclosed.

## Independent executable evidence

`independent_audit.py` does not merely rerun the supplied +1 mutation suite. It independently implements the full 2n-slot raw/absence/context/displacement algorithm and compares it with literal original factor application, checks omitted-raw-factor completeness across all factors of the tested sources, and compares fixed-budget scheduling with literal products.

Results in `independent-receipt.json`:

- 7 accepted sources: b=0, direct-only, left decrement, right guarded increment, mixed original branch order, J=17 context, and multiple incidence branches
- 942 configurations and candidate-completeness checks
- 123222 independent factor-schema/original-factor comparisons
- 468 scheduler checks, including T=0 and multiple steps, plus 71 strict underbudget rejections
- 485 multi-active factor instances, 20 competitor exclusions, 14 multi-particle context rejections
- 392 exhaustive signed constant-division fibers
- 36 polynomial syntax/ledger cases, including 100-digit signed coordinates and verification that coefficients/structure do not depend on sampled input values
- 189 simultaneous positive/negative-part mutations rejected by canonical-sign constraints

Finite checks corroborate the proof and exercise branches absent from the original sample; they do not replace the theorem or establish universal arbitrary-mass coefficient generation.

## Final interface correction replay

The producer subsequently tightened `build(target=...)` to require exactly two strictly increasing exact Python integers in a list/tuple, rejecting Booleans, floats, and integer subclasses. The artifact binding checker likewise now checks exact integer coefficient/index types, monomial degree/range/order, and typed declaration equality. I inspected those changes and replayed `test_interface.main()` in both normal and optimized Python, redirecting only its receipt writes into this audit directory. Both replays passed: 13 malformed targets, 5 other malformed inputs, and 10 malformed serialized/source cases rejected; a valid 301-digit-coordinate trace accepted. The exact sample circuit counts remain unchanged. See `interface-replay.log`, `interface-optimized-replay.log`, and `replay-interface*-receipt.json`.
