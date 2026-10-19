# Joint dispatch and incidence packet: ordinary proof obligations

This combines the contextual-reuse report's selector dispatch with the detour
report's membership definition, truth-constant fusion and congruence splitting.
It changes a finite equational input. It does not change the 241-state machine,
establish a smaller Turing machine, or close an internal PA interpretation.
The inherited FC13B calibration and Sheffer single-axiom theorem remain explicit
dependencies. No new bit count is asserted before root executes the builder.

## Exact transformation order

Start with the pinned native-equality FC13B theory and its delivered 23-clause
equality-free completion. Write `d` for its designated constant and
`o₀ = I(d,d)`. The implication-incidence and empty-incidence clauses give
`Inc(s,o₀)` and `¬Inc(s,d)` for every `s`. Nonemptiness therefore implies
`d ≠ o₀`. For `B(x,y) = C(C(d,d,x),o₀,y)`, the two assignment laws give
`V(B(x,y),d)=x` and `V(B(x,y),o₀)=y`. The original atomic-incidence clauses give

`E(x,y) ↔ Inc(B(x,y), A(d,o₀))`.

Replace every primitive membership atom by this definition and remove its
redundant congruence clause. The reverse expansion defines `E` by the displayed
formula; every original native axiom is recovered. In the equality-free
presentation this is justified through the equivalence quotient and retained
function/Inc congruences. The explicit finite Horn proof also derives the
removed membership-congruence clause from C congruence and Inc congruence.

Next replace each binary `f ∈ {V,A,U,F}` by `H(tag_f,x,y)`, where the four tags
are new nullary symbols. Retain C and I, all native theory clauses, Eq
equivalence and Inc congruence. Replace those four function-congruence clauses
by the single law

`Eq(x,x') ∧ Eq(y,y') → Eq(H(t,x,y), H(t,x',y'))`.

The actual selector `t` is identical on both sides. There is no congruence in
the selector coordinate. No original object variable is restricted to a subset
of the model's carrier.

Given a nonempty model M of the unpacked theory, use M×J with distinct actual
tags in the finite second coordinate, and let Eq compare first coordinates.
Lift original operations through first-coordinate projection and a fixed
section. For each actual selector, H implements the corresponding old binary
operation on projected arguments, or a fixed default operation. The required
object-coordinate congruence holds even when two different tags are
Eq-equivalent. Induction on terms and literals, including negative literals,
transfers every old clause under every assignment.

Conversely, quotient a packed model by Eq and interpret each original function
using its fixed actual tag. The object-coordinate law makes those operations
well-defined. H itself need not descend on the selector quotient. Thus this
step preserves satisfiability without a cardinality assumption.

In the combined language the membership definition is exactly

`Inc(C(C(d,d,x),o₀,y), H(tag_A,d,o₀))`.

Its congruence proof uses C congruence and reflexivity of the *same ground term*
`H(tag_A,d,o₀)`, followed by Inc congruence. It never transports tags by Eq.
The builder matches that term and all C/H clauses to Opening's independently
authored Horn certificates before serializing either packet.

## The two variants

Both variants retain the same theory clauses and split congruences into
interderivable coordinate groups. Full congruence implies every group law by
reflexivity in unchanged coordinates. Conversely, successive coordinate
updates plus transitivity recover full congruence. Transitivity is derived
from the retained reflexive/Euclidean Eq axioms. For H, only the two object
coordinates participate throughout.

| Variant | C groups | H object groups | Extra alias | Symbol slots | Maximum local variables |
| --- | --- | --- | --- | ---: | ---: |
| `dispatch_no_alias` | first two; last | both | none | 11 | 5 |
| `dispatch_split_alias` | three singles | two singles | `o = I(d,d)` | 12 | 4 |

The expected signatures, in serialized order, are

`d:0, C:3, I:2, p_Inc:2, p_Eq:2, N:2, tag_V:0, tag_A:0, tag_U:0, tag_F:0, H:3`

and the same list followed by `o:0`. The structural equation counts are 18 and
21 respectively. Both signatures plus local-variable capacities fit exactly
16 opcodes. The actual encoder must confirm these facts and measure the full
packet; no total bit count is assumed. Keeping the alias with the unsplit
five-variable H law would instead require 17 opcodes and lose this boundary.

## Boolean algebraization and truth fusion

The packed clause theory is still an equality-free universal clause theory;
Eq is a predicate. Apply the inherited Boolean algebraization. Truth-table
checks validate each exact retained group after membership and dispatch
substitution, and each newly introduced Horn equation. They do not prove
model existence or the original FC13B consistency calibration.

Fuse Boolean `top` with source `d`, retaining `d = N(d,N(d,d))`. For a source
model M, embed its carrier into the Boolean algebra P(M), sending its
distinguished `d` to M itself and every other element a to `{a}`. A retraction
to M interprets all source operations; predicate operations return M or ∅.
This preserves the packed universal clauses for arbitrary assignments. It
does not require H to respect Boolean equality or selector Eq congruence.
Conversely an ultrafilter on any nontrivial Boolean model recovers the clause
predicates, keeping the same carrier and source operations. The inherited
Sheffer basis supplies the Boolean-algebra structure. This establishes the
ordinary ZFC-level semantic bridge for the fused equations.

For the alias variant add the explicit equation `o = I(d,d)` and replace that
ground subterm elsewhere. Expanding o recovers the old theory, and every old
model has the uniquely prescribed expansion. This is a conservative term
definition and is charged in the packet. The ground endpoints in both
variants are `N(d,d)` and `d`.

The inherited ground-term quotient/completeness argument then relates
non-reachability of these two endpoints to nontrivial equational models.
Composing the foregoing ordinary equivalences transports the original packet's
consistency calibration. It is not inferred from finite serialization tests.

## Root-only validation

`build_joint.py` imports only two exact pinned inherited modules: the ground
rewrite kernel/codec and Boolean equation builder. It invokes no search or
bounded NAND synthesis. It uses fixed transformed baseline groups and a
deterministic linear Horn-to-NAND formula for the added congruences. It binds
the exact independent helper source and replays its 12 certificates/49 Horn
inferences, with explicit schema and membership-term checks.

The finite checks include all original/transformed Boolean groups, exact
signature and arity validation, complete packet roundtrip, every strict
truncation, three malformed/trailing controls, both contextual orientations
of every equation, term-node census and full header/payload/endpoint bit
accounting. Every input is rehashed afterward. Fresh output is required;
exceptions preserve a FAIL record once output preparation has begun.

Suggested root command, after source and dependency review:

```sh
python -B /tmp/zfc-joint-equational-packet/build_joint.py --output /tmp/zfc-joint-equational-packet-run1
```

Root should use its normal bounded process-group wrapper. No invocation,
serialization, TM simulation, compiler run or claimed new PASS is part of
this source proposal. Original delivered inputs and the earlier unexecuted
pending-helper draft remain unchanged.
