# Exact source construction for the canonical-membership-binder parent

These three standard-library Python scripts reproduce and check the 225-state
parent used by the 224-state candidate. They perform no search. The separate
state-fold certificate turns this parent into the final 224-state table.

Run the scripts with Python 3.10 or newer, without `-O` or `-OO`:

```sh
python3 -B construct_rel225.py --baseline-root BASELINE/portable --output WORK/rel225
python3 -B check_emitter.py --baseline-root BASELINE/portable --output WORK/rel225/emitter_contract.json
```

`BASELINE/portable` is the recovered, unchanged Source124 K225 packet. The
explicit `--baseline-root` argument makes these commands independent of where
the scripts are placed. `local_bisimulation.py` must be beside the two drivers.
No third-party Python package is required.

## Construction and finite evidence

`construct_rel225.py` checks four pinned input hashes and makes the following
exact changes to the original K225 source and table:

1. Cancel eight negation constructors, consisting of three double-negation
   pairs at existential/conjunction boundaries and one pair at the final
   conjunction boundary. This reduces 5,121 source leaves to 4,745.
2. Reassociate the two remaining existential constructor programs and replace
   their now unnecessary context-dependent `All; Imp` dispatch by a direct
   dispatch. The source DAG decreases from 211 to 210 nodes; this stage still
   has 225 machine states because the removed source node had shared a machine
   state with another source node.
3. Replace the binder-producing word in equality vacuity. The old word pushes
   parameter `c`; the new word pushes the already used membership code
   `4*P(a,b)+1`. The resulting equality helper is exactly
   `I(E(a,b), Q(R(a,b), E(a,b)))`. The new word has 80 source leaves in place of
   26, so the resulting source has 4,799 leaves. The original gate, full
   relational-vacuity family, eight logical rows, register encoding, and proof
   enumerator remain as in the pinned source.
4. Reassociate the closed suffix to expose the useful shared dispatch. Both
   complete guarded control-flow resolvers verify identical instruction effects
   and successors before and after this reassociation.

The construction driver checks every source decoder prefix, and it executes
all 409,835 blank-startup transitions, checking the complete resulting tape:
351 one-cells, head position -5, and blank everywhere else. The endpoint agrees
with that of the original K225 source packet.

The output table hashes are fixed:

| File | SHA-256 |
|---|---|
| `candidate225.k.tm` | `4526bd8cf2160ac5dfce039add0550e9788095f60ecc6b4462afd4ebbfd42790` |
| `candidate225.tm` | `b5111f270791fd0686df6f99af25648d7cf6e00ad57091b25b58e068abcd1898` |
| `sites225.json` | `309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878` |

The first table uses the inherited original K state labels with start 0 and
terminal 254. The second uses the packet's legacy labels with start 95 and
terminal 254, so the pinned universal-runtime adapter can be used without
modification. These labels are distinct from the final consecutively numbered
224-state deliverable.

## Arithmetic macro certificates

`local_bisimulation.py` constructs finite relations between decrement
instructions and normal returns in two closed register-program graphs. It
checks that every test-free segment accumulates the same vector of register
increments, that related decrement instructions test and decrement the same
register, and that both successors are related. This gives a bisimulation by
induction on segments for **all nine independent natural register values**.
It preserves the complete final register vector, normal return, halting, and
divergence. The `test_pairs` field counts related branch cutpoints, including
the return cutpoint; it does **not** count sampled counter values or bounded
executions. There are 263 such pairs across the eleven macro contracts.

The old side of each certificate is expanded directly from the pinned
`Dag230.v`. Its arithmetic meaning is supplied by the corresponding lemmas in
the unchanged pinned `ProgLib230.v`:

| Checked word | Upstream source nodes | Upstream arithmetic contracts |
|---|---|---|
| Implication | 119 | `cons119` |
| Universal quantifier | 180 | `wal180` |
| Negation | 218 | `wn218` |
| Conjunction | 178 | `wa178` |
| Existential quantifier | 183 | `wex183` |
| Conjunction then existential | 110 | sequential composition of `wa178`, `wex183` |
| Push one | 177 | `v177` |
| Push parameter c | 168 | `par168` |
| Membership atom on a,b | 166; 121; 181 | `par166`, `par121`, `wel181` |
| Equality atom on a,b | 166; 121; 182 | `par166`, `par121`, `weq182` |
| Universal quantifier then implication | 180; 119 | `wal180`, `cons119` |

The optimized source blocks may use different binary parentheses, control-depth
numbers, or orders of increments within a test-free segment. The finite
bisimulations are what justify inheriting the upstream arithmetic contracts.
The upstream constructor contracts require the two scratch registers to be
zero. The local bisimulations themselves are valid for arbitrary registers.

## Exact emitted expression

`check_emitter.py` recovers the AX macro word from the pinned `Dag230.v`, then
symbolically executes macro positions 88 through 148 on arbitrary natural
parameters `a,b,c`, an arbitrary previous top formula, and an arbitrary older
stack. The expression nodes stand for arithmetic code constructors, so equality
of the expression trees entails equality of natural codes for every input.
The script checks the original KCode230 expression, the expression after the
four double-negation cancellations, and the expression after changing only the
equality-helper binder. It also checks the final stack effect.

The binder is fresh because `P(a,b) >= a,b`, and hence
`4*P(a,b)+1 > max(a,b)`. This includes `a=b=0`; the value 1 is used as a variable
label in the helper, irrespective of its separate role as the designated false
formula code.

## Scope and dependencies

These scripts give exact finite evidence for the source construction,
arithmetic macro contracts, suffix reassociations, emitted expression,
decoder prefixes, and complete blank startup. The two semantic formula changes
require the accompanying mathematical calibration proof. The all-register
binary-runtime certificate and the all-tape 225-to-224 state-fold certificate
are separate necessary parts of the complete argument.

The drivers use the unchanged Source124
`baseline226/verification/reconstruct227.py` for tree parsing, metrics, two
control-flow resolvers, and startup simulation. The packet must also retain its
pinned upstream source and attribution. This support does not claim that the
new whole-machine consistency theorem has been rechecked by a proof-assistant
kernel. Its new certificates are executable ordinary mathematical proofs,
combined with the stated upstream arithmetic contracts and the new logical
calibration argument.
