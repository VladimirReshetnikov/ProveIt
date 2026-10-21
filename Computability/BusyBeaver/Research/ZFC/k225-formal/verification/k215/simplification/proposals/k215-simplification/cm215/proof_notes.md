# A compact formal proof for the existing CM215 alternative

## Verified contribution

The published CM215 alternative is not a new machine in this packet. It already
exists under `candidate-k215/alternatives/conditional-marker` at commit
`b6c7087477e51c017003bd729e712c8969733223`. The new contribution is a compiled Lean
relative correctness theorem for that exact table, with a reusable positive
stuttering lemma, an explicit inductive invariant, and an adapter to the
repository's `Machine 215` semantics. Its correctness no longer needs a second
proof of the register interpreter, command enumerator, arithmetic compiler,
numerical calculus, or ZFC consistency calibration.

The inherited primary table SHA-256 is
`9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.
The inherited CM215 native table SHA-256 is
`e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252`.
The data generator verifies both input byte hashes, maps the 215 working labels
in ascending order to 0 through 214, and maps native halt 254 to separate halt
215. The terminal is totalized by an absorbing row only for the proof's iteration
function. It is not counted among working states and is not an added physical
stay-put transition.

## Why this alternative is the best next formalization target

- `commands120` changes the command language tags and therefore needs command-level
  correspondence, source correspondence, decoder proof, and finite startup work.
- `composed` preserves the source but changes its decoder allocation, requiring
  machine/source correspondence or a new direct local transfer argument.
- `rebalanced` reduces address depth 47 to 41, but changes 4,120 addresses. It does
  not simplify the logical proof, and address depth is not proof length.
- `reencoded` has a changed root seed and a longer blank prefix, needing an
  additional seed-calibration proof.
- `direct-transfer` (ST215) reduces a source command from 78 to 35 leaves, but its
  partial AX startup sits above opaque tail 2 containing falsity; correctness
  uses a substantive protected-tail credit/scheduler proof. Fewer source leaves
  do not mean a shorter complete formal proof.
- CM215 has an exact local relation to the already formally proved K215, for
  every tape at the designated start state. This makes its *additional* proof
  small. It does not shorten the full foundational proof from scratch.

This ranking concerns marginal proof obligations, not claims that other candidates
are incorrect or cannot eventually have equally short transfer proofs.

## Strong local invariant

Write c = (q,h,t), where t is the whole Boolean tape. A directly inductive
invariant is the conjunction of:

1. q=52 implies t(h-1)=1.
2. q=176 and t(h)=0 imply t(h-1)=0.
3. q=156 implies t(h+1)=1.

The third clause turns the two-step predecessor argument in the ordinary
exposition into a one-step induction. It is preserved because every incoming
edge to 156 writes one and moves left. Every incoming edge to 52 writes one
and moves right. Incoming edges to 176 either write zero and move right, or
come from 156 on symbol one and move right; the latter route cannot scan zero
at its destination, by clause 3. The Lean proof checks all finite incoming
claims by kernel reduction on the literal table, not by bounded execution.

Let phi identify old state 176 with 52 and fix every other old control. The
new machine takes one step for an ordinary old transition and the common one
branch of 52/176. For the zero branches it takes:

- marker one: 52 -> 176 -> 129 -> 154;
- marker zero: 52 -> 176 -> 185 -> 168.

Each three-step block restores both inspected cells and ends one cell right,
so the complete tape and head equal those after the original one-step row.

## General stuttering lemma

Suppose deterministic totalized transitions f and g have a mapping phi at
simulation boundaries; I is an f-invariant at the initial state; every source
step from I is simulated by k>=1 target steps; and phi preserves and reflects the terminal
predicate. Assume terminality persists under target transitions. Then source
and target halt equivalently. No uniform upper bound on k is needed.

The useful proof organization is to establish simulation times t_n >= n.
A source halt directly gives a target halt at t_n. If the target halts after n
steps, it is still halted at t_n; reflection gives a source halt after n steps.
Thus backward simulation, injectivity of phi, and reasoning about infinite
streams are unnecessary. Positive k is essential: allowing all steps to take
zero target time would invalidate the reverse direction.

The concrete CM215 blocks use k in {1,3}. The all-tape theorem needs no
finite-support hypothesis, numeric register invariant, spare-list condition,
proof-code validity, or ZFC assumption. The Core adapter then specializes
this stronger statement to the actual repository machine/tape type.

## Artifact boundaries

`PositiveStuttering.lean`, `CM215Data.lean`, and `CM215Transfer.lean` use only
Lean's standard library. `CM215CoreBridge.lean` additionally imports the unchanged
pinned `BusyBeaver.Core` module copied under `BusyBeaver/Core.lean` for offline
reproduction. `CM215RepoBridge.lean` imports the real repository's `KDense215`
module and proves that the copied parent transition function equals its literal
`machine215` transition function on all 430 rows. Its calibration theorem has
an explicit hypothesis; it does not silently assume or reprove the K215 endpoint.

The full inherited K215-to-ZFC dependency closure need not be rebuilt to check
this new relative theorem. Applying `inherit_calibration` to the repository's
existing `KEndpoint215.blank_halts_iff_zfc_refutation` is the final integration
step. A new fresh build of that complete endpoint is a separate verification
claim and must not be inferred from the present relative proof.
