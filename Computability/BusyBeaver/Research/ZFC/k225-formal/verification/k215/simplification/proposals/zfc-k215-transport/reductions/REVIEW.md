# Independent review of the CM215 proof bridge

## Verdict and precise status

The mathematical transport architecture is sound. The generic Lean modules
have clean, inspected kernel reports: `PositiveStuttering.Simulation.halts_iff`
uses no axioms; `MarkerTransport.all_tape_halts_iff` and the finite-checker
soundness results use only `propext` and `Quot.sound`. No custom oracle,
consistency assumption, reverse-simulation premise, or injectivity premise
is hidden in those results.

The exact-table client has now also completed a clean 24-module Lean build.
I inspected the successful receipt and endpoint assumption reports in
`work_root/lean/kernel_receipt.json` and `logs/CM215Certificate.log`.
The all-tape and blank equivalences use only `propext` and `Quot.sound`;
the 215-state counts and six-row difference are also kernel checked. The
nineteen finite chunks cover all 303 native label slots, as certified by
`partition`; the final client combines those proved checks. The earlier
monolithic compilation failure is superseded and supplies no evidence.

The proved direct conclusion is all-tape halting equivalence of the two
exact native machines, from initial control zero, in the supplied
`Int -> Bool` TM semantics. The separate adapter to ProveIt's existing
machine/run definitions and final composition with its ZFC endpoint remain
explicit integration work. The completed standalone equivalence is not yet
a newly compiled repository ZFC-consistency endpoint.

## Positive stuttering

The generic source and target are deterministic partial functions. The source
invariant is inductive, source terminals map to target terminals, and every
successful source step has a positive finite target block with the mapped
endpoint.

Forward halting preservation is finite concatenation. Backward preservation
uses strong induction on the length of a target halting run. Determinism
forces a simulated target block to be a prefix of that run, and positivity
strictly decreases its remaining length. This is sufficient without a reverse
simulation or a uniform upper bound on block length. It also avoids selecting
an infinite sequence of witnesses by a choice principle.

The terminal clause is needed in the forward direction. The strict positivity
clause is needed in the backward direction. Neither is decorative. The proof
of `prefix_halt` properly rules out extending a successful prefix past a
terminal target configuration.

## Marker invariant and local blocks

The invariant concerns only three source controls:

- At 52, the left neighbor is one.
- At 176, either the current bit is one or the left neighbor is zero.
- At 156, the right neighbor is one.

The incoming-row facts establish these conditions for arbitrary whole tapes.
In particular, the exceptional incoming edge to 176 from 156 preserves the
second condition because 156's right-neighbor invariant supplies the new
current one bit. It is not an assumption that the tape was blank.

The control map sends 176 to 52 and fixes every other control. When the current
bit is one, both old roles take the same one-step path. When it is zero, the
new machine uses a three-step block through its repurposed helper 176. For an
old 52 configuration it reads a one marker and reaches 154; for an old 176
configuration it reads a zero marker and reaches 168. Every microstep writes
the bit it reads, so the entire tape is preserved. The head ends one cell
right in both cases. The remaining controls use literal one-step row equality
modulo the control map.

This is a valid noninjective simulation. The repurposed new helper 176 need
not be an image checkpoint: it may occur inside target blocks. No target
invariant or reverse case analysis is required. All blocks have length one
or three and cannot hide a premature halt.

## Finite certificate and exact bytes

`FiniteMarkerCertificate` checks both symbols at every element of `Fin 303`,
proves soundness of the Boolean scan, and separately requires ten literal row
equations. The generator fills those equations with `rfl`. Ordinary `rfl`
and `decide` retain kernel checking; there is no executable `native_decide`,
`unsafe`, `extern`, `sorry`, or custom axiom in the reviewed source files.

I independently parsed all 860 generated Lean row branches and compared them
with the two native input tables. Every row agrees. The independent receipt is
`REVIEW_LITERAL_TABLES.json`. It binds the reviewed generated source hash and
both input hashes:

- Parent: `9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.
- CM215: `e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252`.

Each table has exactly 215 working labels and 430 rows. The type `Fin 303`
is a convenient container for sparse native labels through 302; it does not
make this a 303-working-state machine. There are 88 labels with no outgoing
rows, including 254. All targets outside the working-label set are exactly
254. Thus the other 87 undefined labels cannot be reached from the working
initial control, on any tape. No extra reachable halt is introduced by them.

The current `liveCount` definition counts the labels whose zero row is
present. This correctly counts these literal tables because each displayed
branch supplies both symbols. For a future arbitrary table that count should
be accompanied by a two-symbol totality fact.

The generator's input hashes agree with my independent references. Hashes bind
the public data and generated text; they do not replace the kernel theorem.
After changing the generated proof assembly, update its output hash and build
receipt even if its transition definitions stay byte-identical.

## Review of the proposed next selector reordering

The shared zero successor of controls 154 and 168 is a real design opportunity,
but not a one-state saving by itself. At CM215 control 52, let the current bit
be zero, predecessor marker be p, and next bit be b. The existing four-step
combined selector/decoder block has this complete contract, with tape unchanged
and final head two cells right:

| Condition | Final control |
|---|---:|
| b = 0 | 166 |
| b = 1, p = 0 | 98 |
| b = 1, p = 1 | 12 |

A reordered implementation must realize all three branches, preserve the
current-one behavior of control 52, restore any temporarily changed cells,
and preserve every other use of any reused helper. It must add no replacement
state if deleting helper 176 is to give a net saving of one.

This optimization combines several old steps. The present single-old-step
control map does not automatically certify it. It may need a refined
configuration map or a positive simulation between suitable common
checkpoints, together with a proof that no infinite computation remains
inside an omitted macro. These are substantive additional obligations.
No table meeting them has been constructed in this packet.

## Scope of this review

This was an independent source-level and finite-data review within the same
collaboration. I did not rerun the large repository proofs or the root's exact
literal-client compilation. The successful final build receipt and its assumption reports were inspected
as described above. The generic theorem review, all-table comparison, and
remaining repository-integration limitations are independent checks of its
mathematical scope.
