# Three 242-state folds of combined243

All three tables have 242 working states, 484 total binary rows, no added adapters, and a separate halt state. The old-label start is95 and halt is254. The accompanying canonical tables start at0, use working states0–241, and halt at242. This is a self-authored executable mathematical certificate, not a proof-assistant kernel theorem.

## Exact base

The base is `candidate-combined243` at repository commit `e58338db7545909907e07a7603e8eb88625c527a`, old-label SHA256 `4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300`. The 6,459-site QT source is unchanged by these folds, SHA256 `3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4`.

## Inductive local invariant of the base machine

For a configuration `(q,h,tape)`, impose only the following requirements:

- At q∈{15,18,47,65,171}, tape[h−1]=0
- At q∈{91,94}, tape[h−1]=1
- At q=27, tape[h]=0
- At q=50, tape[h−1]=1 or tape[h]=1
- At every other control, no restriction

These requirements hold at95 with every head and arbitrary full binary tape. They are preserved by every base transition. The first two lines follow immediately from all incoming transitions, which respectively write0 or1 and move right. All incoming transitions to27 come from18/0,47/0,65/0 and move left; their predecessor guards force the destination symbol to0. Entries to50 either write1 then move right (34/1,127/1), or move left from91/1 or94/1, whose left symbol is1. The destination thus has left1 or current1.

`prove_local_folds.py` independently enumerates all 32 assignments to offsets−2,…,2 at every base state. Every invariant-admissible assignment is checked against the literal next transition and destination invariant:7,640 checks. Because a single step moves only one cell, every destination guard cell lies in this enumerated window. No assumption about source reachability, finite-support tapes, numeric register values, or blank startup is used in this invariant.

## Candidate A: merge old27 into15

Delete27. Replace15/0 by0L32 and redirect18/0,47/0,65/0 to15. Leave15/1=1R22 unchanged. All other retained rows are identical.

The original entry to15 has left0. If it reads0, its old one-step transition0R21 is replaced by the three-step path:

`15/0 →0L32; 32/0 →0R45; 45/0 →0R21`.

Both paths leave the entire tape unchanged, finish at21, and displace the head right once. When18,47 or65 reads0, its old two-step passage through27 equals its new two-step passage through15: the common left0 guard makes both intermediate controls read0. Both end at32 after moving left twice.

Comparison checkpoints exclude old27. There are480 ordinary identical rows and4 exceptional schema rows. Positive blocks have old lengths1 or2 and new lengths2 or3. All512 admissible 9-bit assignments across the four schemas pass the complete-tape equality check.

## Candidate B: merge old50 into27

Delete50. Replace27/1 by0L20 and redirect34/1,91/1,94/1,127/1 to27. Leave27/0=0L32 unchanged.

Original27 always reads0, so its changed read1 row is irrelevant at old comparison checkpoints. A right-entering old50 caller writes1 to the left of the new head. If the destination reads0, the old0R39 transition is matched by:

`27/0 →0L32; 32/1 →1R46; 46/0 →0R39`.

The left1 and current0 cells are preserved exactly. If the destination reads1, the new27/1 transition equals old50/1. The left-entering callers91/1 and94/1 necessarily land on1 by their guards, so they also use equal read1 behavior.

Comparison checkpoints exclude old50. There are479 ordinary identical rows; old27/1 is invariant-impossible. Six exceptional schemas split the right-entering callers by their destination bit and handle the two left-entering callers. Old blocks have length2; new blocks length2 or4. All768 admissible 9-bit assignments pass.

## Candidate C: merge old171 into27

Delete171. Replace27/1 by1R202 and redirect150/0 to27. Leave27/0=0L32 unchanged.

The only old171 caller150/0 writes0 immediately to the left of its destination. A destination1 uses the same1R202 action in the old and new machines. A destination0 replaces old0R21 with the same three-step left0 detour through32 and45 as Candidate A. Original27/read1 is invariant-impossible.

Comparison checkpoints exclude old171. There are482 ordinary identical rows and two exceptional schemas, distinguished by the right-hand bit at150. Old blocks have length2; new blocks length2 or4. All256 admissible 9-bit assignments pass.

## From local identities to full-machine equivalence

For each candidate relate an old checkpoint configuration to a new one when the control is not the removed old state, the head and full tape are identical, and the old inductive invariant holds. The relation initially holds at95 for every head and binary tape.

At any related nonhalting configuration, the literal row classification gives either one identical transition or exactly one applicable exceptional block. The blocks cover every invariant-admissible assignment at each exceptional start. Their endpoints are equal in control, head and full tape and lie outside the removed control; the invariant holds there by old-machine induction. No exceptional path halts internally. Ordinary halting transitions are identical.

Every matched block has a positive length on both sides. Both lengths are uniformly bounded (at most2 old steps and at most4 new steps). Thus an infinite computation has infinitely many matched checkpoints on both sides, while a finite halting computation is matched to a finite halting computation. The three candidates therefore have the same halting behavior as combined243 from95 with arbitrary initial head and arbitrary binary tape. This is stronger than source-frame-only or blank-only equivalence. The invariant is asserted for old checkpoints, not for every intermediate new configuration: merged controls may intentionally serve a different intermediate role.

The exceptional verifier enumerates every assignment to offsets−4,…,4. It checks every read/write remains inside that footprint and compares entire local tape sets at the endpoints. Every exterior cell is untouched and unexamined, so the identities quantify over arbitrary two-way infinite tape exteriors. Translation supplies arbitrary initial head positions.

## Independent startup and runtime gates

A separate sparse interpreter reaches exactly the combined243 calibrated full blank frame for all three candidates:

- Candidate A:407,979 transitions
- Candidate B:408,291 transitions
- Candidate C:407,985 transitions

The frame has old dispatcher96, head−5, marker−6, header176, logical registers(3,0,0,0,3,0,0,0,0),167 spare blocks of value1 and351 one-cells, with all other cells zero. The times are actual simulations, not differences added to an earlier timing.

All candidates first passed25,170 new QT-source finite samples. A separate dense baseline cross-check verifies all expected full tapes, heads and affine durations over13,144,352 transitions. The candidate finite search uses a weaker safe-frame comparator; these finite screens are not the proof. The all-tape equivalence above transfers the independently validated combined243 behavior. A separate reviewer is also checking each candidate directly against the unchanged unbounded runtime contract and independently confirming startup; its artifacts are distinct from this local proof.

## Attribution and scope

The inherited calculus/program, verification and compiler remain credited to Mira-Cult, Jeff Ketchersid and Andrew James Wade; earlier source/routing/initialization work remains credited to ProveIt. The supplied combined243 artifact attributes the compensated fold and QT rotation to their respective incoming contributions and the combination to subsequent repository work. These three new local folds were found by the present compensated-overlay search; no unsupported personal author is inferred. Inherited licenses and source attributions should be preserved.

These results do not establish absolute consistency, unconditional nonhalting, minimality, a lower bound, internal PA calibration, or a new end-to-end proof-assistant consistency theorem. They establish the stated ordinary positive all-tape transfer for exact binary tables.
