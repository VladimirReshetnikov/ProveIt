# Binary-odometer initialization: proof, measurements, and scope

## Result and provenance

The smallest new output in this engineering lane is a **299-working-state,
two-symbol, blank-start compiler control**. It uses the existing 202-node
decoder and the entire inherited runtime, a new register-clock initializer,
the existing shared-dispatcher return technique, and an exact transition
quotient. The corresponding `nextproof = 2` control has **300 states**.
Neither number is a new ZFC-consistency record. The public 253-state machine
is smaller, and these new tables have no new kernel-checked arbitrary-runtime
or internal consistency theorem.

Source identities are ProveIt
`61e77836565f63582561f54745f633d50efd9c7d` and Jeff's upstream
`297ab8df7e5de329605c3875b4934643b371a5e3`. The original machine is Mira-Cult's,
its upstream verification is Jeff's, and the binary/register framework is
Andrew James Wade's. The public 253 reduction is attributed to mira-emmy,
at PR20 head `0d544f2a2e3c18f12278441a74b7879f31cbe856`.

The odometer, register-payload reuse, seed-2 finishing path, and one-sentinel
refinement were developed in this session. The final dispatcher-return
sharing follows the earlier source34 initializer technique; the exact
transition quotient is an ordinary standard finite-state quotient. No
claim of literature-wide originality for binary counters is intended.

## Tape convention

All machines have a two-way infinite tape initially zero, head at integer
coordinate zero, and a separately designated exit state. A register with
value `v` is encoded by `0 1^(v+1)`. The nine physical register positions
contain logical registers in the order

`[2,4,3,7,6,8,0,1,5]`.

Thus the logical `nextproof` register, number 0, is physical position 6.
At exit, for a head position `h` and gap `g`, the complete tape is:

* a marker 1 at `h-1`;
* zeros at positions `h` through `h+g-1`;
* a header 1 at `h+g`;
* the specified register blocks to its right;
* zero at every remaining integer position.

The PC is empty. For a register clock with `n>9`, the first nine blocks have
the specified logical meanings and the remaining `n-9` blocks are zero
spares. No arbitrary nonzero scratch marks remain. The checks compare the
entire finite support against this description, not just a bounded window.

## The common odometer invariant

Place a two-cell left sentinel `11` at coordinates `a,a+1`. To its right,
the counter consists of `n` pairs `0 b_i`, with the least significant bit
first. Initially every `b_i` is 1, so the value is `N=2^n-1`. The initial
left marker is at `a-2`, with one zero between it and the sentinel. An end
sentinel, encountered only in separator phase, bounds the counter on the
right.

At the beginning of successful iteration `j`, for `0 <= j < N`, the head
is on the low-bit separator, the counter value is `N-j`, the marker is at
`a-2-j`, all cells strictly between marker and left sentinel are zero, and
the fixed data to the right of the counter has not changed.

The transition pair `dec_sep/dec_bit` performs a usual binary decrement.
It changes each borrowed zero bit to one and the first one to zero. Let
`r=v_2(N-j)` be the number of borrowed bits. The `back_scan/back_test`
pair then returns left. Counter bits are separated by zeros, so the first
adjacent pair `11` encountered in this direction is exactly the left
sentinel. The next scan crosses the zero gap, erases the old marker,
writes a new marker one cell farther left, and returns to the low-bit
separator. This establishes the same invariant for `j+1`.

Every successful iteration moves the marker exactly one cell left. It
neither changes the fixed right-hand data nor leaves any additional mark.
After `N` such iterations the counter is zero. The next decrement borrows
through all `n` bits, makes every bit one, and reaches the right sentinel
in separator phase. That is the unique cleanup event.

This argument concerns every natural `n` in the declared constructor
domain, not only the tested values. It is an ordinary inductive proof,
not a supplied Lean or Coq proof object.

## Exact running time of the common loop

One successful iteration with index `j` and borrow count `r` takes

`4r + 2j + 12`

literal moves. The four portions have lengths `2r+2`, `2r+3`, `j+3`, and
`j+4`: decrement, return to the sentinel, move the marker, and return to
the low-bit separator. Since

`sum_{k=1}^{2^n-1} v_2(k) = 2^n-1-n = N-n`,

the total successful-loop time is exactly

`N^2 + 15N - 4n`.

The initial monotone writer takes one move per emitted cell; after it
writes the marker, three further moves reach the first counter separator.
The explicit cleanup counts below therefore give full blank-start times.

## Auxiliary-counter initializer

For arbitrary nine-register values of sum `S`, print the reversed desired
register payload, a right `11` sentinel, `n` counter pairs, the left `11`
sentinel, a zero, and the marker. On underflow erase both counter bits and
separators and the left sentinel, erase the first right-sentinel cell,
and keep the second as the final header. Return left to the marker.

The monotone seed has `S+24+2n` cells. The odometer and cleanup use 11
control states. The read-zero rows of `skip_sentinel` and `clean_bit`
serve as the first two seed writers, and the existing `place_marker`
state writes the final marker. During the arithmetic phase
`skip_sentinel` reads only the second left-sentinel 1 and `clean_bit`
reads only a counter or sentinel 1. Thus this sharing does not change
any arithmetic transition.

The complete contract is:

`states = S+32+2n`,

`gap = 2^n+2n+3`,

`moves = S+4^n+14*2^n+2n+17`.

The cleanup takes `4n+N+5` moves. Together with the seed, the three setup
moves, and the common-loop sum, this proves the displayed time formula.
The absolute final head is `-(18+S+gap)`.

For a required gap `D`, choosing the least permitted `n` gives
`S+O(log D)` states and time S+O(gap^2), which is quadratic in the resulting gap for fixed payload sum S. This improves
the growth order of the earlier counter/stride family, whose optimized
variable state cost is of square-root order in `D`. This is a comparison
of explicit constructor families, not a lower bound for arbitrary
initializers or a claim that logarithmic-state counting is new in general.

At `n=7`, the zero and seed-2 initializers have 46/48 states, gap 145,
and 18,207/18,209 moves. They produce the original 219-DAG controls of
332/334 states before exact quotient and before dispatcher sharing.

## Reusing the register payload as the counter

For a zero start, the nine register blocks are already copies of `01`.
They can themselves be the initially all-one binary counter. The
underflow pass restores every bit to one, hence restores exactly the
original zero-valued register blocks. No separate counter payload is
needed.

The initial two-sentinel version prints `2n+6` cells and has 12 control
states. Two known read-zero rows serve as seed writers and
`place_marker` again writes the final cell. Therefore, for `n>=9`,

`states = 2n+15`,

`gap = 2^n+1`,

`moves = 4^n+14*2^n+2n+1`.

Cleanup erases both right-sentinel ones, retains all counter pairs,
erases the first left-sentinel one, and retains the second as the
header. The cleanup length is `4n+N+7`. The absolute final head is
`-(2n+2+gap)`.

At `n=9`, this is a 33-state initializer, gap 513, and 269,331 moves.
The larger gap is permitted by the same inherited runtime interface.
The objective here is the complete state count, so overshooting a
required minimum gap is useful even though it increases running time.

## Seed 2 without two extra states

The same 33 states also initialize `nextproof=2` and all other logical
registers to zero. On underflow, retain the second right-sentinel one
and erase the first. Flip the separator immediately after physical
register 6 from zero to one. Locally, at `n=9`, the last three original
zero-register blocks and the right sentinel change from

`01 01 01 11`

to

`0111 01 01`.

This puts value 2 in physical position 6, hence in logical register 0.
All other physical values remain zero. For larger `n` the same edit
shifts the subsequent zero blocks by one position and leaves `n-9`
zero spare blocks.

No new control state is needed. The seed writer previously read only
zero on each new blank cell. Its read-one rows are therefore available
for a fixed return walk after underflow. For `k=n-7`, the finish path
uses seed states `2,4,...,2k`, then the read-zero row of state `2k+2`
to flip the separator, and the read-one row of state `2k+3` to enter
the finish scan. At `n=9` these are read-one states `2,4,7`, with the
existing read-zero row of seed state 6 performing the flip.

The finish scan starts strictly left of the newly formed run of three
ones, so it cannot mistake that run for the left sentinel. All
read-zero actions used during initial emission are unchanged. The
arithmetic phase never enters the seed states. These are the precise
guards justifying reuse of the read-one rows.

The seed-2 contract is the same state count and gap, with

`moves = 4^n+14*2^n+2n-1`.

It saves two cleanup moves. At `n=9` the exact time is 269,329 and
head is -533. The whole tape contains ones exactly at

`[-534,-20,-18,-16,-14,-12,-10,-8,-6,-5,-4,-2,0]`.

## One-sentinel refinement for the zero start

A zero start does not need the second right-sentinel cell: `dec_sep`
recognizes a one in separator phase, irrespective of the following cell.
Erase this one and immediately begin the leftward finish scan, retaining
all `n` counter pairs. This saves one emitted cell and two cleanup moves.

The implementation starts at the old second seed writer and reuses the
now-free read-zero row of `skip_sentinel` to absorb seed state 2. No
arithmetic read-one row is changed. The resulting contract is

`states = 2n+14`,

`gap = 2^n+1`,

`moves = 4^n+14*2^n+2n-2`.

The absolute head is `-(2n+1+gap)`. At `n=9`, there are 32 private
initializer states, 269,328 moves, and head -532. This exact zero frame
has no spare block and no terminal debris. This refinement is separate
from the seed-2 construction, which uses the extra terminal cell as
part of its payload.

## Sharing the final return with the runtime

The final initializer scan has rows `0 -> 0 L self`, `1 -> 1 R root`.
Instead, redirect its incoming initializer edges to existing runtime
state `e:2`, and remove the private scan state. The actual runtime rows
are checked to be:

* `e:2/read0 = 0 L e:2`, `e:2/read1 = 1 L e:4`;
* the nine read-zero states `4,6,9,13,19,29,41,58,74` proceed left,
  the last into `e:84`;
* `e:84/read0 = 0 R e:84`, `e:84/read1 = 1 R root`.

The first scan crosses the zero gap and retains the marker. There are
nine leftward moves through the known blank exterior, ten rightward
moves back across those blank cells, and one rightward marker move to
root. Relative to the private marker transition this adds exactly 20
moves, preserves every tape cell and the final head, and removes exactly
one private state. No inherited runtime row changes. The construction
requires this exact nine-state dispatcher; the script checks every
needed row rather than assuming it from a name or an old source.

This is an application of the prior source34 sharing technique. With
the new odometer, the final private costs are 31 for the refined zero
start and 32 for seed 2. Their exact times are 269,348 and 269,349.

## Exact transition quotient

The emitted table has a standard exact quotient merging the inherited
`b:1` and `e:5` states. They have identical actions after the quotient.
The independent certificate checker verifies a total map `h`, with
the start mapped to the start, working states mapped only to working
states, the terminal state mapped to terminal, and every row satisfying

`delta'(h(q),b) = (write, direction, h(next))`

whenever `delta(q,b)=(write,direction,next)`. Induction on the number of
steps gives the same whole tape and head after every corresponding
step. Terminal status is equivalent, so halting times and final scores
are identical on every input. This claim requires no empirical
invariant or symbolic register-box assumption.

The supplied Python checker verifies those finite equations after
independently parsing both literal tables. No new Lean certificate
instance is supplied. The quotient theorem itself is ordinary
mathematics and has an existing generic Lean counterpart in ProveIt.

## Final matched measurements

All entries below include the entire initializer and both binary rows
of every working state. Each raw table has one more state than its
listed exact quotient.

| Decoder input | Refined zero quotient | Seed-2 quotient |
|---|---:|---:|
| Original 219-node DAG | 316 | 317 |
| Source08 rebracketed 207-node DAG | 304 | 305 |
| Source19 rebracketed 206-node DAG | 303 | 304 |
| Existing 202-node decoder | **299** | **300** |

The comparison with the best previous source34 controls is matched on
the decoder202 input and initial register vector:

| Item | Prior zero | New zero | Prior seed 2 | New seed 2 |
|---|---:|---:|---:|---:|
| Raw states | 312 | 300 | 314 | 301 |
| Quotient states | 309 | 299 | 311 | 300 |
| Private initializer states | 43 | 31 | 45 | 32 |
| Gap | 41 | 513 | 41 | 513 |
| Blank initialization moves | 393 | 269,348 | 395 | 269,349 |

The prior numbers are recorded at the pinned ProveIt source path
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/34-k12-engineering-results-evidence.json`,
entries `decoder202_np0_contiguous_shared` and
`decoder202_np2_contiguous_shared`; the corresponding independent review
is `intake-152-source-34.md`, especially its initializer/quotient section.
The prior quotient hashes are
`9e9197bf37d8c7e403c680b6979d4bd32251996c9645337b3edc0f8553cc4b2c`
and `29f91aa9ea621816e6dc9576745200531be93b095fcb425627ecf4931f1b2862`.

The input202 data is
`20-complete-vendor-decoder255-data-candidate202.json` in the same data
directory. The source08/source19 inputs are respectively
`08-schema-machine-results-rebracketed_dag.json` and
`19-subst-engineering-artifacts-full_logic_best.dag.json`.
These decoder attributions and their earlier evidence are inherited;
they are not newly invented program equivalence theorems.

## Reproduction and verification boundary

The standalone initializer script checks 36 cases: auxiliary counters
`n=1..9` with three payloads, and each register-clock form for
`n=9,10,11`. It checks literal moves and the complete finite support.
Fourteen full integrations each passed all 8,391 inherited affine
instruction cases, for 117,474 case evaluations. Each integration also
preserved every named runtime row and ran its complete numeric blank
bootstrap. The shared-return versions then preserved those runtime
rows and gaps exactly, checked their complete new blank runs, and
received independently verified quotient certificates. The affine
checks were not needlessly repeated for a changed initializer with an
identical runtime and gap.

Run the cheap packaged verifier with the packaged data and machine
directories. To regenerate the full compiler controls, run:

```
python integrate_odometer.py --proveit /path/to/pinned/ProveIt --output /tmp/odometer-base
python share_odometer_exit.py --controls /tmp/odometer-base --output /tmp/odometer-shared
python integrate_odometer.py --proveit /path/to/pinned/ProveIt --output /tmp/odometer-refined --one-sentinel-only
python share_odometer_exit.py --controls /tmp/odometer-refined --output /tmp/odometer-refined-shared
```

The checkout is read-only and must be at the stated pin; all generated
tables are placed outside it. The direct initializer and quotient
tools use only Python's standard library. The full integrator reads
the existing pinned ProveIt backend and its attributed finite data.

The state savings are proved for these initializer constructions and
measured complete compiler controls. They do not establish a new
equiconsistent theory, a new complete calculus, a formalized compiler
simulation, an internal PA/ZFC proof for the emitted literal tables,
or any improvement to the public 253-state consistency machine.
