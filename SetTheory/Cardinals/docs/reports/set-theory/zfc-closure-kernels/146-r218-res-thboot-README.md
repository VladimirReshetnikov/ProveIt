# Bootstrap investigations for the provisional 218 table

These files are exploratory. They do **not** establish a blank-starting
218-state machine. The table under investigation is
`root218/candidate218/candidate.tm`, SHA256
`cd2e25ad8bd58112b74d671ff78334eacc0eb237201b32c871a73424e134073f`.

## Fixed two-row repair screen

`repair_122_137.cpp` tests all 760,384 replacements of rows `(122,0)` and
`(137,0)`, retaining the provisional table's other rows. Each replacement
is checked against 191 radius-seven postinitialization windows: at most
128 candidate steps must join one of the first 40 configurations of the
reference trace before leaving the represented window. Only the
unchanged pair passes these finite sufficient conditions. The receipt
does not prove that every possible two-row repair is impossible.

## Reparameterizing the spare list

Every nonempty finite list can be written as an arbitrary finite prefix
followed by one arbitrary final element. Thus the universal runtime
checker's original "first spare plus arbitrary tail" parameterization
can equivalently be changed to "arbitrary prefix plus last spare".
`spare_last_contract.py` makes this change using the same checked unary
block traversals and finite-list word identity. This permits a target
contract in which a CI instruction increases the final spare value,
rather than appending a new spare.

At the local CI tail, replacing `(94,0)` by the following rows has the
indicated effect:

| Replacement | Local effect on the nonempty spare list |
| --- | --- |
| `0 L 40` | Preserve it |
| `1 L 40` | Increase its final value by one |
| `1 R 198` | Increase its final value by two |
| `1 R 66` | Increase its final value by three |

The last replacement passes the selected arbitrary-natural CI interface
for each of the nine register choices. These are **selected CI interface
proofs only**. The same row also participates in the shared decoder, and
the complete source-wide check fails at its first CD8 interface.

This failure has a concrete witness, so it is not merely an unsupported
symbolic proof step. With source address `000`, all nine logical registers
zero, gap 12, and spare list `[3,4,5]`, the `1 R 66` replacement returns
source address `01`, logical registers
`[0,0,2,0,0,0,3,0,0]`, and spare list `[4,5]`. Correct CD8-zero execution
leaves every register and spare unchanged. The diagnostic is retained
in `spare_alternative_global_check.json`.

The four replacements also fail blank initialization by simple outward
ray loops at steps 37, 45, 183, and 91, respectively. Consequently none
is an accepted repair. The equivalent spare-list parameterization may
still be useful at a tail gate separately proved to have no decoder role.

## The two-spare proposal

The ordinary tail writes a separator and two ones via states 94, 66,
and 198. To append two zero-valued spares directly, it would naturally
write `0101`. After changing `(198,0)` to write the second separator and
move right, the next row would need to write one and move left into
state 54. No existing row on zero has action `1 L 54`. Re-entering 94 or
198 on successive fresh zero cells repeats the tail without a terminating
phase. The alternative one-writing rows at states 16 and 97 enter
different return procedures; they do not directly establish the required
arbitrary-list CI contract. This is a structural observation about this
simple proposal, not an impossibility theorem for more extensive repairs.

## Other files

`clean_blank_screen.cpp` recognizes the generalized clean logical seed
family proved independently in `source218/general_seed_lemma.md`. It is
a finite discovery simulator, not an unbounded runtime proof. The older
`start_state_screen.cpp` used the stricter published seed and was not
used to claim completeness for the generalized family.

All complete logical research notes remain frozen separately in
`theory218/` and `theory_notes/`. The present bootstrap experiments do
not change their claims or calibrate a modified calculus.

## Fixed power-of-two scheduling and loader redesigns

`residue_scheduler.tex` is an include-ready mathematical section. For
the inherited uniformly successful family

    N_U = P(3,P(1,P(1,P(U,R)))),
    P(a,b) = (a+b)(a+b+1)/2 + b,

it proves that `F(t)=N_(U0+16t)` satisfies
`v2(F(t)-F(s))=v2(t-s)` for every `s<t`. Hence `F` induces a permutation
modulo every fixed power of two. Every residue class contains cofinally
many successful candidates, which validates a sound enumerator that
eventually visits one fixed arithmetic progression of stride `2^k`.
An increment on every variable-length command run is outside this theorem.

`certify_residue_schedule.py` checks the two exact polynomial identities
used in the proof and a finite arithmetic regression. The all-natural
result is the written mathematical argument. Its retained receipt is
`residue_lemma_receipt.json`.

Six exact source variants and their protected-row cost receipts are
retained in `load_after_body`, `leading_wrapper`, `shared_restore`,
`stride2`, `rotated_restore`, and `rotated_restore_ci`.
`recheck_scheduler_artifacts.py` independently reconstructs their source
shapes and metrics. It also replays the short blank prefixes of the
retained literal tables and proves their outward self-loops. The
resulting `scheduler_probe_report.json` records the cost-screen scope;
none of these tables is an accepted blank-starting machine.

The trailing `CD0` placement issue is recorded in
`new_loader_entries.json` and `trailing10_counterexample.json`.
The portable finite replay is:

    python replay_loader_entry_screen.py --table /path/to/k219.native.tm

It tests 876 single-row actions at each of the two specified addresses,
with a 12,000-step positive-input filter. The sole surviving action for
`CD0` at address `11110` fails a concrete zero-register case at step 160.
This is a bounded, fixed-table entry census, not a proof that every
possible alternate primitive implementation is impossible.

The `0<->8` register transport is retained in `np_pl_swap`. Its 218-state
literal table reaches an outward ray loop at step 90. This negative
startup result is independently replayed by the scheduler checker.
