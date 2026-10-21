# Scope and reproduction of the repair searches

These searches did not produce a calibrated machine with 217 states. They are
included to make the explored families concrete and to distinguish successful
initialized-frame verification from failed blank initialization.

The literal 217-state core in `data/core217.native.tm` has a complete unbounded
primitive-interface receipt elsewhere in this packet. The independent one-row
ray replay is also part of the main verification. Neither positive initialized
runtime nor a finite screen substitutes for a blank-start consistency theorem.

## Finite primitive cases

`code/prepare_cases.py` generates two complete finite assignments for each of
the 6,167 guarded K218 primitive interfaces: 12,334 cases in total. The first
uses all-zero primary registers, except value one for the tested positive
decrement, gap zero, and spares `[0]`. The second uses register values `i mod 3`,
with the tested decrement forced to zero or two, gap three, and spares
`[2,0,1]`. Every target includes the complete represented tape and head position.

The unchanged core passes these cases in 6,122,052 physical steps; the maximum
individual duration is 748. Passing the cases is a discovery filter, not an
unbounded proof.

The one-row screen allows 20,000 steps per primitive. The two-row screens allow
5,000 and also detect exact repeated configurations. Both use a finite tape
window, allowing head positions from -1022 through 7165. They reject wrong
complete-frame endpoints, incorrect halts, outward blank rays, and bound
exhaustion. A time or tape bound rejects a proposed implementation only within
this search; it does not prove that a slower implementation is impossible.

## Completed transition-mutation families

All row numbers are native labels. The table has 217 working states despite
gaps in those labels. Each replacement action chooses a write bit, left or
right motion, and an existing working target or the original halt target.

| Family | Actions or pairs examined | Pass the first selected case | Pass all finite cases |
| --- | ---: | ---: | ---: |
| One row on the original start-0 prefix | 37,453 | Not separately counted | 50 |
| One row on any original blank-start prefix | 199,459 | Not separately counted | 252 |
| Core two-row repair, first row `36/0` | 39,757,666 | 368,377 | 0 |
| Core two-row repair, first row `51/0` | 39,647,920 | 394,157 | 0 |
| Subset with `51/0` fixed to `0 R 16` | 33,098 | 482 | 0 |
| Marker-relay repair, first row `103/0` | 63,696,230 | 131,032 | 0 |
| Marker-relay CC2 bridge using one helper | 216 | Not separately counted | 0 |

The restored-51 subset is included in the larger 51-row family; its count
should not be added when reporting distinct pairs.

The one-row family uses the 229 rows visited from some original working initial
state. If a one-row mutation changes none of those rows, all original blank
trajectories remain identical. The 252 finite survivors are retained in
`data/one-row-survivors.txt`. All 217 initial states of each survivor reach
exact outward blank rays. The separate Python replay verifies all 54,684
witnesses, totaling 459,639 finite transitions, followed by an induction on the
blank half-line. This particular negative result is unbounded.

For a two-row family, the first action is chosen freely on the named primary
row. The first failing finite case supplies a necessary set of second-row
choices: a repair must change a row encountered before the recorded failure.
The search tries every allowed action on those rows and then tests all affected
cases. Cases whose original trajectories touch neither changed row remain
identical. For the already-invalid marker relay, every initially failing case
is also included. These restrictions and the finite bounds define the searched
family; they do not establish a lower bound on all two-row repairs.

The bridge family sets `108/1 = 0 L q` and `q/0 = 0 L 122`. In the intended CC2
context the intermediate cell is known zero. It tries all 216 eligible existing
helpers `q`; the first failing interface for each is retained in
`evidence/searches/relay217-bridge-rejections.txt`.

## Source rotations and blank startup

The rotation search changes both a binary source association and its four
physical decoder rows. A rotation

```text
((A,B),C) <-> (A,(B,C))
```

requires that A has no escaping break and C has no escaping continue. A break
escaping B still exits after the same whole fragment, and a continue escaping
B still returns to its beginning. The prospective physical states have
bit-preserving right-moving rows; the rotated child has its unique incoming
edge from the rotating parent.

`--active-start0` requires every rotation to touch a transition row on the
current blank run from state zero. Other rotations may be needed to enable a
later useful one, so the unrestricted search omits this condition. Every
visited layout is tested using all 217 possible working initial states.
Previously established outward rays are reused when the changed rows do not
occur on their finite prefix or their ray transition.

The bootstrap test recognizes complete unary register frames at any source
PC, including internal source ordinals. It has a 300,000-step limit. It can
terminate earlier on a literal halt or an exact outward blank ray. The original
receipts retain counts and the absence of a frame, but not an aggregate census
separating those early outcomes from bound exhaustion. Consequently the
rotation results are reported as finite bootstrap searches; they are not
claimed to provide individual infinite-ray certificates for every layout.

Before a frame would be promoted to a hit, the driver rechecks the complete
decoder-role relation, the primitive word, and the guarded ordinal control-flow
graph. Intermediate search layouts are allowed to fail that decoder check.
Even a reported frame hit would still require a full unbounded runtime check
and an admissible-seed argument. No frame hit was found.

| Seed and search | Distinct layouts | Required blank tests | Coverage |
| --- | ---: | ---: | --- |
| Primary core, active prefix, depth 4 | 75 | 1,104 | Complete within this family |
| Primary core, unrestricted, depth 3 | 45,440 | 716,955 | Complete within this family |
| Primary core, active prefix, depth 16 | 28,704 | 433,029 | Stopped after 240 seconds |
| Composed source and row157, active prefix, depth 12 | 15,456 | 218,964 | Stopped after 150 seconds |
| Zero-terminal source, active prefix, depth 8 | 4,241 | 62,324 | Complete within this family |
| Retagged source, active prefix, depth 8 | 4,241 | 62,324 | Complete within this family |
| Composed source, active prefix, depth 8 | 4,241 | 62,324 | Complete within this family |

The primary depth-16 run deduplicated by physical table alone. Subsequent runs
also include the source tree. The portable driver provides
`--table-only-dedup` for the former convention. Time-limited counts vary with
hardware; they are snapshots of completed work rather than exhaustive counts.
Counts across families overlap and must not be added as distinct constructions.

The timed composed-row157 search reached a layout with nine live ones at the
end of a 248-step prefix. A fresh full decoder-prefix check rejects that layout.
It is not a candidate or a valid source allocation. The other listed searches
have maximum final support eight.

## Reproduction commands

Run these commands from the extracted packet directory. The generated finite
cases are about several megabytes and are reconstructed instead of duplicated
in the archive. The C++ searches require a C++20 compiler. Their output prefix
should be fresh because their ordinary file streams overwrite existing files.

```sh
python code/prepare_cases.py --output /tmp/zfc217-finite-cases

g++ -O3 -std=c++20 code/search_boot.cpp -o /tmp/zfc217-one-row
/tmp/zfc217-one-row data/core217.native.tm \
  /tmp/zfc217-finite-cases/cases.txt /tmp/zfc217-one-row-result 1

g++ -O3 -std=c++20 code/search_two.cpp -o /tmp/zfc217-two-row
/tmp/zfc217-two-row data/core217.native.tm \
  /tmp/zfc217-finite-cases/cases.txt /tmp/zfc217-finite-cases/source.txt \
  72 /tmp/zfc217-two-row36-result 1

/tmp/zfc217-two-row data/core217.native.tm \
  /tmp/zfc217-finite-cases/cases.txt /tmp/zfc217-finite-cases/source.txt \
  102 /tmp/zfc217-two-row51-result 1

g++ -O3 -std=c++20 code/search_two_restore51.cpp -o /tmp/zfc217-restore51
/tmp/zfc217-restore51 data/core217.native.tm \
  /tmp/zfc217-finite-cases/cases.txt /tmp/zfc217-finite-cases/source.txt \
  102 /tmp/zfc217-restore51-result 1

g++ -O3 -std=c++20 code/search_relay.cpp -o /tmp/zfc217-relay
/tmp/zfc217-relay data/relay217-failed.native.tm \
  /tmp/zfc217-finite-cases/cases.txt /tmp/zfc217-finite-cases/source.txt \
  206 /tmp/zfc217-relay103-result 0

g++ -O3 -std=c++20 code/search_cc2_bridge.cpp -o /tmp/zfc217-bridge
/tmp/zfc217-bridge data/relay217-failed.native.tm \
  /tmp/zfc217-finite-cases/cases.txt /tmp/zfc217-finite-cases/source.txt

python code/rotation_boot_search.py --active-start0 --depth 4 \
  --seconds 120 --output /tmp/zfc217-rotation-active4

python code/rotation_boot_search.py --depth 3 \
  --seconds 600 --output /tmp/zfc217-rotation-unrestricted3

python code/rotation_boot_search.py --active-start0 --depth 12 \
  --seconds 150 \
  --table data/composed-row157-core217.native.tm \
  --sites data/composed-sites.json \
  --output /tmp/zfc217-rotation-composed157
```

The integer row key in the C++ programs is `2*state + read_bit`. Output JSON
from the portable rotation driver additionally records the input hashes and
the current driver hash. The supplied historical receipts retain their
original fields and have not been rewritten to imply a fresh execution of the
portable adaptation.
