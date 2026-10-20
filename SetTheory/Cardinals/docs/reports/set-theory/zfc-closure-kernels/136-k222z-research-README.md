# Supplementary machine-level searches

These files record completed bounded searches around the incoming G223 machine
and the new conditional-G222 machine. No 221-state survivor was found in these
families. This is not a minimality claim.

The primary 222-state construction does not depend on these negative searches.
See `search_receipt.json` for exact counts, baseline hashes and limitations.

## Reproduction

The C++ programs require a C++17 compiler. The supplied baseline arguments must
be the **native K-label** tables, with start state 0 and halt state 254.
Canonical dense tables use a different halt label and cannot be substituted.

```
python3 reproduce_searches.py \
    --gc222 /path/to/candidate222.k.tm \
    --g223 /path/to/candidate223.k.tm \
    --output /path/to/new-search-output
```

The G223 argument is optional. Omitting it reproduces only the searches on the
new 222-state table. The script pins the supplied table bytes to the receipt.
It compiles each program in the output directory and reruns the completed
scopes. Depending on the host, a two-helper scope takes a few minutes.

Adding `--finite-fixture` replays a further completed search on the supplied
`finite_GC222.txt` fixture. That fixture contains 25,806 windows observed over
17,868 finite source frames, 9,128,832 transitions, and the exact blank startup.
It is strictly discovery data, not a universal invariant certificate. No
candidate survived that search either. Its complete parameters and hash are
in the receipt, and its search output is retained separately.

`neutral.cpp` enumerates alternative transition rows that meet a bounded local
positive-block simulation test. `two_helpers.cpp` first considers ordinary
folds and one neutral helper, then combines two distinct neutral helpers when
each individually repairs one partial retained row. This last restriction is
part of the search family: the program is not exhaustive over arbitrary pairs
of helper changes.

`halting_folds.cpp` permits a terminal endpoint to have a different head
position and tape contents, as those do not affect halting equivalence.

The all-tape domains are finite window overapproximations obtained by starting
with every window at state 0 and propagating arbitrary incoming exterior bits.
They are sound for discovering sufficient local simulations, but may contain
configurations that the proof-search computation never reaches.

## Independent inspection of the successful folds

In the 224-state compiled parent, the only incoming transition to native state
159 is `152 0 0 L 159`. Thus entry to 159 puts a zero immediately to the right
of the head. The only incoming transition to 118 is `159 1 1 R 118`, so every
old entry to 118 reads zero. Both statements hold from start state 0 on every
binary initial tape.

Consequently the unused old row `118 1 1 R 173` may be replaced by
`118 1 1 R 153`. State 303 then has exactly the two rows of 118 and can be
merged into it. After this redirection, state 302 has exactly the rows of 159
and can be merged into that state. The only other retained-row change is
`224 0 0 R 302` becoming `224 0 0 R 159`.

This yields a direct one-step simulation under the map
`303 -> 118`, `302 -> 159`, with all other states fixed. Tape, head position,
start state and halt state are preserved. The old invariants are used only
to justify the old transitions; they are not asserted for the final machine.
Indeed, the final machine intentionally permits entries that invalidate them.

## Provenance

The C++ search programs adapt Source 127's retained helper-screen programs in
ProveIt commit `6ab3e41e4dcddfbd7f843bdf4be48ae5c7ba2430`, under
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/`.
The changes to `neutral.cpp` and `two_helpers.cpp` select native start state 0
instead of inherited label 95. The terminal-relaxed program is copied without
behavioral changes. Original project attribution and licensing remain in force.
