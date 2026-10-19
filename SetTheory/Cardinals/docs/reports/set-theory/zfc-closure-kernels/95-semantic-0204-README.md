# A scanner failure on the edited machine's own blank run

`rejected-short-scanner-244.tm` is the literal baseline table with
`delta(41,0) = (0,L,58)` replaced by `(0,L,84)` and state 58 removed.
It has 244 working states, starts in original label 95, and halts at label 254.
It is a **rejected candidate**, not a claimed consistency machine.

Run from this folder:

```sh
python blank_scanner_audit.py --table ../../inputs/routing245-original-labels.tm --sites ../../inputs/routing245-sites-logical.json --shorten --output /tmp/scanner-replay.json
```

The first qualifying empty-pointer frame occurs at binary time 107,914. A
qualifying frame has gap at least 64 and pointer depth at most 51.
Its logical seed is `(4,3,0,0,3,0,0,0,0)`. After 259 correctly
simulated source steps, source leaf 6367, a decrement of zero register T at
path `1111000000`, exits with pointer `1111001`; the intended next pointer is
`111100001`. The step begins at binary time 346,939 and ends at 348,237.
All primary registers, spare blocks, head, and header agree at those proposed
exits. Exactly cells −1 and +1 differ.

The tool's first literal interpreter uses a set of one-cell coordinates; a
second, independent implementation replays the entire blank prefix using a
byte array and indexed transition rows. Their final state, head, and complete
tape agree exactly. The source interpreter computes pointer carry, break,
continue, and primitive register updates without importing inherited modules.

This disproves the intended one-source-instruction contract **at the next
qualifying dispatcher return** on an actual blank run. It does not prove
eventual halting inequivalence or rule out a later matching frame under some
different stuttering relation.

The baseline positive control is:

```sh
python blank_scanner_audit.py --table ../../inputs/routing245-original-labels.tm --sites ../../inputs/routing245-sites-logical.json --instructions 274 --output /tmp/baseline-replay.json
```

It checks 274 complete source steps through binary time 891,107, including a
second complete dense blank replay. `reachability.py` separately supplies
source-only reachability checks. Retained JSON contains exact checkpoint
tapes and witness data. The top-level verifier reconstructs the literal
mutation and requires the stated times and pointers.

The baseline source and table are inherited from the pinned ProveIt package;
the independent interpreters and actual-blank counterexample are new work.
See the top-level NOTICE and retained component licenses for attribution.
