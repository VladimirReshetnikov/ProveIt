# Runtime193 startup corroboration

This folder contains the exact inputs, program, original log and empty hit
file for the fresh experiment counted in the main report. It corroborates
an existing negative search family; it is not claimed as a new reduction.

The supplied Runtime193 table was tested after each of **58,485 pairs of
candidate rewrites on distinct transition rows**, with **all 193 existing
controls** as the blank starting control for every pair:

| Recorded quantity | Value |
|---|---:|
| Supplied candidate row rewrites | 346 |
| Distinct-row pairs | 58,485 |
| Blank-start simulations | 11,287,605 |
| Literal transitions executed | 2,173,634,233 |
| Halting runs | 117,274 |
| Certified outward blank rays | 11,159,792 |
| Runs stopped at a bound | 10,539 |
| Complete physical source frames found | **0** |

Each simulation has a 200,000-transition bound, an absolute head-position
bound of 20,000, and a finite-support-size bound of 20,000. A bounded run is
not certified divergent. Outward rays follow a cycle of zero-reading rows
all moving in the same direction, strictly beyond the finite support.

The detector requires the **whole** finite tape to be a valid source frame
at native dispatcher 84, at one of source sites 25 through 44. It permits
any tape translation, padding at least 48, arbitrary values of all nine
working registers, and an arbitrary nonempty finite spare list. It checks
the marker, complete source path, register delimiters, and blank exteriors.
The zero-hit result therefore does not rely on a restrictive proof-store
seed, or merely on observing a particular control label.

The supplied 346-entry pool includes speculative arithmetic-box edits.
Neither individual runtime neutrality of every entry nor neutrality of
their simultaneous combinations is assumed. No complete frame was found;
no candidate was promoted as a consistency machine. This does not exclude
other edits, longer starts, or other 193-state constructions.

## Reproduce

Python 3 and a C++17 compiler suffice. No repository checkout or other
research packet is needed:

```sh
python3 replay.py --output /tmp/runtime193-startup-replay
```

The script verifies input hashes and the exact TSV derivation from the
supplied JSONL pool, compiles the included program, and repeats the screen
without overwriting these recorded logs. `receipt.json` contains all bounds
and the original totals. `PROVENANCE.json` gives the pinned repository
paths, verified Git blob identities, SHA-256 hashes, and attribution.
Original runtime license notices are retained in the enclosing archive's
`licenses/` directory.
