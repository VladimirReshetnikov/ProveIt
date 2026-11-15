# Focused smaller-header feasibility check

This appendix examines the new PA194JH5X source, whose maximum binary source
address length is 34. It supplies no 193-state blank-start consistency machine
and no universal state lower bound.

## Results

The existing 194-state table satisfies all 4,794 literal source outcomes when
the minimum header length is reduced from 48 to 36, using 1,097,281 symbolic
steps. The transferred Runtime193 core satisfies all 4,794 at 36 as well,
using 1,097,601 symbolic steps. All 194 controls of the original table occur
in the source contracts: there is no control used only during initialization
under these universal contracts. A compact 20-case selection replays that fact.
The additional source-closure check verifies all 4,793 live outcomes against
the actual instruction successors after padding to 36; every computed address
has length at most 34 and no address overflows.

The physical table and its accepted blank initialization have not changed.
The complete 57,922-step startup still creates a 48-cell header. It is simply
represented by gap 12 under the 36-cell convention. Header length is a tape
parameter; changing its minimum does not itself delete a control.

At headers 34 and 35 the retained symbolic checker stops on its first selected
longest-path increment case, because an additional interpreter read needs a
known zero. These are recorded as NOT_CERTIFIED, not as counterexamples or
proof that a different case-splitting checker could not establish a contract.

For the fixed Runtime193 core, all 193 choices of blank start control are
classified by exact finite traces: 2 reach halt and 191 reach an escaping
self-loop ray, in at most 93 transitions. Its designated native start 74
reaches its ray after 92 transitions. Across all starts there are only 10
visits to boundary control 84, each with at most 4 one cells. Any complete
canonical frame, at any source site and any nonnegative header length,
requires at least 12 ones: two markers and at least 10 unary blocks (nine
work registers plus a nonempty spare list). Hence none of those visits can
be a canonical frame. The terminal rays never return to 84. This obstruction
is independent of header capacity and does not use a simulation time cutoff.

Thus smaller padding validates an additional runtime convention but does not
repair the fixed core's initialization. A 193-state construction would need
further transition changes or another representation/startup argument.
Arbitrary bootstrap changes and other 193-state constructions are not excluded.

## Reproduce

From the physical-runtime packet root, a quick independent replay of every
finite rejection trace is:

```sh
python3 -B header_feasibility/replay_traces.py header_feasibility
```

Recompute the exact startup, all fixed-core blank classifications, and 20
universal source-usage witnesses with Python's standard library:

```sh
python3 -B code/header_screen.py inputs/PA194JH5X --checker literal_checker --usage-witness header_feasibility/source_usage_witness.json --output /tmp/pa194-header-quick
```

Rerun all 4,794 outcomes for both the 194-state table and transferred core
with the full literal sweep:

```sh
python3 -B code/header_screen.py inputs/PA194JH5X --checker literal_checker --usage-witness header_feasibility/source_usage_witness.json --output /tmp/pa194-header36 --literal-header 36
```

Runs at 34 or 35 reproduce the explicitly uncertified attempts. Assertions
must remain enabled. The full source sweep took approximately 142 seconds
combined in the recorded environment; all counts, clocks, and table hashes
are recorded separately from elapsed wall time.
