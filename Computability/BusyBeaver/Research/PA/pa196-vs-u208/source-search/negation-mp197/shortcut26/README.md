# A second blank-start reader shortcut

Starting from the [shortcut101 machine](../shortcut101/README.md), make the
additional native transition change

```
26 1 1 R 42     ->     26 1 1 R 91
```

The resulting [native table](machine.native.tm) is still a **197-working-state**
experimental candidate, with native start 74 and halt 254. It preserves the
blank-start halting behavior of shortcut101 by the following independent
finite-invariant argument; neither this claim nor its connection to PA is
formalized inside PA.

Recompute the radius-six blank-window closure on the **first-shortcut table**,
not on the original combined table. It has 266,707 abstract state/windows and
can reach abstract halt. At native state 26 reading 1, its five-cell masks are
`5, 6, 7`: the two cells to the right of the head are both zero. Thus the old
three steps

```
26/1: write 1, move R, state 42
42/0: write 0, move R, state 13
13/0: write 0, move L, state 91
```

end with the same control, head and entire tape as the new single transition.
No intermediate state is halt. All other rows agree. Induction over matched
boundaries therefore gives equal blank-start halting behavior. The script
audits every closure successor, compares the complete projected closure to the
independent existing implementation, and checks the local macro on all three
admitted windows. This does not by itself establish a PA consistency
biconditional for either candidate.

The candidate reaches the exact original clean startup frame after 58,102
literal steps. The archive's symbolic checker passes all 4,641 branch cases
for 3,573 source sites. These are executable checks, not a kernel certificate.
All 197 working states remain graph reachable.

From the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/negation-mp197/shortcut26/replay.py --output /tmp/shortcut26-receipt.json --out-dir /tmp/shortcut26
```

The replay checks both shortcuts and their separate radius-six invariants,
rebuilds both tables byte for byte, and reproduces both symbolic/startup
checks. Its output matches [receipt.json](receipt.json). Python `-O` is not
supported because the inherited symbolic checker uses assertions. The output
directory contains both native tables with explicit start directives.

The separate U208-derived runtime checker also passes all 4,641 primitive
cases at the actual startup header gap 48, covering all 394 transition rows.
It checks arbitrary primary-register values and nonempty finite spare lists;
the deterministic summary is [runtime48-receipt.json](runtime48-receipt.json).
This is executable symbolic evidence, not an internal PA proof. After running
the [parent replay](../README.md) to produce `/tmp/negation-mp197/sites.json`
and the replay above, reproduce it from the repository root with:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/startup-preserving/check_runtime48.py --machine /tmp/shortcut26/machine-double-with-start.native.tm --sites /tmp/negation-mp197/sites.json --mapping Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/allocator-screen/legacy_mapping.json --output /tmp/shortcut26-runtime48 --expected-states 197
```

The generated `runtime.json` includes elapsed time and detailed block and
label maps; the retained receipt records the deterministic summary. Both runtime engines retain their original
licenses and attribution.
