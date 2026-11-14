# Head-displaced control identification

These are new, completed searches on eight 194-state tables. They found no
193-state construction. `summary.json` records 308,049 admissible
pair/displacement instances, 449,943,424 single-row proposals, 4,473,267
joint two-row combinations, and zero survivors.

## Search model

Identify a removed control `a` with retained control `b`, representing the
old head by a new head displaced by `delta` in `{-2,0,2}`, with the tape
unchanged. Every unchanged entering move `d` must satisfy
`d + delta in {-1,1}`. The two retained transition rows are synthesized
jointly, including all write bits, directions and retained targets (or halt).
A simulated step may revisit the retained state. It must reach the exact
projected old endpoint in 1 through 160 transitions without leaving the
radius-six window. Terminal tape and move decorations are ignored.

The 23 arithmetic-box controls and source dispatcher 84 are protected.
Source contexts range over arbitrary nine-register canonical frames,
both decrement branches, nonempty spare lists, and the interiors of
accelerated constant-symbol scans. The collector deliberately overapproximates
stream correlations. The search adds every context in an exact 100,000-step
blank run. Any control without a collected context receives all 8,192 windows.

This is a finite local synthesis model. Its negative result does not exclude
wider windows, different representations, changes inside the arithmetic
engine, two or more simultaneous removals, or a different source algorithm.
It does not prove 194 minimal. In particular, a finite nonhalting prefix is
used to add rejection contexts, never as proof of eventual nonhalting.

## Reproduce

Python 3.10+ and a C++17 compiler are sufficient. From the archive root:

```sh
python3 -B search/offset/replay.py --family all --output /tmp/pa194-offset
```

This regenerates source contexts, checks their exact byte identities,
compiles the search, and compares integer counters and survivor records
with the frozen observations. Timings are not acceptance criteria.
Use `--family primary`, `four_l`, `ax11h`, `generalizer`, `ax11qh`,
`ax11s`, `ax11g`, or `gh` for one family. `--recorded-contexts` skips only
context regeneration.

The separate positive control has two redundant states and all 32
radius-two bit patterns. It yields the expected one-state quotient:

```sh
g++ -O3 -std=c++17 search/offset/search.cpp -o /tmp/offset-search
/tmp/offset-search search/offset/positive_control/redundant.tm search/offset/positive_control/patterns.tsv 2 16 0 100
```

`inputs/` contains the exact table and source inputs for each run;
`recorded/` contains context envelopes, receipts, and the empty survivor
files. `PROVENANCE.json` identifies the imported symbolic engine and
hashes every input. License notices are in `licenses/`.
