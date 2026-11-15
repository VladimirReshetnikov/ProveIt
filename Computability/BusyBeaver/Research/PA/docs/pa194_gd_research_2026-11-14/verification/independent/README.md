# Independent verification of the new GD family

All requested gates passed. The delivery names are **PA194GD**, **PA194GDH**,
and **PA194GDHS**. Frozen verification directory names are respectively
`GD194sum`, `GD194H`, and `GD194HS`; `delivery_names.json` binds the aliases
to exact table hashes.

| Delivery name | Source sites | Branch outcomes | Independent symbolic operations | Maximum per outcome | Blank startup |
|---|---:|---:|---:|---:|---:|
| PA194GD | 3,654 | 4,755 | 1,068,318 | 379 | 58,154 |
| PA194GDH | 3,653 | 4,754 | 1,091,812 | 385 | 57,922 |
| PA194GDHS | 3,650 | 4,750 | 1,095,734 | 385 | 57,768 |

Every table has 194 working states, 388 transitions, binary alphabet, all-zero
two-way infinite initial tape, start 0, head 0, and separate halt 194. Native
tables start at 74 and halt at 254. The dense/native conjugacy was checked
directly, and all working states are reachable in the transition graph.

## What was independently checked

The literal checker imports neither the construction compiler nor an
arithmetic-box oracle. It rederives four unary/list-sweep induction lemmas
from each literal table, checks the source graph using two independently
implemented address resolvers, and checks every primitive source branch.
The symbolic domain includes nine arbitrary natural primary registers,
both branches of decrement, an arbitrary nonempty finite spare-register
list, an arbitrary nonnegative extra header gap, and complete blank tape
exteriors. These are symbolic universal contracts, not bounded sampling of
register values.

The closure audit found each source branch exactly once. All thirteen
coefficients of every affine duration are nonnegative; every duration has
constant at least three. All nonhalting outcomes have zero affine head
motion. Each machine has exactly one halting source outcome, of duration
three. All 388 literal rows occur in the symbolic cases.

The independent startup checker uses an unbounded integer-coordinate set
of one-cells. It checks the entire finite support of the final tape against
the source frame, including the exact source address, logical seed
`(2,0,...,0)`, physical register permutation, and 26 spare one-registers.
It does not use a window match. The inherited symbolic checker separately
checks the same full startup using a bounded array whose head bounds are
checked throughout the run.

Exact complete tuples establish that all three new graphs are different
from all 139 spanning 194-state graph classes in the current pinned corpus
and from one another. The comparison allows arbitrary state renaming, any
spanning root, reflection, bit exchange, and terminal-action erasure. Bit
exchange is only a structural screen and is not asserted to preserve the
zero-blank initial condition.

Ordinary control bisimulation leaves all 194 states distinct in each new
table. This excludes a direct context-free control quotient for these
tables, not a context-sensitive transformation or a different design.

All original frozen input bytes remained unchanged. Fresh receipts and
contracts are in `inputs/<verification-name>/independent/`; the complete
run transcript is `literal_replay.log`. `verification_summary.json`
collects the identities and results.

## Offline replay

Use Python 3.10 or newer with assertions enabled. From this directory:

```sh
python3 -B literal/check.py inputs/GD194sum inputs/GD194H inputs/GD194HS
python3 -B check_startups.py
python3 -B audit_closure.py
python3 -B check_novelty.py
```

The last command resolves the package root's `comparison/census_tables.py`
and `comparison/frontier194/` relative to this script. Its `--frontier`, `--machines`, and `--output` options
can select alternative input/output locations. The literal checker writes
only an `independent/` directory under each frozen machine copy. Complete
universal replay can take several minutes.

### Commands from the package root

The short checks and retained-frontier comparison are also callable from
the package root:

```sh
python3 -B verification/independent/check_startups.py
python3 -B verification/independent/audit_closure.py
python3 -B verification/independent/check_novelty.py
```

To regenerate the exact reported repository census, supply its 718 tracked
PA `.tm` files and six pending ZIPs. The recursive ZIP count concerns those
pending archives and their nested payloads. The following example selects
the corresponding input scope from a clean checkout of the pinned revision:

```sh
python3 -B - <<'PY'
from pathlib import Path
import json, subprocess, sys
repo = Path('/path/to/pinned/ProveIt')
tables = sorted((repo / 'Computability/BusyBeaver/Research/PA').rglob('*.tm'))
archives = json.loads(Path('comparison/archive_provenance.json').read_text())['archives']
inputs = tables + [repo / 'docs/incoming' / item['archive'] for item in archives]
assert len(tables) == 718 and len(archives) == 6
subprocess.run([sys.executable, '-B', 'comparison/census_tables.py',
                '--output', '/tmp/pa194-census', *map(str, inputs)], check=True)
PY
```

The six historical U209/U212 ZIP files already filed inside the PA tree are
outside that recursive pending-archive count. Their paths remain repository
provenance, while all 139 comparison representatives required by the new
machines' offline novelty check are included in this package.

## Proof boundary and attribution

These checks bind the exact literal machines to the displayed source
instructions and establish their operational certificates. The new command
algebra and the inherited PA/iPRA calibration are separate mathematical
arguments. A successful Python replay is not a completed end-to-end Lean
or Rocq theorem.

`literal/PROVENANCE.json` pins the unmodified checker and helper files to
the incoming loop-continuation archive at revision
`8d31445d858761a8f6150c2e5012adae8895e932`; its retained license files
remain under `literal/vendor/`. New independent startup, closure,
structural-census and comparison code is supplied beside those inherited
components.
