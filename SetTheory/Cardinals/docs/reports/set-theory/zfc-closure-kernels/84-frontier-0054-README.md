# Exact bounded detector synthesis

New work for this research package. search.py is the initial CNF encoding;
search_sym.py adds state-renaming symmetry, and search_shared.py permits
two already-counted caller states (old4 and old2) to be used during a call.
The original source bytes and recorded hashes are retained.

## Local interface

Start in fresh state0 with head0. All cases know a1 at+2 and a0 at+1.
Short cases k=0..7 have a first left1 at-k and zeros between it and+2.
Only [-k,2] may be read; return in old4 at head-k-1. The long case knows
zeros on[-7,1] and may read only[-7,2]; return in old84 with head in[-7,1]
(or exactly-8 with --exact). Restore every represented tape cell.
Cells outside the window are opaque. These are sufficient local contracts,
not a characterization of every valid full-machine reduction.

The shared template counts n fresh states plus fixed old4 and old2; these
fixed states may be used before the final boundary return. An n=7 solution
would therefore use nine active states locally, seven of them new.
The read-only seven-total-state theorem does not exclude that template.

## Results and reproduction

Install the optional dependency in an isolated environment:

    python3 -m venv .venv
    .venv/bin/pip install -r experiments/detector/requirements.txt

Then, from the package root:

    .venv/bin/python experiments/detector/search_sym.py --states 7 --steps 12 --seconds 120 --solver glucose42 --output /tmp/seven12.json
    .venv/bin/python experiments/detector/search_sym.py --states 8 --steps 8 --exact --seconds 25 --solver glucose42 --output /tmp/eight8.json
    .venv/bin/python experiments/detector/search_shared.py --states 8 --steps 8 --exact --seconds 25 --solver glucose42 --output /tmp/eight8shared.json

The first recorded run returned UNSAT (3,485 variables, 53,560 clauses).
There is no DRAT/LRAT proof artifact; this is a bounded solver report.
The eight-state controls returned SAT and their complete literal replays
passed. Running python3 code/verify.py independently replays both saved
controls without importing PySAT or the synthesis scripts.

Longer seven-state runs returned UNKNOWN or timed out. Exact options and
solver statistics are in each JSON. external-timeouts.json records two
additional CaDiCaL jobs terminated after 180 seconds. Do not report any
UNKNOWN as UNSAT. The scripts' built-in interruption works with glucose42;
CaDiCaL requires external process timeout because its PySAT interrupt is
unsupported.

The sources optionally recognize the original experiment's solver install
directory /tmp/zfc246-solvers when it exists. Otherwise they use ordinary
Python import resolution. No solver binary or installed environment is
included. A SAT model alone is not a valid sub246 full machine: integration,
the whole-frame runtime proof, and a separate blank bootstrap remain required.

## CNF audit

The proof-audit note reviews state/head uniqueness, read/write equations,
absorbing exits, opaque-read guards, restoration, and state-renaming symmetry.
That source review and finite positive controls are distinct from a certified
UNSAT proof or an unbounded impossibility theorem.
