# Alternative conditional/G 222-state candidate

This is a second, distinct 222-working-state binary machine. The primary
result of the packet is the seed/G machine one level above this directory.
This alternative starts from the published conditional-K223 source at
ProveIt commit `6ab3e41e4dcddfbd7f843bdf4be48ae5c7ba2430`, replaces its
independent equality row by G, and deletes the separate equality helper
from its gated bundle.

The canonical table is `results/candidate222.tm`, with start 0, working
states 0 through 221, separate halt 222, and 444 transition rows. It uses
one two-way infinite zero-filled tape, two symbols, and only left/right
moves. Its SHA-256 is

    60e21a040e58e2a2840b0f3d58ad3ee0e6ef4d0d5cdf1372d5a69355f1198ca1

The source has 4,581 primitive occurrences, 209 total distinct subtrees
(186 compound plus 23 primitive), and maximum zero run six. Thirteen
contextual source aliases give 173 decoder states, plus 49 engine states.
The intermediate parent has 224 states. The two exact all-tape folds are
K135 into K118, then K116 into K159. Their proofs are recorded in
`results/folds.json`; the literal before and after tables are also retained.

## Reproduce

From the main packet's `portable` directory, with Python 3.10 or later:

    python3 -B alternative/reproduce.py --output-dir /tmp/conditional222-quick
    python3 -B alternative/reproduce.py --full --output-dir /tmp/conditional222-full

Use an empty output directory outside this alternative directory. The
default reconstructs the source and tables, proves both folds, independently
checks the exact numerical emitter against nine pinned arbitrary-register
macro contracts, checks both complete guarded-CFG resolvers, executes the
complete blank bootstrap, and audits retained full runtime coverage.
`--full` additionally rederives all 5,956 unbounded runtime cases. It uses
the shared `../runtime` modules and unchanged `../vendor/K224_Construction_2026-10-20.zip`;
there is no network access or additional package dependency.

The fresh development runtime proved every case and covered every one of
the 444 rows, using 1,443,614 symbolic proof steps. Every instruction has
positive finite duration, with minimum 13 concrete steps. Startup reached
the exact expected frame after 409,835 transitions; a second dense-tape
implementation independently confirmed it. The complete frame is recorded
in `results/bootstrap222.json`.

## Theory boundary

Write Kc for the exact previously emitted conditional core, RV for the
membership-vacuity formula, and Heq for the old canonical equality helper.
The old bundle was `not (Kc -> (RV -> not Heq))`; the new bundle is
`not (Kc -> not RV)`. The replacement row is

    G(a,b,c) = Eq(c,a) -> (Eq(c,b) -> Q_RelCode(a,b) Eq(a,b)).

The generic G proof in the primary packet is independent of the K core.
It derives the literal old equality row and Heq without assuming either,
and the old row plus Heq derives G. Boolean projection and recombination
of the displayed bundles therefore give equality of all native theorem
sets with the published conditional-K223 calculus. The successful gate
remains `c != a,b`; the G row remains ungated.

The exact source binder verifies those formulas for all natural a,b,c,
including native matrix/private-code coupling. Source changes occur only
at the equality row and the bundle emitter. All other primitive
instructions are unchanged; the closed reassociation is independently
checked against the whole guarded control graph.

The conclusion `Nonhalt(M,blank) iff Con(ZFC)` inherits the published
conditional-K223 native calibration. In particular, the two-marker
hereditary-domain interpretation for conditional K remains an inherited
ordinary mathematical ingredient. The new local construction does not
formalize that interpretation, and it does not claim a newly completed
Rocq or Lean endpoint. The primary seed/G candidate uses the separately
documented seed-theory route.

The original theory, macro programs and binary engine are due to the
authors acknowledged by the primary packet and its pinned archives.
The helper modules in this directory are retained excerpts/adaptations
of the supplied seed and G packets. Their original notices and licenses
remain in the shared vendor archive and the packet's attribution files.
