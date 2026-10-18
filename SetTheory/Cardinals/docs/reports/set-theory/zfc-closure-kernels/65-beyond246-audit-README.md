# Proof audit and prepared-tape obstructions

These are new audit/search artifacts relative to ProveIt commit
`8cdc55ff9281b0aaba49bf74b0b225d57f12b893`. They use the attributed
`zfc-context246-20261018.zip` machine as an input. They do **not** claim a new
machine with fewer than 246 states, a state lower bound, or a mutant's behavior
from blank. The preserved upstream sources and 246-state construction retain
their original attribution.

## Quick reproduction

With the containing research package's default directory layout:

```sh
python3 -B portable/verify_audit.py --output /tmp/zfc-audit-replay
```

For a different location of the extracted context246 baseline:

```sh
python3 -B portable/verify_audit.py --baseline /path/to/zfc-context246 --output /tmp/zfc-audit-replay
```

Only the Python standard library is required. The verifier reads
`machine/zfc_prefix246_old.tm` and `sources/Prog254.v` from the selected
baseline. It checks the exact input hashes, table sizes, mutation rows,
complete sparse tapes, and independent dense-tape results. It writes the
complete witnesses and a compact verification summary in the output directory.

The corresponding preserved input hashes are:

| Input | SHA256 |
|---|---|
| Old-label context246 table | `303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee` |
| Complete original program | `1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746` |

## State204: a genuine original source phase with a live tail

Delete old204 and replace `(172,1)` by `(1,R,252)`. The 245-state mutant halts
from the complete prepared phase
`PC=1111111111`, logical registers `(N,T,W,A,D,H,X,Y,L)=(0,2,0,0,1,0,1,0,151)`.
The small witness has distance 40 and three value-one spares; it halts after
12,808 moves at old halt254/head 12. The unmodified246 table reaches its correct
next empty-PC root after 3,317 moves, with logical registers
`(0,2,0,0,2,0,0,0,151)` and four value-one spares. A second mutant witness uses
distance 181,167 value-one spares and `N=3`; it halts after 10,232 moves, again at
halt254/head 12. Both mutants use the changed row three times and encounter no
complete empty-PC root before halting.

The source phase satisfies `T=D+X=2` and `D>0`. This is stronger than coarse
zero/positive register masks. Code2 is the theorem `All(0,truth)` by
generalization. Code20 is `Imp(truth,All(0,truth))`, obtained from that theorem
by propositional K and modus ponens. The original admissible source root
`(0,0,0,0,2,20,0,0,67611006)` fetches command0 and argument0 while preserving
the old value D=2, and leaves tail151. The source helper checks the Cantor
pairing arithmetic and then replays 220 individual original register
instructions to the displayed phase. The large initial fetch uses the
inherited read/unpair contract; its unary binary execution is not simulated.

The nonzero tail151 is two NIP(0) commands, since `150=P(2,P(0,4))` and
`3=P(2,P(0,0))`. Including that live tail defeats the particular continuation
behavior suggested by earlier all-zero-tail controls. The record includes the
complete 220-instruction source trace and complete binary initial/final tapes.

The geometric prepared tape is **not claimed to be reachable from the mutant
blank run**. The result obstructs reuse of the original phase simulation and
requires any alternative global interpretation to address the live tail. It
does not rule out every conceivable new interpretation of the mutant.

Files: `probe_state204_safe_phase.py`, `source_phase_certificate.py`,
`state204_safe_phase_probe.json`.

## Short detectors: failure at the known distance 181

The exact original source instruction `PC=111010010010000000` is `CD1`.
Use its zero guard, logical registers `(3,0,0,0,0,0,0,0,0)`, distance 181,
and 167 value-one spares. Original246 reaches the exact intended whole-tape
endpoint at head 0 after 1,514 moves.

| Mutation | First false dispatcher origin |
|---|---|
| Delete74, set `(58,0)=(0,L,84)` | Move749, head 11 |
| Delete58,74, set `(41,0)=(0,L,84)` | Move355, head 11 |

For the 245 table, the short detector mistakes the internal word `1 0^8 1`
on cells 10 through 19 for the return boundary. For 244 the corresponding word
is `1 0^7 1` on cells 10 through 18. The certificate checks the exact trigger,
first false origin, expected baseline endpoint, and complete tapes. It makes
no claim about the mutants' eventual execution.

Files: `probe_short_detector_d181.py`, `short_detector_d181.json`.

## Bounded pulse-controller searches

Two additional finite screens allow the number of value-one spares to change
while requiring a finite, nonempty suffix, the correct first nine primary
values, the same macro exit state/head, and the complete preserved exterior.

The Python screen deletes255 and varies all 980 write/move/destination actions
for75/read0. It found no survivor among 58 controls with 5,000 moves of fuel per
macro. Reproduce it with:

```sh
python3 -B portable/search_flexible_spares.py --table baseline246/zfc-context246/machine/zfc_prefix246_old.tm --output /tmp/flexible-spares.json
```

The C++ screen varies75/read0 and one additional row from
`131/0,131/1,112/0,112/1,75/1,109/0,109/1,95/0`. For each of these eight choices
it tested 980² action assignments, for 7,683,200 assignments in total. The
58 controls use a 1,000-move bound and found no survivor. Assignments across
the eight searches need not be distinct. Reproduction takes substantially
longer than the quick witness replay:

```sh
c++ -O3 -std=c++17 portable/search_flexible_spares.cpp -o /tmp/search-flexible-spares
/tmp/search-flexible-spares baseline246/zfc-context246/machine/zfc_prefix246_old.tm
```

These finite searches exclude only the stated tested action families under
the stated exit and tape contracts. They do not exclude joint changes to
more rows, changed macro exits, arbitrary spare values, or a new global
representation, and they prove no state lower bound.

Files: `search_flexible_spares.py`, `flexible_spares_results.json`,
`search_flexible_spares.cpp`, `flexible_spares_oneaux_results.txt`.

## Mathematical proof scope

`audit_fragment.tex` is a report fragment requiring `amsmath`, `amssymb` and
`hyperref` or `url` (its source links use `hyperref`). `proof_scope_audit.md`
provides the longer source audit and exact new-machine obligations. The
requested ordinary ZFC proof can use the specific set-model constructions,
finite syntax inductions and completeness argument. An external closed Lean
theorem alone is not a blanket translation into ZFC, and the separate stronger
PA proof-code internalization remains a different task. No new Lean/Rocq
build or serialized first-order proof object is claimed here.
