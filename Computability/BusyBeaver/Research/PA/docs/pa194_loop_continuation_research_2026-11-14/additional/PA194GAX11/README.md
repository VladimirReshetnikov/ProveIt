# PA194GAX11: relative construction and proof status

This is an independently reconstructed 194-state composition of two inherited command designs:
PA194G's explicit AX-parameter binder `U(c,h)` and PA194AX11's four-field,
eleven-entry fallthrough command. Its hash is
`7e1c6442816e5df05e961f2057719252a1976c9a195a786978bf1e2d3c8e466d`.

The initial 94-graph comparison found no match. The final snapshot
`603c58ca3bd6bf3222fcfc4e308e6b079f65d573` contains an exactly identical
table named PA194AX11G. This folder is retained as a checked concurrent
reproduction and is **excluded from the five-new-machine claim**.
`../../late_snapshot/novelty.json` records the expected match to class L01.

**This reproduction does not claim an absolute iPRA calibration.** `proof.tex` is the
mathematical source/command argument, with explicit inherited dependencies
and the weak-arithmetic formalization obligation. `reference_g_proof.tex`
is the attributed historical PA194G text and refers to its different
table, not this one. The revised AX11H written absolute calibration is a
separate dependency used for LC_AX11H in the main report; it does not
discharge this reproduction's explicitly stated internalization obligation.

The new command is

```
AX(c,x,y,z):(t,w,d,h) ->
  (0,[g,Gamma,h6Q,h5,h4,h3,h2,h1,rho,U(c,h),t;w],z,0).
```

Its shortened generalization compiler is
`Push; Shift; AX(i,0,0,0); Shift^11`; no `Offset_i` command is needed.
All other selectors, reserved-zero MP, total Pop, and the extra-field
scheduler are explicitly proved in `proof.tex` and checked symbolically
by `check_commands_new.py`.

Run with Python 3.10+ and assertions enabled:

```
python3 verify_all.py --output /tmp/gax11-check
```

The combined verifier checks input integrity, reconstructs in an isolated
temporary copy, compares every reconstructed machine/source artifact,
executes the command algebra, and runs both physical symbolic checkers.
It keeps all release files unchanged and places new receipts in the
requested evidence directory. `--quick` skips both physical replays and
records that omission explicitly. The builder uses the frozen local raw
parent table, not a checkout or network request.

The individual replay commands are also available:

```
python3 build_new.py
python3 check_commands_new.py --machine . --output commands_receipt.json
python3 independent/check.py . --output independent/results
```

The individual builder rewrites its generated local artifacts and receipt;
use the combined verifier to preserve them. Its own `--quick` option skips
the construction physical replay and records `runtime: null`.

Provenance: ProveIt commit
`32d0d8b7d93a63ad4106c18cdb29b37927acdad2`, packages
`Computability/BusyBeaver/Research/PA/docs/PA194B_PA194G_research_2026-11-14/generalizer`
and `Computability/BusyBeaver/Research/PA/docs/pa194_ax11_research_2026-11-14`.
The grammar, contextual folds, runtime kernels and command-checker algebra
are adapted from those sources, with original notices preserved under
`licenses/` and `independent/reference/`. The raw parent is pinned to
SHA-256 `b25933d14de19f72709bdecf7a67a4e21c150f525cf61ec76c074ac577d6cc87`.

The optional `research/` records a fresh search over source head order,
parameter permutations, gate variants and binary reassociations. Its
scores are discovery estimates, not a state lower bound or a proof of a
candidate's physical correctness.
