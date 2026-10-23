# Checked K215 scheduler component

This packet contains a checked optional bounded scheduler theorem and its
adapter to the current production `EnumPerm` module. The generic scheduler
is inherited from Source194; the triangular bound is the local refinement
provided here. No transition table or production proof file is changed.

## Checked result

For a target candidate N and state s with `s.np <= N`,
`EnumPerm.find_candidate_bounded` produces a finite successful prefix of
length at most

    T(N) - T(s.np) + s.pl,    T(n) = n(n+1)/2,

ending either at the boundary `(pl,np)=(0,N)` or at a state whose next
transition halts. This counts abstract enumerator steps and excludes that
optional final halting transition.

`complete_from` uses the current direct compiler `build_c222` to remove the
boundary premise from completeness. `halts_iff_from` retains the existing
derivability invariant for the soundness direction. Arbitrary-state
completeness is inherited from Source194's proposal; it is not claimed as
new mathematics here.

The exact three concrete profiles all report only `propext`,
`Classical.choice`, and `Quot.sound`. Lean 4.32.0 checked the 14 production
dependencies fresh, the inherited generic scheduler, the new bound, and the
concrete adapter. The first adapter attempt failed; its raw source, output,
and receipt remain in `history/attempt1`. The accepted repair changes only
the wrapper's reducibility and its explicit run-successor proof.

This is a component check, not a replay of the full binary-machine endpoint
or an internally encoded ZFC/PA derivation. The production compiler, command
encoding, working-register semantics, and public production theorems remain
unchanged.

## Rebuild without the repository

With the complete Lean 4.32.0 distribution and Python 3 on a Unix host:

```sh
python3 build.py --lean /path/to/lean-4.32.0/bin/lean --out /tmp/k215-scheduler-fresh
```

The output directory must not exist. The script checks every vendored source
hash, compiles the 17 modules in order from source only, and records compiler
commands, logs, source hashes, object hashes, and return codes. It never
downloads packages. The shipped `Init` library is an explicit Lean toolchain
boundary. Use `--lock PATH` to join a larger project's serial proof-build lock.

To check input integrity without compiling:

```sh
python3 build.py --out /tmp/unused-scheduler-output --check-inputs-only
```

The portable builder's input route was checked on the final source manifest.
The delivered successful compiler evidence comes from the commands in
`evidence/generic_verification.json` and
`evidence/concrete_final_verification.json`; the original concrete driver is
also retained. Absolute paths in those historical receipts identify where
that check occurred and are not required for a fresh build.

## Integration recommendation

Adopt Source194's existing shared scheduler by transplanting the relevant
sections into the current enumerators. Do not copy its whole old EnumPerm
snapshot: it uses `build (cdom_of_c222 h)` and would undo the production
`build_c222` fusion. The concrete adapter in this packet demonstrates the
current-source attachment without changing any production code.

Keep the bounded extension optional unless explicit command-count bounds
are useful. It strengthens the contract; by itself it adds proof source.
The actual simplification is sharing the repeated scheduler arguments and
preserving existing definitions and wrappers. See `ANALYSIS.md` for the
mathematical argument, prior-work scope, and source census.

## Provenance

All production inputs are pinned to ProveIt commit
`cbf94cb552a3b49509e0eee80e7455d4eb5974c6`; `sources.json` records their exact
paths and hashes. The inherited Source194 file differs only by an appended
line feed from Git blob `b7f62397115104dbe2bd87c01e7883caf2abd1e0`.
Original headers and notices are retained under `licenses/`.
