# Rocq-compatible guarded frame component

This component advances the previously uncompiled left-frame proposal. It
kernel-checks the exact symbolic step definitions and the new twenty-template
family in **Coq 8.18.0** (Ubuntu package `8.18.0+dfsg-1build2`, OCaml 4.14.1).
It is not a rerun of the production Rocq 9.1.0 endpoint.

## Checked results

`K215FrameStandalone.v` extracts the current K215 `Runtime230Core.v` effects,
branch type, box oracle, segments, configurations, peel operations, and `sstep`
as verbatim source substrings. The direction type has its two usual constructors
`L` and `R`; the table `tmn` is universally quantified. Source slices and hashes
are recorded in `EXTRACTION.json`.

The shared proof body establishes:

- `sstep_add_left_eq`: if the symbolic head is not on an empty explicit left
  list, appending a frame commutes with the whole optional step result. This
  preserves failure as well as the exact progress Boolean.
- `run_local_add_left`: every successful fixed-length guarded local replay
  lifts to every appended frame, with the same output and accumulated progress
  flag. This theorem is deliberately one-way: the guard can reject an unframed
  run that would be executable after adding a frame.
- `run_local_sound` and `run_local_frame_sound`: for any explicit semantic
  client whose one-step relation supplies `Reach` and conditional `Reach1`, the
  guarded replay supplies the same facts. All client assumptions are explicit
  universally quantified arguments; no global axiom is introduced.
- `unguarded_empty_left_fails`: a formal counterexample using the frame
  `[SB true]`. At `(0,true,[],[])`, the original executor invents a blank whereas
  the framed executor consumes the appended one. Thus the guard is essential.

`K215FrameTemplates.v` extracts the exact maintained Rocq `table230` and `tmn`
definitions and proves twenty `localN` equations by kernel reduction, followed
by twenty universally quantified `framedN` equations using the shared lemma.
These are the new q=1/q=2 family, totaling 239 local symbolic operations with
maximum 39. Every equation has progress flag `true`.

The historical names `Table230` and `TM230` do not designate a different
230-state candidate here. `tmn` disables fifteen of the 230 sparse positions.
The executable finite audit compares all **430 actions** with both current
Lean `KTable215.lean` and the accepted native K215 file, applying precisely
`301 -> 102`, `302 -> 120`, and `254 -> 230`. Lean has 226 list positions because
the last four disabled states are omitted. Its live actions and those of the
Rocq table agree exactly with the accepted 215-state machine. The native file
has SHA-256
`9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.
This finite binding audit is distinct from the kernel checks.

## Reproduction

The checked sources and their exact upstream slices are self-contained.
With an installed Coq compiler:

```sh
python3 check_component.py --coqc coqc --coqchk coqchk
```

The script regenerates both modules, checks the literal bindings, compiles
them, and recursively checks `K215FrameTemplates` with `coqchk -silent -o`.
It requires five closed generic theorem reports, twenty closed template
reports, and a checker context containing no axioms. Logs and hashes are in
`evidence/`; the compiler binaries and `.vo` files are not needed in the
distribution because the sources reproduce them.

To bind regeneration to a checkout rather than the packaged snapshots:

```sh
python3 prepare_rocq.py --repo /path/to/ProveIt \
  --templates /path/to/templates-q1q2.json
```

The inspected checkout is commit
`cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

## Production integration boundary

`K215LeftFrame.v` contains the **identical proof body** with imports from the
maintained `K215F.TM230` and `K215F.Runtime230Core`. This production adapter is
supplied for integration and was **not compiled in Rocq 9.1.0** here. Compile it
with the same `BusyCoq` and `K215F` logical load paths as the repository's Rocq
reproduction driver.

The abstract semantic interface has a direct intended instantiation:

| Component parameter | Existing production object |
| --- | --- |
| `C` | `Q * tape` |
| `view` | `conc n vs` |
| `reach` | `--> *`, the reflexive transitive machine-step relation |
| `reach1` | `--> +`, the positive machine-step relation |
| `reach_refl` | `evstep_refl` |
| `reach_trans` | `evstep_trans` |
| `reach1_then` | `progress_evstep_trans` |
| `then_reach1` | `evstep_progress_trans` |
| `one_step_sound` | `sstep_sound`, with the four existing box lemmas and `valid br vs` |

The twenty local equations stop at a whole symbolic configuration with empty
explicit left list. Applying `run_local_frame_sound` with the prefix and marker
frame gives the local concrete execution once that interface is instantiated.
The maintained Home/left-word argument must then return from the corresponding
state 1 or 2. Exact source-action framing, the 1,423 template occurrences, the
literal fallback, and the complete endpoint remain integration obligations.
No measured production build speedup or maintained-source reduction is claimed.

Attribution: the executor source retains its original notices identifying
Jeff Ketchersid's pinned m254 `SymExec.v` and the K-family adaptations. The
guarded-frame idea builds on the repository's `round13-left-frame` proposal;
the q=1/q=2 template family is the current package's further refinement.
