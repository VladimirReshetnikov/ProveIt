# Compute the K215 source tree instead of writing it out

Lean proposal, 2026-10-21, against current `main`. Production is unchanged; the proposed file is
[`lean/BusyBeaver/ZFC/KSource215Program.lean`](lean/BusyBeaver/ZFC/KSource215Program.lean).

## The change

`KSource215Program` defines the 180-node program `p215` and then writes its tree out as one
literal, `t215` (a single line of 122,874 bytes), with `t215_eq : ptree p215 = t215 := by rfl`.
The literal is data the kernel already recomputes to check `t215_eq`. The proposal replaces it by

```lean
/-- The program's tree, computed rather than written out. -/
def t215 : Tree := ptree p215

theorem t215_eq : ptree p215 = t215 := rfl
```

Every name and statement is unchanged; only `t215`'s body changes (lines 195–196, 198).
`KSource215Program.lean` goes from 129,741 to 6,867 bytes, which is the largest single
reduction available in the hand-written part of `KEndpoint215`'s closure (about 1.22 MB in 107
modules).

## Cost, measured

The users of `t215` are the nine `KSites215Batch*` modules (`decide +kernel` on
`descend KSource215.t215 path`), `KSites215`, `DecoderSourceBinding` (`rfl` against
`sourceTree`) and `KDecoderPrefix215`. `descend` follows one path, so the kernel unfolds
`ptree p215` only along it. Lean 4.32.0, one `lean.exe` at a time:

| Module | Literal `t215` | Computed `t215` |
|---|---:|---:|
| `KSource215Program` | 38 s | 2.4 s |
| `KSites215Batch004` | 185 s | 202 s |
| `DecoderSourceBinding` | — | 14 s |
| `KDecoderPrefix215` | — | 2.1 s |

All green. Batch004 is about 9% slower; the other eight batches were not rebuilt here (about
28 minutes in total), nor `KSites215` and `KEndpoint215`. Their statements mention `t215` only by
name, so they cannot change meaning; the open question is only their kernel time.
