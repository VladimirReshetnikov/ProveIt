# Represented actual EnumPerm full step: author checkpoint

Author: `circuit_reduction`. This agent authored the new pair, its replay
driver, and the reused command-step packet. The root authored the reused
fetch/parser packets. This receipt is not an independent review.

## Literal interface and theorem scope

The new module imports only `ArithmeticCommandFetchPerm222` and
`ArithmeticCommandStepPerm222`, retaining their actual parser and C222 gate
definitions. The state layout is

```
live(pl,np,work) = P(pl,P(np,work)) + 1
work = P(tw,P(ws,P(d,h)))
```

Zero is an absorbing full-state code. The `execValue` stage takes an actual
raw command, next candidate counter and unshifted work word. If the represented
command result is zero it returns zero; otherwise it returns
`live(tailValue raw,np,result−1)`. Thus the working result's successor tag is
removed before it is placed inside the full live state.

For a nonzero full code, `enumValue` removes its outer successor tag, decodes
`pl,np,work`, obtains the actual `fetchValue pl np`, and runs that execution
stage. In particular, `pl=0` fetches and executes raw candidate `np` with next
counter `np+1`; it does **not** halt or insert an old254 scheduler tick.
`pl=1` fetches and executes raw zero while preserving `np`.

`liveDef`, `execDef` and `enumDef` are actual fixed Sigma-one formulas.
Every intermediate is unbounded, so no unsupported output bound is needed.
Their definedness instances work over arbitrary `IOpen` arithmetic models.
`enum_total` proves the unique output for every internal input. The exact
live-state zero condition is a fetched opcode zero together with work-cache
value one. A zero program-list pointer alone is not a halting condition.

The ordinary adapters use the actual `EnumPerm.St`, `toW`, `execAt` and
`enumStep`, not a copied transition table. `execValue_nat` covers every raw
natural command, next counter and arbitrary register state, using the accepted
all-raw command-step and tail theorems. `enumValue_nat` covers every six-field
ordinary state, including dirty fields. `enumValue_nat_eq_zero_iff` identifies
the numeric zero result with actual `EnumPerm.enumStep s = none`.

## Frozen source

Sources are under `Lean/DiophantineConsistency/`:

| File | Lines | SHA-256 |
|---|---:|---|
| `ArithmeticEnumStepPerm222.lean` | 128 | `d585b357650537d7b2ac2f75e8dfa5a2a9f45bd982830276710df3a5146e9dde` |
| `ArithmeticEnumStepPerm222Checks.lean` | 49 | `1b7cd887dd3f845391d379ec48674e7526f7177a66cc8f807c0e349a614c89bc` |

The complete new main/check sources and all 215 lines of the driver were read
before execution. The complete accepted fetch, parser and command-step leaves
and the actual `EnumPerm` state/command/packing/fetch/execAt/enumStep
definitions were checked against the new interface. The graph does not
import old254 command-step or scheduler statements.

The main passed its first build with an empty log. Two initial focused
checks failed because simplification normalized `0+1` before applying the
continuation theorem, and did not know `first 0=0`. The final checks explicitly
use the actual raw/next continuation theorems and derive `first 0=0` from
`first_cantor` and `cantor 0 0=0`. The main source, transition, graph and theorem
statements were unchanged. Both original source snapshots and failed logs
are retained. No source contains `sorry`, an added axiom, or `native_decide`.

## Replay and dependency provenance

The final fresh pair passed under Lean 4.32.0 with
`-M6000 -j1 -DElab.async=false`, sequential compilation, actual source
pathnames, and a 512 MiB free-space reserve. The private output root is
`/tmp/enum-stepperm222-author-w7ztfyo_/lib`.

| Final fresh object | Seconds | SHA-256 |
|---|---:|---|
| Main | 8.09 | `56323b758f1a5c920e9484113295640fcb85fead96bfdad62f907c001f3d7dff` |
| Checks | 1.90 | `db1152245febfd57c833e8ed3b9b887d8318d5f31ed3cd68a8b363262a63fc7f` |

The repeated main object is byte-identical to the first successful main.
Its log is empty. All eleven final axiom reports use only `propext`,
`Classical.choice`, and `Quot.sound`. The model-theoretic/metatheory choice
dependency is not a claim of an HA derivation of this runtime relation.
Peak child RSS in the final pair was 1,817,800 KiB.

The exact import union is **108 cached current-source modules**, including
**86 Foundation modules**, with **37 explicit package/toolchain boundary
names**. It combines the existing 106 command-step prerequisites with the
accepted fetch and command-step main objects. The fetch prerequisite closure
is already contained in those 106 modules with identical source hashes.
The full union has 366 cached artifact files and 661 deduplicated pre/post
pins. Every selected current source/import and object/available companion is
authenticated; dependency ordering is recomputed, absent custom providers are
rejected, and reused clients are checked not to import either new leaf.
The compiler and parent compiler pins agree. No prerequisite or Foundation
module was compiled, and no shared or symlinked output was overwritten.

The durable summary `arithmetic-enum-stepperm222-replay.json` has SHA-256
`baa28c4880dac35ce88a58d6b99a571069c331357775b2a0301b6615676f200d`.
The 22-file bundle `arithmetic-enum-stepperm222-replay/` has `FILES.json`
SHA-256 `26961344bb6ad3c75c0c244f99048fc0ae33023445cc98ab811d40a76109c137`.
The final terminal record is `attempt-1793061804046827762/RESULT.json`,
SHA-256 `6d1fcdbd64bf206a10fa4490e110efe2f6b4605daca7fc1d0d66052fd1130488`;
its full input manifest SHA-256 is
`fce4608021a01577ae6b94b39d17c3867601491e27b61e387d9a280f983b2802`.
The driver SHA-256 is
`796dfe71f9c843a17bbeddc6ac8c96460f8b49f904e88c81c36e69ca92a48d7e`.
The failed-check attempt is preserved as
`attempt-1793061744778405920/RESULT.json`, SHA-256
`d7c954f94200abc7e47dc1d4657bb759eab24735303409f493b03edd5861dd27`.

This packet stops at one represented enumeration step. It does not prove a
represented run, scheduler fairness, a bounded-stack derivation invariant,
represented proof soundness/completeness, an actual 215-machine simulation,
or a PA/HA consistency/equation equivalence. No accepted source, maintained
equation artifact, shared document or Git state was edited by the agent.
