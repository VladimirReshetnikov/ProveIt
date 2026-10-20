# Encoding diagnostics

## Rejected runtime-only 218-state table

`rejected_runtime_only_218.native.tm` is a **rejected research example**. The
accepted machines are `../../machine/k218.native.tm` and its canonical version
`../../machine/k218.tm`.

The rejected table passed the complete symbolic primitive-interface check:
6,167 guarded cases, 1,512,755 symbolic proof steps, and minimum positive duration
constant 12. Those interfaces start in well-formed interpreter configurations.
They do not establish initialization from a blank tape.

Starting in native state 0 at cell 0 on the all-zero tape, after exactly **85
transitions** this rejected table has state **35**, head position **7**, and one
cells exactly **`{-3,-2}`**, with every other cell zero. Its state-35/read-0
transition is `1 R 35`. Hence, for every natural number `n`, at time `85+n` its
state is 35, its head is at `7+n`, and its one cells are exactly

`{-3,-2} union {x in Z: 7 <= x < 7+n}`.

The scanned cell is always zero. The next transition establishes the same
statement for `n+1`, proving an infinite rightward writing run without a
consistency assumption. Universal primitive-interface correctness therefore
needs a separate complete blank-startup proof.

### Reproduce the diagnostic

From this directory, run:

```sh
python3 -B check_rejected_startup.py
```

The checker uses only the standard library and an unbounded set of one
positions. It verifies the complete 85-step computation and the transition
establishing the induction. It writes `rejected_startup_receipt.json`, including
all 85 literal transitions. Its `PASS` certifies the **rejection diagnostic**.
Use `--output PATH` to write the receipt elsewhere.

### Provenance

| File | Purpose |
|---|---|
| `rejected_runtime_only_218.native.tm` | Exact rejected table; native start 0 and halt 254. |
| `rejected_runtime_only_sites205.json` | Exact source used by its earlier runtime check. |
| `rejected_runtime_only_runtime.json` | Unmodified historical runtime receipt with input, driver, and dependency hashes. The startup diagnostic does not regenerate this symbolic proof. |
| `rejected_runtime_only_recipe.json` | Original changed-row and 88/301-fold recipe. |
| `check_rejected_startup.py` | Independent finite-prefix and infinite-ray checker. |
| `rejected_startup_receipt.json` | Generated PASS receipt and complete finite trace. |

SHA-256 identities:

- Rejected table: `56245ec1973938193a646cbf96712aae000f1958fdcaefd197c703870c730431`
- Source: `0f6c3f9d3f0408f8d5c02d4b2f7c48a3111df4c0e24a1f1816ccab43b11d9a61`
- Historical runtime receipt: `db4b4eb7ee7ec890ab185616654214ee5780c195ffa484f2d4e1104c8009fa18`

The 219-state checkpoint is already included at
`../../verification/construction/intermediate219.tm`, with SHA-256
`f29cf17e6e872b479c9ee11b0e6ab3bb94f3f5497143e5fa85d1798db98a7b12`.
The rejected variant changes `51/0` from `0 R 16` to `0 R 122`, changes `88/0`
from `0 R 122` to `0 L 51`, redirects every target 301 to 88, and removes state
301. Its source is the checkpoint source, before the accepted candidate's
final reassociation.

## Accepted-candidate checker

The pre-existing `check_blank_startup.py` audits the accepted native table,
whose hash begins `2dfaba6d`, and its complete 312,909-step initialization.
It is separate from `check_rejected_startup.py`.
