# Actual C222 bounded row: author receipt

Author: `/root/controller_certificate`, 26 October 2026. This is author
validation of new `ArithmeticRow222` and its focused checks, not an
independent review. Root authorized this bounded-row checkpoint only.
Existing sources, shared objects, earlier frozen packets and Git state
were unchanged.

I read all of the existing `ArithmeticRow254`, `Code254History` row/parser
compatibility, the new actual `Code222Proof` semantics and the bounded
growG/seed circuit interfaces before implementation. I read both new
sources before execution and again in their final form.

## Exact scope

For every IOpen model, `rowKernel k p u v` uses the actual nested Cantor
fields `a=first p`, `b=first(second p)`, `c=second(second p)` and changes
exactly two tags:

```text
9  -> growG a b c + 1
11 -> if c != a and c != b then bundle222 a b c + 1 else 0.
```

All other tags use the unchanged `ArithmeticRow254.rowKernel` on the same
four inputs. Public equations expose both new tags and the unchanged
branch. The parameter-free Sigma0 `rowDef` has a proved graph for this
function on every internal input. Payload components are bounded by the
payload even when a row is rejected; the formula never incorrectly bounds
a rejected intermediate seed by the zero output. The seed's freshness
gate remains just the two actual inequalities.

The standard-Nat `row` makes the same two overrides on the old **numeric**
row interface. `rowKernel_nat` and `rowGraph_nat` bind every tag and payload
to that row for an arbitrary child-result function, including invalid
tags. The supplied first child value is GEN's tail lookup for tag2 and
MP's minor lookup otherwise; the second value is MP's major lookup.
This does not itself represent lookup or treat an oracle as an arithmetic
function.

The new `parsedValue` uses only `Code222Proof.valid222` and
`Code222Proof.conclusion222`. The substantive standard binding is

```text
row (fun code => parsedValue (rec code)) tag payload
  = parsedValue (Code254Proof.decodeStep rec tag payload)
```

for every optional-tree oracle, every tag and every payload. The proof
handles invalid children, all four MP child-validity cases, the new exact
MP conclusion comparison, generalization, all leaves, both bundle gates
and out-of-range tags. It does not reuse the old C254 semantic agreement
theorem. `row_invalid` gives zero for every tag >=12, and `row_congr`
shows that only child indices <=payload matter.

The focused checks retain a=b=1,c=0 as a legal bundle, reject each
forbidden label collision, bind growG at an explicit paired payload,
and expose the complete graph and parser-compatibility conclusions.

This is a represented **row**, not a represented C222 history/checker
totality or a machine runtime translation. Internal seed validity,
actual enumerator calibration and the HA equation equivalence remain
separate obligations. No fixed C254 history was renamed or reinterpreted.

## Frozen sources and successful replay

Source prefix: `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.

| File | Lines | Source SHA-256 | Fresh object SHA-256 |
|---|---:|---|---|
| `ArithmeticRow222.lean` | 181 | `7341c95d5b3d9a9d17eb2f6bfb32c7b1bf781fe86274c0eeba817c953be6c8f1` | `8eed6e75b5bdd4cb8641b33aa9e4509d9f99bf7a842d7c2ca25ab3b2a07b2aae` |
| `ArithmeticRow222Checks.lean` | 50 | `ad3e51c42e88ec378f4b20aefbd0b62c7075e4466af9b561ec34d35ea2deb24e` | `2b8430b1f35fe963e4eeb72536613bad495e62f0f1ac09bed35475d279401e11` |

The final main/check pair passed under `-M6000 -j1 -DElab.async=false`.
The main log is empty. All ten intended axiom reports are standard-only
(`propext`, optionally `Classical.choice` and/or `Quot.sound`); no new
axiom, sorry or native decision oracle was used. The final pair took
8.31 seconds, with maximum RSS 1,822,752 KiB.

The private overlay `/tmp/row222-controller-lcc6qsqx/lib` reuses
107 selected custom prerequisites, including 86 Foundation modules, and
records 37 precompiled external import boundaries. The exact source/object
pins come from the accepted arithmetic/growG base and the frozen seed and
Nat-checker leaf receipts. This task freshly compiled only the two new
row leaves; it did not rebuild Foundation or assert a full fresh closure.

The pre-execution inventory SHA-256 is
`113733085e6ecb2ed4d1b425264f364cdf08d02256544326945dc9e3a1d85f30`.
Compiler and package manifest pins remain respectively
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`
and `95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665`.
All selected source/object, companion, compiler and manifest pins were
checked before and after compilation. The driver enforced a 512MiB disk
reserve before each invocation.

Complete inventory, snapshots, commands, logs, timings, object pins and
the ten axiom reports are in `arithmetic-row222-replay.json`, SHA-256
`5973c5695f0d1eee610a75e6eacf69b23744a585f22f14876b2855a9250de96d`.

## Development record

The first main/check pair already passed. Its main emitted one unused-simp
warning for `h9` in the tag11 branch of `row_congr`; the tag11 equality
alone discharged that case. Removing that redundant proof argument left
all definitions and theorem statements unchanged. Both files were then
freshly replayed to obtain the clean final pair. Both source versions,
logs and timings are retained; there was no failed proof or broad build.
