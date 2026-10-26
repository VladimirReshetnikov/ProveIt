# Independent read-only review: helper-free C222 seed circuits

Reviewer: `/root/complemented47_review`, 26 October 2026.
Status: PASS within the stated code-representation scope; no finding or
source correction. This review includes mathematical/source inspection and
independent provenance checks. **No independent Lean compilation was run.**

I read all 104 main lines and 51 focused-check lines, the entire actual
`KCode222.lean`, the fixed `Circuit` datatype/evaluator/graph/compiler proof,
and the exact tagged arithmetic constructors and Nat bindings used here.
I also read the author receipt and all three preparation/build/receipt
drivers as text; I did not execute those drivers.

## Exact mathematical check

The five circuits reproduce `KCode222.req`, `clos`, `nks`, `vrel`, and
`bundle222` constructor for constructor. In `req`, both occurrences of the
`b` binder remain literal; in `clos`, the nested `a` binders and the `k`
subset binder are unchanged. The specialization
`nks a b c = wal c (wim (clos a b c c) (wim (req b c c) 1))`
retains `c` as both matrix code and private label. There is no alpha-renaming,
fresh-matrix replacement, implicit distinctness assumption, or old C254
container/collection helper inserted.

Every `Circuit.neg` is implication into `Circuit.one`, whose evaluation is
the literal arithmetic code1. This agrees with `Code254.F=1` and
`Code254.wn x=wim x 1`; it is not a new syntax constructor for logical
bottom. The full bundle is exactly `neg (vrel -> nks)`.

The internal representation statements hold for arbitrary arguments in
every `IOpen` model with `ORingStructure`. Each graph is a closed finite
Sigma0 syntax object obtained from `Circuit.graph`; the existing compiler
bounds child codes by the output and proves graph equality. The new wrappers
merely select the exact three/four inputs and literal unused zero argument.
The five Nat equalities unfold only these constructors and the accepted
tagged-code Nat equalities. The final `codeBundle_defined` instance therefore
represents the actual `KCode222.bundle222`, not a similarly named surrogate.

The circuits impose no gate. The actual `C222.bundle` constructor requires
only `c != a` and `c != b`; it does **not** require `a != b` or `c != 0`.
The focused example `C222 (bundle222 1 1 0)` uses that actual constructor
with both legal inequalities. The repeated-label and zero-label structural
examples preserve the same self-label specialization without evaluating
enormous closed numerical codes.

None of these results proves internal logical validity of the seed. The
focused `C222` example is an axiom-instance derivation in the defined C222
calculus, not a `CProv254` derivation or a semantic soundness proof. The
separate obligations of internal seed validity, checker/history semantics,
actual counter4/215-machine runtime, and the requested HA consistency
equivalence remain open. The author receipt states this boundary correctly.

## Source pins

The first six paths below are relative to
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.

| Source | SHA-256 |
|---|---|
| `ArithmeticSeedTemplates222.lean` | `d0f878669c9f8c8c9d94bccf451544aba6f7304368355f0bba440999ce342a59` |
| `ArithmeticSeedTemplates222Checks.lean` | `29252b74570f319271b424daa6e9cf4a83c725be27add34ac44bd5050b56d013` |
| `KCode222.lean` | `fbc4fef6e479b6bc5bc83bcfafa73fb1befdc1b1d02b605da68ecf691f641eb3` |
| `ArithmeticTemplates254.lean` | `2031511caadb7bf794d190cea99bedfa32022197f64612cb270daceee986f65f` |
| `ArithmeticCode254.lean` | `2edf178b0061838b13299f1332d65c4fc3194207cbd0e761f129a7bcc36bdff0` |
| `Code254.lean` | `efffed3d6c96bb073d444c35352361347b6e2415b8c9e95b8bc860ecda3eb05a` |

The author receipt is SHA-256
`f0b53e8bf467e8ce438bda956a0483de87b513e7f7d970b30835e30528365405`;
the complete replay inventory is SHA-256
`f168099d8f4408f384ef4c77dfccfb720fa3336d75b79d21ba9c0597e23750ae`.

## Independently checked replay provenance

I rehashed every one of the 102 selected custom source files, all 360 listed
object/companion files, and all 37 explicit external object boundaries.
Of the custom sources, 86 are Foundation modules. I checked each selected
source/object record against the frozen growG parent receipt, verified the
source import lists and closure relative to the recorded external boundary,
and rehashed the compiler, Lake manifest, pre-execution input inventory,
three driver texts, two fresh source snapshots, two fresh objects, and all
successful logs/timing files. Every hash matched. This establishes agreement
with the recorded accepted-cache evidence; it is not a fresh Foundation or
package replay and does not extend beyond the listed import boundary.

The author's two recorded commands used the private overlay
`/tmp/seed222-controller-t5hxkzq7/lib`, Lean4.32,
`-M6000 -j1 -DElab.async=false`, and both exited0. The main log is empty;
the checks log has exactly16 axiom reports, each restricted to `propext`,
`Classical.choice`, and `Quot.sound`. I read those logs and timing records.
The fresh object hashes are
`f7d7c7dda3d712f4c927934c550abee5fd9b65045eebefd2356468008f2f3b3f`
and `e3183d8663088ebf8298a5c76b3143f84dcd5c836447e0bf498e0ab351b4df86`.
The recorded combined time is6.11s and maximum RSS1,801,492KiB.

I previously authored the C222 internalization audit and parts of the
arithmetic215/native cache provenance reused farther upstream, and reviewed
the growG packet. I did not author the new seed circuits or their generic
`Circuit` compiler. This receipt adds an independent source/math and
provenance review, not an independent kernel replay. No source, shared
object, central documentation, or Git state was changed.
