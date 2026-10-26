# Helper-free C222 seed circuits: author receipt

Author: `/root/controller_certificate`, 26 October 2026. This records author
validation of two new files, not an independent peer review. Root authorized
the isolated seed leaf after the earlier C222 audit by
`/root/complemented47_review`. The frozen growG packet, existing sources,
shared objects and Git state were not changed.

I read the complete new main/check files before execution, comparing every
constructor with the literal definitions in `KCode222`. I also read the
existing finite circuit representation and the relevant row, history and
raw-tree checker sources before proposing the next interface below.

## Exact result

`ArithmeticSeedTemplates222` constructs fixed finite circuits for `req`,
`clos`, `nks`, `vrel` and the helper-free `bundle222`. It supplies
parameter-free Sigma0 graphs and proves their graph equations for arbitrary
internal arguments in every IOpen model. Each standard-Nat function equals
the corresponding actual `KCode222` definition; the final instance directly
represents the actual `KCode222.bundle222` function.

The seed is precisely `neg (vrel -> nks)`, with
`nks a b c = forall c (clos a b c c -> neg (req b c c))`. The repeated `c`
is both the matrix code and the private binder, exactly as in C222. Every
relative negation continues to use false code **1**. No equality-vacuity
helper or old C254 bundle was inserted.

The circuits themselves impose no freshness gate. The actual C222 bundle
axiom retains just `c != a` and `c != b`; in particular `a = b` is legal,
and `c = 0` is legal when both labels are nonzero. The focused file proves
the actual example `C222 (bundle222 1 1 0)` directly with the real bundle
constructor. It also tests repeated labels and the exact matrix/binder-zero
formula without expanding enormous numerical codes.

This packet does **not** prove internal validity of the seed, translate
the full C222 calculus into C254, construct a replacement represented
checker/history, connect the actual 215-machine runtime, or prove the
requested HA equivalence.

## Frozen sources and replay

Both sources are under
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.

| File | Lines | Source SHA-256 | Fresh object SHA-256 |
|---|---:|---|---|
| `ArithmeticSeedTemplates222.lean` | 104 | `d0f878669c9f8c8c9d94bccf451544aba6f7304368355f0bba440999ce342a59` | `f7d7c7dda3d712f4c927934c550abee5fd9b65045eebefd2356468008f2f3b3f` |
| `ArithmeticSeedTemplates222Checks.lean` | 51 | `29252b74570f319271b424daa6e9cf4a83c725be27add34ac44bd5050b56d013` | `e3183d8663088ebf8298a5c76b3143f84dcd5c836447e0bf498e0ab351b4df86` |

Each fresh command used Lean4.32 with `-M6000 -j1 -DElab.async=false`.
Both files passed on their first execution. The main log is empty; all
16 intended axiom reports contain only `propext`, `Classical.choice` and
`Quot.sound`. There is no new axiom, sorry or native decision oracle.
Aggregate elapsed time was 6.11 seconds, maximum RSS 1,801,492 KiB.

The private overlay is `/tmp/seed222-controller-t5hxkzq7/lib`. It reuses
102 selected custom prerequisites, including 86 Foundation modules, by
exact source/object hashes from the frozen growG replay receipt. There are
37 explicitly recorded precompiled external import boundaries. Those
packages and the Foundation closure were not rebuilt. This is two fresh
leaves plus authenticated cache reuse, not a full fresh closure replay.

The pre-execution inventory SHA-256 is
`712eea06a716808c1a0864249053808a11500d217724e6e0807b5f2e36ddadc1`.
Compiler and manifest pins are respectively
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`
and `95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665`.
All selected source/object, companion, compiler and manifest hashes were
checked before and after the two commands. The driver enforces a 512MiB
free-disk reserve before each compilation.

The complete inventory, source snapshots, command/log/timing/object hashes
and all 16 reports are bound in `arithmetic-seed-templates222-replay.json`,
SHA-256 `f168099d8f4408f384ef4c77dfccfb720fa3336d75b79d21ba9c0597e23750ae`.

## Next checker interface: inspected, not implemented

The existing `Code254Proof.RawProof` datatype, `quote`, `height`,
`decodeStep`, `decodeFuel` and `decode_quote` are syntactic and reusable.
In particular tag9 parses the three fields into the constructor named
`.r7`; that name does not force the old rho7 conclusion. A new
`conclusion222 : RawProof -> Nat` must interpret that node as actual
`KCode222.growG`, and the bundle node as actual `KCode222.bundle222`.
Its separate `valid222` must recompute MP comparisons using the **new**
conclusions recursively. Reusing `RawProof.valid`, `RawProof.sound` or
the old checker soundness theorem would be incorrect. The unchanged
parser roundtrip can support a new theorem
`C222 n <-> exists code, check222 code n = true`.

For represented row arithmetic, a separate `ArithmeticRow222.rowKernel`
can override only tags9 and11, retaining the existing payload decoding:

```text
row222 k p u v =
  if k = 9 then growG(a,b,c) + 1
  else if k = 11 then
    if c != a and c != b then bundle222(a,b,c) + 1 else 0
  else row254 k p u v.
```

Here `(a,b,c)` are the same nested Cantor fields of `p`. The new bounded
graph can combine the existing field-decomposition formula, the two
new bounded template graphs, and the old row graph in the `k != 9,11`
branch. This preserves invalid/out-of-range behavior as well as all ten
unchanged rule tags. Expected separate packets are roughly 150 lines
for the C222 raw-tree semantics and 100–180 for the represented row;
these are planning estimates, not completed artifacts.

`ArithmeticHistory254` is explicitly fixed to the old row and cannot be
renamed to claim C222 semantics. Its short use of Foundation
`PR.Blueprint`/`PR.Construction` suggests a new generic history wrapper
parameterized by a represented step function, proving sequence validity,
length, recurrence and lookup stability by the same definable induction.
A C222 instantiation could then prove an all-code Nat binding to the new
checker. The generic PR algorithms themselves should be imported, not
copied or namespace-renamed. This later history/runtime work is unimplemented;
internal C222 seed validity and the actual enumerator/runtime translation
remain separate obligations.

Relevant inspected source pins:

| Existing file | SHA-256 |
|---|---|
| `KCode222.lean` | `fbc4fef6e479b6bc5bc83bcfafa73fb1befdc1b1d02b605da68ecf691f641eb3` |
| `Code254Proof.lean` | `7bb8daf0f1c0965d22f2f16bbb1898d60cfb79f9a6feabe8ab38b3f69b3bc6d1` |
| `Code254History.lean` | `bb999a951167938e7da670e856c8634b964abe2eccf556d23ad4f8f677d732fb` |
| `ArithmeticRow254.lean` | `90c29554d76400618777a6139be5089220093a5effb2b0587f0d3ab497d0ca7c` |
| `ArithmeticHistory254.lean` | `4cf3d35c0c8d156bfb14ceacf87a799e9d4a35108a17c70bb63c4f93278a9e2e` |
