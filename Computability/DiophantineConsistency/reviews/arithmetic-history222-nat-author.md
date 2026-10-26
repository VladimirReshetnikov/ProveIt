# Actual C222 history: all-code Nat binding

The controller-certificate agent authored and fully read the new 108-line
`ArithmeticHistory222Nat.lean` and 52-line focused checks. The final fresh
pair passed with empty main diagnostics and eight standard-only axiom reports.
This is an author receipt. The agent also authored the represented history,
generic history, actual row and actual Nat-checker prerequisites; independent
reviews of those packets are recorded separately.

`positiveStep_nat` identifies the represented positive selector with the
actual `ArithmeticRow222.row`, keeping the same sequence-lookup oracle. Then
`value_succ_nat` uses the proved history lookup and child bounds to replace
that oracle by this same evaluator's child values. The main theorem
`value_nat_fuel` proves, for **every** natural code and **every** fuel strictly
above it, that the represented value is the actual C222 parsed value of
`Code254Proof.decodeFuel fuel code`.

The proof is strong induction on code, generalized over fuel. Zero code is
invalid at positive fuel. For a positive code and successor fuel, one parser
step and `ArithmeticRow222.row_parsedValue` reduce the goal to equality of
the child oracles. `row_congr` queries only indices `i ≤ raw / 12 ≤ raw`, so
the same induction hypothesis applies at both a smaller code and the
remaining fuel. No fuel-monotonicity theorem, valid-tree assumption,
constructor-quotation restriction, duplicate Nat list history or duplicate
numeric fuel evaluator occurs.

Specializing fuel to `code + 1` gives exact interpretations of `valueDef`,
`checkDef`, and `checkValue` on all natural inputs. In particular:

```text
checkDef.Evalb [code, conclusion] ↔ check222 code conclusion = true
C222 conclusion ↔ ∃ code, checkDef.Evalb [code, conclusion]
```

The latter uses the already proved actual C222 finite-proof/checker theorem.
The checks also bind invalid code zero, actual truth, actual growG, the
helper-free bundle, and the legal case `a = b = 1, c = 0`. They do not add a
freshness condition absent from C222.

The old `ArithmeticHistory254` is imported only to reuse
`foundation_div_nat`, `foundation_rem_nat`, and the trivial numeral-12
identity. No old history/value/checker semantic theorem is used. This packet
does not establish internal C222 seed validity, a C222-to-C254 proof compiler,
an interpreter or machine runtime theorem, or HA equivalence. Its actual
all-code interpretation complements the preceding arbitrary-IΣ1-model
representation and totality packet.

Frozen sources and fresh objects:

| Module | Source SHA256 | Fresh object SHA256 |
| --- | --- | --- |
| `BusyBeaver.ZFC.ArithmeticHistory222Nat` | `871f3ef287a10bdbc3da19fd1d513d481ce7c6d36446f6d0c0d4cc7ab57b79ef` | `fde4589e7e69f022d5e605c1b43f343fc42997fad1385f201841c495f00c6468` |
| `BusyBeaver.ZFC.ArithmeticHistory222NatChecks` | `c52ce33b7078ae821fdae72ec265dbfc50f81ca8a71d3d96b9f79efe599af404` | `03a680ffda6cfd1c5aed3407d5d3b7273c05fc70a5117df0fff86c6fe42ef55f` |

The private overlay is `/tmp/history222nat-controller-o2r0a36e/lib`, prepared
at Git snapshot `b3bb9ee902f3092a4709a6d0111a039abcc55b50`. Inventory SHA256:
`31d79c8179642d52267fe31acca156f07e9a233d464e320ac985a10dd20eb5e8`.
All 120 selected custom source files (95 Foundation and 25 project sources),
405 cached object/companion files, and 38 external boundary objects were
authenticated before execution and rechecked afterward. In particular the
old arithmetic-helper module has source
`4cf3d35c0c8d156bfb14ceacf87a799e9d4a35108a17c70bb63c4f93278a9e2e`
and object `199d21187c40609551c3617b6a511bb281b374e510d433868b4cd5c29c005069`.
External package internals were reused, not freshly rebuilt or newly attested
transitively. No broad closure replay or fresh Foundation build is claimed.

The first main compile rejected passing native Nat `≤` directly to the
Foundation `≤` interface. The corrected proof explicitly unfolds
`Arithmetic.le_def` and derives equality-or-strict-order from the same bound.
No statement or definition changed. The failed source, log and timing remain
in the replay record. The final main and checks took 2.02 and 1.55 seconds,
respectively, under Lean 4.32.0 with `-M6000 -j1 -DElab.async=false`.
Peak resident memory was 1,813,016 KiB. All eight reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

Complete source/object pins, source snapshots, commands, compiler/manifest
pins, logs, timings and driver hashes are in
`arithmetic-history222-nat-replay.json`, SHA256
`05d3b53c279829df06a65f2c97d1d6a9ba5cbd7fcb32a1461d67d49495cbbcd8`.
The final free space was 1,216,610,304 bytes, above the 512 MiB reserve. No
accepted source, shared object, Git state or shared documentation was changed.
