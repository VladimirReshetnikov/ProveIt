# Actual C222 represented history: author validation

The controller-certificate agent authored and fully read the new 208-line
`ArithmeticHistory222.lean` and 55-line focused checks before executing them.
Both passed their first fresh compilation. This is an author receipt, not an
independent peer review. The same agent authored the generic sequence history,
Row222, the Nat C222 checker, and the seed/growG prerequisites; those packets
have their own separate review records.

The fixed `positiveStepDef` binds variables in the order `r, s, raw`. It reads
the predecessor's remainder modulo 12 and quotient, the Cantor payload tail
and its two components, then the actual sequence lookups. Tag 2 reads the
whole tail; other tags receive the minor component as the first child. The
second child is always the major component. Its final graph is the new
`ArithmeticRow222.rowDef`, including actual growG and helper-free bundle222.
`stepDef` binds `r, s, code`, rejects code zero, and otherwise requires the
bounded predecessor equation `code = raw + 1`. The existing predecessor lemma
used here is arithmetic only.

The new evaluator instantiates the frozen generic `ArithmeticSequenceHistory`
instead of copying or renaming the C254 primitive-recursion implementation.
It imports no `ArithmeticHistory254`. Its history/value graphs are fixed Σ1
and Δ1 formulas independent of the model, with genuine represented-function
instances. At every element of every IΣ1 model it proves sequence validity,
length `code + 1`, unique history/value, zero and successor equations, the
exact value at every earlier index, and zero at every later index. Quotient
and Cantor projection bounds place all three possible child indices at most
`raw`, including zero predecessor/payload. Thus `value_succ` passes this same
evaluator's actual child values to the actual new row without a child-validity
premise.

The small final layer defines a fixed acceptance relation, represented
Boolean result, unique Boolean evaluation, and the literal closed sentence
asserting that totality. `isigma1_proves_totality` uses Foundation's existing
arithmetic completeness theorem to establish actual IΣ1 derivability of that
sentence. It is not merely an external existence theorem about a desired
checker. It also does not assert internal seed validity, C222-to-C254 proof
translation, interpreter execution, or the requested HA equivalence. Agreement
with `Code222Proof.check222` at every Nat code remains a separate next packet.

Frozen sources and fresh objects:

| Module | Source SHA256 | Fresh object SHA256 |
| --- | --- | --- |
| `BusyBeaver.ZFC.ArithmeticHistory222` | `42c196715f04b4bd8d257a3450e0947a13a62c9332e06c62b556a835d60156b8` | `1bcb989a5ca4e9c40390bc12f2bfbe37a691423ce666eee9b59afb2c602b2057` |
| `BusyBeaver.ZFC.ArithmeticHistory222Checks` | `aa553cf0e5d9ab5b760b3dfafc9f648de97be168e2ce802239ab9814957145f3` | `5dd7eb3601dc9b741f448c2ac9c21f3e3d5a6069a963c2448e630f38d8c491f3` |

The private overlay is `/tmp/history222-controller-bjlb3sco/lib`, prepared at
Git snapshot `7fb9eb574b14ff760c3fee396e07345ea1b4d59e`. Its prerequisite
inventory has SHA256
`c24d3865cf1b501e998581c460b10cbccef6eba7f9e8c99d243bc320ebfd3cd8`.
All 118 selected custom sources (95 Foundation and 23 project sources),
403 associated cached object/companion files, and 38 external boundary
objects were authenticated before execution and rechecked afterward. The
inventory incorporates the accepted generic-history and Row222 objects by
their exact final source/object pins. External package internals were reused,
not freshly rebuilt or newly attested transitively. No broad closure replay
or fresh Foundation build is claimed.

Both direct commands used Lean 4.32.0 with `-M6000 -j1
-DElab.async=false`, private output paths, and the recorded private `LEAN_PATH`.
The main took 10.83 seconds and checks 3.67 seconds; peak resident memory was
1,830,256 KiB. Main diagnostics were empty. The checks exercise both graph
classes, zero/successor conventions, totality, full lookup, child bounds,
the exact new-row recurrence and the actual closed derivability theorem.
All 14 printed axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. Source snapshots, commands, logs, compiler and manifest pins,
timing files and driver hashes are retained in
`arithmetic-history222-replay.json`, SHA256
`2f17663e8b2448c2ed2e7bc8201985dbb862d87cf8580ed384e4df184ab37049`.
The two leaves passed on the first attempt; there are no rejected development
runs. The final reserve was 1,232,949,248 bytes, above the 512 MiB minimum.
No accepted source, shared object, Git state, or shared documentation was
changed by this packet.
