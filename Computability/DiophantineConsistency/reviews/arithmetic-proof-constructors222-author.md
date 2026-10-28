# Actual C222 proof constructors: author validation

Author: `controller_certificate`. This is an author receipt, not an independent
review. I also authored the new seed, row, generic sequence-history, actual
history and Nat-binding prerequisites. Root and the other reviewer separately
review those packets. No accepted dependency, shared object, or Git state was
changed for this checkpoint.

The frozen 126-line main imports only
`BusyBeaver.ZFC.ArithmeticHistory222`; the 58-line focused checks import the
main. The complete sources were read before execution and reread after the
final correction.

| File | SHA256 |
|---|---|
| `ArithmeticProofConstructors222.lean` | `98f9d4e10727e493e721406c30b8c26d4e3b1253bae603fc3f51391090bc5ab8` |
| `ArithmeticProofConstructors222Checks.lean` | `29a69d732ba8d9dc11065a174dc16bb3283b9c30abcd075e89b1f99c3f6aa3b8` |
| `arithmetic-proof-constructors222-replay.json` | `57981cb7b33003a917b600c67933d5c1bd24828513935ad0a6a1b42a01c20627` |

The main defines the literal node `12*payload+tag+1` and its fixed Σ₀ graph.
`value_node` derives quotient and remainder normalization from `tag<12`, then
uses the new evaluator's all-internal successor recurrence. GEN reads the
whole tail child; MP reads both tail projections and retains the exact
positive-child/predecessor gate. The twelve rule cases are truth, MP, GEN,
six unchanged rows r1–r6, changed growG, unchanged r8, and the changed
helper-free seed. Tag 9 has no gate and yields the actual growG template.
Tag 11 requires exactly `c≠a` and `c≠b`; the two forbidden cases return zero.
No claim is made about arbitrary tags outside `[0,12)`.

The checks retain code 0 rejection, arbitrary internal MP and composite GEN
children, the fully expanded growG formula, legal `a=b`, legal matrix/binder
`c=0`, and both rejected seed gates. The false code remains 1. `node_nat`
uses only the shared quotation convention from `Code254Proof`, also used by
`Code222Proof`. The proof structure follows the earlier scalar constructor
equations, but imports no old proof-constructor module or old History254
semantics; every value equation is about `ArithmeticHistory222.value`.

The private overlay is `/tmp/constructors222-controller-lnq94s95`. Before
execution and after both successful commands, the driver authenticated all
119 selected custom source files (95 Foundation), all 404 recorded object
companions, 38 explicit external package/toolchain roots, the compiler and
manifest. The inventory hash is
`259db7e172574ab0c954a1b76fbf8aff9bf82a680be6e2c9dfb063247ba3f44a`;
the recorded repository snapshot is
`88cf5fc90ea7abc2e81be1a01247d2964078965b`.
The cached dependency and external-package scopes are inherited from the
accepted receipts named in the JSON; this is not a fresh Foundation build
or a new full external-package closure attestation.

Both new leaves were compiled freshly with the exact 4.32.0 compiler,
`-M6000 -j1 -DElab.async=false`, to private objects. Main and checks passed
in 5.39 and 2.19 seconds; maximum RSS was 1,820,048 KiB. The final main log is
empty. All 15 intended axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

| Private object | SHA256 |
|---|---|
| main | `718bd034c0394664e9922450a35c1b2d5d856e5e4f75e21e290acbc339d724d1` |
| checks | `cba31b68ed32203f480134b0cbb7512516083d04c10a255bbc49d4f9396ee1e5` |

The first main run failed at a numeral conversion in the private small-tag
lemma. Changing `simpa only` to `simpa` normalized numeral 12 to literal 12;
two unused simp arguments in `node_nat` were removed. No definition or
theorem statement changed. The failed source snapshot and log, the final
snapshots, all commands, timings and hashes are preserved in the replay
JSON. The final disk check left 1,192,009,728 bytes free, above 512 MiB.

These theorems supply actual internal proof witnesses for accepted rule
nodes. They do not establish seed validity in set theory, an interpretation
between C222 and C254, a machine runtime theorem, or an HA equivalence.
The proposed CProv222 logical interface is a separate, not-yet-implemented
checkpoint.
