# Rocq replay of the 629-node certificate

The [current proof](../../../../../../rocq/rocq-extension/coq/215/DomRho8.v) retains the exact `DomImp` API and fully general `rho8_all` theorem. The shared finite plan reduces the replay to 629 source nodes, 735 instructions, and 272 symbolic term entries. The resulting source is 22,673 bytes, down from the first compact proof's 23,678 bytes. The generic soundness proof is unchanged; the untrusted optimizer and renderer contribute only data whose final result is checked by the kernel.

The isolated proof passed in 3.122 seconds with two closed-global-context reports; the exact `ThmDom` caller passed in 0.816 seconds. After adoption, all seven affected dependent modules compiled afresh against a private copy of the accepted phase-one objects. `Correct215` and `CorrectDense215` each reported both exported endpoints closed under the global context. All 230 reused object/source bindings and the immutable phase-one objects were checked.

The focused recursive `coqchk -silent -o K215F.DomRho8` passed in 21.490 seconds. Its context report lists no axioms, unsafe fixpoints, assumed positivity, or type-in-type. This is a check of the changed proof and its dependencies. The earlier full 237-module recursive endpoint check remains [baseline evidence](../../../../rocq/README.md); no new full recursive endpoint replay is claimed here.

`execution.tar.gz` preserves the seven fresh source snapshots, logs and records; the 237-module plan and reuse ledger; the focused checker log; isolated tests; generator checks; and the original phase-one source/renderer and metadata pins. It contains no compiled objects. [result.json](result.json) states the execution boundary; [index.json](index.json) binds every archive member. The baseline’s three imported utility axioms remain distinct from the four closed endpoint reports; the latter describe the endpoint proofs’ dependencies.

Regenerate the source without a solver using:

```sh
python3 ../../../../../../generate_domrho8_rocq_compact.py --output /tmp/DomRho8.v
```

Run this command from this directory, or use an absolute generator path. The exact Source149 input selects the shared plan by default; explicit `--plan` and `--no-plan` are supported. Other input certificates keep the earlier generic renderer behavior. All 42 `regenerate215.py` outputs matched current canonical source byte-for-byte. The two current metadata pins were updated by literal replacement, preserving formatting and all old receipts.

The historical incremental runners in the archive retain the actual local paths. For an independent fresh build, use the maintained [Rocq driver](../../../../rocq/README.md). The saved-output auditor beside this README only checks recorded evidence and current source bindings; it does not invoke Rocq.
