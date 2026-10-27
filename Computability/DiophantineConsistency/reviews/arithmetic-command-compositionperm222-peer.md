# Independent actual C222 append-composition review

26 October 2026. PASS, with no source correction requested. Root authored
the 155-line main, 36-line checks and author replay packet. I read their
complete sources and driver, the actual Append/WordEvaluation/Run/Tick/Word/
Replace modules and relevant Step laws before independent execution. I
previously reviewed Replace independently and authored earlier C222 syntax,
history and proof-constructor dependencies; I did not author the runtime
composition under review. This is an independent review of this new leaf,
not an independent reproof of every prerequisite.

The extension preserves the distinction between halt `0` and successful
completion `live 0 W`: the latter becomes `live right W`. Active ticks
commute with continuation extension using actual append and raw-tail
replacement, including raw command 0/NIP. The fixed-left/right/state
induction has a represented pointwise Sigma1 invariant: either the current
pair agrees or a bounded earlier stopped pair agrees. It does not quantify
over arbitrary predicates or invoke an unbounded least stopping time.

The terminal proof uses the actual left drain bound, the run addition law,
and equality of stopped runs. It does not infer an unsupported inequality
between append codes or demand that the composed stopping time be below
the append code. Positive left completion starts the right evaluator;
left halt stays absorbing. Consequently the exact option-encoded equation
`eval (append left right) W = if eval left W = 0 then 0 else
eval right (eval left W - 1)` has the correct subtraction and branches.
The explicit empty-word, halt and successful-completion clients agree.
All claims concern arbitrary internal IΣ1 runtime execution, not a proof
compiler, C222 proof-state invariant, machine calibration, or HA equivalence.

Frozen sources:

- Main: `1e277495b4f9975ae642879a04e68f4bf906f033c02185d8007f88924d75ec2b`.
- Checks: `2494607a25aaa7b029628bd9e10636c2f3815e1a58dd4d97f4403483741c2719`.
- Author replay: `030dd9838e7d5d15546f6184922cd7fa543bb4f9ed2bc38ae01049cc967ad957`;
  author nine-file manifest:
  `d550aa7e65141345e1a7e5bbfd6a6d3a664230467d4d8e89dcd9dc282740b56c`.

Independent private main/check builds both pass, in 6.797s and 1.728s.
The main log is empty; all thirteen checks report only `propext`,
`Classical.choice`, and `Quot.sound`. Both independently generated regular
objects are byte-identical to the author objects:
`6e629ca4e067de5179cdfaa201cdbbbda9fd1cb0e8b6e5efb60e39d6779dbfe2`
and `72b8eb7088809260001f584d729949c19e3b733ed5e69629c81fd58646d90c90`.

The replay authenticates 121 cached custom prerequisites, including 95
Foundation modules, 406 prerequisite artifacts, 38 external boundaries,
and the 1814 inherited/explicit pin records. Current import lists, exact
private provider links, source bytes, compiler, boundary and artifact hashes
were rechecked after the builds. Only these two leaves were compiled;
there is no full-closure fresh replay claim. `LEAN_PATH` excludes the
shared project cache and uses the private overlay plus the pinned package
and Lean runtime paths. Each invocation uses Lean 4.32,
`-M6000 -j1 -DElab.async=false`, with no dependency build.

After the successful main, the 512 MiB guard observed 535,957,504 free bytes
and stopped before any checks invocation. That incomplete record is
preserved. Root later restored disk space through content-preserving
deduplication; I resumed only the checks after full pin reauthentication.
There was no failed Lean invocation, main rerun, or peer cleanup. Both
drivers, the preserved partial record, source snapshots, command arrays,
logs, timings, final hashes and exact object paths are frozen in the
[independent replay](arithmetic-command-compositionperm222-controller-peer-replay.json)
and its [evidence manifest](arithmetic-command-compositionperm222-controller-peer-replay/FILES.json).
The primary private overlay is
`/tmp/command-compositionperm222-controller-peer-d_j3izsj/lib`.
