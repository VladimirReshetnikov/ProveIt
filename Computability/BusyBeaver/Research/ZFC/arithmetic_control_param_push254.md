# Actual MP parameter pushes and comparison tail in internal arithmetic

`ArithmeticControlParamPush254` proves both actual MP parameter pushes in
all models of IΣ₁. The initial block runs from control 6367 to the unpair
entry 6393. The success block runs from 6434 directly to fetch 0. With both
scratch registers initially zero, each sends

```
TW := old param1
WS := cantor(old TW, old WS)
```

and preserves every other physical register, including param1, cache and both
scratch registers. The proof composes checked transfers, copying and pairing
through finite shapes whose controls and continuations are bound to the actual
program. The initial push reuses the checked MP pairing occurrence; the success
push has its own actual pairing shape. No new induction is introduced.

The parameter copy-and-restore sub-block has the exact logical runtime
`7*param1+2`. It adds param1 to TW and preserves all other fields when scratch1
is zero. The full pushes have positive internal runtime witnesses because the
pairing contract has an existential runtime.

The module also closes the tail from actual comparison entry 6423 to fetch.
This contract requires only scratch2=0. Comparison clears scratch1 and cache.
On equality of their original values, the success push then runs; on inequality,
the checked comparison returns directly to fetch. The whole-file endpoint
records both cases explicitly. An audit caller specializes the success push
to TW=0, giving `WS := cantor(0, old WS)` for the eventual full MP composition.

The first source and focused audit checks passed 12 ordered axiom probes and
22 callers with only `propext`, `Classical.choice` and `Quot.sound`, and no
warnings. Source checking took 8.220 seconds and the audit 2.572 seconds.
The guard matched 97 project prerequisites, six cached external boundaries and
217 inputs before and after checking. It recorded the fresh source object
before the audit and verified the same object afterward.

The two proof commands used one thread, 4 GiB, default Lean limits and a
120-second timeout. Dependencies, site guards and bootstrap proofs were not
rebuilt or replayed. The portable guard is byte-identical to the executed
guard. The initial scratch-path and maintained-default preparations each
queried the compiler version and compiled no proof. The source author and root
reviewed the source and evidence; no additional independent child review is
claimed.

Full MP still needs the short unpair at 6393–6403, constructor pairing at
6404–6413, times-four transfer at 6414–6419, transfer at 6420–6422, and their
composition. AX, the internal interpreter-to-Enum connection and final PA
equivalence remain open. No first-exit property, exact binary-step clock or
new machine state count is asserted.

```sh
python Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_param_push254.py \
  --repo "$PWD" --dependency-root /path/to/pinned/Proofs \
  --compare-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-compare254-verification.json \
  --output /external/fresh/param-push-check
```
