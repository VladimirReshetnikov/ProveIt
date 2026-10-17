# PA proves the fixed 252-state bootstrap result

[`ArithmeticBootstrapPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticBootstrapPerm252.lean)
transfers the already checked 82,552-step bootstrap into every IΣ1 model and
proves its fixed arithmetic sentence in IΣ1 and PA. The result code denotes
the entire existing target tape and canonical dispatch state 94. Its numeric
state code is 95.

Two finite zipper lists describing the same complete Core configuration have
the same numeric tape code, even if one lists more trailing blank cells. This
uniqueness connects the [numeric run](arithmetic_machine_perm252.md) with
`BootPerm252.fullBootstrapPerm252`. The new proof reuses all 25 checked boot
blocks; it does not recompute the 82,552 transitions.

The represented run has the same fixed Σ1 graph over Nat and every IΣ1 model.
Function absoluteness therefore transfers each external natural time and its
result to the corresponding numerals. Specializing at 82,552 gives the exact
bootstrap equality. Arithmetic completeness then yields the fixed IΣ1 and PA
derivations. This finite-prefix result does not supply unbounded instruction
simulation at arbitrary internal register sizes.

The [fresh check](results/arithmetic-bootstrap-perm252-verification.json)
passes eleven axiom reports and thirteen callers, with only standard Lean
axioms and no warnings. It reuses 24 machine-arithmetic prerequisites plus
the separately identified literal Boot module, five external providers and
toolchain Omega. The [independent review](results/arithmetic-bootstrap-perm252-review.json)
checks the complete source, audit and provider identities.

The early source and audit attempts exhausted the kernel memory limit while
reducing the huge tape numeral during specialized simplification. Proving
the graph-evaluation lemmas at generic arguments first removes that reduction.
The final source and audit pass in about two seconds each. The failed attempts
remain recorded; no resource limit was raised.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_bootstrap_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --machine-evidence /outside/successful-arithmetic-machine/verification.json \
  --bootstrap-evidence /outside/arithmetic-machine-perm252-integration-verification.json \
  --output /outside/new-empty-arithmetic-bootstrap-check
```

Maintained-default preparation is recorded separately from the kernel check.
The actual 252-state table and bootstrap retain the attribution in
[`BootPerm252`](../../Lean/BusyBeaver/ZFC/BootPerm252.lean) and
[`BinaryPerm252`](../../Lean/BusyBeaver/ZFC/BinaryPerm252.lean). The whole PA
consistency equivalence remains open.
