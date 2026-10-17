# Internal zero and one scans in both directions

[`ArithmeticMachineUniformScansPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticMachineUniformScansPerm252.lean)
extends the [first actual scan](arithmetic_machine_scan_perm252.md) to either
bit and either direction. Each theorem assumes the corresponding self-loop
equation for the actual `actionLookup`. A finite literal-row check supplies
that premise for a chosen numeric state in every IΣ1 model.

For `frame q L R = cantor q (cantor L R)`, the rightward endpoint is

```
runFrom n (frame q L (bitPrefix b n X)) = frame q (bitPrefix b n L) X
```

The left-facing representation is
`leftFrame q L R = frame q (L/2) (L%2 + 2*R)`. Its endpoint is

```
runFrom n (leftFrame q (bitPrefix b n L) R) = leftFrame q L (bitPrefix b n R)
```

All lengths and tape halves are arbitrary internal values, including zero.
The left representation moves the numeric reference position to the adjacent
cell and retains both halves. It introduces no external head-coordinate
assumption. Both proofs use Π1 induction with universally quantified tape
parameters and total Δ1 functions. These are endpoint theorems; an identical
bit at the suffix boundary may allow the scan to continue.

One prefixes use the existing bounded graph. Zero prefixes are
`Exp.exp n * suffix`; their fixed Σ1 graph uses an existential power witness,
so zero suffixes do not require an invalid bound on that power by the output.
The action-decoding lemmas retain the write and direction in both cases.

The [fresh check](results/arithmetic-machine-uniform-scans-perm252-verification.json)
passes 21 axiom reports and 18 callers with standard Lean axioms and zero
warnings. Four callers use actual rows: numeric state 10 scanning zeros
right, 72 scanning ones right, 4 scanning zeros left, and 3 scanning ones left.
The [independent review](results/arithmetic-machine-uniform-scans-perm252-review.json)
binds the complete source, audit, 27 project providers and fresh object.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_machine_uniform_scans_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --scan-evidence /outside/successful-machine-scan/verification.json \
  --output /outside/new-empty-uniform-scans-check
```

The portable checker prepares successfully with maintained defaults and in
a separate minimal checkout with relocated prerequisite objects. Those
preparations build no proofs. The original failed source attempt is retained;
qualification, numeral typing and simplifier fixes resolved its elaboration
errors without changing the scan contracts. The complete register/dispatcher
and PA consistency comparisons remain open.
