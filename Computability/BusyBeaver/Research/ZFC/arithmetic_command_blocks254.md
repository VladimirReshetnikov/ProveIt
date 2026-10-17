# Arithmetic graphs for the actual compiler blocks

[`ArithmeticCommandBlocks254`](../../Lean/BusyBeaver/ZFC/ArithmeticCommandBlocks254.lean)
constructs fixed Σ1 graphs for the command blocks used by the existing
`Enum254` proof compiler. It represents their numeric word construction in
every IΣ1 model and proves that, on ordinary natural inputs, the results are
exactly the shifted encodings of the original command lists.

A small circuit language combines four inputs, 0, 1, addition, literal Cantor
pairing, and the already represented command-word concatenation. For each
fixed circuit, its graph has argument order `(out, a, b, c, u)` and determines
one output at every internal input. Intermediate append values are
existentially quantified; there is no assumed bound by the final output.
The circuit itself is finite external syntax. This is not yet an interpreter
for arbitrary internally coded circuits.

The constructors retain the actual command format: every nonempty word has
the `+1` marker, and an axiom command uses outer tag `c + 3`. The proved
adapters cover individual MP, DROP, NIP and AX commands, the discard block,
all eight leaf blocks, the bundle leaf, and the GEN and MP blocks. The GEN
and MP adapters accept arbitrary symbolic encoded child lists. Their final
three commands are exactly `DROP 0; NIP 0; NIP 0`.

Repetition counts in the block circuits are external natural numbers; the
fixed compiler uses counts at most eleven. The internal append operation
handles model-valued word operands. No recursion on a nonstandard repetition
count is claimed here.

The proofs keep closed command encodings opaque and use symbolic packing
and concatenation equations. This avoids expanding the enormous natural
numbers that encode even short nested command lists. It changes proof
normalization cost, not the machine or its coding.

The [verification record](results/arithmetic-command-blocks254-verification.json)
and [independent review](results/arithmetic-command-blocks254-review.json)
cover fifteen axiom reports and twenty-five callers. All reports use only
standard Lean axioms. The narrow check reuses seventeen matched project
objects from the represented-append evidence and freshly checks this module
and its audit, with no warnings.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_command_blocks254.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/dependency-checkout \
  --append-evidence /outside/successful-command-append/verification.json \
  --output /outside/new-empty-command-blocks-check
```

The [arithmetic compiler history](arithmetic_proof_word254.md) now selects
these blocks using the decoded proof rule and earlier child words. The
[checker recurrence](arithmetic_history_recurrence254.md) supplies the
accepted-child conditions for its later correctness proof. Command execution, scheduler transport, and PA consistency equivalence
remain separate obligations. This result changes no state count.
