# H2082 with shared products: 440 operations

The nine-positive equation now has **440 live binary operations**, down
from443, with the same polynomial and exact degree **1,845,940**. The
nine-natural translation drops from450 to447 operations. Every coefficient,
variable, witness domain and named register retains its original value.
This is an ordinary algebraic reduction made while Lean work is paused.

## The three savings

Use the parent candidate's registers `M,U,k,C,D,R`. Introduce the
abbreviation `MU=M*U`, which adds no unknown. Replace

```
P = 2*M^2*U       by P = 2*M*MU
A = M*(U+1)       by A = M+MU
E = k*D*C         by E = k*(C*D).
```

The parent already needs `C*D` in `Lambda=C*D+1-A`. The `P,A` pair
therefore costs four operations instead of five; the `E,C*D` pair costs
two instead of three. Finally, the parent's rank is computed as

```
R1 = L*(Scode+Tcode+1)-Scode
R  = R1-1.
```

Use `R1` directly in `K=R1+h*(P-1)`. This removes the parent's operation
which recomputed `R+1`. All three changes are identities over every
commutative ring, without positivity or nonzero assumptions.

| Domain | Parent | This circuit | Multiplications | Additions | Subtractions |
|---|---:|---:|---:|---:|---:|
| Nine positive integers |443|440|261|157|22|
| Nine natural numbers |450|447|261|165|21|

Counts charge every live binary addition, subtraction and multiplication,
including squares and multiplication by a fixed scalar. Reusing a register
and constructing a fixed numeral are free, as in the parent comparison.
All nodes and all nine inputs in both delivered DAGs are live.

## Exact identity certificate

`positive_rewrite.json` and `natural_rewrite.json` give the complete gate
remaps and four changed-node certificates. An independent verifier expands
each changed expression as a small sparse polynomial over **integers** in
its earlier parent registers. It checks coefficient equality exactly.
Every other retained gate must have the same operation and remapped
operands, with only the commutativity of addition/multiplication allowed
when ordering operands. It checks that every new node is accounted for,
all named values are preserved and both output nodes correspond.

Induction over the original DAG proves equality of its named registers
and final output with this DAG. The local cut points always precede their
changed original node; thus there is no circular equality assumption.
The two circuits represent exactly the same polynomial. In particular,
their zero sets in the stated domains agree, and the parent's ordinary
cancellation-aware exact-degree certificate transfers unchanged.

Each domain also has60 modular assignments, using the actual fixed
integers, comparing every named value and the output over three primes.
These are transcription diagnostics in addition to the ring identities.
Changing the new `A=M+MU` operation to subtraction is rejected by the exact
identity check, even though the circuit's operation count is preserved.

## Coefficients and mathematical scope

All11 nonliteral fixed leaves are reused byte-for-byte from
[`../gap2082-compact54/fixed/BINDING.json`](../gap2082-compact54/fixed/BINDING.json).
Each DAG repeats the unchanged coefficient recipes and source/layout pins.
The builder authenticates both parent circuits and every compressed and
uncompressed fixed-leaf hash. No unprinted new parameter is introduced.
The parent is retained without changes.

The parent source/kernel/packing proof obligations and native calibration
status are inherited exactly. This size reduction does not complete the
native machine calibration or the object-language ZFC equivalence, and
does not add a Lean theorem. See the parent README for that boundary.

## Reproduce

From the repository root:

```
python3 Computability/DiophantineConsistency/tools/build_shared_products66.py --check
python3 -O Computability/DiophantineConsistency/tools/build_shared_products66.py --check
```

Without `--check`, the same tool regenerates the six JSON artifacts.
`MANIFEST.json` authenticates their deterministic bytes. No Lean process
or compiler is invoked.
