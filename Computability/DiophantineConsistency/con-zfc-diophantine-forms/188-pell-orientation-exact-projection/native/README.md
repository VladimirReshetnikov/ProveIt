# Two lower-degree fourteen-positive consistency equations

Prepared for ProveIt, 25 October 2026 (client date), with AI assistance.
Comparison snapshot: `cdfea7d90176775d74c1c30afbe49fa78ade9897`.

| Literal circuit | Domain | Unknowns | Binary integer operations | Exact degree |
|---|---|---:|---:|---:|
| `circuits/q66_d118.json` | strictly positive integers | 14 | 66 = 37 multiplications + 16 additions + 13 subtractions | 118 |
| `circuits/q67_d94.json` | strictly positive integers | 14 | 67 = 37 multiplications + 17 additions + 13 subtractions | 94 |

Both use the complete current block-mask2963 coefficient tuple: four fixed
integers, 69,685 raw bytes. The compressed payloads and exact hashes are
included, together with the complete printed finite recipe in
`sources/block-mask2963_equation.tex`. That historical TeX prints the P66
parent on its front; the two new equations are defined in `PROOF.md` and
the literal circuits. Its constant suffix is the new circuits' exact tuple.

These are proved compositions of the incoming first-Pell carrier reduction
and existing reduced/ordinary strong norms. They are a complementary
arithmetic improvement, not a new proof-calculus encoding or a claim of
literature-wide novelty. The incoming Carrier65 equation already has 14
positive unknowns,65 operations,degree150. Our first point pays one operation
to reduce its degree to118; the second pays two to reach94. The earlier
source142 fourteen-positive forms cost70/189 and71/157. Our equations
improve those two in both cost and degree. Lower-degree forms, such as
fourteen-positive24/101, remain separate tradeoffs. The source59 parents
of the present constructions had15 positive unknowns and67/125 or68/101.

`PROOF.md` proves the new transformations, gives the exact full definitions,
and describes the inherited native/Pell/refutation boundary. It establishes
the ordinary ZFC-formalizable equivalence

    no positive integer zero  <->  Con(ZFC).

No consistency assumption, proof of unsolvability, global minimum claim,
or new end-to-end Lean/Rocq certificate is made.

## Reproduction

Use Python 3.10 or later, standard library only:

    python3 build.py
    python3 verify.py

The producer reconstructs both literal circuits from authenticated parent
data. The independent verifier imports no producer. It checks all arithmetic
rows through24 exact display-cut identities per circuit, full liveness,
integer-only leaves, charged operation counts, the entire323-term main-norm
expansion, both complete40-term highest homogeneous forms, and a nonzero
fixed-coefficient monomial at the reported degree. It authenticates all four
coefficient payloads and checks their scalar ranges, low residues, population
balance and the two closed mask recipes. The final `verification.json`
contains its actual receipt. Its signed sample evaluations are transcription
diagnostics; the ordinary proof supplies the unbounded theorem.

`evaluate.py` accepts one JSON dictionary containing exactly the fourteen
positive witness values. For example:

    python3 evaluate.py q66_d118 example_witnesses.json --modulus 1000000007

Omit `--modulus` for exact evaluation; values may become very large.
The supplied all-ones dictionary is only an evaluator example and is not
claimed to solve either equation.

## Provenance

`SOURCE_PROVENANCE.json` identifies the exact upstream paths, pins and hashes.
The current native proof, its retained finite controller certificate, the
block-mask recipe identity, the earlier relaxed-rank proof, the squared-
modulus reconstruction, and the first-Pell carrier proof are included under
`sources/`. Historical internal relative paths in copied proof documents
are preserved as provenance; the explicit source ledger gives their origin.
No unchanged native/compiler/proof-assistant check is represented as a new run.

The new code and proof are offered under the accompanying MIT No Attribution
license. Upstream attribution and Wade/K215 notices are retained.
