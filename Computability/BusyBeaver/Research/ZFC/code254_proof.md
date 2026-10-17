# Finite proof data for the exact numerical calculus

`Lean/BusyBeaver/ZFC/Code254Proof.lean` adds `Type`-valued finite raw syntax for
all twelve `Code254.C254` rules. Its quotation theorem targets the
same formula numbers, not a replacement calculus. The original calculus is
attributed to Mira-Cult; `Code254.lean` identifies the upstream definitions
used by the independent Lean formalization.

The proof encoding is separate from the formula encoding. A proof node is
`12 * payload + tag + 1`, so zero is rejected. Proof code 1 proves formula
code 0 (truth); it does not prove formula code 1 (the relative falsity code).
Cantor pairing carries fields and child proof codes.

| Tag | Rule | Payload |
| --- | --- | --- |
| 0 | truth | 0 |
| 1 | MP, with proposed output `b` | `P b (P minorProof majorProof)` |
| 2 | GEN | `P binder premiseProof` |
| 3 | rho1 | `P a b` |
| 4–7 | rho2–rho5 | `P a (P b c)` |
| 8 | rho6 | `P a b` |
| 9 | rho7 | `P a (P b c)` |
| 10 | rho8 | `P a (P b (P c u))` |
| 11 | gated bundle | `P a (P b c)`, requiring both `c ≠ a` and `c ≠ b` |

The untrusted, fuel-bounded parser returns `Option RawProof`. Structural
functions compute a tree's conclusion and validity. MP requires valid children
and exact equality of the major conclusion with `wim minor.conclusion b`;
GEN validates its child, and bundle validates both freshness inequalities.
The final Boolean checker also compares the conclusion with the requested
formula code. It uses proof-code-plus-one fuel. Quotation bounds tree height
by the code, and the parser roundtrip recovers every original raw tree,
including invalid proofs. Soundness and existence of valid proof data give
the external equivalence

```text
C254 n ↔ ∃ code, check code n = true.
```

Proposition-valued C254 proofs are eliminated only into existence of valid
finite data, avoiding an unspecified chosen proof-tree computation. The checker and
quotation themselves are computational definitions. This is a prerequisite
for the proposed arithmetic interface in [pa_internalization.md](pa_internalization.md).
It supplies neither a PA representation/totality proof nor a compiler from
this proof data into the enumerator, and adds no machine endpoint or
consistency calibration.

The fresh scoped Lean 4.32.0 source check passed in 1.249 s, with empty diagnostics.
Ten axiom reports and thirteen callers passed in 0.233 s; only the three standard
Lean axioms occur. The callers cover arbitrary rule parameters, generic parser
roundtrip and accepted-code soundness, literal MP/GEN acceptance, malformed
parsing, invalid MP, both bundle collisions and requested-conclusion mismatch.
The unindexed revision was independently read in full and found sound.
Evidence: [code254-proof-verification.json](results/code254-proof-verification.json).

The initial indexed draft hit expensive generated recursor normalization and
was not verified. Its diagnostics remain in scratch history. The final
unindexed representation needs no increased elaboration limits. This audit
reuses the source-verified Code254 dependency closure; it does not rebuild the
whole project or imply arithmetic internalization.

The subsequent [explicit compiler](code254_proof_compiler.md) now consumes
this raw proof data and has also passed its scoped check. Both are included
in the checked142-unit umbrella; their internal arithmetic representation
remains a separate obligation.
