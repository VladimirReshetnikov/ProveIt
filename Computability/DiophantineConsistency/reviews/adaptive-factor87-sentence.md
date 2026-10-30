# Arithmetic sentence for the 87-gate adaptive expression

`AdaptiveFactor87Sentence` defines the two actual arithmetic no-zero
sentences using `ArithmeticExpression.noZeroSentence`, proves that both are
closed, and proves that their satisfaction is equivalent in the arithmetic
structure associated with every commutative semiring. It uses the literal
zero-test equivalence already established for arbitrary internal tuples.
The new definition is for the 13-variable adaptive equation, not the
14-variable equation in `equation.pdf`.

This is a Lean metatheorem about satisfaction. It is not yet an HA or PRA
proof of the object-language equivalence, and it does not establish either
sentence's equivalence to `Con(ZFC)`. Turning this semantic bridge into a
suitable formal derivation and completing the parent adaptive construction are
separate obligations.

The author build `/tmp/adaptive-factor87-sentence-author-dhbjk05i` and the
independent build `/tmp/adaptive-factor87-sentence-independent-1p2n4_0i`
used the separately replayed literal providers. They passed the main and
check modules with matching source, object and complete log hashes:

| Module | Source SHA-256 | Object SHA-256 | Log SHA-256 |
| --- | --- | --- | --- |
| `AdaptiveFactor87Sentence` | `6c809a17971c50cb7c088bfe42f739dec7e9d92c140af057cca70a4d1fa3a21d` | `00faeb94bd8ac81aa53b2e697867dab476a4cc5b99e7ca6510272a5f4ce62b0e` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `AdaptiveFactor87SentenceChecks` | `d907479a05205a3865a3c9b789cc3184231012d2e8519f84569649daa0b45c89` | `297260dbf1e9906860a1581fbd7118aef09413502c96ba4064d9bce061b18d66` | `e3925da7755bbabb94df60073a83c01dc22b7867fd9bd4312eafecd34b9641f0` |

The retained [logs](adaptive-factor87-sentence-replay/) report only
`propext`, `Classical.choice` and `Quot.sound`. The guarded literal providers,
Mathlib and the Lean toolchain are inherited boundaries of these builds.
