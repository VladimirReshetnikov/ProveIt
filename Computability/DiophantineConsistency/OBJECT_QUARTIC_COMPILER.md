# The literal quartic conversion proved inside ZFC

`ObjectQuarticCompiler.zfc_proves_compiler e` is an unconditional derivation
in the existing sealed `ZFCax_s` calculus. For every supplied finite integer
expression `e`, it proves the biconditional between the actual sentences
saying that `e` and its compiled quartic have no natural zero.

The compiled expression is the existing `QuarticSyntax.expression`: the
literal squared tree-gate residuals, output equality and normalization guard,
with its existing explicit finite coordinate map. `compiled_degree_le_four`
proves that this expression's actual integer multivariate polynomial has
total degree at most four. The construction does not select a representation
from an existence theorem.

## Why the proof covers internal naturals

`GatesSemiring.lean` proves completeness and soundness for the existing
`QuarticCompiler.Gates.residualSyntax` over an arbitrary commutative semiring.
Its interpretation of integer residual syntax is equality of the two existing
`splitNatural` components. Every expression node has its canonical semiring
value, and every assignment satisfying the literal local residuals has that
value at the root. These are finite inductions on supplied syntax; they make
no assumption that the semiring's values are external Lean natural numbers.

`QuarticSemiring.lean` includes the exact guard and equality of the two output
roots. Its existential theorem preserves precisely equality of the supplied
natural source expressions. The distinguished input coordinate remains unused,
exactly as in the original compiler.

The object-language proof instantiates these theorems with the entire internal
omega semiring of an arbitrary ZFC model. The internal sum-of-squares theorem
identifies the actual compiled expression's zero relation with conjunction
of its literal residual equations. The coordinate equivalences then give
exact zero-existence equivalence, and the existing object polynomial semantics
give the corresponding no-zero sentences. Completeness for the actual sealed
calculus yields `BProv ZFCax_s [] (compilerSentence e)`.

All intermediate values and all source/target assignments range over the
model's entire omega, including nonstandard elements. No conversion of a
nonstandard model element to an external numeral or formula is assumed.
No consistency premise occurs in the compiler theorem.

## Scope and validation

The theorem proves the tree-to-quartic compiler step inside ZFC. It does not
internalize an arbitrary external `Rep.correct` theorem. In particular, the
full numeric proof-checker representation, its internal coding/iteration
proofs, and the final equivalence to the existing internal consistency
sentence remain separate obligations. Nor does this theorem itself improve
a closed equation's variable or operation count. Shared-register quadratic
compilers need their own internal semantic bridge.

The three source modules and the umbrella standard build pass. The dedicated
`checks/ObjectQuarticCompiler.lean` exercises an actual `BProv` instance and
the actual degree theorem, and audits21 dependencies. These use only standard
Lean axioms or subsets: `propext`, `Classical.choice` and `Quot.sound`.
