# Proof trust audit and remaining boundaries

## Scope

This review concerns the mathematical arguments and formalization plan in
this packet, against ProveIt commit
`bb86091690bc4f920f046a37cfc87719299b4019`. It is a targeted source and
mathematical review, not a verification of all research packets in ProveIt.
The new Lean files have not been compiled. Numerical verification results
are recorded separately and do not prove universal statements.

## Distinct proof claims

| Claim | What it establishes | What it does not establish |
|---|---|---|
| Explicit PR definition or bound | The stated operation belongs to the intended computational class | Its proposed specification is true or provable |
| Human iPRA proof with an induction audit | A mathematical argument using the permitted schemas and explicit finite constructions | A kernel-checked encoded derivation |
| Host Lean theorem | A theorem in Lean about the supplied semantic data | An embedded iPRA derivation without a further construction |
| `Prf PRAAx Γ φ` construction | An object-calculus derivation from exactly the context Γ, after compilation | Discharge of Γ or a uniform evaluator for all PR definitions |
| Executable checker accepts a proof code | Acceptance by that implemented checker | Internal semantic reflection for every accepted sentence |
| Python diagnostics | Correct output on the listed finite examples | Universal correctness or a complete formalization |

The current packet distinguishes these statuses explicitly. Defining a
desired Lean proposition is not proving it. An uncompiled proof expression
is not yet a checked theorem.

## Arithmetic trust boundary

The target theory is intuitionistic first-order arithmetic with specified
PR symbols and quantifier-free induction. Quantified hypotheses are allowed,
but they remain in a fixed context while the induction formula is a Boolean
equality representing a bounded invariant. The guarded-loop rule requires
the context to be independent of its local step variables.

The bounded Booleanization proof uses prefix products/disjunctions and
first-success registers. It does not assume bounded induction as an
unproved extra principle. A finite proof transformation consumes actual
local arithmetic derivations; truth or primitive recursiveness of an
operation alone does not supply those derivations.

All operations are totalized on natural codes. Typing, nonzero denominators,
valid table shapes, and relevant carrier membership remain explicit guards.
Setoid equality requires its own proved congruence laws and must not be
replaced by literal equality of numerical representatives.

## Categorical scope

The paper distinguishes three settings:

1. Uniform numerical theorems about finite tables.
2. Theorem schemes after fixing PR presentations and their laws.
3. An external category organizing those fixed presentations.

The third setting is not silently internalized as a universe of all
functions. The diagonal argument rules out exactly a total PR evaluator on
natural codes covering all unary PR functions. It does not rule out FinSet
exponentials, which have explicitly finite domains.

The finite category constructions handle empty domains and `0^0=1`.
Finite Kan extensions use explicit generators or compatibility equations,
and their universal-property proofs include mediators and inverse
correspondences. The split-equivalence criterion supplies the lift and
object-isomorphism data; in infinite presentations these cannot be extracted
from a bare cardinality or essential-surjectivity assertion without an
additional bounded-search or selection argument.

The finite-query contract category uses forward data and backward finite
sets of questions. Composition uses finite union. Its products satisfy
the categorical uniqueness property with the stated extensional equality
of query sets. No function-space or closed-structure theorem is imported
from the general Dialectica literature.

## Algebraic production scope

Acceptance of the supplied degree caps yields exact multiplication
identities. Evaluating them at any common zero gives a nonzero common left
eigenvector. The denominator lemma and the absolute column-sum bound give
the displayed finite rational grid. Matrix commutation and independence
of the spanning family are unnecessary.

The negative outcome is a separator for one finite linear system. It does
not prove that the polynomial equations have no rational solutions. The
algorithm does not repeatedly increase degree caps without a proved bound.

A full coordinate action certificate forces a finite-dimensional quotient:
the explicit fixed-order monomial reduction gives a spanning family. Finitely
many rational points alone do not imply this algebraic condition. Therefore
the result does not provide general Faltings or Siegel bounds, a missing
global finite cover, or a uniform cap theorem for every intended input.

## Gluing and inverse-limit scope

Finite sheaf gluing uses exact compatibility and bounded least-patch search.
Replacing exact equality with approximate agreement would require a different
error contract and does not retain the same uniqueness conclusion.

The CRT result glues two finite residue conditions, including noncoprime
moduli. It does not identify arbitrary compatible infinite congruence towers
with rational or ordinary integer solutions of a separate problem.

The explicit binary tree has PR tests and a PR selector at every finite
level but no computable coherent branch. Its restriction maps are not
asserted surjective. The positive tower theorem adds a proved bounded
surjective lifting contract; least-preimage search and PR iteration then
give a coherent point.

The decidable two-class equivalence-family obstruction rules out a uniform
computable covering-list producer. It is not an independence claim for any
particular elliptic curve. The positive skeleton theorem instead consumes
a supplied complete finite cover and produces its representative sublist
and equivalence data explicitly.

## Outstanding formal verification

The exact Lean and Mathlib pins, intended build commands, file-by-file
status, representation differences, and completion milestones are in
`lean/FORMALIZATION.md`. The main unfinished layers are numerical PR
reification, Boolean validation/reflection, local arithmetic object proofs,
the bounded solver and constructor correctness proofs, and their final
`Prf PRAAx` derivations. Native translation is performed only after those
derivations exist.

There is no newly checked Lean theorem in this delivery, no generic verified
proof compiler, and no exported arithmetic proof checker. The finite Python
diagnostics are useful implementation checks with deliberately narrower
scope. These limitations leave the mathematical arguments and explicitly
stated conditional constructions intact while identifying the work needed
for complete formalization.
