# Repository and certification-boundary audit

Inspection date: 2026-11-15.

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned `main` commit: `d72c8b24637e342816dc92d11bef337748683e51`.

The GitHub branch response identifies this commit and its tree
`a1b1627d8b6d90203d5fbac5739803ab137606b1`. All source reads listed below used
that commit as their `ref`. The repository's toolchain is
`leanprover/lean4:v4.32.0`; its Lake manifest requires Mathlib `v4.32.0`.

## Reusable, inspected source interfaces

All names in this table lie in namespace `LeanProofs.ConciseIPRA`.
The source directory is
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/`.

| Source | Inspected definitions and results | Use in the proposed formalization |
| --- | --- | --- |
| `Syntax.lean` | `Syn`, `Fm`, `Fm.QF`, capture-avoiding substitution, `Fm.all`, `Fm.ex`, `Fm.imp`, `Fm.or`, `Fm.eq` | Define the arithmetic sentence and its bounded/quantifier-free matrix. |
| `Deduction.lean` | `Theory`, `Prf`, intuitionistic natural-deduction constructors, substitution/weakening/cut, equality transport | Construct a derivation in the object theory, not only an external theorem about numbers. |
| `PR.lean` | `PR k`, constructors `zero`, `succ`, `proj`, `comp`, `prec`; `PTm n`; `PRAAx`; `PRA.qfInd` | Compile each fixed primitive-recursive program and carry out only quantifier-free induction internally. |
| `BiInterpretation.lean` | `biInterp`, `pra_iff_teq`, `teq_iff_pra`, `pra_theorem_iff` | Transport an established internal theorem between ordinary iPRA and the scalar presentation. |
| `NativeBiInterpretation.lean` | `NFm.ofPRA`, `NFm.toPRA`, `pra_iff_native`, `native_iff_pra` | Transport an established internal theorem into the native concise calculus. |
| `Lindenbaum.lean` | Quotient `Q Γ`, `Q.sound`, `Q.exact`, `Q.eqInd` | Optional route for doing internally certified equation algebra. |
| `TeqArith.lean` | `Tm.sel`, `Tm.add`, `AddCommMonoid (Q Γ)` | Existing selector and internally certified addition. |
| `TeqOrder.lean` | Order through truncated subtraction, `Q.add_monus_of_le`, `Q.succ_le_pow2` | Basic order and coarse numerical growth estimates. |
| `TeqPair.lean` | `Tm.pair`, `Tm.pfst`, `Tm.psnd` | Encode finite loop states. |
| `TeqRec.lean` | `Tm.prc`, `prc_zero`, `prc_succ` | Simulate parameterized primitive recursion by the scalar iterator. |
| `TeqReflect.lean` | Boolean reflection `chi`, `chi_iff`; `Teq.qfInd` | Package finite conjunctions and comparisons into equation induction. |

The ordinary iPRA presentation has the defining equations of all PR symbols,
successor injectivity, successor nonzeroness and induction for quantifier-free
formulas. `PRA.qfInd` takes a syntactically quantifier-free formula, a base
derivation and a successor-step derivation. Its conclusion is an internal
universal formula. In particular, unrestricted external Lean induction is
not a replacement for these arguments.

## Exact theorem boundary

A completed formalization must construct a closed formula
`aperyFormula : Fm PTm 0` and a term of type

```lean
([] : List (Fm PTm 0)) ⊢[PRAAx] aperyFormula
```

The matrix should assert the paper's concrete, denominator-cleared finite
separation inequality, with every displayed cutoff represented by a fixed
PR function symbol. No variable ranging over arbitrary real numbers,
arbitrary functions or infinite sequences is needed.

After this derivation exists, `pra_iff_native` produces a derivation of
`NFm.ofPRA aperyFormula` in `NPrf`. The bi-interpretation does not turn an
arbitrary theorem proved in Lean's ambient mathematics into an iPRA theorem.

Likewise, an external statement that a checker is primitive recursive, an
inhabitant of a structure assuming all missing bounds, or a theorem about
Mathlib's `Real` alone would not cross the required boundary. An external
real-analysis corollary may identify the rational name with the usual
`ζ(3)`, but the internal finite theorem is a separate deliverable.

## Related draft actually inspected

`docs/drafts/basel_ipra.zip` was fetched at the pinned commit and unpacked.
Its Git blob SHA is `e75b8b86bc07d387b1e2db7f78e2e71f572e3c15`.
The inspected files include its README, `lean/BaselSpec.lean`,
`lean/ObjectTheoryTarget.lean`, and `lean/ROADMAP.md`.

That package explicitly labels its Lean files as uncompiled specifications
and a roadmap. It does not provide a completed object-theory Basel proof.
It is useful for the raw signed-fraction convention `(positive, negative,
denominator)`, natural-number comparison after cross-multiplication, fixed
loop compilation, and the distinction between semantic agreement and an
internal derivation. No missing Basel theorem is imported as an assumption
in the Apéry argument.

The current `docs/drafts` listing also contains PNT, Brun, calculus and zeta
packages, but directory listing alone does not establish their mathematical
or formal status. No such package is used as a proved dependency here.
The listing contains no archive whose name identifies an Apéry proof.
GitHub code-search results were used only for discovery; their index referred
to an older commit, so they are not evidence of a complete current-tree audit.

## Build status and reproducibility

The inspected ConciseIPRA README reports that its modules build without
`sorry`, custom axioms or `native_decide`, and reports the ordinary
`T_eq`/iPRA bi-interpretation as depending on `propext` and `Quot.sound`.
That is the repository's recorded status. A full repository build was not
repeated for this package.

No `lean`, `lake` or `elan` executable was found on `PATH` or by the scoped
toolchain search in the authoring environment. New Lean files supplied with
the package must therefore be described as uncompiled specifications/outline
unless a subsequent environment actually checks them. A file without `sorry`
can still be only a specification: explicit hypotheses and uninhabited
obligation structures must not be presented as a proof.

To complete the formalization, place the new modules in a Lake library in
the pinned checkout, run the matching Lean 4.32.0 toolchain, and inspect both
the type and `#print axioms` output of the final internal theorem. The type
must contain `Prf PRAAx`; the axiom report must contain neither `sorryAx`
nor a custom assumption supplying any arithmetic lemma.

## Source URLs

- https://github.com/VladimirReshetnikov/ProveIt/tree/d72c8b24637e342816dc92d11bef337748683e51/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
- https://github.com/VladimirReshetnikov/ProveIt/blob/d72c8b24637e342816dc92d11bef337748683e51/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/d72c8b24637e342816dc92d11bef337748683e51/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/d72c8b24637e342816dc92d11bef337748683e51/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/BiInterpretation.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/d72c8b24637e342816dc92d11bef337748683e51/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/d72c8b24637e342816dc92d11bef337748683e51/docs/drafts/basel_ipra.zip
