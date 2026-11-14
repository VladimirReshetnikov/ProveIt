# PA194 finite derivation compiler

`PA194DerivationCompiler.Derivation` is the numerical calculus whose axiom
heads are implemented by the PA194 source: the six inherited logical heads,
the restricted propositional head, the guarded old gate, and the separate
diagonal head. It includes modus ponens and theorem generalization.

`compile_result` constructs a finite command word for every such derivation.
From any incoming top and stack with clean caches, its execution either halts
early or returns the derived formula as top while preserving the stack.
`haltWord_universal` consequently produces, from a derivation of code 1, a
finite command word that halts from every incoming store. Both theorems print
`[propext, Quot.sound]`. All six inherited-head selectors, the restricted
propositional selector, and both the old-gate and diagonal selectors have
been checked for the separate-diagonal PA194 interpreter.

This is a standard-natural-number Lean result for the displayed numerical
calculus. It does not yet prove that the scheduler enumerates every compiled
word, translate arbitrary PA refutations into this calculus, or formalize
those claims in PRA/iPRA. The source/interpreter halting equivalence is proved
separately in `../pa194-command-source`; its source tree retains the pinned
Python grammar-translation boundary documented in `../pa194-source-tree`.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-derivation-compiler/check.sh
```

The script rebuilds the source, command, and diagonal-selector prerequisites
in private tmpfs and checks the remaining selectors and compiler. The complete
fresh script has passed, including all selector modules and the compiler.
