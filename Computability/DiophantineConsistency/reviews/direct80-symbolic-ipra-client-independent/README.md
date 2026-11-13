# Independent review: parameterized and fixed symbolic iPRA clients

The accepted `Direct80SymbolicIPRA.lean` parameterized client and `Direct80SymbolicFixedIPRA.lean` specialization assert **syntactic derivability in the named intuitionistic theories**, not merely a model equivalence. Their claims concern the selected symbolic Lean graph. They do not yet identify that graph and its symbolic coefficients with the retained 80 K0, the direct-BFS kernel, or `equation.pdf`; they do not constitute an independent audit of every transitive imported object.

## Exact expression and consistency forms

Let `e=(graph (integerPorts p)).output`, an expression with ten free graph coordinates and four natural parameters supplied by p. `positiveShift e` substitutes `x+1` for every graph variable once. `IPRAExpressionNative.nativeNoZero` universally quantifies those ten natural variables and asserts inequality of the two nonnegative terms in the expression's `splitNatural` pair. Thus the asserted sentence is the native no-zero statement for that exact **shifted Lean expression**; connecting it to a different displayed equation requires a separate graph/file/port identity.

The client forms are exactly:

```text
standardTheory ⊢ nativeNoZero (positiveShift e) ↔ ¬mappedNativeRefutation embedding
standardTheory ⊢ nativeNoZero (positiveShift e) ↔ (lMap embedding sourceSentence)ᴺ
referenceTheory ⊢ erase (nativeNoZero (positiveShift e)) ↔ ¬erase (mappedNativeRefutation embedding)
referenceTheory ⊢ erase (nativeNoZero (positiveShift e)) ↔ erase ((lMap embedding sourceSentence)ᴺ).
```

The second pair applies the stated order erasure. Here `sourceSentence` is defined in the imported Foundation pipeline as the consistency sentence of Foundation's `ZermeloFraenkelChoice` theory, `lMap embedding` is its target-language map, and `ᴺ` is the pipeline's negative translation. The other right side is the negation of its specifically defined mapped native refutation predicate. These precise forms should not be silently replaced by an unexamined, differently encoded or untranslated consistency formula.

The repository's `Lean/DiophantineConsistency/IPRAStandardTheory.lean` presents `standardTheory` with intuitionistic first-order logic, finite-code primitive-recursive function symbols and their defining equations, equality reflexivity and atomic substitution, successor basic axioms, a characteristic-code `<` relation, and successor-form induction for all quantifier-free formulas with parameters. `Lean/DiophantineConsistency/IPRAEqualityOnlyReference.lean` defines `referenceTheory` in an equality-only finite-code language, with reflexivity and substitution, zero/projection/composition/primitive-recursion defining equations, successor nonzero, and the stated quantifier-free successor induction. The proofs call imported conversion theorems; the scope here is the selected provider and receipt evidence, not a fresh audit of the entirety of those conversions.

## Parameterized and fixed statements

`Direct80SymbolicIPRA.positive_bridge` derives the all-`IΣ₁`-models positive-zero ↔ model-halt bridge from exactly four natural premises

```text
p 0=betaNat       p 1=paramKernel rho
p 2=lowNat        p 3=betaNat+highNat.
```

The four parameterized `standard_consistency`, `standard_translated_consistency`, `reference_consistency`, and `reference_translated_consistency` theorems have those same four premises and the syntactic conclusions above. They invoke the positive-model adapter and the standard/reference derivation conversions. This is an inference in Lean, whose theorem statements are derivability propositions; it does not require printing a literal iPRA proof.

`Direct80SymbolicFixedIPRA.fixedPorts` is exactly `ports betaNat (paramKernel rho) lowNat highNat`. The four corresponding **closed** fixed theorems have no remaining port hypotheses; their proof applies the parameterized theorems with generic four-coordinate projection lemmas, keeping the large kernel opaque. Their graph parameter uses the `CompactSymbolicKernel.paramKernel rho` symbolic/original-kernel choice, not an identification with retained candidate K0 or direct-BFS bytes. This is a material proof milestone for the named symbolic graph and exact formal consistency sentences, subject to the inherited proof/provider and binding boundaries described below.

## Independent receipt checks and limits

`check.py` and `check-fixed.py` verify the current and copied source, runner, log and object hashes, pre/post pins, and first selected direct imports of the accepted parameterized `client-attempt02` and fixed `fixed-attempt01`. They scan both accepted sources for `sorry`/`admit`, check the five and four expected axiom reports, and reject logged diagnostics or `sorryAx`. The fixed client imports the **same** selected parameterized object, SHA `4b809946fdcba0f7f4763b306307945c534f686da8926db52965abcd97381bad`. The parameterized client's other direct input is the positive-model iPRA reference/translation adapter; its symbolic-port projection is the same reviewed object SHA `b29a920b26eaa4ee347d9471a4a32bf38785883719826ceaa3246f37b4ae8809`. All exact selected paths, real paths where applicable, receipt/source/runner hashes, and object hashes are in the two output files. Fixed object SHA `3fb4bd73fad0ffe1d5a57a1fbff8d1d478460f686409dafa8422d0f90dee591a`. Every printed theorem depends on Lean axioms `[propext, Classical.choice, Quot.sound]`.

No independent Lean replay was performed. These receipts pin source-direct imports and record large inherited provider lists; they do not authenticate the complete selected transitive object/source closure, all package/dynamic dependencies, or the external equation files. Consequently the checks should not be reported as an end-to-end proof for the retained 14-variable, degree-150 PDF equation or for a direct-BFS-kernel equation. The separate exact coefficient/file binding and full closure review remain required.
