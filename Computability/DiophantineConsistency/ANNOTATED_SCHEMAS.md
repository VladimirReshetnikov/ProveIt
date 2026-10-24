# Actual schema operations in supplied arithmetic programs

`AnnotatedSchemaMaps`, `AnnotatedSchema`, and `AnnotatedReplacement` extend
the independent annotated proof-checker route through the actual Separation
and Replacement schemas, including their final `sealF` operation. The new
data are literal supplied `ScalarPRCode` values. The schema argument is
represented by a natural number; accepted raw inputs are proved to determine
an actual Lean formula. No axiomhood oracle or external formula-parser
premise is used in these soundness theorems.

## Reusing exact checked variable maps

Write `shiftAt d` for the frozen index map `index 0 0 d`, which adds one to
indices at least `d`, and `instantiateOne` for `index 1 1 0`. The four actual
source maps in `ZF/Zf.lean` have the following proved decompositions, with
composition evaluated from right to left:

```text
rsep = shiftAt 1 ∘ shiftAt 1
rf1  = shiftAt 0
rf2  = shiftAt 1
ri   = instantiateOne ∘ shiftAt 2 ∘ shiftAt 2 ∘ shiftAt 2.
```

The last map sends zero to one, one to zero, and every `n ≥ 2` to `n+2`.
Thus it handles the actual exchanged variables in the Image schema. The
chain correctness theorems use the existing binder-aware renaming theorem;
they also hold under arbitrary nested universal and existential binders.

A fixed list of `(mode,parameter,depth)` triples is executable program data.
The generic `chainProgram` folds that list into literal primitive-recursive
code. Untrusted chain evidence consists of each intermediate formula code
and its guarded renaming table. `exists_chain_iff` proves exact composition
on supplied formulas. `chainValue_sound` proves a stronger all-natural-input
statement for nonempty chains: the first accepted renaming table determines
a real input formula, and the accepted output is its exact composite rename.
The empty chain only checks numeric equality and is not used to validate a
schema argument.

## Literal schema assembly and sealing

`AnnotatedSchema` defines the actual numeric constructor schedules for
`Sep_form`, `Func_form`, `Image_form`, and `Repl_form`. Their formula-code
identities are definitional equalities. `formulaProgram` is a structural
compiler for a supplied finite formula, assembling its code by constructors;
it does not expand a huge formula-code numeral into that many successors.
The supplied body programs have 461 nodes for Separation and 773 for
Replacement.

The complete Separation validator checks its two-step rename evidence,
assembles the literal schema body, and invokes the frozen bound/seal program.
Its main equivalence is

```text
(∃ renamed evidence length table,
  separationProgram.eval
    (separationInput (formCode f) goal renamed evidence length table) = 1)
↔ goal = formCode (sealF (Sep_form f)).
```

`separationProgram_sound` also validates arbitrary natural argument codes:
an accepted raw input yields a real `f` with exactly that code and exactly
that sealed schema goal.

`AnnotatedReplacement` does the same for all three required renamings: `rf1`,
`rf2`, and `ri`. Its finite witness contains three renamed codes, three
chain evidences, a closing length, and a bound table. `exists_program_iff`
proves exact equivalence with `formCode (sealF (Repl_form f))`;
`program_sound` supplies the corresponding raw-input soundness theorem.
The six renaming stages and the bound/seal validator are supplied code data,
not selected from existential primitive-recursiveness claims.

The two `*_axiom` theorems also conclude that an accepted goal is the code
of an actual member of the existing sealed theory `ZFCax_s`.

## Checked metrics and regressions

Lean `decide` proves the following exact syntax counts:

| Supplied program | Nodes | Optimized nodes |
| --- | ---: | ---: |
| `rsep` chain | 7409 | — |
| `rf1` chain | 3739 | — |
| `rf2` chain | 3741 | — |
| `ri` chain | 14753 | — |
| Sealed Separation | 10241 | 9333 |
| Sealed Replacement | 25535 | 23463 |

These counts are primitive-recursive program-tree nodes. They are not a
measured polynomial size or an asserted improvement over the existing
closed construction. The tests check all four maps at their boundary
indices, renaming across both binders, malformed zero evidence, exact schema
assembly, and the actual constructor programs. Only the tiny zero-input
chain is executed through a whole PR validator. Whole schema validators are
checked by their universal theorems: naive PR subtraction and numeric-code
fuel make direct evaluation of even some malformed packets impractical.
The assertions concern every natural input despite this runtime limitation.

## Still open on this independent route

The new files close the previously separate external-natural schema maps,
formula assembly, and sealing interfaces. The remaining full numeric
axiom-tag dispatcher and proof-line/context loop have not yet been supplied
here. Neither these programs nor their external correctness theorems alone
establish their interpretation over arbitrary internal omega codes. That
requires an actual numeric-to-internal-form coding relation and transport of
the local finite-table conditions to the existing internal bound, rename,
and sealing operations. The new internal semiring results support those
proofs but do not supply an automatic transfer principle. No full checker
PR theorem, compiled closed polynomial, or new consistency equivalence is
claimed by these schema modules alone.

The next [context/rule checkpoint](ANNOTATED_CONTEXT_RULE.md) supplies exact
context validation, shifting, lookup and the original assumption-rule validator.
The other rules and full proof-line loop remain open.
