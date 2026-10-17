# Internal interpretation of the C254 propositional axiom

[`ModelCodedDecoderLukasiewicz254`](Lean/ZFCinPA/ModelCodedDecoderLukasiewicz254.lean)
proves, for every IΣ1 model and arbitrary internal `a,b,c,u`,

```text
Provable T (decode (ArithmeticTemplates254.rho8 a b c u))
```

Here `T` is any Δ1 set-language theory, including the actual ZF and ZFC
presentations. The conclusion supplies an actual internal Tait proof witness.
It does not require standard formula codes, consistency, or a separate axiom
interpretation hypothesis.

The source row is the original C254 single propositional axiom:

```text
((c → u) → a) → ((a → c) → (b → c)).
```

The fixed target proof composes `(c → u) → a` with `a → c`, applies Peirce
at `c,u`, and weakens by `b`. This uses the existing internal proof calculus's
classical logic instance. No semantic completeness theorem for nonstandard
formulas, ordinary quotation of a variable formula, or proof-selection oracle
is used. The source calculus and machine retain their attribution to Mira-Cult,
Jeff Ketchersid and Andrew James Wade.

The decoder is not literally an implication homomorphism at source pair
`(0,0)`: both the input and its implication code are zero. The new
`decoded_imp_equiv` proves the needed internal equivalence instead. In the
exceptional case both decoded truth and its self-implication are provable;
otherwise the checked literal decoder equation applies. Internal implication
congruence propagates these equivalences through the six implication nodes
of the actual arithmetic `rho8` definition. Thus the all-zero case is covered
without a positivity assumption.

The focused audit passes **five axiom reports and eight callers**, using only
`propext`, `Classical.choice` and `Quot.sound`, with zero warnings. Callers cover
arbitrary internal models, actual ZF/ZFC proof witnesses, congruence and the
all-zero ordinary natural-number instance. Lean 4.32.0 used one thread and a
4 GiB limit; final source/audit times were 2.234/2.171 seconds. Three earlier
nonpasses are preserved: missing deduction namespace qualification, implicit
Peirce formula arguments, and an audit proof-valued caller needing a
`noncomputable` section. None changed the theorem statements.

The runner reuses exactly 26 checked project predecessors, six external
source/object boundaries and the actual Omega provider. It records all 77
inputs and the fresh output object before/after checking. Combining the
numeric-template and decoder prerequisites exposed two previously checked
compiled artifacts of the identical Cantor source. The guard permits only
that exact frozen pair, checks matching source/compiler/dependency identities,
selects the decoder's artifact as the actual first provider, and hashes the
unused replay artifact as a separate input. It does not accept arbitrary
same-source object variants. No dependency was rebuilt or fetched.

```sh
python Logic/Interpretability/ZFCinPA/check_model_coded_decoder_lukasiewicz254.py \
  --output /absolute/fresh/check
```

The runner accepts repository/dependency, source/audit, predecessor-evidence,
cache and namespace overrides while retaining the frozen hashes. The maintained
guard is byte-identical to the successful executed guard. Maintained-default
and copied-project-cache preparations pass without proof compilation, as do
four rejection controls. Compiler discovery queries `lean --version`.
The initial shadow-control harness omitted the ordinary library paths and was
corrected before recording the intended first-Omega rejection.

This interprets one source axiom row. The other logical rows, the set-theoretic
bundle, accepted-history proof translation and PA consistency comparison remain
separate obligations. No state reduction or complete PA endpoint is claimed.

The [successful check](results/model-coded-decoder-lukasiewicz254-verification.json),
[attempt history](results/model-coded-decoder-lukasiewicz254-history.json),
[guard validation](results/model-coded-decoder-lukasiewicz254-guard-validation.json)
and [independent review](model_coded_decoder_lukasiewicz254_review.md) retain the
exact evidence and scope.
