# Model halt and the +1-shifted generated free-J expression

`FreeJRetainedShiftModel.shifted_model_iff` proves in Lean that, in every
`IΣ₁` model, the following are equivalent:

1. Some unrestricted model-natural `x : Fin 12 → V` is an `InternalZero`
   of `AdaptiveEquationSyntax2011.positiveShift (retainedExpression p)`.
2. There is a model time `T` with
   `ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0`.

`p` is the fixed symbolic free-J tuple, including the high-mask beta shift
exactly once. `retainedExpression` is the generated 95-gate **Lean**
expression in the sibling direct-expression prototype. The `positiveShift`
used here is the qualified adaptive syntax operation substituting `x+1`;
it is not the unrelated `Expr.positiveShift` that substitutes `x-1`.
The proof rewrites the generated expression by its Lean equality with
`Ordinary12FreeJ.literal p`, uses the generic shifted-zero identity, and
translates between unrestricted naturals and positive values using `+1` and
`-1`. It applies the same fixed symbolic all-model halt equivalence in both
directions. The theorem has no explicit port assumptions; its ambient
assumptions are the model `ORingStructure` and `IΣ₁` satisfaction.

This is a theorem about the generated Lean expression and model-internal
halt/zero, possibly at nonstandard values. The generator's correspondence to
the pinned JSON is an external provenance boundary; the symbolic coefficients
are not yet formally identified with retained bytes or a PDF. This theorem
is not a Lean proof that an iPRA derivation exists, nor a result for the
separate 14-variable equation in `equation.pdf`.

The bounded mixed-provider author run `observations/attempt01` actually
exited 0 without warnings or `sorryAx`. Its named Lean metatheory axiom
report is exactly `[propext, Classical.choice, Quot.sound]`, not an
object-theory axiom list. Source SHA-256:
`383d68e58fffeb3ac132e0a81b20dccedb1de664118838b1db05a674c887004a`;
object SHA-256:
`297685a6eb31af3b6c7798baa8f42f168c4c60c5b4a84923f0622cbea07ca485`.
The exact source, direct dependency/companion guards, selected provider
inventories, reverse-provider overlap and terminal receipt are retained in
the attempt. The 514 shared reverse/gamma project files matched at preflight;
no selected same-named provider conflicts were recorded, and direct guards,
selected provider inventories and reverse overlap were unchanged at final
checks. This is one exploratory author build, not a paired replay or a full
transitive, package or dynamic ancestry authentication; filesystem and
resource checks are point-in-time rather than continuous monitoring.
