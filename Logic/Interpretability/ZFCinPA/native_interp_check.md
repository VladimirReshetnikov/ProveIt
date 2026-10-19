# Checked native interpretation and quotation

The [NativeInterp source](Lean/ZFCinPA/NativeInterp.lean) passes a fresh Lean
check and **20 axiom probes with 22 typed clients** after two local proof
repairs. The [actual record](results/native-interp-verification.json) retains
six source linter warnings; the audit has none. Every probe uses only
`propext`, `Classical.choice` and `Quot.sound`.

For a nonempty model of the native theory, `eval_intF` interprets external
finite set-theory formulas in the internally well-founded part of its
bisimulation quotient. Domain elements map to their quotient classes;
the quantifier proofs use representatives of those classes. No external
well-foundedness or injectivity assumption is added.

Separately, in an arbitrary IΣ₁ model, `good_PN` establishes the represented
interpretation parameter's syntactic conditions, including arity and
shift-fixedness. `quote_intF` identifies the interpretation of quoted
external finite formulas with the quotations of their translations.
It does not establish semantic correctness for arbitrary nonstandard
formula codes or prove all interpreted axioms. The native consistency
comparison and final binary-machine PA theorem remain pending.

The original source failed at the two local equality and membership
evaluation steps in `eval_atomI`. Each goal is a definitional equivalence
for the standard set structure, so replacing its simplifier proof by
`Iff.rfl` closes it. The exported statements, hypotheses and options are
unchanged. The [publication](results/native-interp-publication.json) labels
this as a proof repair; the [history](native-interp/history.json.gz) preserves
the original source, failed run, exact diff, independent source/API review
and its subsequent failure diagnosis, earlier guard drafts and final logs.

Source and audit took 5.936 and 2.339 seconds with default proof limits,
one thread, 4,096 MiB and a shared 120-second deadline. All 303 recorded
inputs and the fresh first-provider object remained unchanged after the
audit. The 99 selected project providers come from the actual R2Ax,
ConstructibleInterpretation and BootstrapFrameRotation240 records; seven
opaque boundaries, Init and retained Omega are explicit. The older
parents' different capture policies and warnings remain recorded.
Current companion observations are distinguished from historical evidence;
unselected historical inputs were not rehashed. No dependency rebuild or
complete cache check is claimed. This closes one original validator
inventory entry.
