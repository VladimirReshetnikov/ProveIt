# Checked proof templates over the native theory

The unchanged [NTemplate source](Lean/ZFCinPA/NTemplate.lean) passes a fresh
Lean check and **20 axiom probes with 21 typed clients**, with no warnings.
The [actual record](results/ntemplate-verification.json) checks the native
GIC proof constructor, template-axiom translation and finite-source compiler.

`nativeGic_isProof` constructs an internal proof for an arbitrary internally
coded, well-formed two-variable GIC matrix. Free parameters are allowed:
the construction closes the axiom, proves its recognizer membership, then
opens it. It needs no shift-fixedness premise. `compileN` has a different
scope: it translates a fixed external finite source derivation at arbitrary
internal placeholder formulas of arity at most three, applying the required
shifts at buffers. It is not a compiler for arbitrary internally coded
source derivations.

The semantic comparison retains GIC's global support requirement: collection
elements may have witnesses outside the input set. The reduct and
completeness results require genuine equality and compatible membership;
the GIC equivalence itself does not need the genuine-equality assumption.
These conditional semantic results do not assert that a native-theory model
exists or complete the PA consistency comparison.

Source and audit took 6.958 and 2.542 seconds with default proof limits,
one thread, 4,096 MiB and a shared 120-second deadline. All 239 recorded
inputs and the fresh first-provider object remained unchanged after the
audit. Every probe uses only standard Lean axioms.

The actual [LTemplate](ltemplate_check.md) and
[NativeTheory](native_theory_check.md) records supply 62 selected project
providers. Ten directly imported opaque boundaries, two additionally retained
opaque boundaries, Init and retained Omega are explicit. Earlier warnings
and legacy capture limits remain in the parent evidence; no dependency
rebuild or complete cache check is claimed.

The [publication](results/ntemplate-publication.json) and
[history](ntemplate/history.json.gz) preserve the independent source/API
review, audit, guard and actual logs. An unexecuted guard draft's overly
strict artifact-count check was corrected before compilation, retaining the
exact companion lists of both parents. This closes one original validator
inventory entry.
