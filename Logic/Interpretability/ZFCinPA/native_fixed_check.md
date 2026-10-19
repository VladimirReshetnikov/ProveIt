# Checked fixed axioms under the native interpretation

The unchanged [NativeFixed source](Lean/ZFCinPA/NativeFixed.lean) passes a
fresh Lean check and **14 axiom probes with 15 typed clients**, with no
warnings. The [actual record](results/native-fixed-verification.json)
checks the interpreted fixed ZF axioms and domain nonemptiness.

`fixed_models` retains a nonempty set structure, the repository's six-field
ZF bundle, Power Set and Regularity. From these it proves Foundation's
equality axioms and seven fixed ZF axioms. In a native-theory model, the
internally well-founded quotient supplies that bundle and is nonempty.
The sentence evaluation bridge and completeness then yield native-theory
proofs of the interpreted fixed axioms and of the domain's nonemptiness.
No existence of a native model is assumed by the resulting provability
theorems.

The internalized results hold in every IΣ₁ model. Their axiom parameter is
still an external sentence belonging to `EQ ∪ zfFixed`; they do not cover
arbitrary internally recognized schema instances. Separation, Replacement
and the final consistency transport remain subsequent obligations.

Source and audit took 5.056 and 1.909 seconds with default proof limits,
one thread, 4,096 MiB and a shared 120-second deadline. All 286 recorded
inputs and the fresh first-provider object remained unchanged after the
audit. Every probe uses only standard Lean axioms.

The actual [NativeInterp check](native_interp_check.md) supplies 100
selected project providers, seven explicit opaque boundaries, Init and
retained Omega. Its repaired source, original failure, six source warnings
and inherited historical capture limits remain explicit. Selected pairs
and current companion observations are checked without claiming a rebuild
or complete cache check. The
[publication](results/native-fixed-publication.json) and
[history](native-fixed/history.json.gz) preserve the independent source/API
review, focused audit, guard and actual logs. This closes one original
validator inventory entry.
