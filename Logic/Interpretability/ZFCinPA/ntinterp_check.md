# Checked commutation of interpretation and template translation

The unchanged [NTInterp source](Lean/ZFCinPA/NTInterp.lean) passes a fresh
Lean check and **17 axiom probes with 19 typed clients**, with no warnings.
The [actual record](results/ntinterp-verification.json) checks the bridge
between native interpretation and template translation, including both
quantifier constructors.

`interp_translate` states an exact identity of internal formula codes in
every IΣ₁ model. The template and its arities are external finite data;
its placeholder meanings may be arbitrary internally coded formulas of
those arities, including nonstandard codes with free parameters. Interpreting
the translated template gives the same code as translating the interpreted
template with interpreted placeholder meanings. The proof uses internal
substitution and negation compatibility, and retains the newest-variable
domain guards at quantifiers.

There is no shift-fixedness premise or arity-at-most-three restriction on
this identity. The latter remains a premise of the separate
[NTemplate compiler](ntemplate_check.md) wherever it is used. Sentence
embedding commutation requires an empty source free-variable type. These
identities do not prove all interpreted axioms or perform an induction over
arbitrary internal template syntax; the consistency comparison remains open.

Source and audit took 4.700 and 2.346 seconds with default proof limits,
one thread, 4,096 MiB and a shared 120-second deadline. All 352 recorded
inputs and the fresh first-provider object remained unchanged after the
audit. Every probe uses only standard Lean axioms.

The actual NTemplate and [repaired NativeInterp](native_interp_check.md)
records supply 118 selected project providers, 12 explicit opaque
boundaries, Init and retained Omega. NativeInterp's six source warnings
and original failure remain in its evidence. Earlier capture policies and
current-only companion observations remain distinct; no dependency rebuild
or complete cache check is claimed. The
[publication](results/ntinterp-publication.json) and
[history](ntinterp/history.json.gz) preserve the independent source/API
review, its bounded acknowledgment of the actual result, audit, guard and
logs. This closes one original validator inventory entry.
