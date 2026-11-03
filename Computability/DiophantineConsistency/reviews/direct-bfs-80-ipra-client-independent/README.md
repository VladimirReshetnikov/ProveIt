# Independent review: parameterized direct-BFS 80 iPRA client

The frozen accepted packet constructs the stated Lean proof-existence terms **under four external Lean hypotheses on the port tuple**. For `p : Fin 4 → ℕ`, every theorem assumes `p 0=betaNat`, `p 1=DirectBFSSymbolicKernel.paramKernel rho`, `p 2=lowNat`, and `p 3=betaNat+highNat`. It first constructs `PositiveModelBridge (graph (integerPorts p)).output` by applying the independently reviewed direct-BFS model iff in every IΣ₁ model, with that same `p` and graph.

The next four theorems construct derivability terms for `IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts p)).output)`, applying the positive shift **once**:

* In `standardTheory`, equivalence with `∼mappedNativeRefutation embedding`.
* In `standardTheory`, equivalence with `(Semiformula.lMap embedding sourceSentence)ᴺ`, the mapped Gödel–Gentzen-translated Foundation consistency sentence.
* In equality-only `referenceTheory`, equivalence of the erased no-zero sentence with `∼erase (mappedNativeRefutation embedding)`.
* In `referenceTheory`, equivalence of the erased no-zero sentence with `erase ((Semiformula.lMap embedding sourceSentence)ᴺ)`.

The same four natural port equalities remain **explicit Lean parameters** to all five theorems; this is not yet the separate closed fixed-port client. The named theories and encodings are those of the imported adapters. This Lean graph uses the directly indexed BFS symbolic kernel, distinct from the original-order symbolic kernel and the original 14-variable PDF. This packet does not formalize the external gzip/JSON binding or prove the consistency sentence true.

`check.py` rehashes source/copies, runner, Lean binary, direct providers, object and logs; verifies equal before/after direct snapshots and first resolution; and checks 59 retained chunk receipt hashes. The two direct providers are reviewed `DirectBFS80ModelIffCorrected` `4858598cb5d931d788b6a0a76e00029ecd47cd24062217afa4059713aba9116d` and `PositiveModelIPRAReferenceTranslated` `d285f286b99912f7936f004d9a2472b6d6cce2935db2285522561f987aa6e65b`. The selected `Direct80Graph` and BFS symbolic-kernel object hashes agree post hoc with the model-iff chain; exact paths are in `check-output.txt`. This is not a complete serialized transitive, historical source-object, package or dynamic-load audit.

The accepted output object is `5a568d6580ca19a563a5e59514adcaffea499691183734df13bee9d27d2e4082`. All five named reports are exactly `[propext, Classical.choice, Quot.sound]`, stderr is empty, and the runner enforces a named whitelist and rejects coded diagnostics. Its terminal precedes final assertions; the author reports outer exit 0 but no separately retained actual outer-exit receipt was found. No independent Lean replay was performed.
