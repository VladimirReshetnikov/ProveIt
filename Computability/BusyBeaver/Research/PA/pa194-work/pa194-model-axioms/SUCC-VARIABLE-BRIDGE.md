# Contextual numerical successor-variable value bridge

`PA194SuccVariableBridge.lean` directly connects the numerical PAeq successor-variable dispatcher to the arbitrary-index source equivalence. For model-valued x,z it proves the dispatcher output is a well-scoped source formula, identifies it with the typed translated-value template, and constructs source derivations in either direction between that actual dispatcher formula and the direct successor-value template. The universal source theorem proof and the input derivation are explicit contextual inputs.

The two constructed proof codes are exactly the preexisting `succValueAtCode` outputs, so their already checked fixed Σ₁ graphs apply in every candidate-PRA model with IΣ₁ arithmetic reduct. This result treats the single successor-variable term and explicit packet; it does not prove arbitrary internal-term totality, atomic Leibniz, general formula substitution, the PA induction bridge, native iPRA internalization, or machine correctness.

Run `bash check-succ-variable-bridge.sh REPO NEW_OUTPUT`. The module is recompiled into a fresh output against pinned prebuilt inputs, including the exact repository dispatcher-template equality and arbitrary-index source theorem. The full transitive source closure is not rebuilt. Success includes four axiom reports with no `sorryAx`.
