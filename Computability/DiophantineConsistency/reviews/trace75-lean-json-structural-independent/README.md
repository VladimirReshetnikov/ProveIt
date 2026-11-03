# Independent review: external Lean/JSON structural comparison

PASS for the externally computed structural comparison, with the limits below. This review did not replay Lean.

The checked script pins the Lean evaluator source and JSON circuit, parses the limited `+`, `-`, `*`, nonnegative-integer, identifier and parenthesis fragment, verifies all 27 Lean record fields are assigned exactly once, evaluates all 75 JSON operations, and compares the final output after its interned commutative-ring normalization. The normalization flattens/reorders sums and products, combines constants and additive coefficients, and removes additive inverses and identities; it does not need product expansion. These rewrites are sound in commutative rings, but the normalizer is not claimed complete for arbitrary ring equality. The checker compares the final evaluator output; it does not prove each named Lean record field equals a separately named JSON row.

The independent checker reproduced the recorded PASS and exercised the actual parser/checker against five temporary mutations: changed final JSON operation, unknown JSON operand, duplicate JSON register, unsupported Lean division and changed Lean output; each was rejected. The graph/source pins and exact reported 75 rows/27 fields were rechecked. Script SHA-256 `857fafd44b6c32aaab37ff8418fc54f4e123338445ce78a8158784c11ad3d6f6`; retained result SHA-256 `3cde4a71ee34e090f60395f1a92740a565b0aff9fc3f4eef8c18f763ed71d1f0`.

This is a pinned, external restricted-fragment structural check, relying on its parser's correspondence with the shown Lean and JSON syntax; it is **not a Lean theorem about file bytes** or a general Lean parser. It does not independently certify the JSON's advertised degree, coefficient values or an iPRA proof.
