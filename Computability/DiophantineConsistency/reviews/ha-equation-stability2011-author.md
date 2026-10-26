# HA stability of the exact current equation sentence

2026-10-26. Author: root. Both new sources were fully read and compiled
freshly in dependency order with `lake env lean -M6000 -j1`, async disabled.
The final main log is empty; the checks log has four standard-only axiom
reports. Both final builds exited0. There is no new arithmetic or logical
axiom, semantic oracle, unrestricted DNE, `sorry`, or native evaluator proof.

`HAEquationStability2011` binds the already checked generic closeN-negation
stability proof to `ArithmeticCurrentEquation2011.unsolvabilitySentence`.
The latter is precisely the literal14-variable current equation sentence,
with successor substitution and all fixed coefficient ports. `derives_stability`
has empty context; `proves_stability` has an empty supporting arithmetic
axiom list. It proves existence of an actual HA derivation of
`¬¬NoZero → NoZero`. The focused checks also put that derivation over the
empty axiom predicate and retain the actual sentence-closure theorem.

This is an object-language HA theorem, but it is not the consistency
equivalence. In particular it neither supplies an HA proof of NoZero nor
derives any claim from ConZFC. The final conditional merely composes HA
modus ponens with a supplied HA proof of the double negation. It is not
asserted as the task's endpoint. The arithmetic checker, calibration,
GG arithmetic interpretation and target-translation comparisons remain open.

The private overlay `/tmp/arithmetic-expression-root-n6c1ese3` reused the
accepted arithmetic/compiler leaves and their explicitly recorded older
prerequisite scope. The two frozen deduction/stability objects were linked
there explicitly after an initial import-only failure: Lean selected that
namespace directory and did not combine partial directories from two path
entries. That first command produced no target object and is not accepted.
No source fix, prerequisite rebuild, shared-cache mutation or cap increase
was needed. The root read the complete generic proof sources and author
receipt before these leaf builds; independent review is separate.

| Artifact | SHA-256 |
|---|---|
| Main source | `ef2b90bb86d00541a03ff1647b8ce0d35ae2e1395438a04ab6f1f044f4a6810c` |
| Checks source | `9808a8c56dfb7c51699e5145204aea94de9c82ec9ea50c5902111aa89f7cd23f` |
| Main object | `f4ffa81e715439f0f7db8e1ed7747423b8addc3a3271635b0606c924b8df7085` |
| Checks object | `b66f4f2d3e9777a7ccf66d888b151fac8b5c4ac64936f562af6ab90a6cf75e44` |

The generic dependency objects are HADeduction
`273ee3323c9ca501de119db6e3a72053a4f0a740e361b1edc63c6cd882868798`
and HANegativeStability
`f94d5ddef0005a9e81aec7c2b92dee49c197ffcc3275f08d072254369155d004`.
Final logs: `/tmp/ha-equation-stability2011-main-stage2.log` and
`/tmp/ha-equation-stability2011-checks.log`. The displayed equation and all
current coefficient definitions are unchanged.
