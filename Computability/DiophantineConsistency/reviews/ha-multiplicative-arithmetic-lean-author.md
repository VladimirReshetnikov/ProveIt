# Multiplicative arithmetic in conventional HA: author receipt

Author: `circuit_reduction`. This is an author review and fresh leaf build,
not an independent peer review. Both complete new sources and private drivers
were read before execution. All final proof chains were reviewed against
their literal formulas. No frozen source, shared object, umbrella, vendor file
or Git state was edited.

## Frozen source and build scope

| File | Lines | SHA256 |
|---|---:|---|
| `Lean/DiophantineConsistency/HAMultiplicativeArithmetic.lean` | 220 | `eb4d58cf05fa808399b93956a9fb9b75e44c9af3e8fd6340f2721a0e762bae09` |
| `Lean/DiophantineConsistency/HAMultiplicativeArithmeticChecks.lean` | 97 | `b190df3fe507bd4eefc1b2e911d01ae770305536cc74c1570b3406e19a1f816a` |
| `reviews/ha-multiplicative-arithmetic-dependency-replay.json` | — | `85c7a68ccca986e67714cf4c4878ab7416eef781edf5aba7f69fde32e066313b` |

Final selected-source authentication was recorded at repository snapshot
`b8f4085b41c32e92f4433eaedbee099237159e2c`. The new main imports only
`HAAdditiveArithmetic`. Nine custom prerequisite objects were reused after
checking every corresponding source/object hash and the compiler, toolchain
and package-manifest identities: the five PAHF closure modules, `HAProofs`,
`HADeduction`, `HABasicArithmetic` and `HAAdditiveArithmetic`.
No prerequisite was freshly rebuilt; no Foundation or native-equation module
is imported by this packet. The frozen Basic and Additive main/check source,
object and log pins were reauthenticated unchanged, preserving their 19 and
14 prior audits. They were not freshly replayed in this build.

Both new modules passed their first sequential private direct builds using
`-M6000 -j1` and source-level `Elab.async false`. The overlay is
`/tmp/ha-multiplicative-arithmetic-mzvy_t89`. Both terminal exit codes are zero.
The main log is empty. All 22 check reports use only `propext` and/or
`Quot.sound`; there are no final warnings or other diagnostics. The JSON
receipt records exact commands, logs, hashes and reused-object locations.

Fresh main object:
`a42790bc37b59f9440b1d9415964a2253723eed022564ba5eaa95e1566fda9b9`.
Fresh checks object:
`9985de05aafc11dc0ded9b5d5cb85119df08e8449b8bf4af9b38274de7f49d9e`.

## Object-language proof content

The public `HA.Arithmetic` results prove multiplication by zero on the left,
multiplication by one on either side, both distributive laws, successor on
the left, multiplication commutativity and multiplication associativity.
All statements are `HA.Proves` judgments over the existing PAHF syntax.

The six universal families `zero_mul_all`, `one_mul_all`, `mul_add_all`,
`add_mul_all`, `mul_comm_all` and `mul_assoc_all` use the actual
`Arithmetic.induction` rule, which opens the conventional HA formula-induction
axiom. For parameterized formulas, every ambient term is shifted by
`Nat.succ` before entering the induction slot. Zero substitution removes
that slot, while successor substitution keeps the ambient parameters fixed.
Universal introduction uses `Formula.Ax_s_sentences`, and arbitrary-term
corollaries instantiate the proved universal formulas through HA elimination.

The local four-term additive rearrangement is an explicit chain of five
already proved HA equalities using associativity, commutativity, congruence
and transitivity. It is used in the inductive proof of distribution over a
left-hand sum. No `ring` tactic, arithmetic semantic oracle, or standard-Nat
identity is substituted for an HA proof. `succ_mul` follows from actual
distribution, `add_one` and `one_mul`; it then supplies the step for
commutativity. Associativity uses the proved right-hand distributive law.
Finite relative axiom lists and the actual induction-hypothesis context are
preserved by the existing deduction combinators.

## Checks and limits

Checks cover the exact generic zero and successor substitutions of the
two-parameter right-distribution body, and a two-quantifier multiplication
associativity theorem with a genuine free parameter. Opening both quantifiers
preserves parameter zero even when either substituted term uses it. Further
checks instantiate the two distribution laws and commutativity with nonlinear
terms containing several free indices, construct a four-term product-of-sums
expansion by composing HA derivations, and exercise literal zero/one/successor
cases. Every public main theorem has its own axiom audit.

No `sorry`, `native_decide`, custom axiom, `Classical.choice`, model argument,
classical `BProv` theorem, or arithmetic-image assumption is used in the new
proofs. This packet does not prove order laws, the full Foundation arithmetic
adapter, or the final HA consistency-equivalence theorem.
