# HA finite deduction and negative-fragment stability

Author: `circuit_reduction`. Status: all four new sources fully self-read,
freshly compiled, and frozen. This is an author receipt, not an independent
peer review. No existing source, compiled dependency, or umbrella was changed
by this packet; no Git operations were performed.

## Frozen sources

Paths are relative to `Lean/DiophantineConsistency/`.

| File | Lines | SHA256 |
| --- | ---: | --- |
| `HADeduction.lean` | 134 | `fd71974da01171f90c516b64ecb3c994a761e1163bf978f14eb7b2b6f884bc19` |
| `HADeductionChecks.lean` | 51 | `6341e52323aa23e9748bd62dc63388914c2baf70cbb2ca907ca09b8527913ddb` |
| `HANegativeStability.lean` | 127 | `e6b9bbc501a652444992de39e0924eb8a3596d7938ad3d0db8cb15bff19f586d` |
| `HANegativeStabilityChecks.lean` | 64 | `87da3820bab34329819d075f0fb77424e53ca852c0c6f264f21cfa8ccc3752be` |

## Actual proof constructions

`HADeduction` uses the frozen `HA.Derives` rules from `HAProofs` over the actual PAHF
`Term` and `Formula` syntax. `Relative.mono_axioms` and `Relative.weaken`
retain a finite supporting axiom list. `Relative.combine` concatenates the
two supporting lists and weakens the two derivations into their common
context. Modus ponens, conjunction introduction/projections and implication
composition follow. Implication introduction explicitly moves its discharged
assumption past the finite axiom list. The `Proves` wrappers specialize this
construction to the existing six arithmetic axioms and universally closed
formula-induction instances; they do not add new axioms.

`HA.Negative` in `HANegativeStability` includes falsity, negations of arbitrary
formulas, conjunctions of negative formulas, and universals of negative
formulas. Its principal theorem is, in namespace `HA`,

```lean
Negative.stable (h : Negative a) (G : List Formula) :
  Derives G (.imp (doubleNeg a) a)
```

The proof constructs actual intuitionistic deduction trees. Negation uses
triple-negation elimination; conjunction uses contraposition twice on its
two projection proofs. Universal introduction shifts every assumption by
`Formula.rename Nat.succ`. Universal elimination of the shifted formula at
`Term.var 0` uses the exact PAHF identity
`Formula.subst_instTerm_var_zero_rename_up_succ`, preserving free parameters.
The body induction hypothesis applies in that shifted context. There is no
unrestricted double-negation-elimination rule or classical proof conversion.

`closeN_neg_stability n a` proves in HA

```lean
Proves (.imp (doubleNeg (Formula.closeN n (neg a)))
  (Formula.closeN n (neg a)))
```

No arithmetic axiom is used in this stability proof: its `Proves` witness has
an empty finite axiom list. `sealPA_neg_stability` is also exported.
The frozen root compiler defines
`ArithmeticExpression.noZeroSentence e = closeN n (imp (equation e Fin.val) bot)`;
therefore the generic theorem has the exact needed syntactic shape with
`a = equation e Fin.val`. This packet deliberately does not import that
separately reviewed compiler or claim a new literal-current-sentence binding.

## Focused checks and replay

The checks exercise distinct axiom lists, context permutation and duplicate
assumptions, axiom-set weakening, discharging an assumption across an axiom
list, implication composition, and projection of the actual sealed induction
axiom. Stability checks retain an open parameter under a universal binder,
instantiate the shifted universal explicitly, cover zero/two/fourteen binders
and negated existence, and prove syntactically that raw equality and a raw
LEM disjunction are not constructors of this sufficient fragment. Those last
two checks are not HA independence results.

All four terminal builds exited 0, with `-M6000 -j1` and `Elab.async false`.
Both main logs are empty. Sixteen axiom reports contain only `propext` and
`Quot.sound`; none contains `Classical.choice` or a new axiom. No `sorry`,
`native_decide`, semantic completeness, or classical-PA erasure theorem is
used. An initial stability build failed on Lean constructor/context inference;
explicit constructor names and the universal-elimination context fixed it
without changing any statement, premise, or rule. That failed log is retained.

Private overlay: `/tmp/ha-deduction-stability-1lpilxeq`.
Exact commands, source/object/log hashes and the six reused custom-module
pins are in `ha-deduction-stability-dependency-replay.json`, SHA256
`a6111248da09d776696953ce2e44f7bb191bc642ae8d7e6c502c6218e81c4f25`.
The five-module PAHF closure and the frozen `HAProofs` leaf were rechecked
against their accepted exact source/object pins, matching toolchain and
manifest before use and again at freeze. They were reused, not rebuilt.
Mathlib/package objects were reused under that matching manifest. No broad
dependency replay or source-closure freshness beyond these pins is claimed.

## Remaining HA obligations

This packet proves object-language HA derivability of stability and proof
composition, not the target consistency equivalence. The arithmetic
axiom/induction translation needed by a Gödel–Gentzen transfer, the explicit
PAHF-to-Foundation syntax/proof adapter, and the actual current215
arithmetized machine/native equivalence remain separate obligations. The
generic Foundation theorem adapter does not itself discharge any of them.
