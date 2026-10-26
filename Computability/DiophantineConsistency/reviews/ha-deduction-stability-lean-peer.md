# Independent HA deduction and negative-stability review

2026-10-26. Reviewer: `controller_certificate`. Author: `circuit_reduction`.
Result: PASS, with no requested source changes. I authored neither this
packet nor `HAProofs`; I previously independently reviewed and replayed the
latter. This review made no source, shared-object, umbrella, or Git changes.

## Exact reviewed artifacts

All Lean paths below are relative to `Lean/DiophantineConsistency/`.

| Source | Lines | SHA-256 |
|---|---:|---|
| `HADeduction.lean` | 134 | `fd71974da01171f90c516b64ecb3c994a761e1163bf978f14eb7b2b6f884bc19` |
| `HADeductionChecks.lean` | 51 | `6341e52323aa23e9748bd62dc63388914c2baf70cbb2ca907ca09b8527913ddb` |
| `HANegativeStability.lean` | 127 | `e6b9bbc501a652444992de39e0924eb8a3596d7938ad3d0db8cb15bff19f586d` |
| `HANegativeStabilityChecks.lean` | 64 | `87da3820bab34329819d075f0fb77424e53ca852c0c6f264f21cfa8ccc3752be` |

The complete author receipt was read: `ha-deduction-stability-author.md`,
SHA-256 `d73327f47c37357b05048d6e1d9da2caa888df5580c0e94e2efa74ba5ca9f058`.
Its complete dependency/replay JSON was also read and authenticated:
`ha-deduction-stability-dependency-replay.json`, SHA-256
`a6111248da09d776696953ce2e44f7bb191bc642ae8d7e6c502c6218e81c4f25`.

I read all four sources, the full 147-line `HAProofs`, and the relevant
PAHF syntax/rule definitions and substitution proof: term rename/substitution
120–165, formula rename/substitution 443–467, `closeN` 556–559,
`instTerm` 749–752, the restoration identity 1543–1552, all classical
`Prov` constructors 1602–1628, and the arithmetic/induction schema definitions
8214–8269. This is not a claim to have reread all 66,936 PASyntax lines.

## Mathematical review

`Relative.combine` retains the original finite witnesses `L` and `K`, uses
`L ++ K` as the new finite arithmetic axiom list, and weakens each premise
into `(L ++ K) ++ G`. Each entry of the new list is justified by its original
axiom predicate. It does not turn a metatheoretic proposition into an axiom.
`Relative.imp_intro` explicitly moves the discharged assumption across the
supporting axiom list before applying the genuine implication rule.
The projections, modus ponens, conjunction construction, and composition
wrappers instantiate these finite derivation operations. `Proves` still means
the previously defined `Relative Formula.Ax_s []`, with the same six
arithmetic axioms and universally sealed formula-induction schema.

The negative-fragment proof uses only the existing intuitionistic rules.
Falsity is stable by applying its double-negation hypothesis to the identity
proof. Negation is stable by triple-negation elimination. Conjunction uses
the two genuine projection implications, double contraposition, and the
two inductive stability proofs. No atomic stability premise is silently
supplied.

The universal case was checked with an open context. After implication
introduction, universal introduction shifts *every* assumption in
`doubleNeg (all a) :: G` by `rename Nat.succ`. The shifted universal is
eliminated at `Term.var 0`; its body is `rename (up Nat.succ) a`.
`subst_instTerm_var_zero_rename_up_succ` restores precisely `a`, including
all of its free parameters. Double contraposition then transports the
shifted double-negation assumption to `doubleNeg a`; the induction
hypothesis is available for this entire shifted context. Thus the new
eigenvariable is not identified with an old free parameter or assumed fresh
without the required context operation.

`Negative.closeN` follows the actual definition
`closeN (n+1) a = closeN n (all a)`. Hence the theorem covers any number
of universal binders over any negation, including a negated existential
body and a body with free parameters. `proves_stability` embeds an actual
empty-context logical derivation with an empty supporting arithmetic axiom
list. This uses no arithmetic induction instance. The negative-fragment
definition deliberately omits raw equality, disjunction, and existential
constructors; their syntactic exclusion checks are not independence results
for HA. There is no unrestricted DNE, LEM rule, semantic reflection,
classical-proof erasure in the reverse direction, or oracle in this packet.

## Independent private replay

Overlay: `/tmp/ha-deduction-stability-peer-controller-20261026`.
I authenticated and copied exactly the six prerequisite primary objects
named in the author's JSON: the five-module PAHF closure and `HAProofs`.
Current source hashes, cache-source hashes where supplied, and original
object hashes all matched. The four review targets were absent from the
new overlay before compilation. Each was freshly compiled there, serially,
in the displayed table order. The exact command pattern was:

```sh
lake env bash -c 'export LEAN_PATH="/tmp/ha-deduction-stability-peer-controller-20261026:$LEAN_PATH"; exec lean -M6000 -j1 -o /tmp/ha-deduction-stability-peer-controller-20261026/DiophantineConsistency/MODULE.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/MODULE.lean'
```

All four first attempts exited 0. All sources set `Elab.async false`.
The two main logs are empty. The two checks logs contain exactly sixteen
axiom reports, each using only `propext` and `Quot.sound`; none uses
`Classical.choice` or an additional axiom. All four fresh objects are
byte-identical to the author's frozen outputs:

| Object | SHA-256 |
|---|---|
| `HADeduction` | `273ee3323c9ca501de119db6e3a72053a4f0a740e361b1edc63c6cd882868798` |
| `HADeductionChecks` | `123cddcb6d2d17b6071dd51f230a6756372491a4fb4a8b08e4e7e9d69afc51c3` |
| `HANegativeStability` | `f94d5ddef0005a9e81aec7c2b92dee49c197ffcc3275f08d072254369155d004` |
| `HANegativeStabilityChecks` | `6e9ee70dcb0e5b40ab0e01eadcf192f1e2141ecb9b0b99cf2f8674c763cc7d6f` |

The checks-log hashes are respectively
`2ac960c9aee136ba077630d1e9169b20777f95bc074d3eda164fd90cc3e6eb4f`
and `70cdc8c6836adc476a1acd16bb7895539e480067a32f7f54562d131aa6f28f6f`.
Private `inputs.json` and `outputs.json` retain the exact replay records.
Source and prerequisite-object pins were rechecked after the builds.

The prerequisite authentication remains the accepted HA dependency scope:
prior JSON `f8163c4c5325f30e1e9adfa04fbe3501ef67518072c46ed411b94531ea7ee4ba`,
toolchain `2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e`,
manifest `95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665`.
PASyntax and its closure were reused under exact pins, not freshly rebuilt.
Package objects were reused under that manifest; this is not a full
prerequisite replay. The arithmetic-expression compiler is not an import
of these four leaves.

## Scope

This establishes actual HA derivation construction and negative-fragment
stability over the PAHF arithmetic syntax. It neither proves the consistency
equivalence nor arithmetizes the current 215-state machine calibration.
It does not supply PA-to-HA arithmetic axiom/induction preservation, a
Foundation syntax/proof interoperability theorem, or an HA proof of a
particular no-zero sentence itself. The subsequent exact-current stability
binding is reviewed separately.
