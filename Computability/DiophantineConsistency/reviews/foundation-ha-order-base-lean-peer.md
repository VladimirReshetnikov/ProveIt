# Foundation HA order-base packet — independent review

Reviewer: `circuit_reduction`; author: root. Verdict: **PASS**, with no
source changes requested. I read the complete 72-line main, 36-line checks,
author receipt, actual named PeanoMinus source axioms, the relevant target
syntax, and the constructive natural-case/existential-elimination helpers.
I then freshly compiled both leaves in a separate private overlay. I did
not author this order-base leaf. I did author several reused prerequisites,
including the PAHF syntax/proof adapters, HA deduction/arithmetic helpers and
Foundation equality adapter; this review is independent of the new leaf,
not of every prerequisite.

## Exact source and fresh replay

| Source | SHA256 |
|---|---|
| `Lean/DiophantineConsistency/FoundationHAOrderBase.lean` | `a7c2e8aa895e5c752045e013dcf7c0eef9e7bd4903ce50957ec4c4bf7f42d426` |
| `Lean/DiophantineConsistency/FoundationHAOrderBaseChecks.lean` | `677523fc7ba2a536945123102c98d3ef5586b257ba8793e5a18d8c2f08c7b64d` |
| Author dependency replay | `8fc56248155a5a7ac4eea743d21707ca5e0a0c5ed954de9612c8add527e93682` |
| `reviews/foundation-ha-order-base-peer-replay/PEER.json` | `bf133a5cfd82c69a54fb9ffc1ffda1e81549052b59b2c1e2df5e5f284cf1228c` |

Private overlay: `/tmp/foundation-ha-order-base-peer-xymj43pp/lib`.
The two direct compiler commands used `-M6000 -j1 -DElab.async=false` and
returned exit 0. The main log is empty. The check log contains ten reports,
all using only `propext` and `Quot.sound`; no other axioms or diagnostics
occur. Both fresh objects are byte-identical to the author's frozen objects:

- Main: `3e21ed462df34a77a612691034758af1f5be4858578212a89feffe79ac8b95ae`.
- Checks: `8e3cb3b1913577980c2ef97b91e0d199cfaf52c3c8bcbd5b3034b72c3566298e`.

The replay bundle preserves my fully read driver, exact source copies,
commands, logs and all prerequisite pins. All 23 author bundle files and the
aggregate input manifest were verified. The 93 prerequisite module records
include 76 Foundation modules. Sources, available trace records and all
listed object companions were checked; the inherited 499 path observations,
compiler, package identities and prior replay manifest were rechecked before
and after both fresh commands. No prerequisite was rebuilt and no shared
object or frozen source was changed. This is a two-leaf fresh replay over
an authenticated reused closure, not a fresh Foundation or native closure.

## Mathematical and proof-calculus review

The named endpoints target exactly `sentence PeanoMinus.Axiom.zeroLtOneᴺ`
and `sentence PeanoMinus.Axiom.zeroLeᴺ`. Independent definitional checks
bind both to the actual target syntax, including the source disjunction's
negative encoding and the universal closure in `zeroLe`.

`zero_lt_one` supplies the literal witness zero for the existing order
interpretation `exists z, 0 + S z = S 0`; the equality is the genuine HA
zero-addition proof. The named source endpoint then applies constructive
double-negation introduction. It does not use an order model or assume
order positivity as an axiom.

For arbitrary target term `t`, `zero_le` uses the already proved HA
zero-or-successor decomposition. The zero branch reverses `t=0` using HA
equality symmetry. In the successor branch, existential elimination shifts
the whole context and conclusion. The predecessor is retained as variable
zero, every free variable in `t` is renamed, and that predecessor becomes
the witness for `0<t`. The resulting equality follows by transitivity from
`0+S z=S z` and the reversed decomposition equality. The exact renaming
identity for `ltFormula` and the checked instantiation identity prevent
capture; no unshifted arbitrary term is smuggled under the witness binder.
The sparse-parameter check uses variables zero and seven in a nonlinear
term and therefore exercises more than the closed numeral case.

`encoded_or` is valid for an arbitrary finite target context and arbitrary
axiom predicate. Under the negative-pair assumption it eliminates the actual
input disjunction; each branch obtains a contradiction by double-negation
introduction of its own assumed disjunct. It introduces no stability or
excluded-middle principle and contains no GG recursion. The context-retention
check leaves the input disjunction undischarged. Reclosing the concrete
instance uses actual sentence axioms and preserves the source quantifier.

The packet proves two actual arithmetic-image cases and a constructive
auxiliary `zero_le` theorem. It does not prove the seven remaining order
axiom images, complete PA-to-HA arithmetic transfer, or the target equation's
HA consistency equivalence. No findings were identified within this scope.
