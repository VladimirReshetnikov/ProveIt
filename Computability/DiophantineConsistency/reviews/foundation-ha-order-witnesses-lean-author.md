# Successor and transitive order images in HA — author receipt

Author: `circuit_reduction`. This is author validation, not independent
review. The full new main, checks, private build and freeze drivers were read
before execution. Only new owned files and private cache links were written;
no frozen source, shared object, vendor file, umbrella or Git state changed.

## Frozen source and replay

| File | Lines | SHA256 |
|---|---:|---|
| `Lean/DiophantineConsistency/FoundationHAOrderWitnesses.lean` | 161 | `4b4d66e06bc6443c8e4dc32a45435b93ff3c7aad7bc5fe30a9cad759e17ea0b5` |
| `Lean/DiophantineConsistency/FoundationHAOrderWitnessesChecks.lean` | 108 | `7d6172b82aeb23734e9cc3dbddbd00905c2289438f808b99301bb3350454f9b7` |
| `reviews/foundation-ha-order-witnesses-dependency-replay.json` | — | `a2de378685941a5072db3f15e54b7f04bbf0833e33b7611f94e328b3a1f9c1ee` |

Snapshot: `9294c63bd0562a7e7bfc76c4e87e957d5265e839`.
Private overlay: `/tmp/foundation-ha-order-witnesses-gzwctvpw/lib`.
Both final direct fresh builds returned exit 0 using
`-M6000 -j1 -DElab.async=false`, with a 512 MiB reserve. The main log is
empty. Checks contain 24 reports and no diagnostics. Fresh objects:

- Main: `db4c19f17ef96203c83166dd5e21943d93f9ed736b08b176f06ea5b4158af9ac`.
- Checks: `a21ccd3febc3cea5ca79ddac366f802bf84e68140e7a62add0059d4819517202`.

All reports use only `propext`, `Quot.sound` and inherited `Classical.choice`
for the exact Foundation implication conversion. That existing theorem is
explicitly audited. All new ordinary witness and finite logical helpers
use only `propext` and `Quot.sound`. No custom axiom, `sorryAx`, native
decision procedure, model oracle or classical HA rule is accepted.

The bundle `reviews/foundation-ha-order-witnesses-author-replay/` retains
all four executed development records, source snapshots, commands and logs.
The rejected main draft needed `True.intro` after a context-membership
simplification and removal of an unused simplifier argument. The rejected
check draft had an ambiguous `one_le_of_zero_lt` name colliding with an
imported Foundation theorem. Final checks qualify the new HA theorem,
including its axiom report. No target or premise was weakened. Failed
reports, including their elaborator placeholders, are retained solely as
rejected history; the claimed 24 reports are the clean final run only.

## Exact actual-source endpoints

In namespace `DiophantineConsistency.FoundationHAOrderWitnesses`:

```lean
oneLeOfZeroLt : HA.Proves
  (FoundationPAHFSyntax.sentence PeanoMinus.Axiom.oneLeOfZeroLtᴺ)

ltTrans : HA.Proves
  (FoundationPAHFSyntax.sentence PeanoMinus.Axiom.ltTransᴺ)
```

These target the actual named source axioms
`forall x, 0<x -> 1<=x` and
`forall x y z, x<y and y<z -> x<z`.
The exact source closure counts are one and three. Four definitional checks
bind the complete translated sentences, the negative encoding of the
`1<=x` consequent, and the conjunction of the two double-negated order
premises. No source-axiom image premise is supplied.

## Actual witness construction

`one_le_of_zero_lt` first eliminates the actual predecessor witness `d` in
`0+S d=t`. Genuine HA zero-addition gives `S d=t`. It then uses the already
proved HA zero-or-successor theorem for `d`. If `d=0`, successor congruence
and equality transitivity give `1=t`. If `d=S e`, it supplies `e` as the
actual witness for `1<t`: HA successor-addition and zero-addition prove
`1+S e=S(S e)`, and the two retained equalities identify this with `t`.
Every free parameter and open assumption shifts again when the second
witness is introduced. No semantic decomposition of a standard natural is
used in place of the HA case theorem.

`lt_trans_imp` opens the two actual predecessor witnesses for `s<t` and
`t<u`. After the second existential elimination, `d` is in slot one and
`e` is in slot zero. All ambient terms have been shifted twice. The new
predecessor is `S d+e`. Genuine HA successor-addition, associativity and
equality congruence prove
`s+S(S d+e) = s+(S d+S e) = (s+S d)+S e = t+S e = u`.
The retained first equality and second equality are retrieved from their
actual twice-shifted finite context. The general `lt_trans` helper applies
this theorem under arbitrary finite assumptions.

The translated endpoints do not extract witnesses from double-negated
order premises. The first composes its ordinary disjunction proof with
`encoded_or`, then applies stability only to that literal negative
consequent. For transitivity, `pair_doubleNeg` constructs
`not(not(P and Q))` from `not(not P)` and `not(not Q)` by two nested
intuitionistic continuation arguments; it never obtains `P` or `Q`.
The existing `map_doubleNeg` then lifts ordinary transitivity. Finally the
checked Foundation implication equivalence and actual universal closure
produce the named source sentences. There is no duplicated GG recursion,
order DNE, equality DNE or model-semantic induction.

## Tests, authentication and limits

Checks exercise both zero and successor predecessor instances, the
preservation of the first witness when the second binder opens, the literal
`S d+e` witness term and a negative control distinguishing its two slots,
nonlinear sparse parameter terms with free variables zero/four/seven,
arbitrary finite contexts and axiom predicates for the logical pairing,
and ordinary/negative transitivity with retained open assumptions.

The private overlay reuses 95 source/object-authenticated modules: the
previous 94 Additive prerequisites and its frozen main object. It still
contains exactly 76 Foundation modules; there are no new Foundation
imports, no prerequisite builds, and no broad closure refresh. Parent
manifest, selected source/object/trace pins, inherited path inventory,
compiler and package identities were checked before/after builds and at
freeze. Only the two new leaves are freshly compiled.

The remaining three source arithmetic cases are `mulLtMul`, `ltIrrefl`
and `ltTri`. This packet claims neither those cases, complete PA-to-HA
arithmetic transfer, nor the final equation/consistency equivalence in HA.
