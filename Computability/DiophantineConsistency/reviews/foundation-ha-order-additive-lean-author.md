# Two additive order images in HA — author receipt

Author: `circuit_reduction`. This is author validation, not independent
review. The complete new main, checks, build and freeze drivers were read
before execution. Only new owned source/check/receipt files and private
cache links were written. No frozen source, vendor file, shared object,
umbrella or Git state was changed.

## Frozen packet and execution

| File | Lines | SHA256 |
|---|---:|---|
| `Lean/DiophantineConsistency/FoundationHAOrderAdditive.lean` | 146 | `e2e8f088c8bf09db9aac2f912423ba1907761abeddfa917dab93e792483b3670` |
| `Lean/DiophantineConsistency/FoundationHAOrderAdditiveChecks.lean` | 106 | `ffde326f36dd60e0ae4798e6f895008fe551c3eeeaafa43e0a4dde20ebd32604` |
| `reviews/foundation-ha-order-additive-dependency-replay.json` | — | `e7883cb236b90d156acc459293c731e66f9be679034c017178e998160a003bf6` |

Snapshot: `fa4d69613c35076c15f8746dc2efb145418c3bc3`.
Private overlay: `/tmp/foundation-ha-order-additive-yw0gcpn7/lib`.
Both final direct fresh builds passed on their first attempts, using
`-M6000 -j1 -DElab.async=false` with a 512 MiB disk reserve. Main output is
empty; checks have exactly 26 axiom reports and no diagnostics. Fresh objects:

- Main: `51e3580cd4d0350b2117f923b34e76903d3ceec1e61abd2f881344cde8730141`.
- Checks: `ef1fbfe58998f45482b842829e022eb74ff7eeb0f3215dc69eb77308050b4ec7`.

All reports use only `propext`, `Quot.sound` and, for the actual source
implication conversion, inherited `Classical.choice`. The existing
Foundation `imply_doubleNegation` theorem is explicitly audited. All new
logical/witness helpers themselves use only `propext` and `Quot.sound`.
No `sorryAx`, custom axiom, native decision procedure or model oracle occurs.
The HA target calculus is unchanged and has no classical rule added.

Exact commands, logs, source snapshots, drivers and cache records are in the
replay manifest and `reviews/foundation-ha-order-additive-author-replay/`.
Only the two new leaves were compiled. The private cache reuses 94 modules,
including the same 76 Foundation modules as the frozen OrderBase packet.
This consists of its 93 pinned prerequisites plus the independently replayed
OrderBase main object. Source/object/trace pins, compiler, package identities
and the inherited path inventory were verified before and after builds and
at freeze. There are no new Foundation imports or prerequisite builds. This
is not a fresh 94-module closure replay or a native-closure refresh.

## Exact actual-source endpoints

In namespace `DiophantineConsistency.FoundationHAOrderAdditive`:

```lean
addEqOfLt : HA.Proves
  (FoundationPAHFSyntax.sentence PeanoMinus.Axiom.addEqOfLtᴺ)

addLtAdd : HA.Proves
  (FoundationPAHFSyntax.sentence PeanoMinus.Axiom.addLtAddᴺ)
```

These are the literal named Foundation axioms, respectively
`forall x y, x<y -> exists z, x+z=y` and
`forall x y z, x<y -> x+z<y+z`. Their exact target closure counts are two and
three, with the respective matrix indices `(1,0)` and `(2,1,0)`. Separate
`rfl` checks bind both actual translated sentences and the existential
consequent's complete negative encoding. No source axiom-image hypothesis
is supplied.

## Witness and logical reasoning

The existing target strict-order formula is
`exists d, shifted(s) + S d = shifted(t)`. `add_witness` eliminates that
actual existential and chooses `S d` for the sum witness in
`exists z, shifted(s)+z=shifted(t)`. Its generic substitution and renaming
identities preserve all ambient terms under the witness binder.

`add_lt_add u` retains the same predecessor `d`. Within the fully shifted
finite context, actual HA associativity, commutativity and equality
congruence derive
`(s+u)+S d = s+(u+S d) = s+(S d+u) = (s+S d)+u = t+u`.
No standard-natural-number equality is used as an HA proof and no new
arithmetic induction is necessary beyond the existing additive theorems.

These ordinary witness proofs do not extract anything from a double-negated
order premise. `map_doubleNeg` lifts a finite relative implication using the
already proved intuitionistic logical map while retaining its exact finite
axiom list. For the sum-existence endpoint, `encoded_exists` converts an
actual existential to `not(forall z, not(not(not(body))))`: under the assumed
universal negation, its actual witness contradicts the double-negation
introduction of the body. Its existential elimination shifts the full open
context and opens the universal with the same fresh variable.

`apply_negative` then uses the proved stability of that syntactically
negative consequent, and only that consequent, to lift the double-negated
order premise. The addition-order conclusion stays double-negated throughout.
Neither order nor equality DNE is invoked. Finally the existing checked
Foundation implication equivalence and exact universal reclosure yield
both source sentences; no GG recursion is duplicated.

## Focused checks and boundary

Checks cover arbitrary axiom predicates/open contexts for the logical map,
a nested existential body with both universal and existential binders,
nonlinear parameter terms with free variables zero, four and seven,
ordinary and negative witness/order transport, literal successor-witness
instantiation, and a negative control excluding captured parameter slots.
A separate structural control distinguishes the negative existential
encoding from an extracted existential witness. Both actual source
endpoints and their imported implication conversion have explicit audits.

This packet discharges these two additive order-image cases. It does not
claim the remaining five cases (`oneLeOfZeroLt`, `mulLtMul`, `ltIrrefl`,
`ltTrans`, `ltTri`), complete arithmetic proof transfer, or the final HA
consistency/equation equivalence. All frozen earlier packets remain unchanged.
