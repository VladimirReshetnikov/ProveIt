# Arbitrary Foundation induction translated into HA — author receipt

Author: `circuit_reduction`. This is author review, not independent review.
All new Lean source, checks, preparation and freeze drivers were read before
execution, and the complete final main and checks were reread. No frozen
source, vendor file, shared object, umbrella or Git state was changed.

## Frozen source and replay

| File | Lines | SHA256 |
|---|---:|---|
| `Lean/DiophantineConsistency/FoundationHAInduction.lean` | 185 | `5bb128fba58b887d8d40a133d8d9e1f4ff122e5dfd6266c0f114858eeb74e42c` |
| `Lean/DiophantineConsistency/FoundationHAInductionChecks.lean` | 132 | `0242cb704546414b35d0d913a177a7dc0b6cd17243c1f97484d42da53b57c3e0` |
| `reviews/foundation-ha-induction-dependency-replay.json` | — | `15f7d958f80986755817dab4e8c0684cd03ec015e284dccbdc6cc8f762c879c4` |

Snapshot: `88cf5fc90ea7abc2e81be1a01247d2964078965b`.
Private overlay: `/tmp/foundation-ha-induction-wjk4g3e1`.
Both final direct fresh builds passed under `-M6000 -j1` and source-level
`Elab.async false`. The accepted main log is empty. All 30 final check reports
contain only `propext`, `Quot.sound`, and, where inherited from the existing
Foundation implication equivalence, `Classical.choice`. The imported
`LO.FirstOrder.Derivation.imply_doubleNegation` is audited explicitly.
No final report contains `sorryAx` or a custom axiom. The target remains the
actual intuitionistic `HA.Derives` proof calculus; a standard metatheory choice
dependency does not add a choice, excluded-middle or DNE rule to HA.

Fresh main object SHA256:
`af8435390f8edc5a49905725b66ed2ddb8f681225e0c7470cd228aeea6b021d6`.
Fresh check object SHA256:
`5c1c91c90f287f13ac3aec2c2ed7d129a2e2715be429a311662b99fce01dfa96`.
The exact commands, source snapshots, logs, drivers and prerequisite inventory
are retained in the replay JSON and `reviews/foundation-ha-induction-author-replay/`.

The accepted runs are main stage 6 and checks stage 2. Earlier rejected
main attempts concerned literal-source notation, free-index normalization,
qualified logical-hom rewriting and finite-context elaboration. The rejected
check run used an ambiguous unqualified `induction_axiom` name and an
unresolved `Set.mem_univ` placeholder. Final checks qualify the actual new
endpoint and supply its exact body. Rejected logs/source snapshots remain
explicitly separate from the successful results; they are not accepted proofs.

## Exact new endpoints

In namespace `DiophantineConsistency.FoundationHAInduction`:

```lean
succInd_open (φ : Semiformula ℒₒᵣ Nat 1) :
  HA.Proves (FoundationPAHFSyntax.formula
    (LO.FirstOrder.Arithmetic.succInd φ)ᴺ)

succInd_closed (φ : Semiformula ℒₒᵣ Nat 1) :
  HA.Proves (FoundationPAHFSyntax.sentence
    (Semiformula.univCl (LO.FirstOrder.Arithmetic.succInd φ))ᴺ)

induction_axiom {σ : Sentence ℒₒᵣ}
    (h : σ ∈ LO.FirstOrder.Arithmetic.InductionScheme ℒₒᵣ Set.univ) :
  HA.Proves (FoundationPAHFSyntax.sentence σᴺ)
```

The source is the existing unrestricted first-order induction schema, not a
new restricted substitute. The final premise is actual schema membership,
not an assumed image-provability predicate. It is eliminated to obtain the
body and its exact source parameter closure. The body is arbitrary: it can
contain quantifiers, disjunction, negation, order and free parameters.

The proof uses the actual source's curried formula
`φ(0) -> ((forall x, φ(x) -> φ(x+1)) -> forall x, φ(x))`.
Source implications are converted through the existing Foundation GG
implication equivalence and the checked `FoundationPAHFLogic` proof map.
No GG recursion is duplicated. Both source premises are introduced as
ordinary finite HA assumptions and retained through the shifted induction
step context. HA's actual formula-induction axiom is applied to `formula φᴺ`.
The closed theorem uses the frozen `FoundationHAClosure.proves_univCl`, so
its quantifier order and free-variable closure are exactly the source's.

## Binder and arithmetic audit

The source zero substitution removes its single bound slot; target ambient
parameter indices decrease by one. The source `x+1` step retains the slot
and leaves ambient parameter indices unchanged. These two operations are
proved separately, not identified by a convenient notation convention.

The step `x+1` is not definitionally `S x`. The proof uses the genuine HA
arithmetic theorem `Arithmetic.add_one (.var 0)` and Leibniz equality inside
the arbitrary translated body. Its temporary equality hole is constructed
by `Formula.rename (SetTheory.up Nat.succ)`: slot zero is fixed, every ambient
slot is shifted, and nested binders are handled by the existing capture-avoiding
renaming/substitution operations. `hole_substitution` and
`successor_substitution` remove the hole exactly. No semantic equality or
standard-natural-number identity is substituted for an HA derivation.

Generalization explicitly uses `Formula.Ax_s_sentences` and shifts the entire
finite context. The universally quantified source step is then opened at
variable zero using the checked `subst_instTerm_var_zero_rename_up_succ`
identity. Thus the open induction hypothesis and both parameterized source
premises have their actual required indices.

Checks include a source with two nested binders, disjunction, order, and free
parameters zero and seven; an arbitrary one-hole target with two binders;
literal zero/successor/add-one/hole slot identities; negative controls for
incorrect parameter movement; a step substitution containing a free
parameter; an undischarged open formula assumption; the exact curried source;
and actual open, closed and schema-membership HA proofs. These are syntax and
proof checks, not model evaluations.

## Authenticated dependency scope and limits

The private prerequisite overlay reuses 85 Foundation modules and 18 custom
modules. All 85 Foundation records belong to the previously accepted
95-module arithmetic215 inventory. Their source, trace, compiler and all four
object-companion SHA256 values were checked, together with the original Lake
source/output hashes. The nine additional Foundation imports relative to the
previous 76-module equality packet are Schemata, Definability and its four
support modules, PeanoMinus.Functions, TA.Basic, and Vorspiel.ExistsUnique.
They were authenticated from that existing inventory, not freshly rebuilt.

The 18 custom prerequisites are the previous 16 equality prerequisites plus
the accepted equality leaf and root's accepted closure leaf. Exact source and
object pins, parent manifests, compiler and package identities were rechecked
at freeze. Only the two new leaves were freshly compiled. This is not a fresh
103-module closure replay, a broad Foundation build, or a native-equation
closure refresh. Although the existing Schemata module also contains model
results, no model-induction theorem is used by this packet.

This closes arbitrary induction-image preservation in conventional HA.
The remaining PeanoMinus order/geometric images, complete arithmetic theory
transfer, the actual machine/refutation arithmetic connection and the final
HA equation/consistency equivalence remain separate obligations. No such
endpoint or arithmetic-image oracle is claimed here.
