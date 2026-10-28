# Guarded profile pairs and ordered codes: source-proof proposal

This is a read-only proposal for `ValidatorSeedProfileCodes222.lean` and
`ValidatorSeedProfileCodes222Checks.lean`, with sole import
`ZFCinPA.ValidatorSeedTransitive222`. No new Lean source, overlay, compiler,
or prerequisite refresh is part of this audit. The Transitive prerequisite
is now independently ROOT accepted; its accepted provider is selected
directly in the accompanying inventory.

The proposed endpoint is an actual internal seed-theory proof of profile
pair and Kuratowski ordered-code existence, followed by the finite code
uniqueness and congruence laws needed for the diagonal and reversal
bisimulation constructions. It does not yet prove any coded `Eqv` law.

## 1. Relations and literal source templates

The source-only guides have five distinct levels, which must not be
identified:

1. Literal equality in Foundation's set language, used by the accepted
   exact tagged-pair theorem and the seed theory's equality axioms.
2. `Profile.Same mem x y := ∀ z, mem z x ↔ mem z y`.
3. `ProfilePairs.ClassMember mem a b := ∃ z, mem z b ∧ Same mem a z`.
4. `ProfileCollection.Eqv`, existence of a coded bisimulation with an edge.
5. `ProfileComposition.Member`, membership saturated by that coded Eqv.

The actual `ProfilePairs.Pair` and `OrderedPair` definitions use levels
2–3, not levels 4–5. The validator's `Eind` is another relation, appearing
only in the later accepted seed-theory-to-C222 proof interpretation.
This preserves the correction recorded for the frozen Transitive proposal.

Work over `{V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* IΣ₁]`, retaining
the selected Type-0 API boundary. Set `Source V := seedTheory.internalize V`.
All public object parameters are arbitrary `Term V ℒₛₑₜ`, including
internally nonstandard free-variable indices. Write `D_t(x)` for the
literal formula `memTerm t x`. The five typed templates, defined uniformly
at semiformula arity n with capture-avoiding `bShift`, are exactly:

```text
S_t(x,y) := ∀ z (D_t(z) → (z∈x ↔ z∈y))
C_t(a,b) := ∃ z (D_t(z) ∧ (z∈b ∧ S_t(a,z)))
Single_t(s,a) := ∀ z (D_t(z) → (C_t(z,s) ↔ S_t(z,a)))
Pair_t(p,a,b) := ∀ z (D_t(z) →
                       (C_t(z,p) ↔ (S_t(z,a) ∨ S_t(z,b))))
OP_t(a,b,c) := ∃ s (D_t(s) ∧ ∃ p (D_t(p) ∧
                 (Single_t(s,a) ∧ (Pair_t(p,a,b) ∧ Pair_t(c,s,p)))))
```

For example the first two literal typed bodies are:

```lean
sameTerm t x y := ∀⁰ (memTerm t.bShift #0 🡒
  (memTerm #0 x.bShift 🡘 memTerm #0 y.bShift))
classMemberTerm t a b := ∃⁰ (memTerm t.bShift #0 ⋏
  (memTerm #0 b.bShift ⋏ sameTerm t.bShift a.bShift #0))
```

The `OP` outer witness is s, its inner witness is p; under both binders
s is #1 and p is #0. The ambient t,a,b,c receive two `bShift`s there.
Define `profilePairBody t a b := D_t(#0) ∧ Pair_t(#0,a,b)` and
`orderedCodeBody t a b := D_t(#0) ∧ OP_t(a,b,#0)` with all three ambient
terms shifted into that existential body.

Also define the five **unguarded** typed finite cores with the same
membership/quantifier skeletons as `Profile.sameForm` and
`ProfileSyntax.classMemberForm`, `singletonForm`, `pairForm`,
`orderedPairForm`. Prove exact typed syntax identities saying
`ValidatorSeedGicImages222.tagged j core` equals the corresponding displayed
guarded template with marker `fvar j`, at every relevant typed substitution.
This binds the new source formulas to the already represented moving-marker
operation, rather than introducing another relativization algorithm.

The external `SetTheory.Form` templates are read and pinned as guides;
their exact five finite shapes are displayed above. The proposed sole-import
leaf does not import `Translation` or `ProfileSyntax`, so it must not claim
a Lean equality to the external `toSet`/`NativeInterp.eqS` constants. A later
literal adapter to those existing constants remains explicit if that route
is used. No semantic satisfaction theorem is used to obtain the new internal
source proofs.

## 2. Precise public judgments and finite helper scope

The two existence endpoints are genuine source judgments:

```text
Source V ⊢ Empty(t) → D_t(a) → D_t(b) → ∃ c (D_t(c) ∧ Pair_t(c,a,b))
Source V ⊢ Empty(t) → D_t(a) → D_t(b) → ∃ c (D_t(c) ∧ OP_t(a,b,c))
```

Suggested names are `profile_pair` and `ordered_code`. Their object
antecedents are part of the formulas; there is no supplied image, model,
collection, distinctness or pair-existence Lean premise. In particular,
a=b and coincident free labels are permitted. The original exact
`tagged_pair` theorem permits untagged endpoints, but profile-pair existence
in the tagged domain must retain `D_t(a)` and `D_t(b)`.

Prove the following finite source logic, with all shown parameters arbitrary:

```text
same_refl:                 S_t(a,a)
same_symm:                 S_t(a,b) → S_t(b,a)
same_trans:                S_t(a,b) → S_t(b,c) → S_t(a,c)
class_member_right_congr:  S_t(a,b) → (C_t(z,a) ↔ C_t(z,b))
pair_singleton:            Pair_t(s,a,a) → Single_t(s,a)
pair_object_congr:         S_t(p,q) → Pair_t(p,a,b) → Pair_t(q,a,b)
ordered_code_congr:        S_t(c,d) → OP_t(a,b,c) → OP_t(a,b,d)
ordered_endpoint_congr:    S_t(a,a') → S_t(b,b') → OP_t(a,b,c) → OP_t(a',b',c)
```

Each line means `Source V ⊢ ...`; none needs Empty(t). Two helpers for
endpoint uniqueness require their literal domain guards:

```text
ordered_first:
  D_t(a) → D_t(z) → OP_t(a,b,c) → C_t(z,c) → C_t(a,z)
ordered_union:
  D_t(z) → OP_t(a,b,c) →
    ((∃ q (D_t(q) ∧ (C_t(q,c) ∧ C_t(z,q)))) ↔
      (S_t(z,a) ∨ S_t(z,b)))
ordered_injective:
  D_t(a) → D_t(b) → D_t(a') → D_t(b') →
    OP_t(a,b,c) → OP_t(a',b',c) → (S_t(a,a') ∧ S_t(b,b'))
```

Do not silently infer `D_t(x)` from `S_t(x,y)` or from an unguarded
membership atom. The OP predicate contains the guards on its two internal
witnesses; it does not itself assert that its outer code c or its endpoints
are tagged. Existence adds the code guard explicitly, and injectivity has
all four endpoint guards. Code/endpoint congruence is only a statement about
the OP formula, not an assertion that a replacement object is tagged.

These finite helper laws, two existence proofs, and actual `Proof seedTheory`
certificates for the two existence conclusions and injectivity are the
coherent proposed pair. No App/Bisim/Eqv definition or theorem is requested
in this first packet.

## 3. Actual proof construction

Use accepted `ValidatorSeedTransitive222.tagged_pair a b t` to choose c.
Its exact membership description says every tagged member of c is literally
a or b. For tagged z, an actual `C_t(z,c)` witness w is tagged and lies in c,
so that description gives w=a or w=b. Actual source equality replacement
then changes `S_t(z,w)` into the corresponding profile equality. Conversely,
if `S_t(z,a)`, use the actual witness a: its guard is an explicit antecedent,
and the exact pair formula at a supplies a∈c using source equality
reflexivity. The b case is identical. Reclose the tagged test z and retain
the c guard. This is the finite source version of `KLowerEqv.tag_pairs`;
it uses no collection instance and no coded Eqv law.

For the ordered-code endpoint, choose a profile pair s of a,a, convert it
to a profile singleton; choose a profile pair p of a,b; then choose a
profile pair c of s,p. Both s and p have constructed domain proofs, so the
third use has its genuine premises. Retain the original Empty(t) and
endpoint-domain assumptions through all three shifted existential
eliminations. Reassemble OP in the order s then p.

The congruence proofs follow the literal finite `ProfilePairs` arguments:
right congruence transports the raw membership of the *tagged* class-member
witness; Pair and OP congruence then use that biconditional. No left raw
membership congruence under Same is asserted.

For uniqueness, derive `ordered_first` and `ordered_union`. Use the second
code's tagged singleton witness s' to show `C_t(a,s')`; its singleton law
at the explicitly tagged a yields `S_t(a,a')`. Compare the two union
descriptions at b and b'. The remaining two cases split on `S_t(b,a)` in
the actual classical source calculus and use Same symmetry/transitivity.
This split is an object-level proof construction with finite contexts,
not a metatheory semantic case distinction asserted as a source derivation.
The resulting first/second endpoints are not swapped.

The selected closure already contains the actual equality-theory inclusion
and `SetCongruence.setReplace`, `set_eq_symm`, `subst_mem`, as well as typed
specialization, finite-context deduction/MP and the quantifier rules.
Existing SetCongruence provenance is inherited: some fixed logical bases
were obtained by its checked outer completeness/specialization lemmas,
whereas its general formula replacement is represented internally. The new
pair must not invoke standard-Nat semantic profile theorems as an oracle
for arbitrary internal source parameters.

## 4. Syntax, code and proof-witness checks

Prove `_shift`, `_free`, typed substitution and moving-marker binding laws
for the five templates and the two existential bodies. A free-variable
shift changes the marker too; under `tagged j`, it becomes j+1. No free
marker is assumed shift-fixed. Every eigenvariable proof shifts the entire
finite context, including Empty(t), endpoint guards, earlier witnesses and
all arbitrary parameter terms.

Bind each finite template to a fixed standard Foundation quotation and
define its total raw constructor by substitution of its term-code arguments.
Give concrete Σ₁ graphs and typed/value equalities for these formula
constructors and the two body constructors. Term-code arguments are not
bare variable indices. The `.get` source proof selectors give actual
internal proof witnesses; they are **not** asserted to have Σ₁ graphs.

Focused Checks should cover the first/second coordinate orientation, s/p
binder order, all guards, repeated endpoints, a marker/endpoint coincidence
without dropping the resulting domain antecedent, sparse free labels,
simultaneous shifts, the literal `tagged j` equations, total raw/typed
bindings and the actual three `Proof seedTheory` certificates. Axiom reports
must use only the inherited standard axioms. No fresh dependency or
Foundation build is proposed.

## 5. Exact proposed dependency boundary

Sole proposed import: `ZFCinPA.ValidatorSeedTransitive222`. The complete
current header DAG, all cached artifacts and actual first-provider paths
are audited by the accompanying read-only script/JSON: **218 cached modules,
136 Foundation modules, 626 cached artifacts, 45 external boundary primaries,
671 actual artifact providers**, zero refresh. The proposed two fresh leaves
would retain `-M6000 -j1 -DElab.async=false`, one thread, fresh regular
nonsymlink outputs and the 512 MiB reserve. No compiler has been launched
for this proposal.

Select ROOT's accepted Transitive provider directly:

```text
/tmp/validator-seed-transitive222-root-qv3nmmuc/lib
main source: 53e600acb96561fb29cc1771a47ca0e2e5f99124a709bb7cfe5d7b5b5e52aec7
main object: dd04c8a90ba6ef19b7a67b39c23b0b25926a3db34b308bc60dacee041b4baf9a
ROOT packet: b442cf5993ce927a8015b11b21cb1041ebbef30f2320673475423f7e323e269c
ROOT 13-file manifest: 40aacd7225f748f5d43a23b2283abdf648efb99847707e5ef65a9c6caee61382
```

The author packet, five preserved attempts and ROOT's independent replay
are separately pinned. Reuse retains all inherited source/run provenance
and missing-companion qualifications. External profile/quotient/WF sources
are source-only guides, not newly authenticated compiled prerequisites.

## 6. Next actual Eqv and ZF obligations

The next source pair after these codes can bind App/Bisim/Eqv and discharge
the **diagonal** and **reverse** GIC instances. Actual guarded transitivity
plus diagonal collection and ordered-code uniqueness gives reflexivity;
reverse collection plus endpoint congruence gives symmetry. Those finite
source proofs are not already supplied by `ProfileCollection`'s semantic
lemmas. The diagonal proof must transport members to a represented input
inside the container; profile equality alone does not put an endpoint in
that container (`bisim_refl_of_collection` makes this distinction explicit).

Transitivity then requires the actual fiber, composition and union template
proofs; extensionality requires forward/backward matching and union. Those
are the precise `ProfileComposition` source obligations, not arbitrary
semantic collection-relation assumptions. `Member` congruence follows only
after the required Eqv laws. The nine-field `KQHyp.QHyp` route additionally
needs interpreted union, interpreted power and singleton-closed containers.
Raw transitivity plus GIC does not prove NativeTheory's literal CP.

`KQ1Model` and `KQ1ZF` give the semantic quotient and well-founded-part
guide, but their NatForm/BProv soundness is not an all-internal Foundation
proof transform. `NativeInterp`/`NativeSchema` currently use native CP/GIC,
so their hypotheses cannot simply be fed the tagged seed results. The
remaining work includes exact source templates/axiom images for the QHyp
route, parameter-safe represented quotient/WF interpretation, arbitrary
internal Separation/Replacement instances and actual ZF proof transfer.
The accepted moving-marker family remains available for the tagged stage;
the old shift-fixed `InternalInterpretation.Good` hypothesis is not true of
a free marker and is not assumed here.

Choice remains separate. `LSchema.provable_falsum_ZF_of_ZFC` is the existing
all-internal IΣ₁ reduction to reuse once genuine ZF-to-seed calibration is
proved. This pair proves neither ZF/ZFC calibration nor a current PA/HA
equation equivalence.
