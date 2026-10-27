# Actual GIC schema images in the moving tagged domain

27 October 2026. Read-only proposal by `/root/circuit_reduction`.
No Lean source, namespace overlay, compiler command or prerequisite refresh
was created by this audit. The recommended next pair is
`ValidatorSeedGicImages222.lean` and `ValidatorSeedGicImages222Checks.lean`.

The substantive target is the actual existing `gicTheory` recognizer,
including arbitrary internal closure counts. It is not merely a standard
quoted instance or an open-body image. Collection has independent ROOT
acceptance. MarkerRelativization has author PASS and remains provisional
until ROOT's review/replay acceptance and a separately pinned provider
supplement. The existing frozen packets are unchanged.

## 1. Exact existing source schema and the slot discrepancy

`Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeGicDelta1.lean` defines:

- `gicBodyMeta` at44: the literal universally quantified bound a and
  existential collected bound b, followed by global support and coverage.
- `gicBody` at56 and `gicBodyVal` at130: typed and arbitrary raw-code bodies.
- `gicBodyVal_eq` at139: their exact identity for every internally typed
  binary matrix. This is available in an arbitrary IΣ1 model.
- `gicBodyValGraph` at212 and its defined instance at229: fixed total Σ₁
  syntax construction.
- `GicR` at255: the actual `SchemaRecognizer ℒₛₑₜ 2 gicBodyVal`.
- `gicTheory` at270 and `gicTheory_delta1` at274: the actual theory and its
  literal recognizer. No new stand-in theory/recognizer is needed.

Its core K uses bound slot0=input x and slot1=output y. Thus its support
substitution `![#0,#1]` reads K(x,y), while its coverage substitution
`![#1,#0]` reads the same relation after binding y last.

Accepted `ValidatorSeedTaggedCollection222.collectionBody` at917 uses
θ slot0=output y and slot1=input x. The matrix fed to Collection must be

```text
θ_(j,K) = (typed R_j(K)).subst ![#1,#0],
R_j(p)  = MarkerRelativization.tagRel j p.
```

Passing K unchanged would reverse the relation. Passing only the swapped
raw K would also omit relativization of quantifiers inside K. The proposed
proof binds this swapped **relativized** matrix to both actual substitution
vectors. It preserves all internally sized free parameters of K.

`tagged_collection` at1043 proves the actual source formula

```text
Empty(t) → t∈a → ∃ C,
  t∈C ∧
  (∀ y, t∈y → y∈C → ∃ x, t∈x ∧ θ(y,x)) ∧
  (∀ x, t∈x → x∈a → (∃ y, t∈y ∧ θ(y,x)) →
     ∃ y, t∈y ∧ y∈C ∧ θ(y,x)).
```

The global-support input x is not restricted by a. Its genuine source
Proof certificate is `taggedCollectionProof_isProof` at1062. This is
exactly the stronger body needed to read the GIC schema in the tagged
raw-membership domain, under the source antecedent Empty(t).

## 2. Proposed open-body endpoint

Work in every arithmetic model V of IΣ1. Reuse `seedTheory`, `emptyCode`,
`tagRel`, and actual Foundation `Provable`/`Proof`. The principal body
statement is:

```lean
-- Proposed, not yet implemented.
theorem gic_body_image (K : Semiformula V ℒₛₑₜ 2) (j : V) :
  Provable seedTheory
    (imp ℒₛₑₜ (emptyCode j) (tagRel j (gicBodyVal K.val)))
```

The proof uses Collection with marker `fvar(j+1)`, bound `fvar 0`, and the
swapped relativization of `K.shift`. The accepted family identities
`tagRel_shift`, `tagRel_free`, `tagRel_subst` and `shift_empty` identify that
formula with the freed outer universal body. The actual typed
`TProof.generalizeAux` then closes a, while retaining Empty(fvar j).
All implication/quantifier identities are syntactic equalities in the
actual source syntax. No model truth or standard-Nat decoding is used to
infer source provability.

Checks must expose the matrix swap, both support/coverage substitutions,
a nested quantified matrix with arbitrary free labels, and marker labels
that coincide numerically with a free parameter. There is no freshness
premise in this body endpoint. The universal closure step below arranges
its marker above the freshly opened bound parameters automatically.

The derived body proof is useful but is not the final advertised scope:
actual arbitrary recognized closed GIC instances must also be handled.

## 3. Arbitrary internal closure with a decreasing marker

The actual recognizer supplies internal m,b,K and equations

```text
p = qqAlls b m,
IsUFormula b, shift b = b, bv b = m,
IsSemiformula 2 K,
subst(fvarVec m)b = gicBodyVal K.
```

This shift-fixedness belongs to the original closed schema body b. It does
not assert that the free-marker domain `domainCode j` is shift-fixed.
`SchemaClosure.schemaRecognizer_quote_iff` is a Nat theorem used to establish
the Δ₁ theory instance; it is not an all-internal inversion oracle. The
new proof extracts the displayed witnesses directly from actual `GicR p`.

The smallest generic closure statement is:

```lean
-- Proposed, not yet implemented.
theorem close_guarded {m b j : V}
    (hb : IsSemiformula ℒₛₑₜ m b)
    (hbs : shift ℒₛₑₜ b = b)
    (base : Provable seedTheory
      (imp ℒₛₑₜ (emptyCode (j+m))
        (tagRel (j+m) (subst ℒₛₑₜ (fvarVec m) b)))) :
  Provable seedTheory
    (imp ℒₛₑₜ (emptyCode j) (tagRel j (qqAlls b m)))
```

For fixed j,m,b define

```text
B_i = subst(fvarVec(m−i))(qqAlls b i),
r_i = j+(m−i).
```

Use actual Σ₁ induction on the internal i with motive

```text
i≤m → Provable seedTheory(Empty(r_i) → R_(r_i)(B_i)).
```

All displayed syntax maps are Σ₁ functions; proof existence is Σ₁ and the
bound antecedent is Δ₀. There is no unbounded marker-family quantifier in
the induction motive. Consequently this closure route requires only IΣ1,
rather than adding IΣ2 merely to quantify uniformly over marker choices.

At i+1≤m write m=k+(i+1). The previous marker is
`j+(k+1)=(j+k)+1`. Put
`X = subst(qVec(fvarVec k))(qqAlls b i)`. Existing pure syntax identities give

```text
free X = B_i,
B_(i+1) = ∀ X,
free(R_(j+k)(X)) = R_((j+k)+1)(free X),
shift Empty(j+k) = Empty((j+k)+1).
```

The induction hypothesis is therefore an actual proof of
`Empty(j+k).shift → (R_(j+k)(X)).free`. Add the disjunction with the freed
negative domain guard, then apply `TProof.generalizeAux` to obtain exactly
`Empty(j+k) → R_(j+k)(∀X)`. The extra guard weakens the universal body;
there is no domain-assumption discharge or unbounded DNS in this step.
At i=m, `fvarVec 0` substitution is the identity on the closed formula.

Existing helpers were inspected before proposing replacements:

- `NativePeel.shift_qqAlls` at81;
- `NativePeel.free_subst_qVec_fvarVec` at90;
- `ModelCodedBindFree.fvarVec_isTermVec` at388;
- `TProof.generalizeAux` in Foundation Proof/Typed at472;
- `NativePeel.peel` at138 and `R2Ax.closure` at71 as source guides only.

The first two NativePeel syntax helpers have no `Good` premise and are
recommended for direct reuse. Its interpreted `peel` and `peel_step` do
require shift-fixed `Good`; neither will be invoked. The existing private
copies in ValidatorFullSeedTheory are not usable as public imported APIs.
A three-import alternative can locally reprove those two small identities,
but direct reuse avoids another copy of their binder reasoning.

## 4. Actual recognized schema and hAx endpoint

After the open body and closure proof, the substantive endpoints are:

```lean
-- Proposed, not yet implemented.
theorem recognized_gic_image {p : V} (hp : GicR p) (j : V) :
  Provable seedTheory (imp ℒₛₑₜ (emptyCode j) (tagRel j p))

theorem axiomImages_gicTheory :
  ValidatorSeedMarkerRelativization222.AxiomImages gicTheory V
```

The first theorem extracts arbitrary internal recognizer witnesses,
forms the typed K from its actual typing predicate, uses the body image at
j+m, and applies `close_guarded`. No `IsSemiformula.sound`/standard quotation
argument is allowed in this internal proof. `gicBodyVal_eq` supplies the
literal typed/raw equality.

For the second theorem, the actual gicTheory Δ₁ membership reduces to
`GicR p`. Unpack the proven implication into its actual source sequent,
then weaken by the typed canonical sideSet j. This yields exactly
`{R_j(p), ¬Empty_j} ∪ sideSet j`. The p<j premise of AxiomImages may remain
unused because this particular image is stronger. No image oracle is
supplied. A selected internal Proof certificate for the literal implication
may be exposed; no total Σ₁ graph for the whole chosen proof-code map is
claimed without a separate representation proof.

Checks should retain internal m (including 0), j=0, m>j, nested K, both
slot orientations, exact literal GicR/gicTheory membership and the fully
unfolded AxiomImages resource. The internal induction, not a finite list
of standard m examples, is the essential closure check.

## 5. Deliberate remaining boundaries

The proposed first pair closes a genuine concrete schema component of
hAx. Finite equality and irreflexivity images would require no new language
or semantic principle: seedTheory already contains the actual source
logical equality axioms and irreflexivity, and their guarded universal
versions can be derived with finite source proofs. They should follow in
a short separate leaf rather than dilute this arbitrary-schema checkpoint.
The earlier ValidatorEqualityImages222 proves images into C222 via Eind;
it is not directly the moving-marker source-image theorem and must not be
cited as if the target languages coincided.

`NativeTheory.nativeTheory` additionally contains its literal power-container
axiom. The tagged seed domain does not supply that CP axiom. The proposed
GIC endpoint must not be promoted to AxiomImages nativeTheory by silently
substituting the tagged interpreted-power result.

The actual external contracts in `KQHyp.QHyp` and `KLowerQHyp.tag_qhyp`
separate GIC from Eqv reflexivity/symmetry/transitivity/extensionality,
profile pairs, interpreted Member-union, interpreted power, and
singleton-closed containers. The new schema image advances its GIC
component only. Remaining all-internal represented source proofs for
those quotient/WF ingredients, the guarded atomic Eqv/Member interpretation,
and the actual ZF proof transfer remain open. The already audited ZFC→ZF
Choice reduction remains a separate reusable theorem once that bridge is
available; no new Choice semantics is required here.

## 6. Exact cache/provider proposal

Recommended four imports:

```text
ZFCinPA.ValidatorSeedMarkerRelativization222
ZFCinPA.ValidatorSeedTaggedCollection222
ZFCinPA.NativeGicDelta1
ZFCinPA.NativePeel
```

The read-only audit passed: **215 cached modules /136 Foundation /623 cached
artifacts /45 explicit external boundaries /668 actual first artifact
providers, zero prerequisite refresh**. No new Foundation boundary appears.
The smaller alternative without NativePeel is 212/136/620/45/665, but needs
the two local syntax-helper proofs. The recommended delta consists only of
the two current leaves plus previously authenticated NativeGicDelta1,
SetRelativization, InternalInterpretation and NativePeel. The latter three
are loaded only to reuse the two pure NativePeel identities.

Collection selects accepted ROOT
`/tmp/validator-seed-tagged-collection222-root-iuusy4yv/lib` directly.
Its ROOT packet is 9f825accf2e3b4c57b6c4eb5bfa9001d6af7f6c5ac71d8b5e55bd2473e0f8597
and its 15-file manifest is 9c0fb3de41ff6a3e7ad5cb71fae094772bb8c832e685a9a2fb08df7a00aec2a9.
MarkerRelativization currently selects frozen author attempt
`/tmp/validator-seed-marker-relativization222-author-scwpqslx/attempts/1793102312940420091/lib`
only for this read-only proposal. Its pending acceptance must be recorded
by a separate ROOT-provider supplement before any new leaf execution.

The four historical modules retain exact source/object and executed-run
provenance from accepted fixed-consistency73 records. Missing companion
artifacts remain explicitly recorded; this audit does not turn them into
freshly rebuilt dependencies. All selected headers, transitive source DAG,
source/object hashes, historical evidence pins, explicit package boundaries
and actual first artifact providers were rehashed without creating an
overlay or invoking Lean. The frozen JSON lists all 4,497 observed paths.

`validator-seed-gic-image-plan.json` SHA256:
`f9c5279931ec426798b8fe1b1143bfb188c90f5ec0d7f27368808cef258ad20f`.
The full read-only auditor and its terminal log accompany this proposal.
Only a separately approved new pair would be compiled, under the existing
Lean 4.32/M6000/j1/async=false/512MiB protocol. No execution is authorized or
claimed by this note.

The additional historical source/object pins are explicit:

| Module | Current source SHA256 | Selected object SHA256 |
|---|---|---|
| NativeGicDelta1 | `9abb4d641e4d3db586c25f525d0efea98da466bc4497f5c11c9f0393078ce861` | `b330dfcbf2c8e23b76676d29b135b1ba4d761db0fbb5cbc4e92d89a431cead04` |
| SetRelativization | `b2d4cec4106aa5ff68a66b1b624415b4ec91f8bcb542340716b83d1f3eadfdae` | `b99c0744a5ac1a58e967d20ec8fd093d29be40ff70bf67020b06ead5b7daf6d2` |
| InternalInterpretation | `60bdb604d5aa34402a3a050a397a4b46b7e2892ae1a14875a806caa9dfac3720` | `9552dfb313ed4cd0de34406310853af9f088b79b906e3533a344a033cff27646` |
| NativePeel | `737541664f434e4c7e94d947a4d663d2e26b935ed1d920f157747bb00eb25b09` | `a07851d3fde91587a0bceff3590a846822d7131d3f4060888b63d90ba20e1b97` |

The selected paths, original executed-run summaries, absent companion lists
and full dependency records are in the JSON. These old objects are reused
only under their recorded current-source provenance, not newly compiled or
newly authenticated whole-transitive-library claims.
