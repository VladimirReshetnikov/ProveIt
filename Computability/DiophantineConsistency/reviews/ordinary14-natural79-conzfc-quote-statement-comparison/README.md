# Natural-79 target and the displayed Carrier65 quote

The natural-79 draft and the historically checked Carrier65 normalized quote can be aimed at the **same specified Foundation ZFC consistency encoding**, but the draft 79 endpoint has not been checked and the quoted endpoint is not a formal interpretation of the TeX or PDF bytes. The following is a statement-level comparison of pinned sources and retained historical evidence, not a newly checked Lean composition.

Let `S` be `IPRAStandardTheory.standardTheory`, `N79` be `IPRAExpressionNative.nativeNoZero Natural79EndpointDraft.expression`, and let `rho` be `provabilityPred ZermeloFraenkelChoice ⊥`. Define:

* `R = mappedNativeRefutation embedding = native (Semiformula.lMap embedding rho)`;
* `C = (Semiformula.lMap embedding sourceSentence)ᴺ`, where `sourceSentence` is Foundation's actual ZFC-with-choice `.consistent` sentence and is definitionally `∼rho` in the classical source syntax;
* `Q` be the intuitionistic sentence returned by the checked normalized `quoteSentence` for Carrier65.

The **unelaborated** 79 source proposes `S ⊢ N79 ↔ ∼R`. The source of `IPRABoundedRhoZFC.zfcEquiv` states `nativeTheory ⊢! C ↔ ∼R`, with `IPRAStandardTheory.provable_iff` transferring derivability to `S`. The historical Carrier65 endpoint reports an existential `Q` with `quoteSentence = some Q` and `S ⊢ Q ↔ C`. Its retained compile log reports `[propext, Classical.choice, Quot.sound]`; the historical outer-session result and independent terminal audit report success for the pinned source snapshot. These are metatheoretic Lean axioms, not additional axioms silently added to iPRA. Historical provider, package and dynamic-import ancestry remain as documented in that endpoint's own records.

Once those proofs are available in one compatible checked context, the two directions compose constructively:

```text
N79 → ∼R → C → Q
Q   → C   → ∼R → N79
```

This gives an internal `S` derivation of `N79 ↔ Q`; similarly, the first two links give `N79 ↔ C`. It asserts existence of internal derivations, not either consistency or non-consistency. It does not identify the two graphs or their coefficients: the proposed 79 expression uses compact symbolic ports, whereas the normalized Carrier65 quote uses the separately specified current ports. Nor does it prove the 79 hypothesis on a historical Carrier65 object without a coherent checked provider composition.

The constructive comparison is not an automatic erasure of Gödel–Gentzen notation. `native` keeps existential and disjunction and reads negative atoms intuitionistically, whereas source-level negation is classical NNF. The general mapped-negation theorem explicitly asks for a backward derivation `rhoᴺ → ∼∼native rho`; the specialized `zfcEquiv` source supplies that comparison for this selected Foundation `rho` via its bounded-matrix construction. The comparison only gives equivalence of the **negated** refutation readings; it need not extract a positive proof witness from a translated one. No extra double-negation elimination is needed when composing the stated biconditionals.

The user has not specified an independently coded Con(ZFC) sentence. If one is specified later, equating it in iPRA with this selected Foundation proof predicate requires a separate constructive comparison. The existing `source_nat_iff_no_refutation` is a standard-natural semantic result and does not by itself provide that iPRA derivation. The normalized quote is fixed Lean token data externally compared with the maintained equation; the historical theorem does not parse the raw TeX or PDF, verify rendering, or prove that a physical file has those semantics. The later 79 packet and its provider closure remain unelaborated, and no Lean command or staging was performed here.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-conzfc-quote-statement-comparison/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-conzfc-quote-statement-comparison/result.json
```
