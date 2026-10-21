# A smaller named calibration boundary

Research only, against ProveIt beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc. No repository edits, received-code execution, or Lean/Rocq run. The prior research packet remains unchanged.

## Results, in adoption order

1. **One fresh universal replaces double negation without another induction.**

   Use pad ψ := all (enc ψ) ψ. Existing Code254GIC.occurs_lt_enc (line109) and not_free_enc (line141) already prove freshness, including all bound-label occurrences. Named universal semantics uses update at a Nat variable label, not a de Bruijn shift.

   The padding code exceeds 1 by the constructor equation alone. EqFree preservation is definitional. Semantic preservation uses sat_ext and the explicit valuation witness e(enc ψ), and needs neither classical double-negation elimination nor irreflexivity. An empty domain admits no Nat→V valuation, so there is no extra nonemptiness assumption or invalid empty-model consistency inference.

   The old double negation adds two implication and two bottom nodes; the fresh universal adds one NF node. Writing c=enc ψ, the new numerical code is 8c²+8c+2. The old double-negation code is 2(2c²+6c+8)²+6(2c²+6c+8)+8. For c=1 these are 18 and 616. These are constructor/code-size comparisons only, not measured proof-size, compiler-time, TM-runtime, state-count, or consistency-strength improvements.

   This also makes the local enc_pos induction unnecessary after the already-proposed syntactic round-trip deletions. Even without adopting the padding, Code254GIC.enc_pos (line97) already supplies that fact.

2. **Use a sparse named axiom theory for the lower bound.**

   SeedAx f := ∃ ψ, EqFree ψ ∧ f = bundleNF 0 1 (enc(pad ψ)) (pad ψ).

   seedAx_derivable proves each such axiom's interpreted code derivable via th_eqFree, enc_bundleNF and C222.bundle. Instantiate the EXISTING c222_complete with SeedAx rather than all DerivableNF. A model of this smaller theory provides exactly the equality-free seed relations consumed by fullSeed_quotient. The equality interpretation, quotient construction, irreflexivity, and explicit valuation remain intact.

   FreshPadding.uncompiled.lean supplies a fully written, but UNCOMPILED, first-stage proposal. Its migration adapter STILL uses seed_of_bundle and TWO sat_encode_decode applications. The import is now KLowerQHyp instead of the unnecessary KEndpoint umbrella; it still transitively imports the old lower calibration and decoder. Nothing has been removed from the production repository or measured in a build.

3. **Eliminate the lower named→code→decoded→named semantic detour.**

   This is the separate, UNIMPLEMENTED second stage. Prove sat_bundleNF_iff_seed for a≠b, k≠a,b and ¬Free k m directly in named syntax. The exact statement and three smaller normalization lemmas are in NAMED_KERNEL.md. Because genuine NF.bot is used, this local theorem needs no irreflexivity; the whole lower endpoint still does.

   With that theorem, stage1's two round-trip uses disappear from the theorem-term dependency path. No new freshness induction is needed. The upper all-natural-code soundness proof must remain untouched, including raw code0, the code1/Rel00 alias and a=b.

## Dependencies and assumptions: exact distinction

| Path | Current production | First-stage proposal | Named-kernel second stage |
|---|---|---|---|
| Lower theory | All DerivableNF | Only SeedAx | Only SeedAx |
| Matrix padding | Double negation | One fresh named forall | Same |
| Padding freshness | Not needed | Existing not_free_enc/occurs_lt_enc | Same |
| Padding semantics | Classical double negation | sat_ext, explicit valuation | Same |
| Bundle semantic adapter | Decoded seed_of_bundle | Still decoded seed_of_bundle | New direct named iff, not yet proved in Lean |
| Semantic encode/decode | Matrix round trip | Bundle and matrix round trips | Neither locally |
| Encoded derivability | enc_dec_enc, eqFree_dec_enc, th_eqFree | th_eqFree, enc_bundleNF | Same |
| Lower model irreflexivity | Required | Required | Still required overall |
| Raw-code upper soundness | Every natural, gated bundles, a=b included | Unchanged | Unchanged |
| Kernel validation | Upstream source/receipts only | Not run | Specification only |

No claim is made that the sparse theory has exactly the same class of models as all DerivableNF. It need not. The generic completeness theorem only requires derivability of its axioms and the absence of an irreflexive model with a valuation under the assumed ZF refutation. Those are exactly the two obligations supplied.

## Module-level adoption, not just shorter theorem bodies

- Fresh-padding helper: current KSeedModel222 already reaches Code254GIC through Code254Models, so no new import is needed for the existing occurrence bound.
- KLower.seedProp_congr already avoids manual seed-witness reconstruction. The standalone proposal can use it after importing KLowerQHyp. To use it earlier inside KSeedModel222, move its generic proof to KSeed222 (where SeedProp is defined), retaining a compatibility alias. Do not import KLowerSeed into KSeedModel222: that would create a cycle.
- Actual decoder-free lower imports require extracting SeedProp to a light semantics module importing TarskiCalculus, and named bundle syntax to a module importing that syntax/semantics layer. Put the direct named normalization there.
- Keep the existing encoding facts and sparse derivability adapter in a separate module depending on Code254/KCode222/KEind222. The lower endpoint still needs those numerical calculus definitions. The aim is eliminating unnecessary DECODING facts from its proof dependencies, not eliminating all numerical syntax or equality interpretation.
- The all-natural upper adapter stays in KSeed222/KUpper222 with sat_dec_agree, decoded normalization and its a=b branch. Sharing a valuation-predicate kernel is optional and not yet implemented.

The draft's narrower import avoids pulling the machine/upper-bound umbrella into the new demonstration, but its existing lower imports still compile the older proofs. A theorem-term dependency proposal is not an accomplished build-dependency reduction.

## Evidence and guards

SOURCE_PINS.json records 17 downloaded source/previous-proposal files. Every saved file's Git blob hash was independently recomputed and matches the connector-reported blob. All were read as data.

The owned check_fresh_padding.py was run with Python -I -B. It checked:

- 108 small formulas against the occurrence bound;
- 6,912 padding semantic instances;
- 6,912 ordinary named-bundle/Seed equivalences over all 16 two-element membership relations, including reflexive models;
- 4,096 raw-code implication semantic instances.

Negative controls establish that literal decoding at wim(0,0) is not homomorphic, encoded bottom is not syntactically bottom and is not semantically false in a reflexive singleton, and a=b can invalidate the proposed named iff even in an irreflexive four-element model. The ordinary-role guard is real, not bureaucracy.

Finite tests are independent sanity checks, not proofs over all formulas or models. The Lean proposal has not been elaborated, its printed axiom dependencies have not been obtained, and its compilation cost is unknown. No incoming script or compiler command was run. Verification of a future integration must compile the exact changed modules and print endpoint axioms, then run the repository's aggregate calibration checks.

## Main pinned sources

- Code254GIC.lean lines97–145: existing positivity, occurrence and freshness facts.
- TarskiCalculus.lean lines31–37,51–70,81–116: named syntax, free/bound labels, update, satisfaction and sat_ext.
- KSeedModel222.lean lines163–270: duplicated positivity, round trips, named bundles, derivability and double-negation seed adapter.
- KEind222.lean line305 onward: generic c222_complete and its explicit valuation.
- KIndisc222.lean: fullSeed_quotient and its equality-free premise.
- KLowerSeed.lean lines26–29: existing seedProp_congr.
- KCode222.lean line92 onward: all-natural soundness that this proposal does not weaken.

All exact GitHub permalinks are recorded in SOURCE_PINS.json.
