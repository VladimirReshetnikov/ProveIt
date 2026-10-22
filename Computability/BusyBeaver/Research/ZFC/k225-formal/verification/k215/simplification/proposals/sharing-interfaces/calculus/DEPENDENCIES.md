# Exact dependency splice

Current KEndpoint imports KLowerQHyp (plus unchanged upper/runtime modules). The lower chain reaches KLowerSeed, whose first import is KIndisc222. KLowerSeed uses that module only for the FullSeed interface; its `formSeed_of_fullSeed` is polymorphic in the domain and membership relation. It does not use Ind, IndQ, mk, qmem or sat_mk. Current KEndpoint is the consumer that selects the quotient model and its witness.

Minimal migration, preserving the FullSeed namespace:

1. Add `seed_direct` to KSeedModel222. Its output is the same as seed_eqFree but WITHOUT an EqFree input. Use the interpreted private label and new named semantic normalization.
2. Replace KIndisc222's implementation with its existing imports/namespace, the unchanged FullSeed structure, and a wrapper:

       theorem fullSeed_direct_of_derivable (mem : V → V → Prop)
           (hirr : ∀ x, ¬ mem x x)
           (hT : ∀ f, DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f) :
           FullSeed mem :=
         ⟨hirr, fun ψ e => seed_direct mem hirr hT ψ e⟩

   Retain old quotient results in a separate optional module if public compatibility matters; do not import it on the lower endpoint path. `hirr` in the direct seed theorem itself can be omitted if its implementation uses only named semantics. It is retained in the FullSeed wrapper because FullSeed includes irrefl.
3. KLowerSeed needs NO change if FullSeed stays in its old namespace and module. `formSeed_of_fullSeed` remains exactly the same. Its conversion `Code254GIC.sat_toNamed` still uses h.irr and is not being weakened.
4. KEndpoint changes only the full-seed constructor and witness, as in DIRECT_FULL_SEED.md. No change to KLowerQHyp, KQ1Model, KQ1ZF, or upper/runtime/source theorems is needed.

Source mass: current KIndisc222 is 151 lines, of which the definition/namespace/import scaffolding can be retained in roughly 25 lines. This is NOT a net 126-line improvement because new direct support/semantics proofs must be added to KSeedModel222. No measured net source count or compilation speedup is claimed.

Avoid a misleading trust argument: dropping the first quotient removes one use of Quotient and representative choice on this path, but downstream tagged/bisimulation quotients and standard completeness still use classical/model infrastructure. It does not remove those axioms from the final theorem.
