# A smaller axiom interface for the existing lower bound

This is a dependency/interface simplification, NOT a new seed/ZF consistency proof and NOT a deletion of the upper raw-code soundness obligation.

Define pad ψ = negNF (negNF ψ), and

    SeedTheory f := ∃ ψ, EqFree ψ ∧
      f = bundleNF 0 1 (enc (pad ψ)) (pad ψ).

Unlike DerivableNF, this theory has no reference to a proof predicate and contains only the one family the lower-model construction uses. Its syntactic generation is decidable given the witness ψ, although recognizing membership without a witness is not claimed here.

Required theorem, with the existing exact interpreted-code target:

    seedTheory_derivable:
      SeedTheory f → C222 (enc (KEind222.th f)).

Proof: unpack ψ; EqFree padψ; enc(padψ)>1 by outer pairing right bound; th_eqFree on bundleNF; enc_bundleNF; C222.bundle with the two gate inequalities. No decoder syntactic round trip, no enc_pos, no general formula theoremhood induction.

Required model lemma:

    seed_eqFree_of_seedTheory:
      (∀ f, SeedTheory f → ∀ e, Sat mem e f) →
      ∀ ψ, EqFree ψ → ∀ e,
        SeedProp mem (fun x y => Sat mem (update(update e 0 x)1 y) ψ) (e 0).

Its proof is the existing seed_eqFree proof, selecting its explicit named padded bundle from SeedTheory. The existing semantic roundtrip moves hT to decoded bundle satisfaction. seed_of_bundle and double-negation semantic equivalence finish. The current assumption that ALL derivable interpreted formulas hold is strictly more than this proof uses.

Then the exact old endpoint can be refactored as follows:

    apply KEind222.c222_complete SeedTheory seedTheory_derivable
    intro D mem hirr hT e
    have hfull := KIndisc222.fullSeed_quotient mem hirr
      (seed_eqFree_of_seedTheory mem hirr hT)
    exact zf_consistent_of_formSeed
      (formSeed_of_fullSeed hfull) hfull.irr
      (KIndisc222.mk mem (e 0)) hf

The nonempty valuation e is retained. No extraction of a model from an empty domain is used. Equality interpretation and quotient are still needed because the seed theory supplies equality-free matrices while the ZF construction uses all named formulas. Raw upper soundness must still validate EVERY actual raw bundle, including degenerate a=b; narrowing the lower theory does not authorize narrowing the machine generator.

Compatibility: the original seed_eqFree can remain as a wrapper, deriving its new hT from seedTheory_derivable and the old DerivableNF assumption. The endpoint can instead use the new smaller theory directly. This is not automatically fewer source lines, but it removes proof-predicate circularity from the model assumption and precisely isolates the machine-independent lower-bound schema.

Uncompiled proposal; ordinary preservation follows by replacing only the theory parameter supplied to the already generic c222_complete theorem and proving both of its existing premises. No new trusted axiom.
