# Direct full seed: remove the first quotient, not the second

Status: mathematically audited proposal, not a compiled Lean patch. Current pin: `6f0d42d368506bc29c70ace1c992ed88b2651346`. The current `KSeedModel222` already adopts the previous 35-line cleanup and the shared bundle semantics. `KIndisc222` is still 151 physical lines and still used by `KEndpoint.c222_of_zf_refutation`. This proposal is additional to that adoption.

## The decisive interface

`KEind222.c222_complete T hT hnone` accepts an arbitrary named-formula theory T. Its syntactic premise is `∀ f, T f → C222 (enc (th f))`, but its semantic premise supplies `∀ f, T f → ∀ e, Sat mem e f`, with **literal equality** in f. It does NOT supply only satisfaction of th f. Its proof invokes ordinary Tarski completeness, then `thm_th`, then `c222_of_thmK`. Its imports are KThmK and KEqCodes222. It does not use KSeed222, KSeedModel222 or KIndisc222. Therefore using this interface to construct a direct full seed has no circular dependency.

## Construction and proof

For every named formula ψ, including formulas with equality, put

    pψ := negNF (negNF ψ)
    cψ := enc (KEind222.th pψ)
    Bψ := bundleNF 0 1 cψ pψ.

The elementary facts needed are:

1. `Free i f → i < enc f`. Prove by induction on f. Relation and equality atoms use the two pairing projections. Implication uses the relevant subformula bound and pairing projection. Universal quantification uses the body bound. Falsity has no free names.
2. `Free i f → Free i (th f)`. Prove by induction. Only equality is substantive: i is one of its two argument names, both survive in the membership-indiscernibility formula because `aux x y = x+y+1` differs from x and y. The all case preserves the same outer binder. This is preservation of FREE support, not a claim about arbitrary syntactic occurrences.
3. `1 < cψ`, from the outer double negation and `le_P_right _ F`, exactly as the already-adopted code padding argument. This requires no positivity induction on ψ.
4. `¬ Free cψ pψ`: otherwise (2) and (1) give `cψ < enc (th pψ) = cψ`. Consequently cψ is also not free in ψ.
5. `th (bundleNF a b k m) = bundleNF a b k (th m)`. Unfold the named macros; all the atoms introduced by the bundle are membership atoms, not equality atoms. No freshness hypothesis is needed for this syntactic identity.
6. Thus `enc (th Bψ) = bundle222 0 1 cψ`, using the existing enc_bundleNF after (5). By (3) this is an enabled C222.bundle instance. In particular Bψ belongs to the existing DerivableNF theory even when ψ contains equality.

For named bundles prove the semantic theorem

    named_bundle_iff_seed (mem) (e) (a b k) (m : NF)
      (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b)
      (hfresh : ¬ Free k m) :
      Sat mem e (bundleNF a b k m) ↔
      SeedProp mem (fun x y => Sat mem (update (update e a x) b y) m) (e a).

This is the named analogue of current BundleSemantics.bundle_iff_seed. Proof: normalize reqNF into the request clause; normalize closNF into the closure clause; the vrel implication is true because k differs from a,b; classical not-forall normalization supplies a container; commute environment updates and use freshness to remove its assignment to k. The conjunction order is reversed, as in the current final `and_comm`. Crucially the named theorem needs NO irreflexivity hypothesis: named NF.bot is genuine False. The numerical theorem requires irreflexivity because decoded code F is a diagonal membership atom. Do not weaken the numerical theorem or change the degenerate-role branch.

Given hT for DerivableNF, apply hT to Bψ and (6). Apply named_bundle_iff_seed with (3),(4). Remove the harmless double negation pointwise with the already-adopted seedProp_congr. The result is SeedProp for ψ itself, including literal equality, on the ORIGINAL domain V. Combine with the supplied hirr to obtain `FullSeed mem`, not `FullSeed (qmem mem)`.

## Exact endpoint change

Introduce `fullSeed_direct_of_derivable` with the same inputs as current `fullSeed_of_derivable`, but conclusion `FullSeed mem`. Then replace the two endpoint lines by

    have hfull := fullSeed_direct_of_derivable mem hirr hT
    exact zf_consistent_of_formSeed (formSeed_of_fullSeed hfull)
      hfull.irr (e 0) hf

The final nonempty witness is e 0, so no inhabited-domain premise is lost. The endpoint theorem's statement, numerical calculus, source program, machine, and axioms are unchanged. Ordinary Tarski completeness remains. The tagged domain, its bisimulation quotient, well-founded part, and ZF model construction remain unchanged.

For dependency pruning, move the eight-line FullSeed declaration to a small shared module or retain it in a reduced KIndisc222 module. After switching the endpoint, the first quotient definitions Ind/IndQ/qmem, sat_Eind, sat_mk, representative choices, and fullSeed_quotient are not required on that endpoint's proof path. They can remain in an optional comparison module if their public API is wanted. The old equality-free-only seed bridge and th_eqFree are likewise unnecessary for the new endpoint. Do not report all these lines as net savings: the direct freshness and named semantics proofs must first be added and compiled.

## Existing Rocq evidence

This is a cross-assistant alignment, not a new foundation. Existing `k225-formal/rocq224/src/Complete222.v` already implements the analogous route:

* tau_fr and th_fr, lines98–123;
* seed_matrix, seed_code, seed_code_gt3, seed_code_fresh, lines125–139;
* tau_th_SeedN and Q_seed, lines144–158.

The pinned file is included as `upstream/Complete222.v`; its verified Git blob hash and exact GitHub URL are in MANIFEST.json. Its private label is `tau (th (Wn (Wn (tr source_names phi))))`. Its frozen roles are 1 and 3, unlike Lean's 0 and 1. Hence the Rocq bound is >3; Lean only needs >1. The lower syntactic Rocq bridge already avoids this preliminary semantic quotient, so do not claim an equal Rocq deletion. The value is matching Lean's proof architecture to the already-existing shorter Rocq route, leaving fewer different mathematical arguments to maintain across both assistants.

## Remaining acceptance tests

1. Compile the two support lemmas, th_bundleNF, and named_bundle_iff_seed in current Lean. Prefer generalizing the shared semantic normalization over an arbitrary matrix/freshness interface to duplicating its proof, but first validate the direct lemma.
2. Compile fullSeed_direct_of_derivable and the unchanged endpoint statement with the new witness e 0.
3. Print endpoint axioms; compare with current trust boundary. No sorry, new axiom, unchecked native reduction, or changed consistency statement is allowed.
4. Check the actual import graph after moving FullSeed. Only then remove obsolete endpoint dependencies and measure net source lines and build times.
5. Preserve the existing numerical bundle theorem for malformed codes and coincident roles, which is still needed by the upper chain. This direct lower bridge does not license deleting those cases.

No Lean or Rocq executable was found on PATH in this workspace, so no compilation or timing claim is made.
