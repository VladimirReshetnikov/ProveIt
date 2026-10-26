# Direct signed-rank residue from a saturated low-mask prefix

## Recommended status

A checked secondary theorem strengthening. It removes unnecessary hypotheses from the parity argument and supplies a reusable modular fact before natural packing interpretation. It is not accompanied by a claim of net source reduction. The current single client may not amortize the generic helper.

Current review head: `3b51c69d42ff99bc420698532af3fe1d1f9bd356`; initial inspected source: `7ba7d102822df1eff376cbca913727d9d588ab4e`. The latest `NativeRankVariation.lean` and `CurrentPackingParity2011.lean` were fetched and confirmed byte-identical to the initial snapshot. Exact blob/hash evidence is in `evidence/rank/provenance.json`.

## Exact theorem

Let

    W(q,C,F,MC,MF,J) = (q(q-F)-C)(q^2-1) + (MC+q MF)J.

This is the existing `NativeRankVariation.windowRank`, specialized to integers. Take q,C,MC,J,k in the naturals, put m=2^k, and allow F,MF to be arbitrary integers. Assume

1. C>0;
2. m divides q;
3. (C-1) AND (MC*J+1) = 0;
4. (MC*J+1) mod m = m-1.

Then W(q,C,F,MC,MF,J) = -1 in ZMod m. Equivalently, the signed integer rank is congruent to -1 modulo m.

If R is a natural number with (R:Z)=W, then R mod m = m-1. This final adapter uses the supplied equality only; it does not prove the rank nonnegative or assume a natural packing representation.

## Proof

Reduce the binary-AND equality modulo 2^k. The second mask operand has its lowest k bits all set. Existing `Nat.and_mod_two_pow` and `Nat.and_two_pow_sub_one_eq_mod` therefore give (C-1) mod m=0. Because C>0, subtraction of one casts exactly, so C=1 in ZMod m.

The saturated-prefix hypothesis gives MC*J+1=-1 in ZMod m and therefore MC*J=-2. The q-divisibility hypothesis gives q=0. Substituting q=0 in the existing signed polynomial eliminates every F and MF occurrence:

    W(0,C,F,MC,MF,J) = C + MC*J = 1-2 = -1.

No ordering argument, natural subtraction in F, repunit balance, positivity of F/MF, or bound C+F<q enters this derivation. k=0 is included: ZMod 1 is the trivial ring.

The hypothesis C>0 remains mathematically necessary for this formulation. It connects the natural truncated expression C-1 used in the mask to the ordinary subtraction appearing after casting. No change to that domain guard is proposed.

## Concrete current target

`CurrentPackingParity2011.packing_rank` (lines 53-74 at the reviewed head) obtains a natural R and its integer-rank equality from `packing_rank_population`. For its parity subproof, lines 66-70 reconstruct R=fourBlocks through `fourBlocks_cast`, and then invoke `fourBlocks_mod_four`.

Add a small direct `rank_mod_four` wrapper based on `rank_prefix_nat` with

- q = `CurrentWordScalarWitness2011.q N`;
- C = the actual source word;
- F = the actual normalized word, cast to integers;
- MC = `lowPort`;
- MF = `highPort+beta`, cast to integers;
- J = `repunit width N`;
- k = 2.

`q_mod_four` supplies the q divisibility. `lowPort_four` and `repunit_mod_four` give `(MC*J+1)%4=3`. `hf.low_mask` gives the bitwise premise, and `hf.scalars.source_pos` gives C>0. The supplied `(R:Z)=rank ...` equality is precisely the adapter's hR.

The parity argument then bypasses `fourBlocks_cast`, its natural truncation guards, and its beta/repunit binding. The full `packing_rank` theorem still needs range information for its population and size conclusions. This proposal does not claim those separate obligations disappear.

The standalone theorem also supports consumers before a natural R has been selected. That is a stronger modular interface than proving parity only after natural four-block reconstruction.

## Strictly wider domain

The checked example is q=4, C=1, F=100, MC=2, MF=-7, J=1, k=2. All mask/divisibility hypotheses hold. The exact signed rank is -5801 and its residue modulo 4 is -1.

Here C+F<q is false and the signed rank is negative, so the natural packing/cast route is unavailable. The new theorem remains valid. The example demonstrates a real weakening of assumptions, not simply a different tactic proving the same guarded statement.

## Novelty boundary

The existing `fourBlocks_mod_four` already derives `(C-1)%4=0` from the successful saturated low mask. That arithmetic step is explicitly not claimed as new; the pilot duplicates it only to be standalone.

Packet o's excluded reflected parity proposal concerns normalized carry digits, and packet zb gives affine rank forms. Existing scalar modular projection and rank cast bridges are also assumed available. The new contribution is the exact signed-rank invariant over every power-of-two low prefix, with arbitrary signed F/MF and without packing-range/beta-J hypotheses.

The refreshed novelty review covers 43 placed packets and 7 incoming archives at the current head. The four new incoming archives contain rank upper deficits, cubic growth, affine comparisons, and carry parity projections, but no matching signed-rank-prefix theorem was found. This is corpus-relative novelty, not a claim that the elementary algebraic principle is mathematically novel.

## Validation

`lean/RankPrefixPilot.lean` compiled with Lean 4.32.0 and mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`. Its copied integer rank-polynomial body was normalized for whitespace and compared exactly with the current generic source body. It proves the signed theorem, the natural-R adapter, and both numerical stress-example assertions.

Axioms printed for each theorem were `[propext, Classical.choice, Quot.sound]`. There is no `sorry`, additional axiom declaration, `native_decide`, or external oracle. Full project integration is not claimed.

## Adoption criterion

Use this lemma when modular rank facts are needed before natural packing bounds, or when a second prefix modulus justifies a general interface. For the existing modulo-four client alone, compare a local direct proof with the helper-plus-wrapper version before merging. The report should describe this as a dependency and assumption simplification, not as a measured line-count improvement.
