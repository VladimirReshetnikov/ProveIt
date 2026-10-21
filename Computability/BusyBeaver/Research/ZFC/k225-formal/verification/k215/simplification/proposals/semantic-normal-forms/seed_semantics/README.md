# Shared semantic normal forms for the K215 seed proof

**Status: kernel checked, Lean 4.32.0.** This packet refactors the seed-bundle part
of the existing K215 correctness proof. It does not construct a smaller machine.
The exact dependency snapshot is ProveIt commit
`b07002a86bcc96e76a31b57dce23d3b8c2b76fa6` (21 October 2026).

## What changed

The old forward theorem `KSeed222.bundle_of_seed` and reverse theorem
`KSeed222.seed_of_bundle` separately decoded the same nested quantified bundle.
The new `KSeed222.BundleSemantics.bundle_iff_seed` proves the equivalence once,
for distinct input and output names. Its proof works through semantic normal
forms for the request (`req_iff`) and closure (`clos_iff`), reusing the existing
fact that the matrix's own code is not a free label (`sat_dec_agree`).

The full forward API permits equal input/output names. That case is retained
and proved separately by `diagonal_bundle_of_seed`; the equivalence theorem
is deliberately not applied there. The existing public theorem signatures,
formula codes, derivability relation, and binary machine are unchanged.

The generic `seedProp_congr` additionally replaces the repeated witness-by-
witness transport at the end of `seed_eqFree` by one line. The patch leaves
the existing syntactic encoding and round-trip lemmas intact, so it is independent
of the earlier proposal to remove those inductions through semantic round trips.

| File | Old lines | New lines | Old bytes | New bytes |
|---|---:|---:|---:|---:|
| KSeed222.lean | 214 | 195 | 7,836 | 8,645 |
| KSeedModel222.lean | 269 | 168 | 11,711 | 7,114 |
| Total | 483 | 363 | 19,547 | 15,759 |

This removes 120 physical source lines (24.8%) and 3,788 bytes (19.4%). The
first file gains explicit reusable theorem statements even as its line count
falls; the principal reduction is in the reverse-direction proof. These are
source-size measurements, not claims about the full endpoint's compilation cost.

## Mathematical content

For a relation Q, write

    Request(Q,A,C) := forall y, Q(A,y) -> exists z, Q(A,z) and z in C,
    Closure(Q,C) := forall y in C, exists x, Q(x,y) and
      forall x' subset y, Request(Q,x',C).

The repository's `SeedProp mem Q A` is
`exists C, Request(Q,A,C) and Closure(Q,C)`.

Let `Q(x,y)` be the truth of `dec c` in the environment obtained from `e` by
assigning x to a and y to b. When a, b and c are pairwise distinct, the new
kernel-checked theorem states

    Sat mem e (dec (bundle222 a b c)) <-> SeedProp mem Q (e a).

It requires irreflexive membership, as the inherited arithmetic code represents
falsity by self-membership. The proof has four steps:

1. The vacuity factor is true because the private label c differs from a and b.
2. Classical normalization turns the negated universal core into an existential
   container, with the closure and request as its two conjuncts.
3. Valuation updates commute at distinct labels, repeated updates absorb, and
   an update to c is invisible to `dec c`. These small algebraic lemmas remove
   the private-container assignment from every matrix occurrence.
4. `req_iff` and `clos_iff` identify the resulting formulas with Request and
   Closure. Exchanging the conjunction's order finishes the proof.

The coincident-role case needs its own argument: assigning the same label to
input and output changes the nested binder's reading. The forward theorem's
separate proof is included and checked. No additional nonemptiness assumption
is introduced; every theorem has the same valuation/domain treatment as its
upstream counterpart.

## Reproduction and evidence

Run, with an installed Lean 4.32.0:

```sh
python3 replay.py --lean /absolute/path/to/lean
```

This verifies the source manifest, freshly compiles the entire 26-source local
closure, and compiles `AuditSeedSemantics.lean`. The typed client checks the
original forward theorem, reverse theorem, and `seed_eqFree` interfaces. Its
four axiom reports are exactly `propext`, `Classical.choice`, and `Quot.sound`;
there is no `sorryAx` or new axiom. The recorded clean replay compiled 27 modules
and succeeded. Raw logs and source/object/log hashes are in `evidence/`.

The existing unused-section-variable warning on `KSeed222.matrix_iff` remains;
its `hirr` parameter was retained to preserve that helper's public interface.
The typed API audit has zero warnings.

`seed-semantics.patch` changes only the two named upstream sources. Apply it
at the repository root after checking that their baseline hashes match
`size-comparison.json`. `baseline/` contains the two exact originals; `lean/`
contains the complete modified dependency closure and audit client.

This is a checked local replacement, not a fresh build of all 184 modules in
the full K215 endpoint closure. Integration should rebuild downstream modules
and repeat the endpoint axiom audit. The original K215 correctness theorem is
not being reclassified here, and no internal PA or ZFC-syntax derivation is
claimed.
