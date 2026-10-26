# Current constructed rank: independent Lean review

Verdict: PASS. The packet binds the actual once-shifted rank to an ordinary
natural four-block integer and obtains its exact population from the SAME
constructed packing. It does not assume a source-system zero, a Pell witness,
or the desired rank population.

## Frozen sources and review scope

The reviewer read the entire 138-line main and 49-line checks before replay,
the complete directly imported rank-variation module, the exact integer
`NativeSourceMask.packing_four_block` identity and surrounding interface, and
the scalar positivity/balance fields used by the final endpoint. The two
other direct imports were already independently reviewed in full by this
reviewer, including their fresh replays. No source finding was raised.

Paths are relative to `Computability/DiophantineConsistency/`.

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/CurrentPackingRank2011.lean` | `614f47e52f31dfc199f98387e5c720f1ae51fb0725ce8d9f21223b540a30c546` |
| `Lean/DiophantineConsistency/CurrentPackingRank2011Checks.lean` | `ba9e6e57d6a608b25064c1adea6dda5dc7d30bc5c958f8b363688d32348e7e42` |
| Import `CurrentNativePacking2011` | `df17b8a5c2913b2ffec6d4b6fbd3fe5127aa45e76273ed88734f30da548fa92e` |
| Import `NativePackingPopulation` | `bc4526d0e9f267df6d027b6f7ec38e5374ecc4f1627d556f4cffd41b0f1cd3ac` |
| Import `NativeRankVariation` | `46c226eba0018eb15eaec66bb31b2ea8af7682fbef76d0245ee45c6aa236ef73` |
| Reused `NativeSourceMask` | `c92d1ee93dff4e8655005bf73d2cedb6ae95a55819c0a14de76202cd0b2a913e` |

The root agent authored this new packet. The reviewer authored
`NativeRankVariation` and earlier copy/padding/source-construction components;
those roles are disclosed rather than presented as independent review of
those prerequisite results. The two preceding peer receipts are
`current-native-packing2011-lean-peer.md` and
`native-packing-population-lean-peer.md`.

## Exact mathematical binding

`q_binary` retains the complete exponent `width*N`, with width 94517. The
`rank` definition uses `windowRank q C F lowPort (highPort+beta) J`:
the source fourth-port beta shift occurs exactly once. The mask used in the
population calculation remains the unshifted `highPort*J-1`.

Both repeated masks are proved strict representatives below q using their
actual finite port inequalities and `beta*J+1=q`. The actual low-even and
high-mod8=4 facts, plus the full finite combined population, supply the
repeated mask population `width*N+2`, including both origin adjustments.

Before casting the four-block natural integer, `fourBlocks_cast` proves the
domains of every subtraction: C is positive, C+F<q, the positive high mask
times the positive repunit is at least one, and the complement bounds follow.
It then invokes the ordinary ring identity with the actual beta-J relation.
Thus neither natural truncation nor a second high-mask shift is hidden.

The generic population lemma applies with A=C-1. The exact identity
`q-1-(C-1)=q-C` is established under C>0 and C+F<q. Both overlap-free masks
are actual inputs in `fourBlocks_population`, and they are taken from the
same `hf` in `packing_rank_population`. Source positivity and the balance
C+F+alpha=q with positive alpha similarly come from that same packing. The
returned R is explicitly the four-block integer, not an unrelated existential
population witness.

The lower bound uses the positive upper complement q-F-1, giving rank at
least q cubed. With N nonzero and the actual positive width, q cubed exceeds
twice `width*N`. This proof uses neither masks nor population nor Pell data.
The intermediate natural lower-bound lemma also permits N=0, where its
C>0 and C+F<q premises cannot simultaneously hold; the principal rank
endpoints correctly require nonzero N.

The focused N=1 examples bind signed/natural rank and population for C=1,F=0;
they explicitly do not claim positive F or an actual one-cell marked tiling.
The final constructed-word check keeps the actual source, marker orientation,
normalized F, and one packing instance coherent.

This packet does not yet prove rank congruences, rank-forced temporal
exponentiation, a fresh Pell seed, a full31-coordinate source, or the
polynomial converse.

## Independent fresh replay

Both frozen files were compiled sequentially with `lake env` and direct
`lean -M6000 -j1`; both set `Elab.async false`. A fresh overlay excluded the
two existing target objects and inserted freshly compiled replacements ahead
of reused prerequisites. Checks therefore consumed the fresh main object.
No existing object or source was overwritten.

Full commands, source preservation, and log/object identities are recorded in
`/tmp/current-packing-rank-peer-7owjyy6y/REPLAY.json`, SHA-256
`6ce8a061d8d57c3302097ab5eaa3734b95222955e4cb29cc6b9ef90c69fb0d02`.

| Build | Result | Time | Peak RSS (KiB) | Fresh object SHA-256 |
| --- | --- | ---: | ---: | --- |
| Main | PASS, no diagnostics | 4.53 s | 3,372,384 | `766f3dfdada26eee44676ea53c83539b67c569efe3643b4064cb9ed9d194f34f` |
| Checks | PASS, no warnings | 2.85 s | 3,331,288 | `677aeace22ad3f2802d9bfb42ffd5024316132516bf8057410cc29e82de8ed54` |

Both fresh objects are byte-identical to the frozen author objects. Both
sources remained unchanged. All eight axiom audits contain only standard
axioms (`propext`, `Classical.choice`, `Quot.sound`); `q_binary` uses only
`propext`. No `sorry`, new axiom, or `native_decide` occurs.

Main log SHA-256:
`e3c00bc6655773a7184a6ea15d0334124443d33e95db2c3d11e9d8a40d1dd054`.
Checks log SHA-256:
`43ddc58a9852019aa0d520285012032cefe19cd92e56d6fcb611d38641e74550`.
Existing prerequisites were reused, not freshly rebuilt by this review.
No frozen source, maintained equation, shared object, or git state was edited.
