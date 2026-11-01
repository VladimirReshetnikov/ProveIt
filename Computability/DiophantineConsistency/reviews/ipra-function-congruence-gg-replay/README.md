# Native iPRA proves actual function-congruence GG images

`IPRAFunctionCongruenceGG.funcExt_image` proves in native iPRA the GG image
of Foundation's actual `Theory.Eq.funcExt f`, uniformly for every arity and
every PR function symbol. The proof uses the previously checked arbitrary
finite-coordinate native Leibniz proof, binds exactly Foundation's variable
layout, and applies the independently developed finite-conjunction GG adapter.
No equality decidability, object-theory induction, or additional equality
axioms are assumed.

This focused suffix rebuilds the adapter on the independently replayed open
function provider. Five unrelated post-merge broad workspace guards remain
excluded and recorded in the manifest; parent-object ancestry is historical
and external transitive ancestry inherited. This is not a fully isolated
post-merge rebuild. The exact no-zero/ZFC comparison and its intuitionistic
consistency bridge are still separate obligations. Run
`python3 Computability/DiophantineConsistency/reviews/ipra-function-congruence-gg-replay/replay.py`.

The first author replay built the first six modules and failed at the GG
client because splitting the scratch proof into modules omitted a local Lean
`language.DecidableEq` instance required for theory modus ponens. The exact
failed source, manifest, logs and state are preserved under `failed-author/`;
the successor restores that metatheoretic instance. It does not assume an
object-theory equality decision theorem.

Successor author PASS; all five closed/image axiom reports were separately
parsed and contain only the standard Lean trio.

Independent peer PASS; all eight source/object/full-log rows match the
successor author, and all five closed/image axiom reports parse as the
standard Lean trio. The original failed author and historical parent/source
guard qualifications remain as documented.
