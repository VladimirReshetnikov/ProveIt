# Intuitionistic PRA: actual equality axiom images

The current target uses `IPRANativeTheory.nativeTheory`, whose equality axioms
are reflexivity and intuitionistic finite-parameter Leibniz substitution. We
are proving the Gödel–Gentzen images of Foundation's actual five equality
axiom families in this theory, without adding equality axioms or assuming an
object-theory equality decision procedure.

Reflexivity and symmetry have guarded independent replays. Transitivity and
binary relation congruence have independently replayed source packets from the
parallel proof. The remaining arbitrary-arity function congruence is now
proved in Lean in the focused author and independent replays described below;
all eight source, object and log hashes match. Equality-family assembly and its import
closure must still be replayed coherently before claiming the whole transfer.

For a function symbol `f` of arity `k`, `IPRAFunctionCongruenceOpen` constructs
an actual Leibniz instance for each coordinate. From `vᵢ = wᵢ`, that instance
and reflexivity derive equality of function values after replacing just the
`i`th argument. A finite metatheoretic iteration combines these steps using
native equality transitivity; this iteration does not assume an induction
axiom in the object theory. A proof of each coordinate equality is extracted
from Foundation's `Matrix.conj`, including the empty conjunction when `k=0`.
The context consists only of closed native equality axiom instances, so it is
shift-invariant and can be universally generalized.

`IPRAFunctionCongruenceClosed` proves that this generalized open formula binds
to precisely Foundation's `Fin.addCast` / `Fin.addNat` variable layout and
that the corresponding direct intuitionistic congruence is proved in the native
theory. `IPRAFunctionCongruenceGG` applies the independently developed finite
conjunction adapter and proves the exact statement

```
∀ {k} (f : language.Func k),
  nativeTheory ⊢ (Theory.Eq.funcExt f)ᴺ
```

The author replay packet is `reviews/ipra-function-congruence-gg-replay/`.
It preserves an initial failed split-module replay, in which a local Lean
`language.DecidableEq` instance had been omitted; that metatheoretic instance
is not a proof that equality is decidable in native iPRA. The corrected author
replay passed with only the standard Lean metatheory axioms. The provider's
historical parent-object ancestry and five unrelated excluded broad source
guards remain explicit in that packet. A source-only post-merge import audit
is recorded in `reviews/ipra-post-merge-source-import-audit/`; it is not an
object rebuild or a clean transitive provenance audit.

These equality transfers do not establish the user-facing equation result.
The exact classical equation comparison, its source-current object provenance,
and especially the interpretation of the negated translated ZFC refutation
predicate as ordinary intuitionistic consistency remain separate obligations.
