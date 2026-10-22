# Named-bundle semantic derivation

All satisfaction expressions in this argument concern the ORIGINAL named matrix m. There is no use, or assertion, of `Sat (th m) ↔ Sat m`.

Fix a structure `(V, mem)`, valuation E, distinct input/output names a,b, and a private name k different from both. Let m be an arbitrary named formula with `¬ Free k m`; m may contain literal equality. Define

    R_E(x,y) := Sat mem (update (update E a x) b y) m.

The only matrix-specific semantic fact used is

    Sat mem (update E k C) m ↔ Sat mem E m.                 (Fresh)

It follows from the existing Tarski.sat_ext: a free name n cannot equal k, so the two valuations agree at n. Applying Fresh after commuting k-updates past a,b-updates gives

    R_(E[k:=C])(x,y) ↔ R_E(x,y).                           (Marker)

No assumption that mem is irreflexive, extensional, or respects a quotient is needed for either fact.

## Request

Unfold reqNF. Classical `¬∀z (P z → ¬Q z) ↔ ∃z, P z ∧ Q z`, idempotence of b-updates, and k≠b yield

    Sat E (reqNF b k m)
      ↔ ∀ y, Sat (E[b:=y]) m → ∃ z, Sat (E[b:=z]) m ∧ mem z (E k).

This computation does not need Fresh: it does not assign k.

## Closure

Unfold closNF. For every y with mem y (E k), its outer negative universal selects an x satisfying m, and its inner universal ranges over x' whose members are members of y. Normalize reqNF under that updated environment and use idempotence/commutation of a,b updates. Since a≠b and k differs from each, the result is

    Sat E (closNF a b k m)
      ↔ ∀ y, mem y (E k) → ∃ x, R_E(x,y) ∧
           ∀ x', (∀ w, mem w x' → mem w y) →
             ∀ y', R_E(x',y') → ∃ z, R_E(x',z) ∧ mem z (E k).

The all-k binder inside the subset test binds only the two membership atoms in that test. It does not bind m in the adjacent reqNF. This lexical scope distinction is important; nothing relies on pulling m through that binder.

## Outer bundle

The gate named formula `(rel a b → all k (rel a b))` is true because k differs from a,b. Consequently the bundle's outer negation and the negative container universal reduce to

    Sat E (bundleNF a b k m)
      ↔ ∃ C, Sat (E[k:=C]) (closNF a b k m)
             ∧ Sat (E[k:=C]) (reqNF b k m).

Use the closure and request identities. Marker removes the k assignment from each R; E[k:=C] k = C. The root request is at input E a because assigning a its current value changes nothing, and a≠k ensures that E[k:=C] a = E a. Swap the two conjunction components. This is exactly `SeedProp mem R_E (E a)`.

In the proposed endpoint take m=¬¬ψ and k=enc(th m). Freshness is established syntactically. Derivability is established using th's homomorphism over the bundle and C222.bundle. These are SEPARATE from model satisfaction: c222_complete supplies satisfaction of the ORIGINAL bundle at m, so every semantic calculation above evaluates m, not th m. Finally classical double-negation elimination and seedProp_congr replace m by ψ.

The numerical upper-chain theorem is not replaced: code F decodes to `rel 0 0`, so that theorem still requires irreflexivity and still handles coincident a,b via its separate diagonal lemma. Here a=0,b=1 always, and named NF.bot is literal False.
