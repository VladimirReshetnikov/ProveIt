# Direct full-seed bridge: a third, longer-term simplification

**Status:** independently reviewed mathematical plan; no new Lean proof or
compilation is supplied here. This is existing repository work in
`proposals/sharing-interfaces/calculus/DIRECT_FULL_SEED.md`, whose own historical
pin differs from the present review pin. The decisive interfaces below were
checked against ProveIt `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

## Recommended interface

The intended new theorem is

```lean
fullSeed_direct_of_derivable
  (mem : V → V → Prop)
  (hirr : ∀ x, ¬ mem x x)
  (hT : ∀ f, DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f) :
  FullSeed mem
```

The maintained theorem has the same premises but concludes
`FullSeed (qmem mem)`. Its route first proves seeds for equality-free
relations and then builds an indiscernibility quotient on which every named
relation, including literal equality, has the seed property. The direct
theorem would give the stronger useful result on the original domain.

The endpoint would retain its source-to-calculus and calculus-to-refutation
statements. Its lower proof would use the direct theorem, then the existing
`formSeed_of_fullSeed`, then `zf_consistent_of_formSeed`, with nonempty witness
`e 0` instead of `KIndisc222.mk mem (e 0)`.

## Why the construction is available without a quotient

The decisive type is `KEind222.c222_complete`. Its syntactic premise says
`∀ f, T f → C222 (enc (th f))`. In contrast, its semantic premise supplies
`∀ f, T f → ∀ e, Sat mem e f`: satisfaction of the original named formula,
with literal equality. It does not merely supply satisfaction of `th f`.
The completeness proof imports `KThmK` and `KEqCodes222`, not the seed-model
or indiscernibility modules, so using it this way is not circular.

For any named formula ψ, with no equality-free restriction, let

\[
p=\neg\neg\psi,\qquad c=\operatorname{enc}(\operatorname{th}(p)),
\qquad B=\operatorname{bundleNF}(0,1,c,p).
\]

The double negation gives `1 < c` using the existing pairing bound. Two
structural support lemmas give freshness: every free name of a formula is
less than its encoding, and every free name survives the equality
interpretation `th`. If `c` were free in `p`, these would give `c < c`.
It is enough to preserve free support; preservation of all syntactic name
occurrences is unnecessary and would be the wrong requirement.

All newly introduced bundle atoms are membership atoms, so the equality
interpretation commutes with the named bundle construction. Therefore
`enc (th B) = bundle222 0 1 c`. Since `c` differs from the fixed roles 0 and
1, the existing numerical bundle rule proves `DerivableNF B`. Applying `hT`
thus gives satisfaction of the *literal named bundle* `B`.

A new general named-bundle semantic lemma converts that satisfaction to
`SeedProp` for the relation defined by `p`, and the existing congruence lemma
removes the double negation pointwise. This gives the seed property for ψ
itself, including its literal equality atoms, on the original domain. The
supplied `hirr` completes `FullSeed mem`.

## Actual remaining proof burden

The mathematical reduction is convincing, but its useful size is unmeasured.
The missing Lean work comprises:

1. Prove the two structural support lemmas, including the equality case of
   free-support preservation through the auxiliary bound label.
2. Prove `th_bundleNF` and derive the code/freshness facts for the padded
   named matrix.
3. Prove `named_bundle_iff_seed` uniformly for an arbitrary named matrix.
   This requires the request and closure normal forms, permutation of
   environment updates, and deletion of the fresh container assignment.
   The named statement needs no irreflexivity premise because named falsity
   is genuine `False`.
4. Compose the direct bridge, retain the same completeness and lower-model
   interfaces, and compile the exact machine endpoint with its existing
   axiom audit.
5. Split the small common `FullSeed` declaration and named bundle definitions
   out of their old heavy modules, or retain reduced compatibility facades,
   before measuring the resulting import closure.

The existing numerical bundle semantics must stay intact. Decoded falsity is
a diagonal membership atom, so that theorem still needs irreflexivity and its
malformed-code and coincident-role cases. A direct lower bridge does not
justify simplifying those upper-chain cases away.

## Plausible dependency reduction, not measured savings

The current endpoint graph has these immediate incoming edges:

- `KLowerSeed` imports `KIndisc222`.
- `KIndisc222` is the only endpoint importer of `KSeedModel222`.
- `KSeedModel222` is the only endpoint importer of `Code254Models` and
  `KEind222`.

An explicit graph experiment cuts imports of the old indiscernibility and
equality-free bridge modules while retaining `KSeed222` and `KEind222`, both
required by the direct route. Exactly the following old modules then leave
the current endpoint graph, including the now-unreachable `Code254Models`:

| Module | Current bytes | Current lines |
|---|---:|---:|
| `KIndisc222` | 7,069 | 151 |
| `KSeedModel222` | 5,148 | 116 |
| `Code254Models` | 3,291 | 72 |
| **Old-source subtotal** | **15,508** | **339** |

This is a conditional list of old dependencies that a redesigned interface
could avoid. It is **not** a source saving, a proposed module-count reduction,
or an implemented patch. Some definitions must move, and all new named
semantics and freshness proofs must be included in any eventual total.

The downstream tagged domain, its bisimulation quotient, the well-founded
part, and the ZF model construction remain. Ordinary Tarski completeness also
remains. In particular, removing this first quotient gives no basis for
claiming that the endpoint no longer depends on `Quot.sound` or
`Classical.choice`.

The repository's existing Rocq `rocq224/src/Complete222.v` already implements
the corresponding syntactic route (`tau_fr`, `th_fr`, `seed_code_fresh`,
`tau_th_SeedN`, and `Q_seed`). Its frozen roles are 1 and 3, so it proves a
bound above 3; the Lean roles are 0 and 1. This direction therefore aligns
the assistants' mathematical architectures rather than promising the same
deletion in both. After the two checked component changes, it is a good next
research target for reducing the number of distinct mathematical arguments
that the project maintains.
