# Source-only retained compact44 kernel plan

This is a proposed definition and proof sequence, not a Lean build or a proof that the retained raw payload is the selected expression coefficient. The symbolic graph sources still quantify over arbitrary `K`. The fixed 2011 coefficient tuple and the alternate BFS-renamed compact tuple are different instances.

## Exact recipe and reusable definitions

The original `candidates/free-j-polarized-positive/source/positive/coefficients/recipe/build_coefficients.py` defines `ρ = 2^67`, `B = ρ^8807`, `beta = B - 1`, `DR = ρ^42`, and `K = DC + B*DR`. Its `DC` dictionary starts with coefficient 1 at exponents 30, 62, 1100, 2201; for every source entry `(e,c)`, it adds `c` at exponents `4393-e` and `5495-e`. Source entries include 943 selectors, 41 copies and the two *zero*-coefficient dummy entries 1063 and 1064. All source indices are below 4393. This is an addition of contributions, including any collision, rather than an unproved assumption that reflected positions are distinct.

`compact44-943-table-prototype/Compact943Data.lean` defines the pinned ordered `rows` and bounded `row : Fin 943 → ...`. `compact44-coefficient-mass-prototype/CompactCoefficientMass.lean` defines the corresponding small `value` and `selector t = 1 + 2^10*(2^41-value t)` and proves finite value and mass bounds in its paired audited scope. `compact44-next-drafts/CompactCopySlots.lean` gives the following 41 positions indexed by coefficient bit: 

```
[1023,1024,1025,1026,1027,1028,1029,1030,
 1013,1014,1015,1016,1017,1018,1019,1020,1021,
 1003,1004,1005,1006,1007,1008,1009,1010,
 983,984,985,986,987,988,989,990,991,
 1031,1022,1011,992,1095,2195,3296]
```

The copy-slots source is an uncompiled draft for this plan; a future build must establish its coherent provider and replay provenance. The recipe uses weight `2^(10+j)` at position `slots[j]`. It explicitly includes the forbidden selector row 1 in K even though the low-mask support removes index 1. The low-mask and high-mask Lean definitions are `CompactSymbolicPorts.lowNat` and `highNat`, and `ports β K L H = ![β,K,L,β+H]`. `CompactFixedBeta.betaNat = 2^(67*8807)-1`; `β+highNat` already incorporates the shift exactly once.

A read-only external Python comparison of the recipe against the Lean table literal checked all 943 ordered rows, all 943 selector formulas, all 41 copy positions, and the two zero entries. This is small finite evidence, not a Lean proof, nor does it validate the raw payload or all-model machine semantics.

## Concrete next Lean definition and theorem

On a single audited, coherent provider containing the precise `Compact943Data` and `CompactCoefficientMass` sources, define `selectorEntries : List (ℕ × ℕ)` by enumerating all 943 rows as `(i, selector row)`, and define `copyEntries` by enumerating the 41 positions above as `(slots[j], 2^(10+j))`. Let `terms := selectorEntries ++ copyEntries`; the dummy entries can be included as `(1063,0),(1064,0)` or omitted with an explicit zero-term lemma. Define symbolically, without expanding powers:

```
ρ := 2^67
B := ρ^8807
DC := (∑ e in [30,62,1100,2201], ρ^e)
      + (∑ (e,c) in terms, c * (ρ^(4393-e) + ρ^(5495-e)))
kernelNat := DC + B*ρ^42
retainedRecipePorts := ports betaNat kernelNat lowNat highNat
```

First prove the small-data theorem `all_entries_below_first_target`: every index in `terms` is `< 4393` (and the 41 slots are ordered as specified). Use the already checked row length and a bounded per-position argument; avoid expanding `ρ`, `B`, `kernelNat`, or the large masks. The next nontrivial semantic lemma is the natural-cast decomposition: for an arbitrary IΣ₁ model `V`, cast `kernelNat` to `V` and rewrite it as the same externally finite sum of cast small coefficients and symbolic powers of `(2:V)`, with the final term `(B:V)*(ρ:V)^42`. Prove it by cast-of-sums/products/powers and symbolic exponent identities, not `decide`, `norm_num` or simplification of `2^590069`. Any conversion to internal `Exp.exp` must invoke an applicable cast/exponent theorem with its actual hypotheses; prove it separately if needed. This would supply a concrete `K` to the existing arbitrary-K theorem, but its graph-zero hypothesis would refer to this new Lean term.

To establish that this term is the **retained original** K, formalize the 943 selector bit-permutation/occupied-field identity, the 41-position mapping, the two reflection sums with collisions, and the four bare shifts against an exact Lean rendition of the original recipe. Bind the original compressed/raw K payload to that rendition by a checked serialization or explicit chunked certificate and a theorem about the selected literal; digest agreement or an external Python comparison alone is not an internal equality. The current external bindings use the original raw K hash `c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e`; the BFS-renamed K has a different hash and must not be substituted. The retained manuscript's own payload copies are absent, so the existing provenance check uses available reconstructed copies.

Separately prove the low/high mask recipe equalities and tuple-to-expression binding. None follows from defining `kernelNat`. The source-only list-to-model cast also does not supply the weighted-word decomposition, carry inputs, graph-to-checker semantics, machine simulation, construction direction, or a PRA/iPRA endpoint. Any prospective Lean build needs a reviewed exact source closure, same-side parent providers, resource protection and independent artifact audit.
