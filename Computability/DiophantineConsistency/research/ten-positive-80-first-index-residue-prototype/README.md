# First Pell index residue for an actual graph zero

`Direct80FirstIndexResidue.graph_first_index_residue` proves in every IΣ₁ model that a positive zero of the exact Lean 80-row graph has a positive first Pell index `n` with the actual first ordinate equation and `2n ≡ rankNat+1 (mod μ²)`. Its hypotheses explicitly include positive beta, `MC<beta`, `MF<2*beta`, and a model witness that beta is odd. The proof binds the graph's first Pell parameter to an exact multiple of μ², invokes the existing all-internal-index Pell residue theorem, and combines it with the independently checked signed-offset congruence.

Guarded author `observations/attempt01/` passed without diagnostics, producing `/tmp/tenpositive-80first-index-residue-9oqw6nxx/Direct80FirstIndexResidue.olean`, SHA-256 `d1ecdf1384540f5da5c9fd2d459bbb25f65db3d9c559bab5c6b1bfe90cabad09`. Printed axioms are `propext`, `Classical.choice`, `Quot.sound`. Selected prototype objects and one inherited provider are pinned; complete transitive project/package/dynamic and historical source-object ancestry remain inherited. Resource checks are sampled; no paired replay is claimed.

This is congruence, not yet the equality `2n=rankNat+1`. Bounds excluding other residue representatives, fixed-recipe port integration, graph-to-halt and the iPRA endpoint remain separate.
