# Independent review of the direct-Q auxiliary exclusion

**PASS, with no requested correction.** I read the complete frozen [direct-Q proof](complete84_auxiliary_direct_q_exclusion.md), including all placements in its three-addition separation lemma, and independently challenged the specialization and original-circuit chronology. The final change after my draft review only removes the draft notice.

The reviewed author note has SHA-256 `a6c33af0b79935a8eae47892be1ce9d237230d562afe24c7876527a04f72ec2e`.

## Exact conclusion and interface

The theorem concerns simultaneous computation of

    V=cTf−c−Rf²,
    Q=Delta²*i²*c⁴,
    S=Delta*f²−Q

from six independent polynomial variables Delta,c,i,f,T,R, with precisely c² and Delta*c² additionally paid. Constants and scalar aliases are free in the stated lower-bound relaxation; arbitrary linear combinations are free only during the specified multiplication-only contradictions. The proof excludes the last inherited5M+4A case. Together with the pinned frontier and the exhibited7M+3A construction, it establishes an exact local cost of ten.

This does not prove optimality of the complete84 polynomial. Different paid ports, compiler relations, altered output cuts, zero-set substitutions and positive coordinate charts are outside the claim. No new complete source array or numerical compiler witness is certified here.

## Independent mathematical checks

1. **Structural lemma with arbitrary paid monomials.** Between additions, multiplicative ancestry gives a monomial times powers of previous addition outputs. I checked the primitive irreducibility arguments for V and P=f²−Delta*i²*c⁴ and the two-addition support argument for V. A binomial power plus one monomial cannot yield V's three noncollinear terms unless the power is one. Its two grouping additions are therefore independent of both Delta and i. These statements survive arbitrary additional monomial inputs.

   I checked all three chronological placements of V and the P/Delta*P core in a three-addition circuit. In the quotient by P with c,i inverted, monomial inputs become Laurent monomials, whereas V retains its three noncollinear terms. Zero or collapsed binomial images only strengthen the support obstruction. In the remaining case h=m*g^r+n, distinct T/R multidegrees cannot all be removed by one monomial; equal positive multidegrees are equally impossible. This proves the claimed separation without any bound on multiplication count.

2. **Removal of the temporary relaxation.** Deleting U=Q and supplying its value as a monomial preserves the other gates' polynomial values. The separation lemma classifies those same three addition values. The proof then restores the original paid interface before every product-count argument. In particular, it does not import the original V,W multiplication lower bound into the enlarged free-Q model.

3. **Specialization and chronology.** At i=0, a later zero product and the latest nonzero coefficient in the earlier Q relation give two different product deletions. For an earlier zero product g with Q outside the paid span plus g, deleting g first leaves a relation with a nonzero coefficient on another product; eliminating the latest such product respects chronology regardless of its former order relative to g. The only remaining possibility is g=alpha*Q+beta*i, since the intersection of the original paid scalar span with the ideal (i) is exactly the scalar span of i. A proportional Q alias would remove U's addition and falls under the inherited three-addition exclusion.

4. **Nonmonomial vanishing products.** When alpha and beta are nonzero, the factor h=beta+alpha*Delta²*c⁴*i is primitive and linear in i, hence irreducible. Every irreducible factor in a multiplication output must originate in an input or an ancestor addition value. Monomial inputs and U cannot supply h; i-free additions cannot supply it by i-degree; h divides neither Delta nor P, the latter being monic in f with h independent of f. Thus the proof correctly strengthens the monomial exclusion to every nonzero product vanishing at i=0.

5. **First quadratic i-degree.** In the restored original circuit, each classified addition is i-free or has i-degree two. Before the first degree-at-least-two gate, all additions are therefore i-free. The first earlier i-dependent product, if any, would use a scalar alias of input i and vanish at i=0. Once this is excluded, the first degree-at-least-two product has the same defect. This argument uses actual counted gates and scalar aliases, not uncharged arbitrary linear combinations.

I also counted the displayed attainment schedule directly: seven multiplications and three additions, with Delta*c² already paid.

## Authenticated inherited dependencies and evidence limits

The four dependency hashes in the author note match the installed inert proof bytes:

| Dependency | SHA-256 |
|---|---|
| [Mixed auxiliary cut](complete84_auxiliary_mixed_cut.md) | `b16bcf8b4013345d25a5d2bbb0598ae2caaaeaa31a529e00af7ea4647d78d7f2` |
| [Nine-gate frontier](complete84_auxiliary_nine_gate_frontier.md) | `ae4925e8bf330fcd1a5d1c0f529e982f0c5df018690a7ef81e4ca27cc5ad4cd2` |
| [Proper-pivot exclusion](complete84_auxiliary_proper_pivot_exclusion.md) | `027c1945025f4bf1e6b9d585ba2befe1af697239787928226b0fd10f868fdf20` |
| [No i-containing monomial products](complete84_auxiliary_no_i_monomial_products.md) | `4d98a15d3eb9ec8beb989149d0b93d5f44fd3094fe31994b8c850891ff0dae59` |

The inherited frontier and original-interface V,W four-product bound remain explicit dependencies, rather than new claims independently reconstructed by this review. My prior reviews separately challenged the proper-pivot and no-i specialization steps. This review covers the entire new symbolic argument and its use of those dependencies. No predecessor program was executed or imported, no numerical search was substituted for proof, and no repository file was edited.
