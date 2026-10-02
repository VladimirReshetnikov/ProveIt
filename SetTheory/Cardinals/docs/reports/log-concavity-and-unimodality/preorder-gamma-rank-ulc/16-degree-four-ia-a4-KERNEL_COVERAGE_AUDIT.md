# Degree-four four-attachment kernel and coverage: independent audit

## Verdict and limits

APPROVED: complete structural coverage, all-population component pruning, canonical marked templates, every binomial support coefficient, and both exported Newton-gap arrays.

Independent reconstruction reproduces exactly:

- 355 labeled four-element preorders
- 4,882 legal core/direction specifications
- 2,874 structurally reduced and 2,008 retained specifications
- 76 canonical templates
- 32,516 quota vectors and 162,580 scalar gamma coefficients
- 258,153 nonzero exported Newton-gap terms

The type-count distribution is {1:1, 2:3, 3:7, 4:8, 5:14, 6:8, 7:12, 8:8, 9:8, 11:5, 15:2}.

This is a coverage and exact-algebra audit. It does NOT prove that all these Newton gaps are nonnegative. The four-attachment positivity layer and consequently the full degree-four conjecture remain pending unless separately certified.

## 1. Complete structural domain

The established Gallai--Edmonds normal form at matching rank r=4 with a=4 attachments gives a core of size at most 3r−2a=4. The core already contains the four distinct attachment vertices, so it is exactly A. All exterior vertices are independent singleton classes, with neighbors only in A.

Each attachment has a fixed strict direction toward all its exterior neighbors. Opposite orientations toward two exterior vertices would force a comparison between them. Equivalence between an attachment and an exterior vertex is impossible: equivalent preorder vertices are twins of the comparability graph; their interchange is an automorphism preserving the canonical D set, whereas exterior singleton components belong to D and attachments do not. Isolated exterior vertices never occur in a matching support and can be discarded.

All core preorders on four vertices, all sixteen orientation masks, and all fifteen nonempty neighborhood types are therefore a sufficient domain. This domain may contain extensions whose actual matching rank is smaller than four; including those is harmless.

## 2. Independent exhaustive preorder generation

The producer scans all 2^12 off-diagonal directed relations and checks transitivity. The independent audit uses a different construction:

1. Enumerate every upper-triangular strict relation on m=1,...,4 vertices and retain the transitive ones
2. Canonicalize each quotient poset by every vertex permutation and the complete adjacency matrix
3. Try every positive block-size composition summing to four, represented by separator subsets of three gaps
4. Expand the blocks into preorder equivalence classes and try all 4! relabelings
5. Deduplicate the complete four-row adjacency matrix

Every preorder is a poset of equivalence classes, and every finite poset has a linear extension. The construction is therefore exhaustive. It produces quotient counts 1,2,5,16, exactly 38 weighted quotient cases, and exactly 355 distinct labeled preorders. No producer generator or canonicalizer is imported.

For each core, all sixteen exterior-direction masks and all fifteen types are checked independently by reflexive transitive closure. One-copy and two-copy legality agree in every case, and every full union of legal types is transitive.

These tests certify arbitrary multiplicities: a two-edge transitivity failure involves at most two exterior vertices. Equal-type failures appear with two copies; unequal-type failures appear in the simultaneous one-copy union. Fixed attachment directions additionally exclude every two-edge path from one exterior vertex to another. Thus cloning does not create untested relations.

Specifications with no legal type reduce to a core of at most four vertices and need no new degree-four certificate.

## 3. Exact all-population component pruning

Take one clone of every legal type. Positive repetitions preserve its connected-component partition and bipartiteness. For a component H, let A_H be its active attachments, those incident with exterior vertices in H. Exactly as in the independently proved three-attachment reduction, its maximum matching number over all populations is

|A_H| + ν((K∩H)−A_H).

The upper bound follows by deleting active attachments from a matching. It is attained with four copies of every present type: match each active attachment to a distinct clone of an incident type, then use a maximum matching of the remaining core. This is a proved maximum-population formula, not an inference from a finite population test.

If a=|A_H|<4, the rank is at most a+floor((4−a)/2)≤3. If a=4, every core vertex lies in H and the maximum rank is exactly four. Thus the producer correctly retains precisely those specifications having a nonbipartite component with all four attachments active.

The independent audit uses the full matching formula, with an independently computed residual-core matching number, and verifies that rank four is equivalent to activity of all four attachments in every tested component. It reconstructs the producer's entire reduced/retained partition.

At zero populations, components may split, but deleting clone types cannot increase their maximum matching rank or destroy bipartiteness. Consequently every omitted specification is covered on all population faces by the established degree-at-most-three preorder theorem or the established bipartite rank-at-most-four theorem, followed by ULC product closure.

The bipartite identification is legitimate: a connected bipartite preorder comparability component on at least three vertices has no equivalence edge and no directed two-edge path through distinct vertices, since either would force a triangle. Its vertices therefore split into genuine sources and sinks, and its disjoint ordered matching supports are exactly the ordinary bipartite shore supports. An equivalence component of two vertices has polynomial 1+2z separately. Support polynomials multiply over components.

## 4. Canonicalization

All four core vertices are attachments. The producer tries every 4! permutation and global relation reversal. The key contains the four complete adjacency rows, transformed four-bit direction mask, and transformed fifteen-type legality mask. Reversal transposes the relation and complements all four orientation bits; its gamma invariance is the bijection exchanging tail and head sets.

The independent audit reconstructs this orbit minimum without importing producer code, checks every stored representative is minimal, and compares the complete regenerated set with all 76 stored keys. Equality of keys supplies an explicit isomorphism or global duality, so deduplication cannot omit an inequivalent family. The JSON and TSV descriptions and all polynomial metadata are also compared exactly.

## 5. All-population support kernel

Every selected exterior vertex needs a distinct core partner in a matching support. Hence at most four exterior vertices occur, and their count is at most the matching size k. For each legal-type quota q of total at most four, require exactly q_t selected labeled exterior vertices of type t. If c_(k,q) is the number of feasible ordered disjoint k-element endpoint pairs containing all those labels, then

γ_k(M)=Σ_(|q|≤4) c_(k,q) ∏_t binom(M_t,q_t).

This identity holds for every nonnegative integer population. The binomial factors choose the selected labels; clone permutations preserve feasibility; unselected vertices cannot be used by a matching of the fixed support. There is no interpolation from bounded populations.

The producer tests perfect-matching existence as a Boolean for each disjoint pair, so multiple matching witnesses do not multiply a support. The independent audit enumerates ternary roles on the four core vertices and binary roles on mandatory exterior vertices, filters for equal endpoint sizes, and checks all Hall inequalities on tail subsets. It deliberately includes the impossible k<|q| candidates that the producer discards, and independently finds them infeasible.

The Hall candidate totals for 0,1,2,3,4 mandatory exterior labels are 19,32,58,104,196. All 162,580 stored scalar coefficients agree. The parser independently verifies every quota domain has exactly binom(d+4,4) vectors, with no repetition or omission, and all five arrays have the corresponding length.

## 6. Independent Newton-gap multiplication

The exported polynomials are the unscaled binomial-basis gaps

4γ_2²−9γ_1γ_3 and 3γ_3²−8γ_2γ_4.

The producer uses a factorial expression for multiplying binomial polynomials. The independent audit instead enumerates all ordered pairs of subsets S,T of a t-element set, with |S|=a, |T|=b and S∪T equal to that entire set. Calling this integer count W(a,b,t), elementary union decomposition gives exactly

binom(x,a) binom(x,b)=Σ_t W(a,b,t) binom(x,t).

The verifier constructs every needed W by literal subset enumeration, applies the tensor-product identity across population variables, and compares each complete resulting sparse gap array, including all signs and zeros removed. All 258,153 exported nonzero terms agree; comparison of complete maps also rules out missing terms.

Exponent encoding uses three bits per population variable. Every gap has total degree at most six, because a selected-exterior count cannot exceed k in γ_k. Thus each exponent is at most six, base-eight encoding has no carries, and fifteen variables fit within 45 bits. This justifies both producer and verifier encodings.

## 7. Arithmetic and reproducibility

The independent C++17 verifier was run with undefined-behavior sanitization and stopped on every discrepancy; it completed with no finding. The largest Hall candidate set has 196 pairs, bounding every input coefficient. At fifteen variables, the largest relevant multiplication has at most binom(18,3)^2+binom(17,2)binom(19,4) ordered term pairs. Every union weight is at most 3^6. Together with the scalar factors and the input bound, even a sum of absolute contributions is below 10^15, safely within signed 64-bit arithmetic. Row masks use at most nineteen vertices, and population exponent codes at most 45 bits.

Run `python3 prepare.py`; compile `recount.cpp` using C++17 and sanitization; run it on `representatives.txt`. Assertions must remain enabled. The audit imports no producer source and uses only standard libraries. `kernel_audit.json` records input and verifier hashes, exact counts, and verdict; `recount.log` records the complete successful run.

The remaining mathematical obligation is an all-population positivity proof for these verified gap polynomials. No finite population scan can replace that layer.
