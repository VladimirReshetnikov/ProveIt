# Constructor-code and source-sharing experiments

These experiments retain the seed-K mathematical theory. They change the numeric representation of formulas, harmless logical symmetries, or the closed source decomposition of the arithmetic emitter. Every numeric result below is a **protected-helper hardware lower bound for a particular source layout**. No changed layout here is presented as a verified binary consistency machine.

The baseline has 4,744 primitive occurrences, 208 distinct source DAG nodes, and 220 working states. The objective is `source_work/hardware_objective.py`; it counts unavoidable new roles and protects the branch skeletons used by the existing arithmetic helpers. A surviving objective value does not itself prove that all role assignments are mutually compatible or that binary runtime is correct. Candidate construction would still require constrained allocation, startup verification, and full runtime certificates.

## 1. Exact symmetries in retained logical rows

When the original Łukasiewicz and rho6 rows are retained, the classical implication/falsum laws and the existing equality bootstrap justify these transformations:

- exchange the first two antecedents in a curried clause;
- replace every equality atom by its converse;
- globally replace membership by its converse, as an isomorphism of the formal signature;
- exchange equality arguments in the two membership-congruence rows, using symmetry of equality;
- use the inherited fresh-binder calibration to reverse the arguments in the arithmetic binder builder of the merged equality row.

The source-preserving implementation changes only the selected parameter-copy register identifiers. It keeps the complete primitive opcode sequence, all source paths, and all control-flow destinations. This avoids the sharing loss caused by replacing a whole interval by one new closed subtree.

`signature_search.py` tests all 128 choices of seven symmetry flags. The baseline is uniquely best at lower bound 220. The nearest changed source, reversing only the merged equality row's binder arguments, has 210 DAG nodes and lower bound 223. These are exact source-tree edits, but the proof of logical calibration still matters: a row's Boolean equivalence is not enough if the propositional basis used to prove that equivalence has also been removed.

`antecedent_search.py` separately tested 480 whole-row replacements in four logical rows. It varied antecedent order, parameter assignment, binary parses of closed macro words, and insertion at the first or last old chunk. The best lower bound was 225. Re-inserting an unchanged formula by this method can already lose several shared subtrees. These negative measurements therefore do not establish that all corresponding logical symmetries must increase state count.

## 2. General suffix codes for formula constructors

Let

\[
P(a,b)=\frac{(a+b)(a+b+1)}2+b
\]

be Cantor pairing. Assign to each constructor \(X\in\{I,Q,R,E\}\) a binary tag word of length \(\ell_X\). Read the tag from the **least significant bit upward**. If its numerical value is \(t_X\), define

\[
C_X(a,b)=2^{\ell_X}P(a,b)+t_X.
\]

Require that the four tag words form the leaves of a full binary prefix tree when read in this order, and require \(t_R=1\), so that \(R(0,0)=1\) remains the distinguished contradiction code. The other constructors may carry tag zero.

### 2.1 Decodability

Let \(m=\max_X\ell_X\). Each tag selects a residue class modulo \(2^{\ell_X}\), or equivalently a subset of the \(2^m\) residues modulo \(2^m\). The prefix-code condition says precisely that these four subsets are pairwise disjoint and exhaust all residues. For any positive natural number \(n\), there is therefore exactly one constructor \(X\) whose tag matches it. Then

\[
k=\frac{n-t_X}{2^{\ell_X}}
\]

is a unique natural number, and inverting Cantor pairing gives a unique ordered pair \((a,b)\). Thus every positive code has a unique constructor decomposition. This is an arithmetic theorem for all naturals, not a claim inferred from testing small codes. The script's finite check of the complete residue partition modulo \(2^m\) is a decision procedure for this finite premise.

The exceptional code 0 remains native truth. Its matching tag belongs to \(I,Q\), or \(E\), since membership has nonzero tag 1. The three possible all-zero constructor meanings are respectively truth implies truth, universal quantification of truth, and reflexive equality. Each is true, so the code-zero convention causes no semantic inconsistency. It is essential to state this exception: the recursive decoder does not descend again into two zero children at code 0.

### 2.2 Strict child bounds and freshness

For all naturals \(a,b\), Cantor pairing satisfies \(P(a,b)\ge a,b\). Every full binary tag has length at least one, so its multiplier is at least two.

If \(P(a,b)>0\), then

\[
C_X(a,b)\ge2P(a,b)>\max(a,b).
\]

If \(P(a,b)=0\), then \(a=b=0\). A positive output code in this case has \(t_X>0\), so it is again strictly larger than both children. Thus every positive constructor code is strictly larger than both arguments. Formula decoding by recursion on the numeric code is well founded. Every variable label appearing in a positive coded formula is smaller than the formula code; code 0 is truth and has no variable labels.

The same bound applies to quantifier labels and atom endpoints because they occupy ordinary pairing arguments. It therefore preserves the key seed-K convention that the matrix's own positive numeric code is a fresh label for its decoded formula. The zero-matrix case is handled by native truth, which is fresh for every label. Reversing the pair arguments, discussed below, does not change the bound.

The merged equality row's binder \(\kappa(a,b)=C_R(a,b)\) also remains strictly larger than both endpoints: its multiplier is at least two and its tag is 1. Hence the inherited fresh-binder theorem remains applicable. These proofs address logical freshness; they do not replace the compiler's arithmetic proof obligations.

### 2.3 Logical calibration

The intended decoded formulas for \(I,Q,R,E\) are the same as before. The full residue partition supplies the constructor case analysis, and strict child bounds supply the recursive interpretation. Every emitted native row therefore interprets to the same logical schema, with the stated fresh-label argument for the gated seed-K matrix. The encoded MP and GEN constructors must be changed consistently with the axiom emitters. Formula lists and command streams continue to use the original Cantor pairing independently of formula tags.

The code-zero convention is treated by native truth rather than by claiming an injective code map on all formal syntax. A putative proof transport that silently identifies arbitrary constructor syntax with code 0 would be incomplete. The interpretation argument has to use truth for code 0 and the unique constructor decomposition only for positive numbers, as in the baseline calibration.

The screens below implement all 81 logical constructor occurrences, including the MP constructor and GEN constructor outside the axiom block. Their arithmetic interfaces remain: consume the old top and the popped stack argument, construct the desired code, preserve the remaining formula stack and unrelated registers, and clear the same scratch registers. They have not been integrated into a new Rocq completeness theorem because none survived the state-cost screen.

## 3. Fixed-length tag permutations

First keep all lengths equal to two. Membership retains tag 1. The remaining tags \(0,2,3\) can be assigned to implication, quantification, and equality in six ways. `tag_permutation_search.py` changes every affected constructor core and tag tail, with several local choices of addition/deletion position and increment association. It produced 22 distinct edited layouts.

| Implication tag | Quantifier tag | Equality tag | Best protected lower bound |
|--:|--:|--:|--:|
| 0 | 2 | 3 | 220, unchanged baseline |
| 0 | 3 | 2 | 229 |
| 2 | 0 | 3 | 235 |
| 2 | 3 | 0 | 245 |
| 3 | 0 | 2 | 239 |
| 3 | 2 | 0 | 244 |

The complete receipt is `tag_variants/results.json`. The unchanged numerical constants are not inherently best for all compilers; they are best in this exact local editing family against the existing table's sharing pattern.

## 4. Reversing Cantor-pair arguments without a stack swap

Each implication constructor's 27-primitive core consists of:

1. an 11-primitive stack-pop fragment;
2. a 10-primitive pair-building fragment;
3. a six-primitive accumulation/multiplication fragment.

At the pair fragment's interface, the relevant values are in registers 6 and 1, and the fragment adds \(P(r_6,r_1)\) to register 7 while clearing registers 6 and 1. Exchanging register identifiers 1 and 6 **only inside this ten-primitive fragment** gives its conjugate under that register permutation. The resulting fragment adds \(P(r_1,r_6)\) and has the same cleared outputs. The surrounding pop and multiplication fragments remain unchanged.

This proves the reversed argument kernel for all natural register contents from the existing pair-fragment contract. It requires no extra stack-swap macro and no change in primitive length. The conjugacy argument is an exact renaming theorem: applying the inverse permutation to the initial state, running the old fragment, and applying the permutation to the result is extensionally equal to running the renamed fragment.

One can reverse the pair order independently for implication, quantification, membership, and equality, provided all occurrences of each chosen constructor—including MP and GEN—are changed consistently. The decoder reverses the recovered child pair for that constructor. The formal signature and the interpretation are unchanged.

`pair_orientation_search.py` tested the 16 choices. The baseline remained uniquely best at 220. The nearest changed case, reversing only quantification, had lower bound 239 and 220 source DAG nodes. Reversing all four had lower bound 245. `orientation_variants/local_audit.json` checks 686 small arbitrary input/tail configurations and preservation of unrelated registers; it supplements the all-natural register-renaming proof rather than replacing it.

The script can jointly vary orientations and fixed-length tags, but that larger family was not run. No negative statement about those untested combinations is made.

## 5. Nonuniform tag lengths

There are five ordered full binary tree shapes with four leaves. For each shape, choose the leaf whose numerical tag is 1 for membership and permute the other three constructor names over the remaining leaves. This gives 30 code families. Six are the balanced, fixed-length families above. The other 24 have length multiset \(\{1,2,3,3\}\).

The family that most directly tries to shorten the frequent implication constructor is, for example,

\[
I(a,b)=2P(a,b),\quad
Q(a,b)=4P(a,b)+3,\quad
R(a,b)=8P(a,b)+1,\quad
E(a,b)=8P(a,b)+5.
\]

Its residue sets are respectively even numbers, numbers congruent to 3 modulo 4, numbers congruent to 1 modulo 8, and numbers congruent to 5 modulo 8. They partition all naturals. Its implication multiplier is two, but the larger atom multipliers and changed source-sharing pattern consume the apparent saving.

`suffix_code_search.py` screens all 30 families, using several positions for inserting/deleting tag increments and two increment associations. After deduplication it evaluates 163 source layouts. All 30 complete residue partitions pass. Its arithmetic constructor audit checks 3,240 cases over the four constructors and small inputs/tails, with no mismatch.

The baseline remains uniquely best at lower bound 220. Among **nonuniform** families, the minimum is **256**, for

\[
I=4P+3,\qquad Q=2P,\qquad R=8P+1,\qquad E=8P+5.
\]

The implication-first example displayed above has best lower bound 257. The full measurements are in `suffix_variants/results.json`. The exact tag words are recorded separately in `suffix_variants/family_results.json`.

The multiplier macro proof is elementary but separate from decodability: each decrement of register 7 performs exactly \(2^{\ell_X}\) increments of the accumulator. Induction on its initial value gives multiplication by two, four, or eight; the subsequent fixed increments add the tag. The pair fragment and stack-pop contract are inherited. The changed loops use only closed source subtrees, and each saved source was checked by both independent source-control-flow resolvers.

## 6. What these negative measurements do and do not establish

The coding proofs show that there is room to change constructor tags, pair order, and fresh-label arithmetic without changing the seed-K consistency target. The experiments show that the tested local source edits do not yield a state saving in the present shared decoder architecture.

Primitive occurrence count is a poor objective here. A 46-occurrence arithmetic shortening can increase the number of distinct source subtrees. Conversely a longer formula emitter can reuse existing subtrees. Protected arithmetic-helper roles also create costs absent from a bare source DAG count. These are reasons to preserve the exact source trees, parameter assignments, helper constraints, and measured receipts in any future search.

Further productive work would synthesize arithmetic and source decomposition together, or reconstruct a compiler that can deliberately relocate shared helper roles and then prove its runtime simulation. None of the bounded screens in this note is a lower bound on all machines for the corresponding logical formalism.
