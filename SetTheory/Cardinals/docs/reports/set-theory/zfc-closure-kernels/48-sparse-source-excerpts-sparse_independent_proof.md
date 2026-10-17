# A sparse exact checker for the pinned C254 numerical proof syntax

This note gives ordinary mathematical proofs, including malformed input codes. It does not claim a new binary Turing-machine table, a checked Lean development of these bounds, or an internal ZFC proof of the set-theoretic calibration. It does establish a concrete replacement for a dense numerical checker history: a canonical sparse history has at most `floor(sqrt(3 b + 1))` rows on a proof code of binary length `b`, and its unencoded code/value data have linear total bit length. The calculation concerns the exact current proof encoding, not a changed calculus.

Sources are `Code254.lean` and `Code254Proof.lean` in ProveIt, pinned to repository commit `fab89c5d26b81cd2ccab2ee5d213ff23725c7726`:

- <https://github.com/VladimirReshetnikov/ProveIt/blob/fab89c5d26b81cd2ccab2ee5d213ff23725c7726/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean>
- <https://github.com/VladimirReshetnikov/ProveIt/blob/fab89c5d26b81cd2ccab2ee5d213ff23725c7726/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254Proof.lean>

The exported formula-circuit source hash is SHA-256 `18311d4a28cba6778a0ba1a1ddee34f5c2dd5044a23958b63f46d0640be4e01e`. An independent control audit on 2026-10-17 confirmed this hash against the local pinned source, re-exported and compared every formula AST, confirmed the expanded constructor depths below, and compared the sparse checker with its independent tree transcription for all input codes from 0 through 48. These small checks corroborate the transcription; the all-input claims follow from the proofs below.

## 1. Exact syntax and the demand tree

Write

\[
 P(x,y)=\frac{(x+y)(x+y+1)}2+y,
 \qquad \operatorname{node}(t,z)=12z+t+1.
\]

This is the dual Cantor pairing used in the pinned files. It is a bijection from pairs of natural numbers to natural numbers, and each component is at most its pair code. Zero is not a proof code. On a positive input `c`, compute its unique tag `t<12` and payload `z` from `c=12z+t+1`. Unpair `z=P(a,r)` and `r=P(p,q)`. The recursive proof premises are precisely:

- Tag 1: both `p` and `q`, representing modus ponens with requested output formula code `a`.
- Tag 2: `r`, representing generalization with binder code `a`.
- All other tags: no recursive premises.

The extra unpairing of `q` at tag 10 supplies two literal numeric parameters to `rho8`; these are not proof premises. Tag 0 succeeds only at payload zero. The bundle tag 11 additionally checks its two literal inequalities. Literal formula and variable codes are used as integers; they are not recursively decoded as proofs.

Define the **positive demand tree** of any natural input `c` as follows. Input zero has the empty tree. A positive input contributes a node labelled `c`. At a recursive tag, attach the positive demanded children and omit every zero child. At other tags the node is a leaf. Repeated codes count as repeated occurrences in this tree, even though a memoized evaluator will share them. We build this tree regardless of whether parsing or proof validation later fails. Thus the estimates apply to every input integer, including a tag-1 input whose first premise is zero, an invalid bundle, and a nonzero-payload tag-0 input.

Every demanded child is strictly smaller than its positive parent: pairing components are at most their payload, whereas the parent is `12` times that payload plus a positive tag offset. Strong induction on the parent code therefore defines the tree, its size, and the numerical checker without any semantic assumptions.

For `c>0`, let `b(c)=floor(log_2 c)+1`; set `b(0)=0`. Let `N(c)` count positive node occurrences, and let `H(c)` be the largest number of positive nodes on a root-to-leaf path, with `H(0)=0`.

## 2. The bit-growth inequality

**Lemma 1.** At any positive demand-tree node with at least one positive child,

\[
 b(c)\ \geq\ 2\sum_i b(c_i)+1,                       \tag{1}
\]

where the sum ranges over its one or two positive children.

**Proof.** There are three cases.

For a tag-2 node with positive child `p`,

\[
 c=12P(a,p)+3\geq 6p^2.
\]

For a tag-1 node with exactly one positive child `p`, either orientation of the inner pair has value at least `p^2/2`. The outer pair is at least its second component, so again `c>=6p^2`.

For a tag-1 node with two positive children `p,q`,

\[
 2P(p,q)-4pq=(p-q)^2+p+3q\geq 0.
\]

Consequently `P(p,q)>=2pq`. Since `P(a,x)>=x^2/2`,

\[
 c=12P(a,P(p,q))+2\geq24p^2q^2.
\]

If `k=b(p)`, then `p>=2^{k-1}` and

\[
 6p^2\geq\tfrac32\,2^{2k}>2^{2k}.
\]

Similarly, for `k=b(p)` and `l=b(q)`,

\[
 24p^2q^2\geq\tfrac32\,2^{2(k+l)}>2^{2(k+l)}.
\]

An integer greater than `2^m` has bit length at least `m+1`. This proves (1). The zero-child and zero-premise cases were explicitly included; no validity assumption was used. \(\square\)

The nested pairing in the actual MP code is essential to the particularly strong binary inequality. Merely bounding the parent by a constant times `p*q` loses the outer squaring and misses the square-root size estimate.

## 3. Square-root size, logarithmic height, and linear bit mass

**Theorem 2.** For every natural input `c`,

\[
 N(c)\bigl(N(c)+2\bigr)\leq3b(c).                   \tag{2}
\]

For a positive code, therefore,

\[
 N(c)\leq\left\lfloor\sqrt{3b(c)+1}\right\rfloor-1. \tag{3}
\]

**Proof.** The empty tree at zero gives equality. For a positive leaf, `N=1` and `b>=1`, so the claim follows. Proceed by induction for a nonleaf.

With one positive child of size `n`, Lemma 1 and the induction hypothesis give

\[
 3b(c)\geq2n(n+2)+3.
\]

Its new node count is `n+1`. Subtracting the desired expression `(n+1)(n+3)` from the right-hand side gives `n^2>=0`.

With two positive children of sizes `u,v`, the same argument gives

\[
 3b(c)\geq2\{u(u+2)+v(v+2)\}+3.
\]

The new count is `u+v+1`. Subtracting `(u+v+1)(u+v+3)` leaves `(u-v)^2>=0`. This proves (2). Completing the square, `(N+1)^2<=3b+1`, proves (3). \(\square\)

**Corollary 3 (canonical cache size).** Let the canonical demand closure contain zero and every distinct positive label in the demand tree. Its number `m(c)` of entries satisfies

\[
 m(c)\leq\left\lfloor\sqrt{3b(c)+1}\right\rfloor.    \tag{4}
\]

For input zero the closure is `{0}` and both sides equal one. For positive input, the number of distinct positive labels is at most the unfolded occurrence count, so (4) follows from (3). This is a statement about the canonical closure and the existence of a certificate of that size. A verifier may also soundly accept larger histories containing irrelevant intermediate rows; their lengths need not obey (4).

**Corollary 4 (height).** For `c>0`,

\[
 H(c)\leq\left\lfloor\log_2(b(c)+1)\right\rfloor.    \tag{5}
\]

Indeed, (1) implies `b(parent)+1>=2(b(child)+1)` on every positive edge, and a positive leaf has `b+1>=2`. Along a path with `H` positive nodes this yields `b(c)+1>=2^H`. An attempted zero child, if counted as a call by an implementation, can add one terminal call beyond this positive-node height.

**Corollary 5 (bit mass).** For the multiset of positive node occurrences `v` in the unfolded tree,

\[
 \sum_v b(v)<2b(c),
 \qquad
 \sum_v b(v)^2<\frac43 b(c)^2                       \tag{6}
\]

when `c>0`. In particular the first sum, being an integer, is at most `2b(c)-1`. The same bounds hold for any set of distinct cached positive codes, by selecting one occurrence per code.

**Proof.** At depth `j`, repeated use of (1) bounds the sum of bit lengths by `b(c)/2^j`. Sum this finite geometric series and compare it with the infinite series. For the second bound, the sum of squares at one level is at most the square of the sum at that level, hence at most `b(c)^2/4^j`; sum again. \(\square\)

These estimates concern the proof-code demand tree, not the formula syntax encoded inside a literal numeric parameter. They also do not require memoization: the unfolded tree itself is already small in input bit length. Memoization makes the numerical-history representation smaller still when labels repeat.

## 4. The square-root order is attained by valid unfolded trees

Let `t_0` be the truth proof, and define

\[
 t_{h+1}=\operatorname{mp}(0,t_h,t_h).
\]

Every `t_h` is a valid proof of formula code zero, because `wim(0,0)=0`. This numerical alias is part of the exact calculus. If `q_h` is its proof code, then `q_0=1` and

\[
 q_{h+1}=12P(0,P(q_h,q_h))+2
 =24q_h^4+48q_h^3+60q_h^2+36q_h+2.                  \tag{7}
\]

For `q>=1`, the right-hand side lies between `24q^4` and `170q^4`. Taking logarithms and solving the resulting recurrence shows \(b(q_h)=\Theta(4^h)\). The unfolded node count is exactly \(2^{h+1}-1=\Theta(\sqrt{b(q_h)})\). Thus the order of (3) cannot be improved for unfolded occurrences, even when restricted to valid proofs.

This family does **not** prove that the distinct-cache bound is asymptotically sharp: it has only `h+1` distinct positive codes and `h+2` rows including zero. For example, at `h=6` the input has 9,156 bits, the unfolded tree has 127 positive occurrences, and the cache has eight rows. Any claim of a matching lower bound for distinct cache entries would need a different argument.

## 5. Exact numerical rows and equivalence to the source checker

Define a total numerical value `E(c)` by well-founded recursion on `c`. Its intended meaning is zero for an invalid parsed proof and `n+1` for a valid proof concluding at formula code `n`. The definition is:

1. `E(0)=0`.
2. At tag 0, return one exactly if the payload is zero; otherwise return zero.
3. At tag 1, let `u=E(p)` and `v=E(q)`. Return `a+1` exactly if `u>0`, `v>0`, and `v-1=4P(u-1,a)`; otherwise return zero.
4. At tag 2, let `u=E(r)`. Return `4P(a,u-1)+3` if `u>0`, and zero otherwise.
5. At tags 3 through 10, return one plus the exact corresponding `rho` formula. Tags 3 and 8 use the pair `(a,r)`; tags 4, 5, 6, 7 and 9 use `(a,p,q)`; tag 10 uses `(a,p,q_0,q_1)` where `q=P(q_0,q_1)`.
6. At tag 11, return `bundle(a,p,q)+1` if `q!=a` and `q!=p`, and zero otherwise.

**Theorem 6 (all-input exactness).** For every natural `c,n`, the pinned Lean definition `Code254Proof.check c n` returns true if and only if

\[
 E(c)=n+1.                                           \tag{8}
\]

**Proof.** Since children are smaller, induction on `c` shows that `decodeFuel f c` stabilizes once `f>=c+1`; the corresponding smaller-fuel calls are still above their respective stabilization thresholds. Alternatively (5) supplies a substantially smaller sufficient bound on positive depth, while calls at zero always fail. Thus the actual source call `decodeFuel (c+1) c` agrees with the terminating recursive parser described in Section 1.

Now induct on `c`, comparing the displayed numerical rows with `decodeStep`, `RawProof.valid` and `RawProof.conclusion`. At a truth tag the claim is immediate. At an MP tag, a child has a valid parsed proof exactly when its numerical value is positive, by induction. When both children are valid, the source's only remaining test is that the major conclusion equals `wim(minor conclusion,a)`, exactly the equation in row 3. Its conclusion is the explicit output `a`. At a GEN tag, validity is the child's validity and the conclusion is `wal(a,child conclusion)=4P(a,child conclusion)+2`; shifting by one gives row 4. Schema leaves and the two bundle inequalities match directly. Zero and failed parsing or failed validation produce zero in both definitions. This proves (8). Eagerly evaluating an otherwise unneeded MP child only adds a terminating computation and cannot change the result. \(\square\)

List the canonical demand closure in increasing order, starting with zero. Evaluate each row using values in earlier rows. Every demanded child is earlier, so all lookups are defined. Induction along the list proves that the stored value at each code is exactly `E` at that code. The final row is the requested input code because every other nonzero closure element is smaller.

A verifier which requires increasing nonnegative codes, starts with `(0,0)`, checks the displayed recurrence at every row using earlier entries, and ends at code `c` is sound by the same induction. Irrelevant rows between zero and the target do not compromise this argument. Requiring exactly the demand closure is optional; it is needed only if every accepted history, rather than a canonical generated history, is to satisfy the row-count bound.

## 6. A rigorous universal bound on output size

The numerical checker is not merely sparse in its dependencies: each cached conclusion has at most a fixed constant times the input node's bit length. The constant is large because the literal bundle expands a deep fixed arithmetic circuit.

Let

\[
 W_k(x,y)=4P(x,y)+k,\quad k\in\{0,1,2,3\}.
\]

For `M=max(x+1,y+1)`, direct expansion gives

\[
 W_k(x,y)+1
 \leq2(x+y+1)(x+y+2)
 \leq8M^2.                                         \tag{9}
\]

When every literal in an expanded constructor expression has shifted value at most `M`, an expression of primitive-constructor depth at most `d` therefore has shifted value at most

\[
 8^{2^d-1}M^{2^d}=\frac{(8M)^{2^d}}8.               \tag{10}
\]

This follows by induction on `d`; the formula at `d=0` is exactly `M`. Depth means a longest path counting occurrences of the four primitive constructors, after expanding the derived operators `wn`, `wa`, `wex` and any bundle abbreviations. The pinned ASTs have the following depths:

| Expression | Expanded primitive depth |
|---|---:|
| `rho1` | 4 |
| `rho2`, `rho3`, `rho4`, `rho5` | 3 |
| `rho6` | 5 |
| `rho7`, `rho8` | 3 |
| `bundleC` | 19 |
| `bundleG` | 16 |
| `bundle` | 23 |

For a `rho` leaf, its proof code `c` is at least four. Every literal parameter is at most the payload, so its shifted value is at most `c`; the constant `F=1` also has shifted value at most `c`. Since `8<=c^2`, induction using (9) bounds a depth-`d` shifted output by `c^(3*2^d-2)`. Every `rho` leaf consequently has `E(c)<=c^94`.

For a valid bundle leaf, write its proof code as `c=12(z+1)`. Payload zero would give all three parameters zero and fail both freshness inequalities, so validity implies `z>=1` and `c>=24`. Every literal parameter plus one is at most `z+1=c/12`; the shifted constant `F+1=2` has the same bound. Taking `M=c/12` in (10) and using depth 23 gives

\[
 E(c)\leq\frac{(2c/3)^{2^{23}}}{8}
 \leq c^{2^{23}}.                                  \tag{11}
\]

Invalid bundles return zero. This slightly improves the simpler estimate `c^(2^24-1)` obtained by using only `c>=8` at each constructor.

**Theorem 7 (uniform output bound).** With the explicit constant

\[
 D=2^{23}=8,388,608,
\]

every positive proof code satisfies

\[
 E(c)\leq c^D,
 \qquad b(E(c))\leq D\,b(c).                        \tag{12}
\]

Here `b(0)=0`. The exponent is a safe upper bound, not an optimized one.

**Proof.** The preceding circuit estimates handle all nonrecursive schema leaves; truth and invalid codes are immediate. If an MP row is valid, its shifted output is `a+1<=c`, which satisfies (12).

Consider a valid GEN row with positive premise code `p`, binder `a`, and child shifted value `u=E(p)`. The induction hypothesis gives `u<=p^D`. Set `s=a+p>=1` and `n=u-1`. Since `D` is a positive integer,

\[
 a+n\leq a+p^D-1\leq(a+p)^D-1=s^D-1.
\]

For any nonnegative pair with sum at most `s^D-1`, the definition of `P` yields

\[
 E(c)=4P(a,n)+3
 \leq2s^{2D}+2s^D-1
 \leq4s^{2D}.
\]

But the GEN proof code is `c=12P(a,p)+3>=6s^2`, and hence

\[
 c^D\geq6^Ds^{2D}>4s^{2D}\geq E(c).
\]

This proves the numerical bound by strong induction. The bit bound follows from `c<2^{b(c)}`; the case `c=1` is immediate as well. \(\square\)

There is no claim that `D` is a pleasant practical constant. The actual valid small bundle code 60 already produces a conclusion with over twenty-two million bits. Polynomial bit complexity is nevertheless the correct asymptotic classification because the arithmetic circuits are fixed and do not grow with the input proof code.

## 7. Consequences for algorithms and arithmetic certificates

From (6) and (12), a canonical sparse history stores at most

\[
 \sum_{c_i>0}\bigl(b(c_i)+b(E(c_i))\bigr)
 <2(D+1)b(c)
\]

bits in its numerical code and value fields. This excludes routine list delimiters and pointers; with `O(sqrt(b))` rows, these also require only `O(b)` bits in conventional encodings. A fixed number of intermediate values per arithmetic circuit preserves this linear-space estimate. MP's temporary formula comparison is also at most a fixed constant times the row-code bit length by (9), so it introduces no unbounded new expansion.

There exists a straightforward implementation with `O(b^2)` elementary bit operations and `O(b)` bits of workspace, treating the fixed constant `D` and fixed expanded circuit sizes as constants. Use ordinary quadratic multiplication and a digit-by-digit quadratic integer-square-root algorithm for Cantor unpairing. A row at code `c_i` then costs at most a fixed constant times `b(c_i)^2`; (6) bounds their sum by `O(b^2)`. Constructing and sorting the closure also fits this bound: with `m=O(sqrt(b))` entries, even `O(m log m)` comparisons of at most `b` bits cost `O(b^(3/2) log b)=O(b^2)`. Appropriate dictionary or sorted-list handling does not exceed this asymptotic bound. This is an existence bound for a bit-model implementation, not a precise performance contract for every Python integer or container operation. Comparing a separately supplied conclusion of length `r` can be included within `O((b+r)^2)` time and `O(b+r)` space.

A dense history covering every integer from zero through `c` has `c+1` rows, which is exponential in `b(c)`. The sparse history covers only the demanded premises. The gain is therefore a proved short certificate representation for the existing numerical checker. It should not be described as converting an exponentially slow recursive source parser into a polynomial one: the unfolded demand bound also applies to that parser's actual recursive dependencies.

For arithmetization, replace each arithmetic operation by its natural-number graph. Pairing has the polynomial equation `2z=(x+y)(x+y+1)+2y`; tag decoding has `c=12z+t+1` and `t<12`. The fixed formula circuits require a fixed finite number of auxiliary variables. A bounded universal condition over rows, with references to earlier rows, can then express exact local recurrence. A Gödel beta function or another standard finite-sequence encoding supplies existential codes for the history. Existence and soundness follow from Theorem 6 and the canonical history construction, uniformly for all natural input codes.

There is a useful explicit simplification. Each primitive constructor is already the integer polynomial

\[
 W_k(x,y)=2(x+y)(x+y+1)+4y+k.
\]

Thus no division is needed to construct formulas. Each constructor is at least both its arguments, so every intermediate of a successful fixed leaf circuit is at most its final output. If code and value fields are interleaved in one beta sequence with witness integer `B`, all decoded fields and all such local circuit witnesses can be bounded by `B`. MP's one comparison and GEN's one constructor can be written directly as polynomial terms, avoiding an auxiliary expected-MP-value that could exceed the stored row values. Premise references are bounded by the current row index. Consequently the graph may be presented with only `m,B,C` existentially quantified outside a fully bounded arithmetic matrix, where `C` is the beta modulus parameter. Strict code increase also implies `m<=c+1`, so even the row-count quantifier may be bounded by the input code. This is a concrete Sigma-1 presentation, not an appeal to general representability alone.

The linear-bit storage estimate above applies to a direct representation of the row fields. It is not automatically the size of a particular beta/CRT integer. For the ordinary CRT encoding of a length-`k` list whose largest entry has at most `L` bits, one may take the modulus parameter `(max+1)k!`; the resulting CRT witness has `O(kL+k^2 log k)` bits. Thus a fixed-width expansion of the canonical rows still admits polynomial-size beta witnesses, but its exact bound should be stated separately from the direct linear-space algorithm.

All the proofs in this note concern finite natural-number computations and induction. They provide explicit mathematical obligations suitable for a Lean or arithmetic formalization, without any appeal to reflecting an arbitrary external Lean theorem into ZFC. They do not themselves supply the remaining set-theoretic interpretation or machine-simulation internalization theorem. Nor does polynomial running time imply a smaller binary transition table: a compact implementation of this particular checker remains a separate state-count problem.

## 8. Implementation audit notes

The reviewed implementation was `zfc_consistency_research_20261017/code/sparse_c254.py` and its `data/formula_circuits.json` at the time of this audit. Its positive-code tag dispatch, dual-Cantor orientation, tag-10 unpacking, shifted numerical values, truth alias, MP comparison, GEN arithmetic and bundle inequalities match the pinned definitions. `demand_codes` inserts zero, rejects a negative proof-code input, checks strict child descent, and sorts the exact dependency closure. `sparse_history` evaluates that order. The supplied `reference_decode` and `reference_value` use a separate tree transcription; both share the exact exported formula-circuit evaluator.

The certificate verifier accepts sound additional rows below the target, as explained after Theorem 6. Its docstring's phrase “extra tails” means rows after the target; it does not promise minimality. The mathematical API has natural-number arguments. If the Python API is exposed to arbitrary untrusted object types, it could additionally reject non-integer conclusions and malformed row element types: for example, Python equality allows the conclusion `0.0` to compare equal to the natural conclusion zero, and malformed row objects can raise a `TypeError` rather than return rejection. These are interface-hardening matters, not discrepancies for natural-number inputs or arithmetic certificates.
