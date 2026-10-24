# Smaller exact local graphs for the direct sealed-ZFC checker

## Result and exact scope

The supplied ordinary integer-coefficient polynomials improve several actual local functions of the direct annotated checker without changing its numeric encoding. All visible variables and all witnesses range over the natural numbers, including zero. Every subtraction in this document and the JSON artifacts is subtraction in an integer polynomial, not truncated natural subtraction.

These are complete local graph constructions with literal expression trees, fully expanded coefficient records, exact counts, and universal mathematical proofs below. They are not a compiled whole-checker consistency polynomial. No Lean kernel verification of these new constructions is claimed. The repository's internal-omega results do not automatically certify the replacements.

The pinned baseline is commit `2605669a532342f153b13eb6b4a0af4b54f5fa37`. Its [complete numeric checker](https://github.com/VladimirReshetnikov/ProveIt/blob/2605669a532342f153b13eb6b4a0af4b54f5fa37/Computability/DiophantineConsistency/ANNOTATED_REFUTATION_PR.md) accepts some raw certificate exactly when the original sealed-ZFC calculus proves bottom. Its 83,281 raw / 76,313 optimized PR program nodes are source counts, not Diophantine variables. The local baseline counts below come from [quadratic pairing](https://github.com/VladimirReshetnikov/ProveIt/blob/2605669a532342f153b13eb6b4a0af4b54f5fa37/Computability/DiophantineConsistency/QUADRATIC_REGISTER_SYSTEM.md), [tree graphs](https://github.com/VladimirReshetnikov/ProveIt/blob/2605669a532342f153b13eb6b4a0af4b54f5fa37/Computability/DiophantineConsistency/QUADRATIC_TREE_CODE_GRAPHS.md), and [guarded graphs](https://github.com/VladimirReshetnikov/ProveIt/blob/2605669a532342f153b13eb6b4a0af4b54f5fa37/Computability/DiophantineConsistency/QUADRATIC_GUARDED_GRAPHS.md).

| Exact local graph | Previous auxiliaries / operations | New auxiliaries / operations | New degree |
|---|---:|---:|---:|
| Max-square pairing | 3 / 46 | 2 / 39 | 4 |
| Same pairing, strict quadratic-row sum of squares | 3 / 46 | 2 / 42 | 4 |
| Either unpair projection | 4 / 46 | 3 / 39 | 4 |
| Predecessor | 0 / 16 | 0 / 10 | 4 |
| Tree left, tree right, actual list tail | 5 / 62 | 4 / 49 | 4 |
| If-zero conditional | 2 / 32 | 1 / 16 | 4 |
| Zero test | 1 / 20 | 1 / 14 | 4 |
| Actual list head, including found-zero marker | 7 / 76 | 5 / 59 | 4 |
| Max-square pairing, selector eliminated | 3 / 46 quartic | 1 / 53 | 6 |

An operation is one binary addition, subtraction, or multiplication in the literal expression tree; repeated subtrees are counted each time. Scalar multiplication and squaring count. Each supplied artifact includes the final addition of zero, matching the baseline constructor convention. Counting that final redundant operation is deliberate. Counts of a separate hash-consed DAG are also supplied, but are not substituted for tree counts in this comparison.

## 1. Two-witness quartic max-square pairing

For natural z,a,b, the exact `Nat.pair` is

    pair(a,b) = b^2+a          if a<b,
                a^2+a+b      if b<=a.

Introduce only natural t,s and put

    B = t(t-1),
    L = a-b-s+t(2s+1),
    E = 4(z-a-b)-(a+b+s)^2+t,
    Pair = B + L^2 + E^2.

For every integer t, t(t-1) is nonnegative. Therefore Pair=0 is equivalent to B=L=E=0. In particular t is exactly zero or one.

If t=0, L=0 gives a=b+s. Then a+b+s=2a, so E=0 gives 4(z-a-b-a^2)=0 and hence z=a^2+a+b. This is precisely the branch b<=a.

If t=1, L=0 gives b=a+s+1. Then a+b+s=2b-1, so E=0 gives 4(z-a-b)-(2b-1)^2+1=4(z-b^2-a)=0 and hence z=b^2+a. This is precisely the branch a<b.

Conversely choose (t,s)=(0,a-b) when b<=a and (1,b-a-1) when a<b. Both choices are natural and make all three terms vanish. This proves the exact unbounded graph equivalence.

The three residuals B,L,E are quadratic. Replacing B in Pair by B^2 gives a literal sum of three quadratic-row squares, with the same zero set, two witnesses, degree four, and 42 tree operations. The 39-operation version saves three operations by using B directly; a compiler restricted to squared rows should use the 42-operation variant until its nonnegative-term extension is proved.

The exact sparse expansion of Pair has 52 monomials and total degree four. For either inverse projection, hide the missing pair component as one more natural witness. Bijectivity of `Nat.pair` gives the inverse graph, with exactly three witnesses and the same polynomial/count.

## 2. A one-witness sextic tradeoff

Eliminate the selector t by solving E=0:

    T = (a+b+s)^2-4(z-a-b),
    Pair6 = T(T-1) + (a-b-s+T(2s+1))^2.

Here T is an integer polynomial, not a new variable and not a truncated natural expression. For every integer assignment, T(T-1)>=0. Thus Pair6=0 forces T=0 or T=1 and the same branch equation as above. Taking t=T reduces soundness to the preceding proof. Completeness uses the preceding natural s and gives T=t. There is exactly one natural witness, ordinary degree six, 53 tree operations, and 86 expanded monomials. This tradeoff does not preserve the quartic degree target.

## 3. Factor the predecessor graph rather than expanding both squares

For natural n,p, define

    Pred = (n-p-1)^2(n^2+p^2).

If Pred=0 then either n=p+1 or n=p=0, precisely the two possibilities for p=pred(n). Conversely both possibilities give zero. This is not a new predicate: it is exactly the factorization

    [n(p+1-n)]^2 + [p(p+1-n)]^2 = Pred.

It needs no auxiliary witness beyond its visible predecessor output, remains quartic, and uses 10 tree operations with the final +0. Its unfenced product has 9 operations, but the table consistently includes the final +0.

## 4. Tree projections and list tail

For the actual tree code n, introduce p=pred(n), the missing pair component, and the two pairing witnesses t,s. Use

    Tree = Pair(p,a,b;t,s) + (n-p-1)^2(n^2+p^2).

Both summands are nonnegative. Thus the zero set is exactly p=pred(n) and p=pair(a,b). Hiding p,b,t,s yields treeLeft; hiding p,a,t,s yields treeRight. There are four witnesses in either case. At n=0, p=0, hence a=b=0, so treeRight is also the exact guarded listTail. No encoding change or additional branch convention is involved. The supplied polynomial has degree four, 49 tree operations and 62 monomials.

## 5. Selector-free conditional and zero test

For natural n,a,b,c, use just one natural slack s and

    IfZero = [n(c-b)]^2 + [(c-a)(n-s-1)]^2.

At n=0, the second factor n-s-1=-s-1 is nonzero; hence c=a. At n>0, the first term forces c=b. Conversely, if n=0 choose s=0; if n>0 choose s=n-1. Both terms vanish for the required c. This is an exact conditional, not a one-sided implication, and uses one witness and 16 operations.

Setting a=1,b=0 gives the zero test

    Zero = (n*bit)^2 + [(bit-1)(n-s-1)]^2.

It has one witness, 14 operations, and forces the bit to be the correct zero-test value without a separate Boolean constraint.

If a predecessor p=pred(n) is already present, set s=p in either construction. This reuses an existing natural coordinate and allocates no new slack. It is a sharing rule justified by the exact predecessor relation, not an assumption that an arbitrary stored register is already correct.

## 6. Exact list head with two fewer witnesses

The checker's actual result is

    listHead(n) = 0 if n=0, else first(unpair(pred(n)))+1.

For visible n,c and five natural witnesses p,a,b,t,s, define

    Head = Pair(p,a,b;t,s)
           + (n-p-1)^2(n^2+p^2+c^2)
           + [n(c-a-1)]^2.

Every term is nonnegative. If Head=0 and n=0, the middle term forces p=c=0, and the pairing term forces a=b=0. If n>0, the middle term forces p=n-1, the last term forces c=a+1, and Pair fixes a as the first unpaired component. These are exactly both branches of listHead.

For completeness at nil take all witnesses and c zero. At positive n, unpair p=n-1, take its canonical pairing witnesses, and set c=a+1. All terms vanish. In particular the code for a cell whose head is zero has output one, not zero.

The middle term simultaneously represents the predecessor equations and the nil-output guard. It is the exact factorization of

    (n-p-1)^2(n^2+p^2) + [c(n-p-1)]^2.

Thus no separate output-bound slack is needed. The ordinary quartic has five witnesses, 59 tree operations and 72 monomials.

## Domains and formalization boundary

Natural witness domains are essential. For example, allowing s=-1 would destroy the conditional's n=0 argument. These polynomials are not asserted to represent the same functions over unrestricted integer witnesses without a separate naturalness encoding.

The proofs use only polynomial identities, cancellation, nonnegativity of squares, and discrete natural order. They therefore suggest a short internal-arithmetic formalization, but that formalization has not been supplied here. The repository's checked [internal quartic compiler](https://github.com/VladimirReshetnikov/ProveIt/blob/2605669a532342f153b13eb6b4a0af4b54f5fa37/Computability/DiophantineConsistency/OBJECT_QUARTIC_COMPILER.md) does not internalize arbitrary new external graph-correctness proofs.

## Reproduction and what the tests establish

Run `python build_local_gadgets.py` or `python -O build_local_gadgets.py`. Both use explicit runtime checks, not removable Python assertions. The generator emits the actual expression trees, full integer coefficient lists, exact variable/degree/tree/DAG/monomial counts, and `LOCAL_CHECK_RESULTS.json`. It independently checks the branch identities, selector-elimination identity, and both factorizations, followed by 1,845,448 finite numeric controls. The universal arguments above, not the finite tests, establish correctness for all naturals.

## Cantor recoding is a different architectural option

Cantor pairing instead has the single quadratic equation

    2z=(a+b)(a+b+1)+2b.

It requires no pairing witnesses and one missing-component witness per inverse projection. This is a reason to investigate recoding, not a drop-in replacement for the existing `Nat.pair` graphs.

For two bijective pairings p and q whose components are smaller than `pair+1`, the recursively defined map tau(0)=0 and tau(p(a,b)+1)=q(tau(a),tau(b))+1 is a bijection on finite binary-tree codes. Its inverse swaps p and q; induction on the code proves both inverse identities. It conjugates zero, cons and tree projections. However it does not preserve arithmetic on numeric labels, and the found-head marker requires a different output translation: 0 maps to 0 and a+1 maps to tau(a)+1, not generally tau(a+1).

The actual checker mixes syntax trees, lists, tags, fuels, reference indices, variables and raw arithmetic data. A correct recoding therefore needs typed field-by-field translations, translated constants, parser/reference/scanner correspondence, and a new whole-checker acceptance theorem. None is supplied by merely replacing the local pairing equation. The unchanged-code reductions above avoid those additional obligations.
