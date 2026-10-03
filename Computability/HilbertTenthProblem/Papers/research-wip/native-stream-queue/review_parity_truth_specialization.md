# Independent review of the parity specialization

**PASS for the stated natural-witness interfaces.** The complete isolated parity penalties cost 8 operations for an already evaluated signed input, 10 when its quotient split is canonical, and 7 for a known-natural input. Explicitly materializing the even-truth output costs one additional subtraction. These are fixed-modulus components; they do not reduce the complete 87-operation universal polynomial.

The source is pinned to SHA-256 `fabf4eef1b31f4cf6695cc5907e2d56f5bd2fac1e9ab8f0ad5b375cbc0100bf7`. The [independent checker](review_parity_truth_specialization.py) compiles those authenticated bytes directly, bypassing bytecode caches, calls only the circuit builders, and interprets every emitted gate itself. It never calls the candidate evaluator, canonical-witness builder or verification routine. The [receipt](review_parity_truth_specialization.json) includes expanded complete polynomials and hashes of all eighteen full gate lists.

## Independent correctness argument

For signed integer L and natural p,m,b, put A=L−2(p−m)−b. Since b(b−1) is nonnegative for every integer b,

```
P8 = A² + b(b−1) = 0
```

forces b to be zero or one and L=2(p−m)+b. Conversely write q=floor(L/2), r=L mod 2. All natural zeros are exactly

```
p=max(q,0)+k, m=max(−q,0)+k, b=r, k∈N.
```

Thus the bit is fixed but the fiber is infinite. Adding p*m gives P10. Every term is now nonnegative on natural witnesses, and p*m=0 fixes k=0, giving one witness for every signed L. For L≥0, q≥0 and m=0; the two-coordinate polynomial `(L−2q−b)²+b(b−1)` gives the unique P7 witness. This restriction cannot represent negative L using natural q.

At the canonical modulus-two parent's zeros, s=0 and h=1−b. On this graph its full polynomial is A²+(p*m)²+[b(b−1)]². Replacing the two product squares by their products preserves natural zeros, giving P10. Dropping p*m gives P8 and loses uniqueness. This is a sequence of graph projection and natural-zero equivalences, not an unchanged-coordinate polynomial identity.

The surrounding compiler may share the parity truth but must preserve the private-coordinate contract. For example, L=0,p=m=1,b=0 is a P8 zero satisfying the additional condition p*m=1, whereas no P10 zero satisfies it. Replacing the atom in a formula that observes those private quotient coordinates is therefore unsound. Real witnesses also change the zero set: L=1,q=0,b=1/2 gives a P7 zero. Signed helpers break the canonical construction: L=3,p=1,m=−1,b=0 gives P10=0 with the wrong even bit. These are explicit exclusions, not tests of supported inputs.

## Complete Boolean example

For two inputs the accepted NAND of their even predicates is true exactly when at least one input is odd. The emitted relation uses an explicit output z and the row `z−1+(b1−1)(b2−1)`; the existing b−1 registers pay the equivalent truth-product expression. All source rows, Boolean terms, squares and final additions are charged.

| Input convention | Supplied-output NAND | With acceptance guard | Substitute z=1 | Fused accepted predicate |
|---|---:|---:|---:|---:|
| Signed, existential quotient split | 22 | 24 | 20 | 17 |
| Signed, canonical quotient split | 26 | 28 | 24 | 21 |
| Known-natural | 20 | 22 | 18 | 15 |

The last column replaces the two separate bit penalties and squared truth product by

```
B(x,y) = (x+y−1)²−xy.
```

This is nonnegative even on all integer pairs, and vanishes precisely at (0,1),(1,0),(1,1). If xy≤0, equality forces x+y=1 and xy=0. If xy>0 the coordinates have the same sign; their sum S is at least two or at most minus two. Using xy≤S²/4 shows strict positivity for S≥3 or S≤−2; S=2 gives only (1,1). Hence the complete fused polynomial enforces both bits and the accepted NAND condition. Adding the two quotient-row squares, and the canonical products when requested, proves the complete natural-domain interface.

Substituting z=1 into the accepted-output circuit gives the projected polynomial identically. If g=(b1−1)(b2−1), the projected polynomial minus the fused polynomial is exactly g²−g on every tuple. The fusion therefore changes polynomial values; correctness follows from the preceding nonnegativity and zero-set argument. The fused circuit has degree two; the other NAND variants have exact degree four. These different interfaces are not interchangeable counts for one unchanged circuit.

## Verification and limits

All eighteen actual complete gate lists match independently handwritten polynomials coefficientwise, have their claimed exact degrees and charged M/A ledgers, and contain no dead gate. The checker examines 24,892 unfiltered natural atom tuples and 10,201 signed integer pairs for B, plus materialized truth and the three domain/private-coordinate counterexamples above. The finite checks support the explicit unbounded argument; they do not establish it by enumeration.

```
python review_parity_truth_specialization.py \
  --source parity_truth_specialization.py \
  --output fresh_parity_review.json \
  --expect review_parity_truth_specialization.json
```

This review establishes the emitted circuits and their stated interfaces. It supplies no general quantifier-elimination algorithm, parity-atom optimality result, ordinary-input evaluation, unbounded-history compression, or arithmetic improvement to a universal equation. Source-input L is already evaluated, and every listed witness is natural, including zero.
