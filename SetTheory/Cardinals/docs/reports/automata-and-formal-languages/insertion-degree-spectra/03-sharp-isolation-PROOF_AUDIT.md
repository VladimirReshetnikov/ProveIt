# Proof audit

## Logical chain

1. Literal source masks give minimum degree equal to the number of receiving gaps for a fixed unary-source target.
2. Taking the minimum over target words gives the language degree formula.
3. At a degree-m exception, accepted deficits of total m must be binary. This gives the largest admissible target language and loses no realizations.
4. Support has at least m coordinates. Capped compositions force T > g(m-1) for m >= 3; the equality neighbor has deficit (m-1,1,0,...), of degree 2 < m.
5. For a nonexceptional output of the same total, at most one one-piece predecessor lies below the center. Only unique-eligible-coordinate outputs can obstruct maximal-language coverage.
6. Their deficits obey lower bounds h_i=(v_i-m+1)_+ outside the unique coordinate. If the outside sum is below m, a nonbinary deficit can always be completed within the capacities. At equality, its being binary is the exact boundary alternative.
7. Minimizing excess mass over the number of high coordinates proves tau(3)=12 and tau(m)=5m-2 for m>=4. A base center plus zero padding and extra mass in a maximum coordinate attains every permitted parameter triple.
8. The fixed-gap length formula is strictly increasing in g. All shortest centers have g=m, excluding the boundary branch. Equality in the mass estimates gives the complete small-case orbit lists.
9. Mandatory targets are exactly unique-special or singleton-predecessor requirements. At most one forbidden predecessor reduces the test to targets with at most two coordinates >=m, plus the forced special target.
10. At shortest degree 3, the complete target and output orbit lists reduce the remaining covering problem to nine disjoint pairs. This proves all language counts and the minimum 37 without relying on program output.

## Important scope checks

- The classification is for m>=3; the length-3 degree-2 example is treated separately.
- Coordinates may be zero; consecutive or endpoint b's are allowed. Positivity is inferred only after g=m is proved for shortest realizations.
- All target words have the same required letter counts.
- Full coverage is not silently dropped.
- The exception is unique and has degree exactly the inserted length.
- No uniqueness of an insertion mask is assumed.
- The strict height condition alone is not treated as necessary: the boundary multiset (M,1,...,1), with m outside ones, is retained.
- The linear-time assertion counts arithmetic operations, not bit operations of unit cost on arbitrarily large integers.
- The count formula counts ordered centers, not center orbits or target languages.
- Residue-wise additivity of target minima is stated with g=m and one forced special target; multiple special targets can couple residue classes.
- Mandatory targets need not collectively suffice. Individual removability does not imply simultaneous removability.
- Minimum target size 37 is for the shortest degree-three problem only.

## Independent finite checks

`data/verification.json` is the authoritative executed receipt. Highlights:

- Literal-mask enumeration is independent of gap-vector degree calculations.
- The direct full-output test does not use the scalar height/volume classifier.
- The local deficit enumerator does use the separately proved volume obstruction but does not use the h/H/M classification.
- Exact ordered-center counts are compared with enumeration of nondecreasing vectors and permutation orbit sizes through m=7.
- Mandatory-target formulas are compared with complete singleton-predecessor constraints for every small extremal type.
- All 19,683 degree-three languages specified by the matching are checked.
- A 37-target example is independently verified by literal insertion masks.

The code is not a formal proof of the universal claims. The manuscript supplies those proofs. The package has not undergone independent peer review or proof-assistant verification.
