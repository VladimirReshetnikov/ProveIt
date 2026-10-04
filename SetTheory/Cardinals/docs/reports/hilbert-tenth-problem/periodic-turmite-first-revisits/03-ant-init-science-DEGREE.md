# Exact degree of the initialization polynomial

This is an optional addendum to `COMPOSITION.md`. It leaves the conjunction source and every preceding gate/witness count unchanged. All degrees below are total degrees in W,Wp,Q,InitialHead,InitialMemoryPlus,RawLeft,RawRight and the 396 newly quantified positive witnesses, with all prescribed fixed numerals treated as coefficients. This is before substituting any parent-history or endpoint expressions.

The source has 234 residuals. Propagate an upper degree at every arithmetic gate: multiplication adds upper degrees; addition or subtraction takes their maximum. Constants have degree zero and every independent port/witness has degree one. The exact variable power G=W^v has degree v=576000. `audit_degree.py` independently performs this propagation along the complete 2,306,387-operation source and records each residual bound.

Exactly two residuals have upper degree 2v=1,152,000: zero-based residuals 16 and 130. They are the modulus equations in the two EXP(G,length,radixPower) macros, namely

    2*a*G - (T + G*G + 1).

Here a and T are independent positive witnesses (with a itself represented as a positive witness plus one), so the first term has degree v+1 and T+1 has degree one. The unique top homogeneous term in each residual is therefore -W^(2v). Every other residual has degree strictly less than 2v. The next-largest propagated bound is 1,127,949, from the final memory relation. Prescribed huge coefficients cannot cancel the two displayed leading terms.

For residuals R_1,...,R_234, set

    F = R_1^2 + ... + R_234^2.

Then over integer assignments F=0 exactly when all 234 equations hold. Its exact top homogeneous term is 2W^(4v), so its exact total degree is **4v=2,304,000**. All 396 witness domains remain strictly positive.

The unoptimized conversion constructs all 234 residual differences, all 234 squares, and a chain of 233 additions. Its extra cost is 234M+467A=701 operations. Consequently this initializer-only single polynomial has

    1,153,426M + 1,153,662A = 2,307,088 operations,
    one equation,
    396 newly quantified positive witnesses,
    exact degree 2,304,000.

No residual or subtraction is made free even if future simplification could save it. `polynomial_initialization.py` emits exactly this single-equation source: the original equality assertions are retained as expression pairs, not also asserted, and only F=0 is asserted. Its full streamed receipt records the new source hash and final output wire. It shares the same G chain and recoder expressions as the conjunction.

These are initializer counts and degree only. The parent-history constraints are still necessary for W,Wp,Q to describe a valid rectangle, and neither their arithmetic nor an endpoint selector has been added to F. Thus F alone is not a universal halting polynomial and its degree is not a global composed degree.
