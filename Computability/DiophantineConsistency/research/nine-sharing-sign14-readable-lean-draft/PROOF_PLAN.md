# Named formula to symbolic polynomial: staged proof plan

The initial source-only probe defines the reviewed named expression and
proposes the generic commutative-ring identity for staged shared07. A full
Lean bridge remains unproved. The intended stages are:

1. Prove generic `CommRing` evaluation identities for named vertical, center,
   product, sum, weight and delta against staged shared nodes. Use the
   independently externally checked local algebraic certificate as a guide,
   not as a Lean premise.
2. Use those identities and shared07 to identify staged shared38 with named
   root minus one, shared41 with root²−1, and shared42/43 with scale/scale².
3. Prove the rank identity by first checking the small ring equality arising
   from `unit = base + 1`; derive staged carry and inner values. This avoids
   expanding the full degree-62 residual in one `ring` call.
4. Prove each of the five staged residual evaluations equal to the respective
   named residual evaluations in arbitrary commutative rings. Compose the five
   equalities before expanding the sum of squares.
5. Specialize the generic seed equality to multivariate indeterminates and
   apply the fixed-input substitution to obtain equality of the named and
   audited Fin14 polynomials. Transfer exact degree and the iPRA polynomial
   bridge in separate guarded clients.

The original JSON/byte reconstruction, constant bytes, and the existing PDF
remain separate external-binding questions. The independent external readable
presentation audit does not itself produce any of these Lean theorems.
