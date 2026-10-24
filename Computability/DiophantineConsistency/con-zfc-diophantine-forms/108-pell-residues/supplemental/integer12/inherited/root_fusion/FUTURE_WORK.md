# Further research questions

The released endpoint is frozen at thirteen unrestricted integer variables,
exact degree 1088, and 195 live binary arithmetic operations. The questions
below are proposals, not additional equations or established improvements.

1. **Can a guard coordinate be removed?** The final equation still supplies
   the nearest-square coordinate `t` in the joint positivity guard. A useful
   next step would be an exact estimate for the canonical ratio `eta/k` from
   the truncated-binomial/Pell construction. If that estimate supplied an
   explicit polynomial replacement for `t` while preserving a positive
   guard, it could reduce the integer variable count. No such replacement
   has been proved. The canonical scale `Y` is not a freely adjustable
   parameter, so an argument based on choosing it arbitrarily would be
   insufficient.

2. **How much further can integral centering reduce the degree?** The
   auxiliary shear lowers the unshifted norm degree, while the four-root
   companion also benefits from the strong and first-Pell centers. The
   negative leading square of the remaining guard radicand obstructs the
   same straightforward cancellation in the five-root endpoint. A useful
   investigation is to characterize which real polynomial centers can
   change that leading norm term and which necessarily leave it nonzero.

3. **Can the same construction use a smaller complete coefficient tuple?**
   Most new lemmas use only the determinant inequalities, the odd fixed
   radix exponent, and the signed source kernel. Repeating the canonical
   determinant calibration for a smaller native tuple may reduce coefficient
   height and storage without changing the norm. This requires a new
   coherent calibration and regenerated guard constants; ports from different
   source tuples must not be mixed.

4. **Can additional scale conditions enter one coprime carrier?** The
   successful step uses `H = 3 (mod q)` and `q = 2 (mod 3)` to prove
   `gcd(H,2q^2)=1` before decoding. Further coordinate elimination should
   begin with an equally explicit gcd theorem. In particular, coprimality
   with `q-1` does not follow from the displayed equations and should not
   be assumed.

5. **What is the best degree/operation tradeoff within this exact norm?**
   The supplied 195-operation circuit is a concrete evaluator, not an
   arithmetic-circuit optimum. Exact common-subexpression and addition-chain
   improvements can be sought without changing the polynomial. Alternative
   equivalent polynomials should continue to report domain, degree, operation
   count, and coefficient costs separately.

6. **Can the native calibration be independently replayed end to end?**
   The new algebra has explicit witness maps and exact finite audits. Its
   interpretation still imports the named ordinary native/compiler and
   refutation-calibration theorems. A separate review should follow the actual
   fixed numerals through every ordinary source theorem, distinguishing this
   task from the repository's remaining proof-assistant formalization work.
