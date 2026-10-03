# Report 25 mathematical review

Date: 3 October 2026

Status: PASS for the exact article identified below, subject to its explicitly stated inherited representation theorems.

Reviewed article: `report25.tex`

SHA-256: `8c726653a01afc017b1bec52437f01824e07d82742713a094043c284c30b77b7`

## Scope and method

The review covers the complete article, from the prescribed-scale positive native domain through the entire-fiber classification, exact height and counting formulas, unsmoothed second term, ranked-height inversion, the sum-of-coordinate-bitlength law, and conditional transport through the original Report 22 outer-fiber bijection. The mathematical arguments were checked directly, with comparison to the primary native proof snapshots in `source/`, the accompanying entire-fiber and second-term theorems in `proofs/`, and the original Report 22 projection theorem. The latter is represented in this release by `proofs/canonical-transport/SUMMARY.md` and its provenance records.

The review is of mathematical content. It does not certify PDF pagination, typography, the eventual ZIP inventory, or a later modification of the article. Finite executable checks supplement the proofs; they are not substituted for a universal theorem or a materialized complete padded native tuple.

## Findings

No unresolved mathematical error was found within the stated scope.

### Positive domain and the seventeen forced coordinates

The fixed arguments have precisely the prescribed dyadic scale and padded AND domain. The twenty-two listed quantities are supplied positive coordinates; computed ports and subtraction registers are not accidentally counted as extra positive witnesses. The formulas for the four fields, packed index, exponent, rounded binomial expression, Pell coordinates, and remaining quotients agree with the native selector and prescribed-scale interface. In particular the upper half-binomial sum has no erroneous factor of two.

The appeal to forward native soundness fixes values for every positive witness before a canonical converse is invoked. The positive converse is used only to certify positivity and integrality of those forced values. It does not impose the canonical auxiliary choice on the full fiber. The enumeration contains exactly seventeen names, and the thirteen unaffected literal comparisons are correctly distinguished from the three comparisons involving `f,i,j,o,y`.

### Relaxed norm and exact main-index progression

The relaxed-norm proof correctly keeps the preliminary inequality `c > A(A²−1)²`. It passes through the squarefree kernel and the least integer-coefficient norm-one unit; it makes no unsupported assertion about the full ring of integers. Strong divisibility, the proper-divisor doubling bound, and the gcd divisibility implication yield an integral Pell index divisible by `p`.

For `m=pk`, the quotient expansion modulo `c` gives the full equivalence

`c² | Δψ_A(m)` if and only if `M | m`, where `M=pc/gcd(c,Δ)`.

The identity `gcd(c,Δ)=gcd(p,Δ)` proves that `M` is a multiple of `c`, and hence that every allowed `m` satisfies the size conditions used later. Sufficiency is actually proved; the article does not silently require an even auxiliary index or an odd first Pell coordinate.

### Both normalized residues and reconstruction

Positivity of `U=jc−p` is derived from the positive supplied domain. The normalized Pell classification, oddness of its index, the two polynomial congruences, and the plus-sign step-down lemma are valid in their stated ranges. The passage from a congruence for `2n` is ordinary division of an integer equality, not cancellation in a residue ring.

Both original, unsquared minus congruences are retained after step-down. Their sign conditions force the translation parameter to be even, yielding exactly `n ≡ p` or `−p (mod 4m)`. The converse checks both signs and produces positive integral `j` and `o`. Positive representatives are exactly the baseline `p` and the two nonbaseline families `4mk−p` and `4mk+p`, with `k≥1`. Injectivity uses the strict increase of the first Pell coordinate to recover `m`, followed by the strict increase of the last coordinate to recover `n`. It does not assume that different pairs always have different heights.

### Exact native height and finite counting

All seventeen fixed coordinates are shown strictly below `c²`, including the separate estimate for the triangular coordinate. The remaining inequalities imply that the actual maximum supplied-coordinate height is exactly `y=ψ_(R_m)(n)` for every pair. Thus the native fiber has no fixed-coordinate initial plateau. The least-height pair `(M,p)` is unique; no unnecessary claim of componentwise minimality is used.

The two-floor formula counts both distinct residues and includes the baseline exactly once. It vanishes before the baseline in a given slice. Its real inverse, integer-floor replacement, monotone finite cutoff, and explicit logarithmic upper cutoff are valid also at exact height boundaries. The periodic fixed-slice phase and the convergent inverse-phase expansion are correct, with a clear warning that an approximate smooth phase cannot be inserted into discontinuous floors to obtain exact counts.

### Leading coefficient and unsmoothed second term

The baseline contributes `1/[M(p−1)λ]` to the coefficient of `log H`; the factor `p−1` correctly includes the varying Pell denominator. The nonbaseline contribution retains the exact convergent series in `β_(Mℓ)`. The proof does not sum a fixed-slice bounded error over the full linear-sized baseline range.

For each sign separately, the exact energy retains its bounded Pell correction. Uniform row and column estimates are proved by inequalities before rounding. The exact boundary choice `K_σ=q_σ(T,L)` gives a genuine admitted overlap rectangle and excludes every point beyond both strips. This proves the hyperbola identity even when `T` is exactly an energy. No unproved cancellation of floor phases or generic-position hypothesis is used.

The exact slope tail, Euler-summation constant, quadratic boundary cancellation, and the choice `L=floor(T^(1/3))` yield the error `O(T^(1/3))`. The two signs give the square-root coefficient `ζ(1/2)/(M√λ)`. The integral remainder and negative sign of `ζ(1/2)` agree with the primary NIST formulas [DLMF 25.2.8](https://dlmf.nist.gov/25.2.E8) and [DLMF 25.2.3](https://dlmf.nist.gov/25.2.E3), checked on the review date.

### Multiplicity, inversion, and outer transport

The counting function counts tuples. The inequality `F(T_v−1)<v≤F(T_v)` makes inversion valid without a separate bound on tied-height multiplicity. Both the coefficient and sign of the square-root correction in `log H_v` are correct. The article explicitly declines to infer a relative multiplicative height equivalent from an unbounded logarithmic remainder. The maximum-coordinate binary-length substitution uses `H=2^b−1`.

The original Report 22 result is used conditionally and only for accepted nonempty fibers in the retained clock constructions. Fixing the outer tuple and inserting it into every native witness gives the stated bijection. The complete height is `max(C_out,y)`, with count zero below the outer cutoff and the native count above it. Such a finite outer cutoff leaves the two asymptotic coefficients unchanged. Initially halted no-witness circuits and a new audit of the old compiler are correctly excluded.

### Sum of all coordinate bit lengths

The additional total-bitlength section is included in this PASS. The exact product identity cancels `f` algebraically without omitting its separate rounded bit cost. The three hyperbolic logarithms give `log(fijoy)=(3n−2)β_m+O(1)` with a single bound uniform over the entire admissible pair family. In particular the baseline is governed by `3p−2`, not `3(p−1)`.

For the exact comparison energy, the nonbaseline slopes are `12Mℓβ_(Mℓ)` and the quadratic model coefficient is `12λM²`. Both sign energies are positive and strictly increasing, so the sign-specific exact rectangle proof applies. Its leading coefficient and square-root coefficient agree with the displayed formulas, including the exact correction relating `κ_s` to `κ/3`.

Rounding five separate coordinate logarithms introduces a bounded discrepancy, and the seventeen fixed bit costs introduce only a fixed constant. The resulting global two-sided count sandwich is valid at powers of two, real budget cutoffs, and ties. It does not claim stability of individual floors or equidistribution of rounding phases. The ranked total-bit formula uses its own ordering and is correctly distinguished from maximum-height ordering.

## Executable corroboration

The following read-only commands were run successfully, both normally and with Python optimization enabled:

- `python audit_dependency.py` and `python -O audit_dependency.py`
- `python check_entire_fiber.py` and `python -O check_entire_fiber.py`
- `python check_second_term.py` and `python -O check_second_term.py`
- `python check_total_bitlength.py` and `python -O check_total_bitlength.py`
- `python check_total_bitlength_review.py` and `python -O check_total_bitlength_review.py`

The dependency replay confirmed four retained fixtures, all sixty-four gates, all sixteen comparison residuals, exactly three varying comparisons, seventeen fixed supplied names, and rejection of its three in-memory failure mutations. The auxiliary replay checked the progression, reconstruction, signed residues, native-coordinate height inequalities and exact finite-count boundaries. The second-term replay matched its saved receipt, including twenty-four exact Pell thresholds, 612 exact hyperbola identities, and eight exact-integer asymptotic model counts. The total-bitlength replay matched its receipt for eighteen auxiliary tuples, fifty-four cutoff checks, eighteen detected product-denominator mutations and six synthetic rounding/tie fixtures; the separate review checker passed nine exact auxiliary tuples and three direct rounding-boundary fixtures. These claims are bounded computational evidence only.

## Limits of the conclusion

This PASS relies on the explicitly inherited native soundness and positive-completeness results, and on the original Report 22 theorem for the transport section. It proves no circuit minimality, uncharged canonicalization, general finite-fold theorem, uniform asymptotic onset across varying external inputs, or literature-wide novelty claim. No full astronomical padded native witness was constructed. The mathematical review did not modify any article or source file.
