# Independent audit: full balanced 2+2 gamma real-rootedness

## Verdict and scope

Approved: for two source centers, two sink centers, all four source-to-sink core arcs, and an arbitrary independent exterior with arcs source→exterior→sink, the full directed-support gamma polynomial is real-rooted. This includes arbitrary nonnegative independent tail/head vertex activities. Every nonconstant root is negative. The stronger weighted signed physical-monomer polynomial is real stable.

The proof counts feasible ordered disjoint endpoint supports, not matching witnesses. It needs neither transitivity nor a bound on the number of physical exterior vertices. This approval does not extend to incomplete 2+2 cores, 1+3 cores, arbitrary edge activities, or all degree-four preorders.

Audited proof: `../BALANCED_REAL_ROOTEDNESS_PROOF.md`, frozen SHA256 `7dc35c81102126e4054fbd4c301fa9f6734194ad92c4c59166e2e1cbc4cba62b`. Its post-review change was status-only.

## Ordinary proof checks

1. **Auxiliary quadratic.** For independent parallel-class sums r_i, the invertible change w=s+L/√2 gives F=w²−Σr_i²/2. Thus its quadratic form has exactly one positive direction. For an alleged upper-half-plane zero x+iy, the imaginary equation makes x form-orthogonal to y; F(y)>0 implies F(x)≤0, contradicting the real equation F(x)=F(y). Nonnegative parallel-class substitutions preserve the upper half-plane. Private dummies ensure rank two; exterior loops are omitted from both B and L.

2. **Coupling.** The complete (2,2)-bounded operator symbol is (ab−1)². Variables a,b in the upper half-plane cannot satisfy b=1/a. Untouched variables contribute independent factors (z+w)^κ, so the coefficientwise extension, rather than only a scalar-valued operator, is justified. Applying it to the stable auxiliary product gives H=B_PB_Q−L_PL_Q+1. The constant coefficient is 1, ruling out the zero output.

3. **Two-copy identification.** Each side's private dummy for a center records that center's unmatched monomer. An exterior singleton's side-basis coefficient records each admissible selected center subset once. Exterior pairs contribute one exactly when Hall's rank-two condition holds. Inversion −1/z and multiplication by the exterior monomer product gives the signed side polynomial. For one core arc, every nonloop exterior singleton contributes once to L, even when it has two center neighbors. This is precisely the required endpoint-support count. Completeness of the core supplies the remaining core connection. Two core arcs contribute one support, not the two matching witnesses. The number of core arcs is fixed by the endpoint support, so these categories neither overlap nor omit a support.

4. **Activities and merging.** Multiplying by ∏w_i and replacing each monomer z_i by z_i/w_i gives activity w_i to used vertices and no activity to unmatched monomers. Source core vertices only have tail roles; sink core vertices only have head roles. The two exterior copies carry their independent role activities. The physical-copy merge has symbol z+r+s; thus it preserves stability. Its four monomial images enforce exactly the three physical states: unused, tail, head, while excluding double use. The empty support's leading coefficient remains 1. Zero activities follow by a nonzero Hurwitz limit.

5. **Univariate conclusion.** The diagonal monomer polynomial is s^NΓ(−s^−2). It is nonzero, real stable, hence real-rooted. A gamma root other than a negative real number would produce a nonreal nonzero monomer root. Gamma has constant coefficient 1, so zero is excluded. Newton then gives actual-degree ULC; degree-four specialization follows when gamma_4>0.

## Primary source verification

The original Borcea–Brändén paper, [The Lee–Yang and Pólya–Schur Programs I](https://arxiv.org/pdf/0809.0401), Theorem 1.1 (printed page 4), directly supplies the plus-sign finite-degree algebraic-symbol criterion. Definition preceding that theorem fixes the binomial factors, including the factor 4 on the st term. Lemma 1.7 (printed page 6) supplies positive scaling, negative reciprocal substitution, real specialization, and variable identification. Theorem 1.6 is the nonzero-or-zero multivariate Hurwitz limit. These primary statements were independently inspected; the producer's survey citation is consistent with them.

## Independent exact supplementary test

`check_full_monomer.cpp` imports no producer code. It enumerates every multiset of up to four exterior types, including type 0 isolates, then recounts feasible ordered disjoint supports directly by Hall's condition. It separately expands the two-copy B/L formula, attaches role weights, and merges copy monomers. It compares every resulting physical monomial coefficient.

All 4,845 type multisets passed in three activity assignments: unit weights, positive integer role weights, and nonnegative weights including zeros. This gives 14,535 exact multivariate identities and 269,050 feasible supports examined. The AddressSanitizer/UndefinedBehaviorSanitizer run also passed without diagnostics, with leak detection disabled because this execution environment does not support LeakSanitizer. These bounded checks support the identification and implementation, while the ordinary stability argument proves the unbounded-population result.
