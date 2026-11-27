# Prime endpoint densities and finite symplectic compressions

Two research notes, prepared 26 November 2026.

1. endpoint/endpoint.pdf develops quantitative return densities for the normalized prime-power ramp in the identity class modulo q. Theorem 1(i) uses Dirichlet GRH alone and works on every geometric mesh. Theorem 1(ii) requires a further estimate on the loss of rational rank among positive zero ordinates. It identifies the cyclotomic root discriminant in the endpoint density. Section 2 traces the analytic inputs to the two linked sources.
2. compression/compression.pdf solves the exact finite-law alternative of the ProveIt article's question spn:q:symplectic. The theorem computes every output likelihood and its joint distribution with intersection dimension over an arbitrary finite field. This is a separate finite-dimensional result.

## Reproduction

In either paper's directory, run pdflatex twice on the corresponding .tex file.
In endpoint/, run python3 check_endpoint.py (NumPy, SciPy and mpmath); compare with check_output.txt. The floating-point checks cover the constants, a truncated zeta formula, and resonant finite-frequency examples.
In compression/, run python3 verify.py (Python standard library); compare with verification.txt. It exhausts the indicated frame/matrix cases using exact arithmetic.
SHA256SUMS records the hashes of the papers, their source and checks, and this README.

## Sources and verification scope

The grh-lean revision inspected was 72fead102f663d5c7a407964a13dc0cf9d977207. See grh/src/Statements.lean, grh/src/Main.lean, grh/GUIDE.md, and grh/src/New/Reduction/OneSidedBound.lean.
The ProveIt revision inspected was 10802a6b360d5cdce48698261bc305e57a934b1f. See Analysis/GeneralizedRiemannHypothesis/Article/README.md and its sections/src.tex, zer.tex and spn.tex.
The merged article describes its 103-report compilation as unreviewed. Its qualitative peak statement and two special compression settings are identified in the two papers. The new arguments are mathematical proofs; the scripts provide corroborating examples. No local replay of grh-lean or formalization of these new results was performed. The endpoint paper identifies related prior work; priority in the wider literature remains open.
