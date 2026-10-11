# Peer review of the arbitrary-ray Tornheim quadratic jet

Reviewed `agent_spectral/tornheim_rays.tex` independently.

1. The six Jonquiere local subtractions exhaust all terms with exponent at most zero near A=B=0. The remaining integrand is integrable for C near zero, after shrinking the parameter neighborhood, and stays integrable after any fixed number of parameter derivatives. This establishes joint holomorphy of H.
2. The displayed meromorphic expression follows by integrating the six terms in a common convergence domain with C sufficiently large, then continuing C to zero. There is no need for the original Mellin integral to converge near the origin.
3. The shifted Hurwitz function `g_t=x^{t-1}+h_t` has `h_0(0)=gamma`, `h_0'(0)=-zeta(2)`. The only cubic poles at t=0 arise from `3*x^{t-1}*h_t^2` and the linear Taylor term of `3*x^{2t-2}*h_t`; their residues are `3 gamma^2` and `-3 zeta(2)/2`. The pure cubic singular term has denominator `3t-2` and contributes no pole at zero.
4. The Fourier triple identity, pair identity and zero mean give the stated diagonal coefficient equation. Solving its constant, linear and quadratic coefficients independently gives `1/3`, `log(2 pi)`, and `log(2 pi)^2-4 zeta''(0)`.
5. The exact axis `T(0,0,C)=zeta(C-1)-zeta(C)` gives the stated H constant and H_C. Symmetry plus the diagonal quadratic jet fixes H_A=H_B.
6. Independently expanding the local meromorphic expression to second order produces all three claimed arbitrary-ray formulas exactly. The symbolic residual at every tested degree is identically zero as a rational function of a,b,c.
7. The c=0 specialization agrees with the independent factorization `T(A,B,0)=zeta(A)zeta(B)`. The a=b=0 specialization agrees with the exact counting identity in step 5.

No analytic gap or coefficient error was found. The admissibility condition `(a+c)(b+c) != 0` is sufficient for the stated ray restriction. No claim about paths contained in those polar hyperplanes is needed.

The separate script and JSON results record the symbolic calculation.
