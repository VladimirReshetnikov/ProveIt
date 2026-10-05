# Independent review of the exact A113226 EGF

Reviewed1October2026: `exact_egf_proof.md`. The exact generating-function argument passes without correction.

The minimum previous ascent top and last label form a sufficient state. If the last label y exceeds the minimum top m, that earlier ascent is necessarily disjoint from the new ascent; any ascent is forbidden. If y<m, none of the earlier ascent tops can precede y in a12-34 occurrence. If y=m, the minimum is the immediately preceding ascent top, and it overlaps the proposed new ascent; every other ascent top is larger. Thus equality must be permitted. Distinct continuous labels remove unrelated equality cases, but the state y=m itself occurs with positive probability and needs its separate function G.

I checked the continuation integrals in all three regions, the uniform convergence near z=0, and the solution of the y>m Volterra equation. The left-limit condition and differential equation for y<m give the stated integral formula; integrating it produces D(m)G(m)=1+z integral(1-exp(-zu))G(u)du. The differentiation, G(0)=exp(z), and x=exp(zm) substitution are exact. Since P_E(E)=E and P_E(1)=1, the logarithmic integral identity reduces G(1) to the claimed exponential integral. The empty-state identity A=H(1)=G(1) uses the correct probability/EGF normalization.

The representations of Elizalde's b_k and c_k satisfy the cited second-derivative recurrences by differentiating the two convolution factors. Their geometric sum is exactly T, and T=S+exp(z)-1. This relation is a consistency/positioning check, not an inference of equality from upper and lower bounds.

Finally, direct integration gives the displayed arctangent form and T(z)=pi/sqrt(rho-z)+rho/2-3+O(sqrt(rho-z)). This review approves the analytic germ and formal EGF. It does not turn the local singular expansion alone into a coefficient theorem; that still requires the separately written contour proof.
