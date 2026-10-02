# Comparison with relaxed binary trees

Conditional on both forward all-orders theorems until the compacted proof's independent audit is complete. This is an algebraic corollary, not an additional spectral argument.

Let r_n count relaxed binary trees and c_n compacted ones, indexed by internal nodes; write their positive amplitudes gamma_r and gamma_c. Their leading factorial, exponential and Airy factors coincide. The respective powers of n are 1 and 3/4, and both first logarithmic correction coefficients are 53z^2/90. The second coefficients are 44z/27 for relaxed and 271z/216 for compacted; the third are 141/140-1304z^3/42525 and 393/1120-1304z^3/42525.

Therefore

\[
\log\frac{c_n}{r_n}
=\log\frac{\gamma_c}{\gamma_r}-\frac14\log n
-\frac{3z}{8}n^{-2/3}-\frac{21}{32}n^{-1}+O(n^{-4/3}),
\]

and hence

\[
\frac{c_n}{r_n}=\frac{\gamma_c}{\gamma_r}n^{-1/4}
\left(1-\frac{3z}{8}n^{-2/3}-\frac{21}{32}n^{-1}+O(n^{-4/3})\right).
\]

The order n^(-1/3) correction cancels. Since z is negative, the first surviving correction is positive. No certified numerical value for the amplitude ratio is supplied.

For the explicit smooth logarithmic models h_c and h_r with their true amplitudes, let n_r=h_r^(-1)(T) and n_c=h_c^(-1)(T). Subtracting the models and using the mean-value theorem gives

\[
n_c-n_r=\frac{\frac14\log n_r-\log(\gamma_c/\gamma_r)}{\log(4n_r)}
+O(n_r^{-2/3}/\log n_r).
\]

In particular this model-inverse gap tends to 1/4. This is a real-model statement; integer threshold differences exhibit rounding and need not converge.

For the exact thresholds N_c(Y) and N_r(Y), c_n<=r_n and eventual c_(n+1)>r_n imply

\[
N_r(Y)\le N_c(Y)\le N_r(Y)+1
\]

for sufficiently large Y. This coarser discrete fact already follows from the established theta estimates and should not be claimed as new to the amplitude convergence proof.
