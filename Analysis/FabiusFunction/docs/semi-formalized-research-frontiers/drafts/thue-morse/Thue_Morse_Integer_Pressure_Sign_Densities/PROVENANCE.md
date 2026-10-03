# Provenance and scope

Date: 1 October 2026

The statement concerns each fixed integer m>=2 in the cosine-phase convention of the ProveIt integer-pressure manuscript. Its coefficients are those of p_m(t/pi), with no factorial rescaling. The three sequences are c_(m,k), c_(m,2j) and c_(m,2j+1). A finite change of initial index has no effect on their lower natural densities.

The lower bound 1/[16m(m-1)^2] applies to each strict sign in each of these sequences. It is a lower-density bound, not a claim that a density exists. No positive constant independent of m or asymptotic law for the first negative degree is proved.

## Mathematical inputs

The exact matrix, atomic spectrum and real-phase simple Perron theorem come from *Integer Pressure and a Missing Taylor Coefficient*, at repository commit

    63a7a325109ba611a1816b61dfd0eb072b896a7a

and Git blob

    1444c01b4b30020f727172f0ee0060cab644f444.

An unchanged copy is included at `inputs/repository_integer_pressure.tex`.

https://github.com/VladimirReshetnikov/ProveIt/blob/63a7a325109ba611a1816b61dfd0eb072b896a7a/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/thue-morse/Thue_Morse_Integer_Pressure/article.tex

The finite radii, imaginary-axis Perron continuation and modulo-four filters were proved in *Infinite Taylor Sign Changes in Integer Thue–Morse Pressure*, 1 October 2026. Its PDF and source are included unchanged. Their hashes are listed in `SHA256SUMS`.

The proof's Darboux step is given explicitly. A primary exposition is Philippe Flajolet and Robert Sedgewick, *Analytic Combinatorics—Complex Asymptotic Methods*, 18 March 2004, Chapter VI, Theorem VI.11, printed page 158:

https://algo.inria.fr/flajolet/Teach/fascII.pdf

## Nature of the new conclusion

The finite characteristic equation has entire coefficients and nonzero constant term. Near any actual finite branch singularity, finite root monodromy and removability yield a convergent Puiseux logarithm without negative powers or logarithmic terms. Removing finitely many fractional powers makes the convergence-circle remainder C^K. Its Fourier coefficients are smaller than the leading fractional terms, which form a real finite trigonometric sum. Mean zero and positive mean square give positive lower densities of both signs.

The bound on the number of leading frequencies comes from characteristic principal minors and a Laurent discriminant. Each characteristic coefficient has Laurent half-width at most m(m-1)/2. The discriminant half-width is at most 2m(m-1)^2. Each exponential root has at most two lifts on a fixed circle, and reflection pairs those lifts under t to -t. The same count applies to each filter's own convergence circle.

No singularity is located numerically and no finite coefficient table is extrapolated. This is an ordinary mathematical argument, not a Lean formalization or an externally refereed publication. Earlier sealed papers are unchanged.
