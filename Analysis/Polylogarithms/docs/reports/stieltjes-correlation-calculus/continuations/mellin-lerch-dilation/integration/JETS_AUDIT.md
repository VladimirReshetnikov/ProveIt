# Independent audit of `sections/03-jets.tex`

Audit performed against the local article source on 2026-10-10. No changes were made to the article source.

## Result

**Careful pass.** No incorrect displayed formula, example value, coefficient, sign, or unstated nonremovable singularity was found. This audit covers the Gamma/Stieltjes jets and anchored primitives. The underlying Mellin identity, branch domain, and uniform domination estimates were treated as hypotheses for the kernel identities; the separate Mellin audit checks those hypotheses.

## Algebraic checks

- The Gamma formula and its arbitrary parameter derivative follow from the same Leibniz expansion: differentiating the kernel (j) times contributes ((-1)^j\log^j x); differentiating the sine (r-j) times contributes (\pi^{r-j}\sin(\pi q+(r-j)\pi/2)). The stated binomial coefficients and overall sign are correct. The apparent issue at (q=1) is removable, with the kernel value (-\gamma).
- Both half-argument examples have the correct factor of two under (x=t^2). Their signs agree respectively with \(\log\Gamma(1/2)=\frac12\log\pi\) and the duplication formula for the generalized Stieltjes constants.
- Both kernels in the Stieltjes recurrence have value ((-1)^m m\gamma_{m-1}) for (m\ge1), and each has value (-1) at (m=0). The stated integration by parts has vanishing boundary terms.
- The resonant germ \((s)_r\zeta(s+r)\) at \(s=1-r\) has exactly the stated elementary-symmetric/harmonic prefactor. Its three concrete \(s=-1\) examples reduce to \(1/2\), \((\gamma-1)/2\), and \(-\gamma-\gamma_1\). These were independently expanded symbolically.
- The third-denominator example was independently reduced symbolically to \(\frac14\log(2\pi)-\frac14-\frac12\gamma\).
- The spectral-derivative formula for the first anchored primitive has the correct factor \(1/(m+1)\) and the correct \(-a(-1)^m\gamma_m\) term. Its \(m=0\) value is \(\log\Gamma(1-a)-\gamma a\).
- The order ladder in the final paragraph is correct whenever the locally uniform differentiation hypotheses in the preceding Mellin section hold.

## Entire spectral parameter and antiderivative singularities

The first anchored primitive has two apparent spectral singularities. At \(s=1\), the pole of the divided zeta difference cancels the pole of \(-a\zeta(s)\); at \(s=2\), the numerator's two zeta residues cancel. The anchored-integral representation proves an entire continuation in \(s\) and fixes the additive constant.

For the higher primitive \(P_{s,r}\), the denominator \((s-r)_r\) vanishes at \(s=1,\ldots,r\). These are removable in the complete expression, including the final \(-a^r\zeta(s)/r!\) term. At \(s=r+1\), the numerator contains zeta poles with cancelling residues. Products of a vanishing rising factorial and a zeta pole must be interpreted jointly; the source's analytic-continuation prescription covers this. The integral representation

\[
\frac{a^r}{(r-1)!}\int_0^1(1-t)^{r-1}
\bigl[\zeta(s,1-at)-\zeta(s)\bigr],dt
\]

is entire in \(s\), gives zero initial derivatives through order \(r-1\), and yields the desired Hurwitz-zeta difference after \(r\) derivatives. For the stated strip in \(a\), the straight segment satisfies \(\Re(1-at)>0\), so no hidden Hurwitz argument crossing occurs. The stronger extension to the whole half-plane \(\Re a<1\) is possible for this primitive alone, but is not needed by the article.

## Independent numerical evidence

`code/check_jets_section.py` and its JSON output record 11 numerical checks at 42 decimal digits, plus exact symbolic assertions. All passed, with the largest numerical absolute discrepancy below \(3.0\times10^{-43}\).

The higher-primitive finite formula was evaluated independently of the anchored integral at generic complex parameters and at removable spectral values \((s,r)=(1,1),(1,3),(2,3),(3,4),(4,3)\). At removable values, a Cauchy mean of the complete finite expression was used. This includes both vanishing-denominator cases and the numerator-pole case \(s=r+1\). Further checks covered the elementary \(s=0\) value, the Gamma primitive at \(s=1\), and direct anchored Stieltjes integrals for orders 1 and 2. The rational \(\operatorname{Li}_{-1}\) logarithmic example was also verified through an independent beta-integral derivative.

These numerical checks are evidence for the audited identities, not the proofs. In particular, no claim is made that every polylogarithm order-derivative kernel was independently evaluated by direct quadrature; the rigorous algebraic checks for those use the master transform whose analytic proof is separately audited.
