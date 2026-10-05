# Independent review of A126348

Reviewed the finalized modular version of `../derivation.md` on 2026-10-01. The analytic claims pass, including the stated all-orders remainder and the range inverse. The conclusions do not include an effective numerical onset, an unconditional exact ceiling formula, or exponentially small coefficient sectors.

## Exact normalization

With `F=(-q/δ;q)_∞`, Jacobi's triple product uses the argument `-q/δ`. The bilateral exponent is `-tk²/2+(λ-t/2)k`. Completing the Gaussian square contributes `λ²/(2t)-λ/2+t/8`; division by the Euler-product modular transformation contributes `π²/(6t)-t/24`. The resulting linear term is therefore exactly `t/12`.

The identities were checked against the primary DLMF entries:

- https://dlmf.nist.gov/17.8.E1
- https://dlmf.nist.gov/17.2.E6_1

The partner logarithm is `G=Σ_{j>=1}(-1)^(j+1)δ^j/[j(1-e^(-jt))]`, including its `j=1` constant. The limiting logarithmic constant is consequently `-1`.

## Complex and all-orders uniformity

On the disk `|z-t|<=t/(K L²)`, the denominator lower bound uses `Re z>0`, so there is no small-denominator resonance in the small-fugacity series. Its tail after `j=J+1` begins at order `t^(J+1)`. Each remaining summand is analytic at zero after its removable singularity is filled. The only logarithm is the explicit `Log(1/z)`, giving at most the stated affine logarithmic dependence.

The theta displacement satisfies `|Im(λ(z)/z)|=O(1/(tL))`, while the Gaussian dual suppression is a fixed positive multiple of `m²/t`. The latter dominates uniformly. Thus the modular remainder is exponentially small throughout the major neighborhood, not merely on the positive real axis.

The global triangle-inequality estimate uses approximately `L/t` factors with `r^k/δ>=1` and controls every nonzero lattice arc. Its bound at the major-neighborhood endpoint is `exp(-c/(tL³))`, which stays negligible after the Gaussian normalization.

For the central expansion, the auxiliary radius

`ρ=c_J/[(1+L)^(1/2)(1+|X|)^3]`

bounds the exact analytic phase correction and the finite logarithmic amplitude uniformly. On this circle `|w|` is small, `Q=O(ρ |X|³/(1+L))`, and `R_J=O_J(ρ²(1+L))`. Cauchy's remainder after degree `2J+1` is therefore exactly of the form

`O_J(ε^(2J+2)(1+L)^(J+1)(1+|X|)^(6J+6))`.

The actual auxiliary parameter obeys `ε<=ρ/2` uniformly on `|X|<=ε^(-1/4)`. Gaussian integration produces the announced `O_J(t^(J+1)(1+L)^(J+1))`, with no hidden extra logarithmic power. Odd coefficients are odd in `X`, so their symmetric integral vanishes. The intermediate arc has a uniform negative quadratic phase, and the amplitude perturbation is only `O(t(1+L))`. These facts justify all remainder comparisons.

## Coefficient and inverse checks

The two displacement terms in `C_2` are necessary and have the displayed signs. They come respectively from the quadratic expansion of `(1+w)P_1(L-log(1+w))` and its odd linear term paired with the cubic phase.

The identities `H'=e^L V`, `N'=e^(2L)V` and `dN/dH=e^L` are exact. The first two Lagrange terms give `e^L T-C_1` and `(T²+2TT')/(2V)`. The omitted forward logarithmic error `O(t²L²)` becomes `O(tL²)` in index; ordinary finite Taylor reversion gives the stated, slightly weaker, `O(t(1+L)^3)` bound for the explicit inverse. The optional next coefficient `B_1` has the correct signs. No differentiation of an uncontrolled asymptotic remainder is needed: finite analytic models plus monotone bracketing suffice.

Strict monotonicity follows from the separated `1/(1-q)` factor and the positive coefficients of the `k=2` factor. Nearest-integer inversion on the sequence range is justified once the error is below one half. A global ceiling requires an additional boundary check, as the proof correctly states.

`check_coefficients.py` independently reconstructs the logarithmic modular coefficients through order six, `C_1,C_2` by the exponential coefficient recurrence and Gaussian moments, and the two inverse carrier derivative identities. It imports no producer code; its output is separate. These symbolic checks validate transcription and are not substitutes for the analytic proof.

## Final manuscript transcription

The final `../package/article.tex` was read on the same date and passes. Its new exact generating-function sector formula follows by multiplying the absolutely convergent theta series by the partition series. The bound `|D_r(u)|<=exp(O(sqrt(r)))` uniformly for real u proves the fixed-order sector tail.

The new direct inverse proof has the correct shifts

`Δ1=tT/V`,

`Δ2=t²[TT'/V²-(V+V')T²/(2V³)-C1/V]`.

The residual is `O(t²(1+L)²)`, division by the derivative of size `V/t` gives root-coordinate error `O(t³)`, and multiplication by `N'=V/t²` gives index error `O(t(1+L)²)`. Expanding `N(L+Δ1+Δ2)` yields the stated `Nhat` exactly through the retained terms. This confirms the slightly weaker theorem error. The printed `V5,V6`, displaced `C2` terms and threshold qualifications also match the approved formulas.
