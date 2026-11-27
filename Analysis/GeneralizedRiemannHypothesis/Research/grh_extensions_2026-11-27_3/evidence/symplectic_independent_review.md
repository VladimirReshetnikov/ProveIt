# Independent mathematical review: symplectic precision theorem

Reviewed `agent_algebraic_notes.md` against an independent derivation on 27 November 2026. No mathematical gap was found in the main theorem, including residue characteristic two, the stated stable range, and passage to infinite precision. This is a mathematical review, not machine verification.

## Main checks

Let the observed matrix have size 2a by 2b, let c=n-a, and put m=2b and d=m(m-1)/2. Use P(k)=product_{j=1}^k(1-q^{-2j}) and D(v,k)=P(v)/P(v-k).

1. **Coordinate sign.** With gX=(B;C) in the symplectic decomposition associated with Y, M=J_a B. Thus B^T J_a B=-M^T J_a^{-1} M, so the residual is exactly H(M)=J_b+M^T J_a^{-1}M. The plus sign is correct.

2. **Normalization.** There are q^{e(2nm-d)}D(n,b) symplectic m-column frames over R_e. The observation space has q^{2ame} elements. Therefore its likelihood against iid uniform entries is f_{c,m,e}(H)/D(n,b), where f is the Gram density relative to uniform alternating matrices. No extra GL or stabilizer factor is present.

3. **Differential.** At C_0, the image of D -> C_0^T J D+D^T J C_0 is precisely the alternating forms vanishing on ker(C_0) x ker(C_0). In a source basis C_0=[C';0], the upper block is Z-Z^T, the cross block is arbitrary, and the lower block is zero. This gives codimension binomial(dim ker C_0,2) in every characteristic. In characteristic two Z-Z^T still ranges over all zero-diagonal alternating matrices; division by two is never used.

4. **Lifts.** If dim ker C_0 <=1, every specified next target digit has q^{2cm-d} lifts. Iteration works in arbitrary equal or mixed characteristic DVRs, because pi^{2j} vanishes modulo pi^{j+1} for j>=1. Contributions from such residue matrices are independent of all higher target digits.

5. **Embedding counts.** A rank-2r alternating form on an h-dimensional domain has q^{2ch-binomial(h,2)}D(c,h-r) injective isometric maps to the ambient symplectic space when h-r<=c. Splitting r symplectic pairs and choosing the radical vectors gives this expression. For a prescribed one-dimensional kernel inside the radical, passing to the quotient gives exactly one such embedding problem, with no missing quotient-basis factor.

## Independent unified sign inequality

Suppose the residual reduction has rank 2r<m. Put t=m-2r>=2 and v=c-m+r+1. In the stable range c>=m-1, v>=0. The normalized contribution of just kernel dimensions zero and one is

    L = product_{j=v+1}^c(1-q^{-2j})
        * [1+q^{-2v}(q^{-1}+...+q^{-(t-1)})].

This formula also includes the boundary c=m-1,r=0: the full-rank contribution is zero and the kernel-one contribution gives exactly the displayed expression with v=0.

Set u=q^{-2v}<=1. The finite product is strictly greater than 1-u/(q^2-1). Hence

    L > (1-u/(q^2-1))*(1+u/q)
      = 1 + u*(q^2-q-1-u)/(q*(q^2-1))
      >= 1.

The last numerator is nonnegative for q>=2 and 0<u<=1; its only borderline is q=2,u=1, and the preceding product inequality is strict. Thus f(H)>=L>1>D(n,b). This independently verifies the core likelihood sign.

For nonsingular residual reduction, all solutions are injective and smooth, and f(H)=D(c,b). Since a>=1, D(c,b)/D(n,b)<1. Thus the negative part of the signed measure is exactly a constant multiple of uniform measure on the nonsingular residual event. Its mass is (1-alpha)*beta at every precision.

## Infinite precision and transpose symmetry

Finite quotients generate the Borel sigma algebra of the compact matrix space. Conditional expectations with respect to those quotients show that total variation on the limit is the supremum of finite-precision distances. Consequently the identical finite distances give the same infinite distance, and the same residue event attains it.

Under exchanging X and Y and sending g to g^{-1}, the observed matrix becomes -M^T. Sylvester's determinant identity makes the two residual-nonsingularity events equivalent. Also

    D(n-a,b)/D(n,b)
      = P(n-a)P(n-b)/(P(n-a-b)P(n))
      = D(n-b,a)/D(n,a).

Either stated stable inequality implies n>=a+b, so these expressions are defined. Thus the symmetric range extension is valid with the original formula.

## Optional Fourier density: independently verified

For a primitive additive character of R_e and the upper-triangular pairing on alternating matrices,

    f_{c,m,e}(H)=sum_{W in Alt_m(R_e)}
         q^{-c length(im W)} psi_e(-<W,H>).

Indeed one symplectic row pair x,y contributes x y^T-y x^T, whose pairing is x^T W y. Averaging in y, then x, gives |ker W|/|R_e^m|. This proof is valid also in characteristic two.

Put Z_e(c,m)=sum_W q^{-c length(im W)} and Z_0=1. If A_m(r) counts rank-2r alternating matrices over F_q, then

    Z_e(c,m)-Z_{e-1}(c,m)
      =sum_{r>=1} A_m(r) q^{-2cr}
       q^{-r(2c-2m+2r+1)(e-1)} Z_{e-1}(c,m-2r).

For a fixed rank-2r residue matrix, choose an invertible alternating leading block and use its Schur complement. The complement is pi T, the number of choices for the other blocks is q^{(e-1)(binomial(m,2)-binomial(m-2r,2))}, and the image length is 2re+length(im T). These produce exactly the displayed recursion. Alternating block elimination works in characteristic two.

At c>=m-1 every exponent r(2c-2m+2r+1) is at least r(2r-1)>0. Induction on m gives bounded Z_e and summable conductor tails. With compatible additive characters this proves absolute uniform convergence of the Fourier series and a continuous infinite-precision density.

An optional additional conclusion follows: if f_e is inflated to the infinite ring, then

    ||f_infinity-f_e||_infinity = Z_infinity(c,m)-Z_e(c,m).

The upper bound is the absolute coefficient tail; equality holds at H=0. Writing lambda=2c-2m+3, the recursion gives

    ||f_infinity-f_e||_infinity
      ~ [A_m(1) q^{-2c} Z_infinity(c,m-2)/(1-q^{-lambda})]
          q^{-lambda e}.

The r=1 summand dominates; every r>=2 has a strictly greater exponent. This sharper quantitative statement is not needed for the total-variation theorem.

## Wording limitations to preserve

- The residue event preserves optimal equal-prior testing and total variation. It is not claimed to be a sufficient statistic for every prior, loss function, or repeated-sample experiment.
- The stable range is sufficient; no necessity or sharpness is proved.
- The finite algorithm for beta and the Fourier formula are exact, but neither should be advertised as a simple closed product formula for every residual.
- The result is unconditional local algebra. It should not be described as a consequence requiring RH or GRH.


# Final manuscript audit: bounded density and sharp convergence

The complete final `symplectic_precision.tex` was independently reviewed, including the added bounded-density threshold, the sharp uniform convergence exponent, and the cheaper rank-chain computation. The main conclusions remain valid. No substantive mathematical correction is required.

## Exact threshold

For integers s>=2 and c>=0, the proof establishes that the Gram law has an essentially bounded Haar density exactly when c>=s-1.

- **Sufficiency:** the conductor recursion has exponents lambda_r=r(2c-2s+2r+1). In this range lambda_r>=r(2r-1)>0. Every lower-dimensional factor Z_e(c,s-2r) is uniformly bounded by induction, using the already-defined bases s=0,1. Summation over the finitely many r and over e proves that the sum of absolute Fourier coefficients is finite. Fourier inversion therefore gives a continuous density with the correct cylinder integrals.
- **Necessity:** if c<=s-2, then lambda_1=2c-2s+3<=-1. Since A_s(1)>0 for every s>=2, the r=1 term makes Z_e(c,s)-Z_{e-1}(c,s) grow without bound. At H=0 all Fourier characters equal one, so f_e(0)=Z_e. This is exactly the Gram probability of the ball pi^e Alt_s(O), divided by that ball's Haar measure. A bounded density would uniformly bound all such averages, giving the contradiction. This argument does not presume absolute continuity outside the bounded range.

The inverse of a nonsingular alternating matrix is alternating over a local ring, also when two is not invertible: symplectic Gram-Schmidt brings the matrix to the standard alternating matrix by congruence, and inversion preserves that congruence description. Thus the alternating Schur complement used in the recursion is valid in both equal and mixed residue characteristic two.

## Sharp exponent and coefficient

Let lambda=2c-2s+3. Under c>=s-1 one has lambda>=1 and

    lambda_r=r*lambda+2r(r-1).

Every r>=2 therefore has strictly greater decay exponent than r=1. The lower-dimensional factor in that first term tends to Z_infinity(c,s-2)>0. Consequently

    Z_e-Z_{e-1}
      ~ A_s(1) q^(-2c) Z_infinity(c,s-2) q^(-lambda(e-1)).

Summing from e+1 onward gives exactly the manuscript's coefficient

    [A_s(1) q^(-2c) Z_infinity(c,s-2)/(1-q^(-lambda))]
        q^(-lambda e).

There is no missing shift of e or extra power of q. Absolute Fourier summation bounds the uniform density error by this coefficient tail, and evaluation at H=0 attains the bound, proving the exact uniform-error identity before taking asymptotics.

At q=2 and c=s-1 the exponent is lambda=1 and the coefficient is finite and strictly positive. The borderline in the separate likelihood-sign inequality is also valid because the finite-product estimate is strictly stronger than its infinite geometric lower bound.

## Bases s=0 and s=1

The section explicitly assumes s>=2. Values s=0 and s=1 occur only as induction bases: their alternating spaces consist of one point, every density and every Z_e is one, and the approximation error is identically zero. The nonzero-tail asymptotic with A_s(1) is not a statement for those bases. For maximal standalone clarity the theorem could begin 'Let s>=2 and c>=0 be integers,' but the existing section setup already supplies this restriction.

For s=2 the recursion reduces to an exact geometric sum with Z_e(c,0)=1 and A_2(1)=q-1, so both the threshold c>=1 and the displayed leading constant agree directly with the elementary one-pair case.

## Final main theorem and computation

The combined testing range n>=a+b+min(a,b)-1 is exactly the union of the two orientation-specific sufficient ranges. If only the transposed orientation is stable, its continuous likelihood transfers through the homeomorphism M -> -M^T. There is no need to claim that the original-orientation Gram law is globally bounded outside its own range.

The added rank-chain formula for beta is correct. A rank increase occurs exactly when the projected update vectors in the radical quotient are independent. A rank decrease requires both vectors in the current column space and one prescribed nonzero symplectic pairing, yielding the displayed probabilities. Starting at J_b and adding a independent row pairs gives the residual nonsingularity probability after a steps. The sign change in subtracting rather than adding a decomposable form preserves the uniform distribution of the update.

Finally, the manuscript correctly distinguishes the sharp threshold for bounded Gram densities from the merely sufficient threshold for total-variation persistence. The former does not establish sharpness of the latter.
