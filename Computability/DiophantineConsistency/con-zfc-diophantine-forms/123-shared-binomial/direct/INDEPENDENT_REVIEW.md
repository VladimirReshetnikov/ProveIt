# Independent review of the merged factorial/modular-residue quartic

Date: 24 October 2026. Reviewer: a separately tasked research agent.

## Verdict

The new arithmetic composition is sound and complete over the nonnegative integers. I found no circular use of a binomial, factorial, CRT product, or modular-index meaning in the stated proof. The source calibration remains the explicitly inherited ordinary C222/refutation theorem; no end-to-end formal proof is newly asserted by this review.

I inspected `proof_encoding/build_modular_factorial.py`, its complete `PROOF.md`, the relevant Round14 reciprocal-CRT, factorial-carrier and derived-label proofs, and package108's common modular Pell-root argument (report Sections5--6). I separately expanded every squared residual of the 319-variable equation with a short independent Python coefficient accumulator, without importing a generator, optimizer, or supplied polynomial verifier. It agrees exactly with every delivered coefficient.

The inspected equation has 319 variables, 254 quadratic residuals, 10,283 collected monomials, degree4, and maximum absolute coefficient86,842,335. All319 variables occur in the full polynomial. The SHA256 of the inspected `merged_cantor/natural/equation.json` is `831c22287a4885e812d8828fc74177a5db2c2bdcb803b15b16f7a59c5274c4d6`.

The supplied contraction certificate has its own exact independent replay. This review does not relabel that replay as a new fully independent implementation of the whole natural-domain optimizer; my additional computation is the complete coefficient expansion and census, while the arguments below independently audit the changed mathematics.

## Attribution correction found during review

The factorial fixed-point theorem is already present in the inspected repository, more generally for all natural arguments, in `con-zfc-diophantine-forms/105-bootstrap-certificates/direct/proofs/NEW_RESULTS.md`, Section2. The same proof is copied in `research/power0-output-square-frame/source/bootstrap_NEW_RESULTS.md` and the incoming Synchronized Exponents manuscript. The initial new proof draft called it a new ingredient; I notified the author to correct this wording.

What is new relative to the inspected sources is the literal identification of that theorem's binomial with the reciprocal CRT product, the independent radix bootstrap that makes this identification noncircular, and its materialized composition with the common modular-residue construction. A correct rediscovered proof of a known factorial lemma is useful exposition, but is not a new-lemma claim.

## 1. The simultaneous bootstrap has an independent starting point

The proposed factorial output `F` is initially only natural, but `B=b0+2` is literally at least2. The source sets

    t=t0+16, R=2+t+x+y+F, K=2R,
    N=B^K, q=N^K, V=(F^2+1)^t.

The exact powers have their own common Pell frame; none of them is justified using the binomial meaning of `B`. All their exponents are positive from the actual definitions. The base `F^2+1` is positive even when `F=0`; `B` is at least2; the remaining positive bases are recovered by the exact-power modulus rows and then by the power identities. The frame's `A>W^W` proof depends only on the literal natural atoms and positive bootstrap ordinate.

Thus `N>=2^K` and `q>=2^(4R^2)` are available before interpreting any binomial. For `n=F^2+t` and `0<=j<=t`,

    binom(n,j) <= n^t <= (R^2+R)^t
                  <= 2^(2Rt) < 2^(2R^2) < q.

Here `R^2+R<=4^R` holds for positive integralR by a one-step induction, and `t<R` is literal. There is no use of `F=t!`, `B=binom(F^2+t,t)`, or a derived label bound in this estimate. The exact modular digit can therefore recover the binomial meaning of `B` first.

The ceiling rows

    V+B=BF+r+1, B=r+s+1

give `V+s=BF`, `0<=s<B`, and hence `F=ceil(V/B)`. They also exclude `F=0` because the already recoveredV is positive. This closes the starting point without an assumed factorial bound.

## 2. The fixed-point proof used here is correct

For positiveF and `t>=6`, write

    H_t(F)=t! product_{i=1}^t (F^2+1)/(F^2+i).

A ceiling fixed point gives `H_t(F)<=F<=t!`. If `F<t`, monotonicity in the positive radius gives `H_t(F)>=2^t/(t+1)>t>F`. If `t<=F<t^2`, the product is greater than1/2, so `H_t(F)>t!/2>t^2>F`. Therefore `F>=t^2`. Now the sum of the product defects is strictly below `1/(2F)`, whence

    H_t(F)>t!(1-1/(2F)).

If `t!>=F+1`, this is greater thanF, a contradiction. Thus `F=t!`. Conversely the same estimate atF=t! puts the ratio in `(F-1/2,F]`. Every inequality applies at the actual `t>=16`; there is no missing small case.

Because this is the same `B=binom(F^2+t,t)` as the reciprocal CRT product, one exact binomial now serves both purposes. The old different radius `Ft^2` required two distinct exact binomials.

## 3. Common modular root and free Pell parameter

The six exact powers are literally

    V=(F^2+1)^t, N=B^K, q=N^K,
    Dt=q^t, Dy=q^(y+1), Dx=q^(x+1).

The `t+1` denominator is `Dt1=q Dt`. The builder does not introduce a hidden seventh power, and the retained metadata has six exact requests and15 indexed Pell seeds. Its eleven modular requests consist of one exact binomial and ten divisibility ranges.

The new common-root modulus is the polynomial product

    M=q Dt1 Dx Dy=q^(t+x+y+4).

Every used denominator is among `Dt,Dt1,Dx,Dy`, so `qd|M`; since `N|q`, also `Nd|M`. OmittingDt from the product is valid becauseDt dividesDt1. This addresses all actual moduli; it is not a generic assertion that an arbitrary product happens to dominate every request.

The equation

    2A(q+1)=(q+1)^2+1+M h0

is simultaneously soluble with an arbitrarily large positiveA: `gcd(q+1,M)=1`, so the gcd of its linear coefficient withM is1 or2. In the latter case the right side is even. Therefore the congruence has a full unbounded arithmetic progression of solutions. ChooseA above the previously constructed lower Pell bound and large enough for `h0>=0`; then invoke the inherited simultaneous index-completeness theorem at that chosenA.

The recurrence gives

    R_n=X_n(A)+(q+1-A)Y_n(A)=(q+1)^n mod M.

Also `R_n>0`, because `X_n>(A-1)Y_n` for positive indices; the zero index would give1. Thus the quotient in each modular row is natural whenever the row uses the true least nonnegative residue. The proof does not need the enormous complete numerator `(q+1)^n` as an unknown.

The modular upper indices are positive from their literal definitions: eight positive representatives, a positive encoded index, `F^2+t>=16`, and the derived label expression containing1. Their size need not be bounded by the exact-power frame. Their index is certified by the retained Pell-index equations, including every explicit `index_at_most_Y` row. Treating those upper indices as unbounded modular indices is legitimate; treating them as bounded exact-power inputs would be an unnecessary stronger condition.

## 4. Every remaining digit bound remains strict

The ordinary representative bound is still `n<=9N^2`, with lower index `k<=R-1`. Consequently

    binom(n,j)<=9^k N^(2k)<2^(4R)N^(2k)
              <=N^(2k+2)<=N^K=q.

The strict inequality earlier in the chain survives even when the final exponent comparison is equality. No assumption thatq is strictly larger thanN^K is needed.

For the derived label expressionJ, the retained literal DAG bound gives `J(A)<=N^(3ell)`, `ell=2^22`. The factorial threshold supplies

    3ell(t+1)<=2F<K=2R.

Thus its coefficients through degreet+1 are strictly belowq. This strict final comparison is important: the old parent ended with `N^K<q`, but the newq equalsN^K. The initial draft was checked for this boundary, and the completed proof uses the stronger strict exponent inequality explicitly. J is correctly excluded from the aggregate representative bound; including it there would destroy the stated CRT completeness construction.

## 5. CRT decoding and completeness

AfterF=t! is known, the reciprocal moduli `d_i=1+F^2/i` are positive integers, pairwise coprime, and every prime divisor exceeds t. Their product is exactlyB. WithN=B^K, a prime power `p^(Km)` from one chosen modulus is at least2^K, exceeding the recovered local majorants. The one-sided binomial range lemma gives a bounded residue for each local coordinate and the index. The original index congruence identifies the intended row, and evaluation modulo the prime power gives an actual integer zero of the bounded local polynomial. The additional range ofJ supplies the local label bound. No converse of the one-sided range lemma is used.

For completeness, representatives are chosen at precision `d_i^(2K)`. A falling-factorial numerator then has a factor of valuation at least2Km, while the denominator loses at mostk-1<=K-1; this supplies every desiredN-divisibility. The representatives lie in `[1,N^2]` and their nine-term aggregate has a natural slack. Polynomial congruence also handlesJ, with its separately justified digit bound.

The witness order is coherent: finite refutation; bounded horizon and beta data; F,B,R,K,N,q; CRT representatives; the six exact power values and true modular residues; lower Pell frame; sufficiently largeA in the soluble common-root class; all common index/comparison witnesses; remainder and quotient witnesses; natural arithmetic gates. Every quantity used to chooseA is already fixed, while nothing in the earlier semantic construction requiresA.

The inverse direction recovers arithmetic in the reverse dependency order proved above, then the pairwise-coprime label/Horn-flow certificate and the inherited calibrated calculus refutation. This proves the raw equation's existence equivalence. Exact nonnegative restorations give the same equivalence for the contracted319-variable quartic.

## Conclusion of the independent review

The construction is a concrete improvement of the direct natural quartic tradeoff: 349 to319 unknowns, 268 to254 residuals, 12,768 to10,283 terms, and coefficient height86,915,503 to86,842,335. It does not improve the repository's separate few-variable norm polynomials or its37-integer quartic with large coefficients. The new mathematical contribution should be described as the merged factorial/CRT carrier and independent radix, composed with the credited modular-residue compiler. The squared-radius fixed-point lemma and modular-residue idea individually predate this work.
