# Independent review of the natural-density bridge

Reviewed the smooth-factor argument in the incoming `mcnew_density_and_grh_transfers` report, especially its finite exchange, extension lemma, and reciprocal-mass-to-natural-density section. The generalized argument is valid for any certified constants tau,g satisfying

W(B)-W(A)-tau W(B\\A) >= g

for every rational-ratio-free A subset S_5, with B integer-ratio-free, and tau at least sum_{r notin S_5} r^(-2).

## Cross-boundary progressions

Replace E intersect S_5 by B and, for each new b in B\\A, delete b*r^2 for integer r having a prime divisor greater than 5. A newly introduced integer-ratio progression must contain such b. If r is 5-smooth, all its members lie in S_5 and contradict B's avoidance. Otherwise b can only be the first member, since its outside prime valuations are zero; its last member was deleted. Total deleted reciprocal mass is at most tau W(B\\A). Hence U_I(Y) >= U_Q(Y)+g for every finite prime cutoff Y>=5.

## Upper bound requires no fiber densities

For each rational-ratio-free E with natural density d, decompose n=h*s uniquely into Y-rough h and Y-smooth s. Harmonic weighting gives

sum_{n<=x,n in E}1/n <= U_Q(Y) sum_{h<=x,h rough}1/h.

By partial summation the left side is (d+o(1))log x; periodicity of roughness at finitely many primes and partial summation give the right harmonic coefficient c_Y. Thus alpha<=c_Y U_Q(Y). No density is assumed for the individual smooth fibers.

## Lower bound uses finite sets first

For a fixed finite integer-ratio-free F subset S_Y, take E_F={h*s : s in F, h Y-rough and squarefree}. CRT at finitely many primes gives the truncated density. The discarded tail is uniformly at most sum_{p>K}p^(-2) in upper density, so the set of allowed h has natural density c_Y v_Y, where v_Y=product_{p>Y}(1-p^(-2)). Every scaled h-set has density c_Y v_Y/s, and they are pairwise disjoint by unique factorization. Since F is finite, E_F has natural density c_Y v_Y W(F).

An integer-ratio progression in E_F would have outside prime valuations forming arithmetic progressions inside {0,1}; those valuations must be constant. Its rough part h is therefore constant, leaving a forbidden progression in F. Hence E_F is admissible.

Finite truncations of any admissible smooth set approximate its reciprocal mass since W(S_Y)=1/c_Y<infinity. Taking the supremum over finite F gives beta>=c_Y v_Y U_I(Y). This step does not assert that an infinite optimizer has natural density, nor that either supremum is attained.

## Conclusion

beta-alpha >= c_Y(U_I-U_Q)-c_Y U_I(1-v_Y)
             >= c_Y*g - sum_{p>Y}p^(-2).

The last step uses c_Y U_I<=1 and 1-product(1-a_p)<=sum a_p. Improved finite-exchange constants do not alter this reasoning. The exact numerical tariff and the two finite certificates remain the responsibility of their explicit checkers; this review concerns the mathematical bridge and density-existence issue only.
