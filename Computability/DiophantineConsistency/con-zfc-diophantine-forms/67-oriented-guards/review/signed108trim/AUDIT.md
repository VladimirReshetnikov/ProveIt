# Independent review: two-bit trim of the split108 signed-ten source

Relative to the already reviewed split108 signed-ten equation, the only mathematical changes are Tnew=Told−2, removal of N² from the binomial argument X, and division of the fixed threshold Y by four. The complete source tuple, layout, all Sun registers and two-root finalizer remain unchanged.

Before binary recovery, all positive weights make the zeroth base-B digit of M0 equal B−1, hence M0>=B−1. Therefore Tnew>=B−3>0. The prior leading-kernel proof gives positive integer Jc and Sc>=N0. It follows that Xnew=Sc(N−1)+Tnew N+N−1>N0(N−1)>3b. The old tight bound Sc+Told<N implies Sc+Tnew<N. The reduced Y remains a positive integer exceeding max(b,256); its fixed power-of-two coefficient exponent remains positive.

After binary recovery, b is an even square and thus divisible by four. Since g=bg0, bit1 of g is zero. The old mask has zeroth base-B digit B−1 and therefore bit1 equal to one; subtracting two clears precisely that bit without borrowing. Consequently g AND(M0−2)=0 is equivalent to g AND M0=0. The higher disjoint blocks and source zero tests are unchanged.

For N=2^u and nonnegative S,T with S+T<N, the two disjoint binary blocks of Xnew=(S+T)N+(N−1−S) give

popcount(Xnew)=u+popcount(T)−[popcount(S)+popcount(T)−popcount(S+T)].

The old N² block contributed exactly one population bit; clearing the unused mask bit removes another. Thus the exact divisibility threshold is Yold/4, not Yold/2. In the revised layout the exponent is2195v−31k−23, matching the emitted coefficient.

All unconditional tail congruences survive. Xnew remains odd, Xnew+1=−g modb², and Xnew=Tnew=0 mod3 because Told=2 mod3. The constructive h and k restrictions therefore retain their proofs. No extra witness or sign assumption has been introduced.

The final proof and circuit were reviewed against the predecessor. Fresh normal and optimized replay logs, a file-hash snapshot and a separate DAG structure receipt accompany this note. No incompatibility was found under the inherited source/compiler and Sun interfaces. This final refinement is519 live operations with exact-degree certificates at3,327,556, compared with520/3,327,948 before trimming. No kernel-verification or global-minimum claim is made.
