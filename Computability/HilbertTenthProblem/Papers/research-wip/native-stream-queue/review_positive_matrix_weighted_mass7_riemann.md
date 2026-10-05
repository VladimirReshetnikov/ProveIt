# Independent review of the weighted seven-coordinate positive lift

The weighted positive7 packet passes independent proof review. It preserves the inherited six-dimensional projective scalar-zero language over one fixed alphabet, uses seven strictly positive integer state coordinates and the unchanged three-operation ordinary-input loader, and supplies exact dyadic total-mass growth. Its history result is conditional on separately certified duration, height and selected-source interfaces. It does not establish a complete universal Diophantine operation count.

The final author note and metadata are pinned in the accompanying reviewer receipt. The full initial note and receipt were read inertly, followed by the amended Section 4. The author retained the one review clarification as numbered Review remark 3. No scientific helper was executed or imported and no source array was evaluated.

## 1. Inherited predicate and the new coordinates

I read all 315 lines of `group_projective_zero_mortality6.md`. The inherited interface uses both projective blocks, the fixed subgroup, and the sum of two squared first coordinates. Its congruence argument removes the negative projective sign; after pulling the subgroup equality back to the embedded original group, the b-exponent and graph-group abelianization remove the remaining stabilizer powers. The source explicitly retains the failure of the single-block replacement. External effective embedding foundations and the unmaterialized fixed universal alphabet remain inherited; this review is not a new external universality audit.

The actual program recipe gives alpha=12*2^(p+1), gamma=12*2^p+1 and tau=alpha*x+gamma, with positive ordinary x and fixed program p. Thus tau>=37 on valid slices. The alphabet is fixed across p and x. The three rows `scaled=alpha*x`, `tau=scaled+gamma`, `tau2=tau*tau` cost 2M+1A, and every row and both program ports are used. Copies and fixed entries in the supplied column are not hidden variable operations.

The displayed inverse of Q is integral and correct: z4=y4, z1=y1-y4, z2=y2+y4, z3=y3+y4, z5=y5+y4 and z6=y6+2y4. Therefore G=Q A Q^(-1) is a fixed integral alphabet. With h=(1,1,1,1,1,2), k=(h,1), D=[I|-h] and E=[I;0], one has DE=I, Dk=0 and sum(k)=8. Direct substitution gives

    D(3,tau,tau^2,2,tau,tau^2,1)^T
      =(2,tau-1,tau^2-1,1,tau-1,tau^2-2)^T=Qv6.

All seven supplied entries are positive. No positivity hypothesis on an arbitrary signed G-trajectory is required. The first row of Q is the inherited accepting row, and h1=1, so the decoded zero is precisely equality of coordinates 1 and 7.

## 2. Positive lift and unchanged zero language

Let R be the maximum absolute row sum over the entire fixed G-alphabet, let kappa be one power of two greater than 28R (or 1 if R=0), and put C=8kappa. For c^T=1^T G and b^T=kappa*1^T-c^T D, the proposed matrix is

    L=E(8G)D+k b^T.

Its entries are integers. The first six columns have corrections to k_i*kappa of magnitude at most 8R+6k_i R<=14k_i R. For the last column, |Gh|<=2R coordinatewise and |c^T h|<=12R, giving a correction at most 16R+12k_i R<=28k_i R. The bottom row has no E-term and satisfies the same weaker bound. Integrality and the strict choice of kappa give L_ij>=k_i>=1, including the separately stated R=0 case.

The three identities are exact:

    DL=8GD,  1^T L=C1^T,  Lk=Ck.

The middle identity follows by cancellation of 8c^T D, using sum(k)=8; the last uses Dk=0. They have different roles and cannot be interchanged with an unproved unweighted row-sum identity.

With the author's unchanged word order, induction gives DL_w=8^n G_w D. Conjugation by Q then proves that terminal coordinate 1 minus coordinate 7 equals 8^n times the inherited scalar. Since 8^n is nonzero, the accepted language is identical. This also covers the empty word, whose difference is 2. Every positive-state step remains strictly positive. There is no duration witness hidden in this operational predicate and no claim that the lifted alphabet represents group inverses or full-operator mortality.

## 3. Exact mass, ratios and the separate positive8 intermediate

The initial mass is H0=2tau^2+2tau+6. Common column sum C gives total mass C^n H0 for every length-n word. Positive integrality implies that every coordinate is at most that mass minus six. C^n is dyadic; its product with H0 is not asserted to be a power of two.

For K=diag(k), P=K^(-1)LK/C is row stochastic and P_ij>=k_j/C. Subtracting this common row leaves a nonnegative matrix of row sum theta=1-1/kappa. Consequently ratio oscillation contracts by theta at every positive-length step. Along an infinite word, the extrema are monotone and have a common limit. The conserved mass fixes the limit as H0/8 for the ratios, equivalently C^(-n)L_w z tends to k H0/8. The kappa=1 case is covered by immediate contraction after one step.

Author Review remark 1 is correct: for G=I6 and kappa=32, rows with k_i=1 sum to 225 and the row with k_i=2 sums to 442, while columns sum to 256. The endpoint difference 2*8^n never vanishes although its normalized value tends to zero. This is an algebraic boundary example, not a universal accepted-input instance.

For the separate positive8 construction, I checked all four block formulas. Their row and column sums both equal 8kappa, the correction bound 15R suffices for positivity, and D8L=8G D8. The scale is 8^n relative to the previous signed G-action and 16^n relative to the older Gram conjugation action. Only zero acceptance is preserved.

**Review remark 1 (author's retained Review remark 3).** The preliminary positive8 section defined R only for a displayed matrix while claiming a common alphabet normalization. I requested that it explicitly take R=max_(sigma,i) sum_j |G_sigma,ij| and then choose one kappa. The author made exactly that clarification and retained the former shorthand and a counterexample to per-letter choices: G=0 could use kappa=1 and G=I7 could use kappa=16, giving different C values 8 and 128. This was a shared-quantifier clarification; the weighted positive7 theorem and every individual letter formula were already valid. The corrected common-alphabet statement passes.

## 4. Conditional history recovery and its carry boundary

I read the full 229-line canonical-history47 proof and the relevant actual range/recovery interfaces in atomic-context lines 40–170 and uniform-context lines 28–165. The earlier canonical method is correctly credited. The atomic source has four range lanes and the preceding uniform source has eight; their old numerical ledgers do not transfer to the seven-coordinate alphabet.

Under independently certified n>=1, P=B^n and B>C^n H0, every actual selected trajectory coordinate through time n lies strictly below B. The positive bound sum_i H_i+slack=P gives each proposed history its canonical length-n base-B expansion. Exact digitwise selected-source products are a separately required interface, even before the histories have been recovered.

In the residual BV_i-H_i-F_i P+z_i, the constant coefficient is z_i-x_i(0), strictly between -B and B. After all earlier digits have been recovered simultaneously, the next coefficient is the actual next state minus the next canonical digit and has the same strict bound. Successive reduction modulo B therefore recovers every digit. The top coefficient recovers the endpoint without a prior endpoint range assumption. Conversely, actual mass below B at every stored position makes the sum of the seven packed histories less than P, giving a strictly positive bound slack. This proves exactly the stated conditional two-way interface. Seven additions for seven history words and the slack is the correct local bound ledger; its comparison and all other history costs remain separate.

The all-size scalar family in author Review remark 2 is correct by direct hand algebra. For every C>=2, set B=2C^2, P=B^2, M0=2C+1, H=M0+BC and Mend=C^2+1. The intermediate relation CM0=B+C produces one carry, and

    (BC-1)H=P*Mend-M0.

All three proposed mass digits lie strictly between 0 and B and H<P/C, but the actual first update is B+C rather than C and the actual final mass is C^2 M0 rather than Mend. For C=8 both sides of the displayed equality are 1064943, as stated. Dyadic C gives dyadic B and P. These examples do not use the special initial mass polynomial of the seven-state loader and are not asserted to extend to a complete selected-matrix certificate. They refute only the stated attempt to infer coefficientwise mass correctness or a valid height bound from the aggregate equation and listed size conditions alone.

Finally, summing vector residuals using the exact partition and column identities does give an aggregate mass residual. Replacing one vector comparison by an independently paid mass comparison is an algebraic reformulation; it is not an unconditional deletion. Author Open question 1 correctly retains the unpaid duration/height, selection and complete-history obligations. No arithmetic frontier improvement follows from this packet alone.

## 5. Provenance and execution limits

Fresh metadata work authenticated all four committed dependency files, their author-declared line-span hashes, byte lengths, line counts and Git blob identities calculated from bytes. It also authenticated the two frozen positive8 predecessor files. Commit identifiers are retained as author-declared provenance; this lane did not check commit membership or run Git. My newly read dependency spans total 813 lines and are individually pinned in the receipt. The earlier positive8 predecessor was independently reviewed fully in this same session.

No supplied, committed, archived, copied, modified or frozen scientific helper was run or imported. No saved source was numerically or symbolically evaluated; no degree propagation, sampling, build or test execution was performed. All algebra above was checked directly in the proof. Only fresh byte/JSON metadata processing ran. The reviewer pair is separate from every author and predecessor artifact, and no repository file was changed.
